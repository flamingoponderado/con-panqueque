import ConPanqueque.T.Ind.ParamLevels
import ConPanqueque.T.Core.IsPropType

/-!
# The block's result sort, and whether it is `Prop`

`readBlock` reads the first type's result sort: past its `nP + nIdx₀` binders (`stripPis`), a `sort`'s level,
the zero level otherwise; the block is propositional when that level equals zero (`lvlEq?`, undecided
counting as not).  `resSort(n, T)` returns the level, `isPropL(u)` the flag.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI
open ConPanqueque.T.Big

/-- `readBlock`'s result sort. -/
def resSortT (n : Nat) (T : EIdx) : AM LIdx := do
  match ← stripPis n T with
  | some q => do
    match ← view q.2 with
    | .sort s => pure s
    | _ => zeroLevel
  | none => zeroLevel

/-- A decided `true`. -/
def optTrue : Option Bool → Bool
  | some true => true
  | some false => false
  | none => false

/-- `readBlock`'s flag. -/
def isPropT (s : LIdx) : AM Bool := do
  let z ← zeroLevel
  let eq ← lvlEq? s z
  pure (optTrue eq)

def rsN := ofString "rs_n"
def rsT := ofString "rs_t"
def rsR := ofString "rs_r"
def rsW := ofString "rs_w"
def rsU := ofString "rs_u"
def fResSort := ofString "resSort"

def rsParams : List MlS := [rsN, rsT]
def rsLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, rsR, rsW, rsU]

def rsZero (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rsU (.load .one (.const (ecell C (C.PO + pinCount + 1))))) (.return (vv rsU))

def rsBody (C : Ctx) : ProgHOL 64 := prologue rsLocals
  (.seq (.call (some (some (.local, rsR), none)) fStripPis [vv rsN, vv rsT])
  (.ite (.cmp .equal (vv rsR) (.const 0)) (rsZero C)
  (.seq (.assign .local rsW (.load .one (vv rsR)))
  (.seq (.assign .local rsW (.load .one (.op .add [vv rsR, .shift .lsl (vv rsW) (.const 3)])))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv rsW)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 2))
    (.seq (.assign .local rsU (.load .one (vv lRp))) (.return (vv rsU)))
    (rsZero C)))))))))

section
variable {σ : Type}

theorem rs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rsLocals → (ctxEnv C ++ rsParams.zip vals).get x = none :=
  Knot.params_none C rsLocals rsParams vals (by decide) (by decide)

/-- A level handle that denotes, in a bigger heap. -/
def PostRS (C : Ctx) (u : LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW u ∧ SR (ctxH C H') s' st ∧ (denoteL s'.store.ls u).isSome = true

theorem postRS_locals (C : Ctx) : ∀ (a : LIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRS C a w s' st → PostRS C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hs, hd⟩ => ⟨H', hp, hw, sr_of_eq hs rfl rfl rfl rfl, hd⟩

theorem rsZero_spec (C : Ctx) (hok : CtxOK C) (H H1 : List (BitVec 64)) (hp : H <+: H1) (s1 : AState) (Γ : Env)
    (M : Mem) (hD : rsU ∈ ctxLocals ++ rsLocals) :
    SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ M (ctxLocals ++ rsLocals)) (rsZero C) s1 zeroLevel (PostRS (ctxH C H)) := by
  refine specR_congr (m' := pinZeroLevel >>= fun z => pure z) (by simp [zeroLevel]) ?_
  have hokX := ctxOK_H hok H1
  refine specR_pinXI (C := ctxH C H1) hokX pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H1) hokX hp) (pin_zeroLevel_cell hokX) rsU hD ?_
  exact specR_returnI _ (Enc.idxW C.pins.zeroLevel) (by simp [sev, Env.get_cons]; rfl)
    (fun t ht => ⟨H1, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, sr_zeroSome (C := ctxH C H1) ht.sr⟩)

/-- **`resSort`**. -/
theorem rs_spec (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (n : Nat) (hn : n < 2 ^ 64) (T : EIdx) (H : List (BitVec 64)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rsParams.zip [BitVec.ofNat 64 n, Enc.idxW T])) (rsBody C) s (resSortT n T)
      (PostRS (ctxH C H)) := by
  refine specR_prologue (postRS_locals _) (rs_none _ _) ?_
  unfold resSortT
  refine specR_callNIH (C := ctxH C H) rsR fStripPis [pFu, pH] [vv rsN, vv rsT] (stripBody C fStripPis 6)
    [BitVec.ofNat 64 n, Enc.idxW T] (by decide) rfl (by simp +decide [ctxLocals, rsLocals]) hcs
    ⟨by simp +decide [sev, Env.get, rsParams, ctxEnv], by simp +decide [sev, Env.get, rsParams, ctxEnv], trivial⟩
    (PostSP (ctxH C H)) (fun o w s' H' => (o = none → w = 0) ∧
      ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact stripPis_spec C hok hcs n hn H s T _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun o w s1 H1 hp1 ⟨hnone, hsm⟩ => ?_)
  have hpH : H <+: H1 := hp1
  rcases o with _ | ⟨tys, b⟩
  · have e0 := hnone rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact rsZero_spec C hok H H1 hpH s1 _ _ (by simp +decide [ctxLocals, rsLocals])
  obtain ⟨ob', rfl, hblk⟩ := hsm tys b rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hblk
  have hHN' : H1.length ≤ C.HN := hHN
  have hne : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hl0 : (ctxH C H1).H[ob']? = some (BitVec.ofNat 64 (tys.length + 1)) := by
    show H1[ob']? = _; rw [hblk.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H1) rsW (vv rsR) ob' _ hl0 (by simp +decide [ctxLocals, rsLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  have hbw : (ctxH C H1).H[ob' + 1 + tys.length]? = some (Enc.idxW b) := by
    show H1[ob' + 1 + tys.length]? = _
    have := hblk.2 tys.length (by simp); simpa using this
  refine UD.specR_heapLoadI' (C := ctxH C H1) rsW _ (ob' + 1 + tys.length) _ hbw (by simp +decide [ctxLocals, rsLocals])
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C ob' + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv rsW) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine specR_viewP (C := ctxH C H1) b (by simp) (by simp +decide [Env.get, Env.get_cons] <;> rfl)
    (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  refine specR_runBind (show ConRon.Arena.view b s1 = .ok (v, s1) by rw [view_run, hv]) ?_
  have htg := ConPanqueque.T.WC.sev_eqNatB (Γ := (lRp, P) :: (lRn, BitVec.ofNat 64 (encEView v).length) ::
    (lDt, BitVec.ofNat 64 b.tier.toNat) :: (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 b.idxNat) ::
    (lDh, Enc.idxW b) :: (lFl, C.FLe) :: (rsW, Enc.idxW b) :: (rsW, BitVec.ofNat 64 (tys.length + 1)) ::
    (rsR, cellA C ob') :: (ctxEnv (ctxH C H) ++ rsParams.zip [BitVec.ofNat 64 n, Enc.idxW T]))
    (a := vv lDg) (b := .const 2) (x := v.tagN) (y := 2) (by cases v <;> simp [ENodeView.tagN]) (by omega)
    (by simp [sev, Env.get_cons]) rfl
  cases v with
  | sort u =>
    refine specR_ifI _ _ htg (fun _ => ?_) (fun h => by simp [ENodeView.tagN, boolW] at h)
    refine specR_loadI' rsU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp [sev, Env.get_cons])
      (by simp) (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
    exact specR_returnI _ (Enc.idxW u) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H1, hpH, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, sr_sortSome ht.sr hv⟩)
  | _ =>
    refine specR_ifI _ _ htg (fun h => by simp [ENodeView.tagN, boolW] at h) (fun _ => ?_)
    exact rsZero_spec C hok H H1 hpH s1 _ _ (by simp +decide [ctxLocals, rsLocals])

end

def ipxU := ofString "ipx_u"
def ipxZ := ofString "ipx_z"
def ipxQ := ofString "ipx_q"
def fIsPropL := ofString "isPropL"

def ipParams : List MlS := [ipxU]
def ipLocals : List MlS := [ipxZ, ipxQ]

def ipBody (C : Ctx) : ProgHOL 64 := prologue ipLocals
  (.seq (.assign .local ipxZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, ipxQ), none)) LLeq.fEqv [vv ipxU, vv ipxZ])
    (.return (.cmp .equal (vv ipxQ) (.const 2)))))

section
variable {σ : Type}

theorem ip_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ipLocals → (ctxEnv C ++ ipParams.zip vals).get x = none :=
  Knot.params_none C ipLocals ipParams vals (by decide) (by decide)

/-- **`isPropL`**: the level equals zero (the comparison as a hypothesis, as `isPropType` takes it). -/
theorem ip_spec (C : Ctx) (hok : CtxOK C)
    (hcE : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one))
    (H : List (BitVec 64)) (s : AState) (u : LIdx) (hden : (denoteL s.store.ls u).isSome = true)
    (hLE : (denoteL s.store.ls C.pins.zeroLevel).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW C.pins.zeroLevel)]) LLeq.eqvBody s
        (lvlEq? u C.pins.zeroLevel) (LLeq.PostOB (ctxH C H))) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ipParams.zip [Enc.idxW u])) (ipBody C) s (isPropT u) (PostB (ctxH C H)) := by
  refine specR_prologue (Knot.postB_locals _) (ip_none _ _) ?_
  unfold isPropT
  have hokX := ctxOK_H hok H
  refine specR_congr (m' := pinZeroLevel >>= fun z => lvlEq? u z >>= fun eq => pure (optTrue eq))
    (by simp [zeroLevel]) ?_
  refine specR_pinXI (C := ctxH C H) hokX pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H) hokX hp) (pin_zeroLevel_cell hokX) ipxZ (by decide) ?_
  refine specR_fact (fun t ht => sr_zeroSome (C := ctxH C H) ht.sr) (fun hz => ?_)
  refine specR_callNIH (C := ctxH C H) ipxQ LLeq.fEqv [LEq.pLa, LEq.pLb] [vv ipxU, vv ipxZ] LLeq.eqvBody
    [Enc.idxW u, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hcE
    ⟨by simp +decide [sev, Env.get, Env.get_cons, ipParams, ctxEnv], by simp [sev, Env.get_cons]; rfl, trivial⟩
    (LLeq.PostOB (ctxH C H)) (fun o w _ H' => H' = H ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun v hv _ hlk => Knot.specR_of_pre v (pre_of_lookups hv [LEq.pLa, LEq.pLb] _ rfl hlk) (hLE hz))
    (fun o w s1 H1 _ ⟨eH, hw⟩ => ?_)
  subst eH; subst hw
  exact specR_returnI _ (boolW (optTrue o))
    (by rcases o with _ | _ | _ <;> simp [sev, Env.get_cons, LLeq.obW, boolW, optTrue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun t ht => ⟨H1, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
