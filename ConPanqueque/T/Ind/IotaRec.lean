import ConPanqueque.T.Ind.DropVars

/-!
# What every rule of a recursor reads off its type (`iotaRecMajor`)

An `IotaRec` is a block `[pre, minors, us, params]`: the rule prefix (cells from `pre + 1`, as `stripPis` leaves
them), the minor premises' positions, the major's levels and its parameters (the index variables dropped).
`tsub(a, b)` is the truncated difference.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI
open ConPanqueque.T.WC ConPanqueque.T.ExS ConPanqueque.T.ExG

def tsA := ofString "ts_a"
def tsB := ofString "ts_b"
def fTSub := ofString "tsub"

def tsBody : ProgHOL 64 := prologue []
  (.ite (.cmp .lower (vv tsA) (vv tsB)) (.return (.const 0)) (.return (.op .sub [vv tsA, vv tsB])))

section
variable {σ : Type}

theorem ts_spec (C : Ctx) (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (H : List (BitVec 64)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s [(tsA, BitVec.ofNat 64 a), (tsB, BitVec.ofNat 64 b)]) tsBody s
      (pure (a - b)) (PostN (ctxH C H)) := by
  refine specR_prologue (postN_locals _) (fun x hx => by simp at hx) ?_
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower _ (vv tsA) (vv tsB) a b (by simp +decide [sev, Env.get, ctxEnv])
    (by simp +decide [sev, Env.get, ctxEnv]) (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
  · have c : a < b := by by_cases c : a < b; exact c; simp [bw, c] at h
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by rw [Nat.sub_eq_zero_of_le (by omega)]; rfl,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have c : ¬ a < b := by intro c; simp [bw, c] at h
    exact specR_returnI _ (BitVec.ofNat 64 (a - b))
      (by simp +decide [sev, Env.get, ctxEnv]; exact ofNat_sub_small a b (by omega) (by omega))
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- A `tsub` call: the difference, the state and heap kept. -/
theorem rb_tsub (C : Ctx) (hc : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one))
    (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (H : List (BitVec 64)) (s : AState)
    {β : Type} {Γ : Env} {D : List MlS} {M : Mem} {rest : ProgHOL 64} {k : Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (ea eb : ExpHOL 64) (hx : x ∈ D)
    (hea : sev Γ ea = some (BitVec.ofNat 64 a)) (heb : sev Γ eb = some (BitVec.ofNat 64 b))
    (hk : ∀ H1, H <+: H1 → SpecR (Inv (ctxH C H1) s ((x, BitVec.ofNat 64 (a - b)) :: Γ) [] D) rest s (k (a - b)) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (.seq (.call (some (some (.local, x), none)) fTSub [ea, eb]) rest) s
      (pure (a - b) >>= k) R :=
  specR_callNIH (C := ctxH C H) x fTSub [tsA, tsB] [ea, eb] tsBody [BitVec.ofNat 64 a, BitVec.ofNat 64 b] (by decide) rfl
    hx hc ⟨hea, heb, trivial⟩
    (fun r w s' st => (pure (a - b) : AM Nat) s = .ok (r, s') ∧ PostN (ctxH C H) r w s' st)
    (fun r w s' H' => w = BitVec.ofNat 64 r ∧ r = a - b ∧ s' = s)
    (fun r w s' st ⟨hr, H', hp', hw, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact ⟨H', hp', ⟨hw, hr.1.symm, hr.2.symm⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [tsA, tsB] _ rfl hlk)
      (ts_spec C a b ha hb H s)))
    (fun r w s' H' hp' ⟨hw, hr, hs'⟩ => by subst hw; subst hr; subst hs'; exact hk H' hp')

end

section
variable {σ : Type}

theorem minorsFrom_bound (pre : List EIdx) (mot : Nat) : ∀ n q (s s' : AState) (r : List Nat), pre.length - q = n →
    minorsFrom pre mot q s = .ok (r, s') → ∀ x ∈ r, x < pre.length := by
  intro n
  induction n with
  | zero =>
    intro q s s' r hn hr x hx
    rw [minorsFrom, if_neg (by omega)] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr; simp at hx
  | succ n ih =>
    intro q s s' r hn hr x hx
    rw [minorsFrom, if_pos (by omega)] at hr
    obtain ⟨b, s1, -, h1⟩ := bind_ok_inv' hr
    obtain ⟨rest, s2, h2, h3⟩ := bind_ok_inv' h1
    have ihr := ih (q + 1) s1 s2 rest (by omega) h2
    cases b
    · simp only [Bool.false_eq_true, ite_false, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, -⟩ := h3; exact ihr x hx
    · simp only [ite_true, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, -⟩ := h3
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact ihr x hx

/-- An `IotaRec` at `o`: the prefix block (`stripPis`'s, its count one more than the prefix), the minors, the
major's levels and its parameters. -/
def IotaRecRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (rr : IotaRec) : Prop :=
  (∃ op, H[o]? = some (cellA C op) ∧ H[op]? = some (BitVec.ofNat 64 (rr.pre.length + 1)) ∧ EElems H op rr.pre) ∧
  (∃ om, H[o + 1]? = some (cellA C om) ∧ BlkAt H om (rr.minors.map (BitVec.ofNat 64))) ∧
  H[o + 2]? = some (Enc.idxW rr.us) ∧
  (∃ opp, H[o + 3]? = some (cellA C opp) ∧ BlkAt H opp (rr.params.map Enc.idxW)) ∧
  ∀ j (hj : j < rr.minors.length), rr.minors[j] < 2 ^ 63

theorem iotaRecRep_mono {C : Ctx} {H H' : List (BitVec 64)} {o : Nat} {rr : IotaRec} (h : IotaRecRep C H o rr)
    (hp : H <+: H') : IotaRecRep C H' o rr := by
  obtain ⟨⟨op, a1, a2, a3⟩, ⟨om, b1, b2⟩, c, ⟨opp, d1, d2⟩, e⟩ := h
  exact ⟨⟨op, get_prefix a1 hp, get_prefix a2 hp, fun j hj => get_prefix (a3 j hj) hp⟩, ⟨om, get_prefix b1 hp,
    blkAt_mono b2 hp⟩, get_prefix c hp, ⟨opp, get_prefix d1 hp, blkAt_mono d2 hp⟩, e⟩

/-- An optional `IotaRec`: `0` for none. -/
def PostIR (C : Ctx) (o : Option IotaRec) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ rr, o = some rr → ∃ ob, w = cellA C ob ∧ IotaRecRep C H' ob rr

theorem postIR_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostIR C a w s' st → PostIR C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

def irP := ofString "ir_p"
def irL := ofString "ir_l"
def irD := ofString "ir_d"
def irN := ofString "ir_n"
def irK := ofString "ir_k"
def irMo := ofString "ir_mo"
def irMs := ofString "ir_ms"
def irDm := ofString "ir_dm"
def irDh := ofString "ir_dh"
def irU := ofString "ir_u"
def irA := ofString "ir_a"
def irC := ofString "ir_c"
def irM := ofString "ir_m"
def irPs := ofString "ir_ps"
def irO := ofString "ir_o"
def fIotaRecMajor := ofString "iotaRecMajor"

def irmParams : List MlS := [irP, irL, irD, irN, irK]
def irmLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, irMo, irMs, irDm, irDh, irU, irA, irC, irM, irPs, irO]

def irmBody (C : Ctx) : ProgHOL 64 := prologue irmLocals
  (.seq (.call (some (some (.local, irMo), none)) fTSub [.op .add [vv irL, vv irN], vv irK])
  (.seq (.call (some (some (.local, irMs), none)) fMinorsFrom [vv irP, vv irL, vv irMo, .const 0])
  (.seq (.assign .local irDm (.load .one (.op .add [vv irD, .op .add [.panop .mul [vv irN, .const 8], .const 8]])))
  (.seq (.call (some (some (.local, irDh), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv irDm])
  (.ite (tagIsE irDh 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv irDh)) (.seq eViewP
    (.seq (.assign .local irU (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.call (some (some (.local, irA), none)) fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv irDm])
    (.seq (.assign .local irC (.load .one (vv irA)))
    (.seq (.call (some (some (.local, irM), none)) fTSub [vv irC, vv irN])
    (.seq (.call (some (some (.local, irPs), none)) fDropMap [vv irA, .const 0, vv irM, vv irN])
      (alloc4 C irO (vv irP) (vv irMs) (vv irU) (vv irPs) (.return (vv irO)))))))))))
    (.return (.const 0)))))))

end

section
variable {σ : Type}

theorem irm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ irmLocals → (ctxEnv C ++ irmParams.zip vals).get x = none :=
  Knot.params_none C irmLocals irmParams vals (by decide) (by decide)

/-- The functions `iotaRecMajor` calls, and theirs. -/
structure IRCodes (C : Ctx) : Prop where
  irm : C.code.lookup fIotaRecMajor = some (irmParams.map (fun p => (p, ShapeHOL.one)), irmBody C, .one)
  ts : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one)
  mn : C.code.lookup fMinorsFrom = some (mnParams.map (fun p => (p, ShapeHOL.one)), mnBody C, .one)
  im : C.code.lookup fIsMinor = some (imParams.map (fun p => (p, ShapeHOL.one)), imBody, .one)
  pt : C.code.lookup fPiTele = some ([(pFu, .one), (pH, .one)], ptBody C fPiTele, .one)
  ga : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)
  dm : C.code.lookup fDropMap = some (dmParams.map (fun p => (p, ShapeHOL.one)), dmBody C, .one)
  dv : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ifa : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  ic : Codes C (body C)

/-- **`iotaRecMajor`**, the rule prefix the recursor's first `pre.length` binders. -/
theorem irm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : IRCodes C)
    (pre doms : List EIdx) (op od nIdx k : Nat) (hL : pre.length < 2 ^ 58) (hN : nIdx < 2 ^ 58) (hk : k < 2 ^ 63)
    (hnd : nIdx < doms.length) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hpc : H[op]? = some (BitVec.ofNat 64 (pre.length + 1))) (hpre : EElems H op pre) (hdoms : EElems H od doms)
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (irmParams.zip [cellA C op, BitVec.ofNat 64 pre.length, cellA C od,
      BitVec.ofNat 64 nIdx, BitVec.ofNat 64 k])) (irmBody C) s (iotaRecMajor pre doms nIdx pre.length k)
      (PostIR (ctxH C H)) := by
  refine specR_prologue (postIR_locals _) (irm_none _ _) ?_
  unfold iotaRecMajor
  let Γ0 : Env := ctxEnv (ctxH C H) ++ irmParams.zip [cellA C op, BitVec.ofNat 64 pre.length, cellA C od,
    BitVec.ofNat 64 nIdx, BitVec.ofNat 64 k]
  have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ irmLocals → z ∉ irmLocals →
      Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
    have hne : z ≠ x := fun e => hz (e ▸ hx)
    simp only [Env.get_cons, hne, ite_false]
  have pk : ∀ (Γ : Env), (∀ z, z ∉ irmLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ irmParams → ∀ v,
      Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
    have hyl : y ∉ irmLocals := by
      simp only [irmParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl <;> decide
    simp only [sev, sev_vv, hΓ y hyl, h]
  have vP : Γ0.get irP = some (cellA C op) := by simp +decide [Γ0, Env.get, irmParams, ctxEnv]
  have vL : Γ0.get irL = some (BitVec.ofNat 64 pre.length) := by simp +decide [Γ0, Env.get, irmParams, ctxEnv]
  have vD : Γ0.get irD = some (cellA C od) := by simp +decide [Γ0, Env.get, irmParams, ctxEnv]
  have vN : Γ0.get irN = some (BitVec.ofNat 64 nIdx) := by simp +decide [Γ0, Env.get, irmParams, ctxEnv]
  have vK : Γ0.get irK = some (BitVec.ofNat 64 k) := by simp +decide [Γ0, Env.get, irmParams, ctxEnv]
  -- the motive's position
  let mot := pre.length + nIdx - k
  refine specR_pureBind mot ?_
  refine rb_tsub C hc.ts (pre.length + nIdx) k (by omega) hk H s irMo _ _ (by simp +decide [ctxLocals, irmLocals])
    (by
      have e : sev Γ0 (.op .add [vv irL, vv irN]) = some (BitVec.ofNat 64 (pre.length + nIdx)) := by
        simp only [sev, sev_vv, vL, vN]; simp; exact ofNat_add_small _ _ (by omega)
      exact e)
    (by have e : sev Γ0 (vv irK) = some (BitVec.ofNat 64 k) := by simp only [sev, sev_vv, vK]
        exact e)
    (fun H1 hp1 => ?_)
  let Γ1 : Env := (irMo, BitVec.ofNat 64 mot) :: Γ0
  have hΓ1 : ∀ z, z ∉ irmLocals → Γ1.get z = Γ0.get z := fun z hz => cnl (by decide) hz
  have hp01 : C.H <+: H1 := hp.trans hp1
  -- the minors
  refine specR_callNIH (C := ctxH C H1) irMs fMinorsFrom mnParams [vv irP, vv irL, vv irMo, .const 0] (mnBody C)
    [cellA C op, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 mot, BitVec.ofNat 64 0] (by decide) rfl
    (by simp +decide [ctxLocals, irmLocals]) hc.mn
    ⟨pk Γ1 hΓ1 irP (by decide) _ vP, pk Γ1 hΓ1 irL (by decide) _ vL, by simp [Γ1, sev, Env.get_cons] <;> rfl, rfl, trivial⟩
    (fun ms w s' st => minorsFrom pre mot 0 s = .ok (ms, s') ∧ PostNL (ctxH C H1) ms w s' st)
    (fun ms w _ H' => (∃ om, w = cellA C om ∧ BlkAt H' om (ms.map (BitVec.ofNat 64))) ∧ ∀ x ∈ ms, x < pre.length)
    (fun ms w s' st ⟨hr, H', hp', hsr, h⟩ => ⟨H', hp', ⟨h, minorsFrom_bound pre mot _ 0 s s' ms rfl hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mnParams _ rfl hlk)
      (mn_spec C hok hc.mn hc.im hc.pt hc.ga pre op mot (by omega) (by omega) pre.length 0 H1 s hp01
        (fun j hj => get_prefix (hpre j hj) hp1) (by omega) (by omega))))
    (fun minors wm s2 H2 hp2 ⟨⟨om, hwm, hmb⟩, hmlt⟩ => ?_)
  subst hwm
  have hp12 : H1 <+: H2 := hp2
  have hHH2 : H <+: H2 := hp1.trans hp12
  let Γ2 : Env := (irMs, cellA C om) :: Γ1
  have hΓ2 : ∀ z, z ∉ irmLocals → Γ2.get z = Γ0.get z := fun z hz => by
    simp only [Γ2]; rw [cnl (by decide) hz]; exact hΓ1 z hz
  -- the major's domain
  have hget : exprGetD doms nIdx = pure doms[nIdx] := by simp [exprGetD, List.getElem?_eq_getElem hnd]
  rw [hget, pure_bind]
  have hdm : (ctxH C H2).H[od + 1 + nIdx]? = some (Enc.idxW doms[nIdx]) := get_prefix (hdoms nIdx hnd) hHH2
  refine UD.specR_heapLoadI' (C := ctxH C H2) irDm _ (od + 1 + nIdx) _ hdm (by simp +decide [ctxLocals, irmLocals])
    (by
      have gD := pk Γ2 hΓ2 irD (by decide) _ vD
      have gN := pk Γ2 hΓ2 irN (by decide) _ vN
      have e : sev Γ2 (.op .add [vv irD, .op .add [.panop .mul [vv irN, .const 8], .const 8]]) =
          some (cellA C (od + 1 + nIdx)) := by
        simp only [sev] at gD gN ⊢; rw [gD, gN]; simp; exact cellA_mulIdx C od nIdx (by omega)
      exact e) ?_
  let dom := doms[nIdx]
  refine specR_callNIM irDh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv irDm]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom] (by decide) rfl (by simp +decide [ctxLocals, irmLocals]) hc.ga
    ⟨rfl, by simp [sev, Env.get_cons] <;> rfl, trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel dom s2 = .ok (a, s') ∧ Post (ctxH C H2) s2 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H2) hc.ga coreWalkFuel dom s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun dh w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hs.symm
  subst hs'
  let Γ3 : Env := (irDh, Enc.idxW dh) :: (irDm, Enc.idxW dom) :: Γ2
  have hΓ3 : ∀ z, z ∉ irmLocals → Γ3.get z = Γ0.get z := fun z hz => by
    simp only [Γ3]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ2 z hz
  refine Knot.specR_tagIteV irDh dh 3 (by decide) (by decide) (by simp [Γ3, Env.get_cons]) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [ite_eq_right (show ¬ (dh.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hHH2, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl,
      fun _ e => by simp at e⟩)
  rw [ite_eq_left (show (dh.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv irDh) (Enc.idxW dh) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP dh (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, irmParams, ctxEnv] <;> rfl) (by simp +decide [ctxLocals, irmLocals])
    (fun v P' hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨cj, us, rfl⟩ := UD.tagN_const h3
  have hvc : s2.store.viewConst dh = some (cj, us) := ConPanqueque.T.WC.viewConst_of_view (by rw [htc]; rfl) hv
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' irU _ (P' + 8) (P' + BitVec.ofNat 64 8) (Enc.idxW us) (by simp +decide [ctxLocals, irmLocals])
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P' (Enc.idxW cj) (Enc.idxW us) [] []) ?_
  refine specR_dropMem ?_
  let Γ4 : Env := (irU, Enc.idxW us) :: (lRp, P') :: (lRn, BitVec.ofNat 64 (encEView (.const cj us)).length) ::
    (lDt, BitVec.ofNat 64 dh.tier.toNat) :: (lDg, BitVec.ofNat 64 (ENodeView.const cj us).tagN) ::
    (lDi, BitVec.ofNat 64 dh.idxNat) :: (lDh, Enc.idxW dh) :: (lFl, C.FLe) :: Γ3
  have hΓ4 : ∀ z, z ∉ irmLocals → Γ4.get z = Γ0.get z := fun z hz => by
    simp only [Γ4]
    rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz,
      cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ3 z hz
  -- the major's arguments
  refine specR_callNIH (C := ctxH C H2) irA fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv irDm] (gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom] (by decide) rfl (by simp +decide [ctxLocals, irmLocals]) hc.gaa
    ⟨rfl, by simp +decide [Γ4, Γ3, sev, Env.get_cons] <;> rfl, trivial⟩
    (PostA (ctxH C H2)) (fun args w _ H' => ∃ oa, w = cellA C oa ∧ BlkAt H' oa (args.map Enc.idxW))
    (fun args w s' st ⟨H', oa, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨oa, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ConPanqueque.T.ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H2 dom s2))
    (fun args wa s3 H3 hp3 ⟨oa, hwa, hab⟩ => ?_)
  subst hwa
  have hp23 : H2 <+: H3 := hp3
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H3.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hal := blkAt_len hab
  simp only [List.length_map] at hal
  let Γ5 : Env := (irA, cellA C oa) :: Γ4
  have hΓ5 : ∀ z, z ∉ irmLocals → Γ5.get z = Γ0.get z := fun z hz => by
    simp only [Γ5]; rw [cnl (by decide) hz]; exact hΓ4 z hz
  have hc0 : (ctxH C H3).H[oa]? = some (BitVec.ofNat 64 args.length) := by
    show H3[oa]? = _; rw [hab.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H3) irC (vv irA) oa _ hc0 (by simp +decide [ctxLocals, irmLocals])
    (by simp [Γ5, sev, Env.get_cons]; rfl) ?_
  let Γ6 : Env := (irC, BitVec.ofNat 64 args.length) :: Γ5
  have hΓ6 : ∀ z, z ∉ irmLocals → Γ6.get z = Γ0.get z := fun z hz => by
    simp only [Γ6]; rw [cnl (by decide) hz]; exact hΓ5 z hz
  let m := args.length - nIdx
  refine specR_pureBind m ?_
  refine rb_tsub (D := ctxLocals ++ irmLocals) C hc.ts args.length nIdx (by omega) (by omega) H3 s3 irM (vv irC) (vv irN) (by simp +decide [ctxLocals, irmLocals])
    (by simp [Γ6, sev, Env.get_cons]) (pk Γ6 hΓ6 irN (by decide) _ vN) (fun H4 hp4 => ?_)
  let Γ7 : Env := (irM, BitVec.ofNat 64 m) :: Γ6
  have hΓ7 : ∀ z, z ∉ irmLocals → Γ7.get z = Γ0.get z := fun z hz => by
    simp only [Γ7]; rw [cnl (by decide) hz]; exact hΓ6 z hz
  -- the parameters
  have hp04 : C.H <+: H4 := ((hp.trans hHH2).trans hp23).trans hp4
  refine specR_congr (m' := ((args.take m).drop 0).mapM (exprDropVars nIdx) >>= fun ps =>
      pure (some (⟨pre, minors, us, ps⟩ : IotaRec))) (by simp [m]) ?_
  refine specR_callNIH (C := ctxH C H4) irPs fDropMap dmParams [vv irA, .const 0, vv irM, vv irN] (dmBody C)
    [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 m, BitVec.ofNat 64 nIdx] (by decide) rfl
    (by simp +decide [ctxLocals, irmLocals]) hc.dm
    ⟨by simp +decide [Γ7, Γ6, Γ5, sev, Env.get_cons], rfl, by simp [Γ7, sev, Env.get_cons] <;> rfl,
      pk Γ7 hΓ7 irN (by decide) _ vN, trivial⟩
    (PostA (ctxH C H4)) (fun ps w _ H' => ∃ opp, w = cellA C opp ∧ BlkAt H' opp (ps.map Enc.idxW))
    (fun ps w s' st ⟨H', opp, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨opp, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dmParams _ rfl hlk)
      (dm_spec ra C hok hc.dm hc.dv hc.srt hc.ifa hc.ic args oa m nIdx (by omega) (by omega) (by omega) (m - 0) 0 H4 s3
        hp04 (blkAt_mono hab hp4) rfl (by omega)))
    (fun ps wp s5 H5 hp5 ⟨opp, hwp, hpb⟩ => ?_)
  subst hwp
  have hp45 : H4 <+: H5 := hp5
  let Γ8 : Env := (irPs, cellA C opp) :: Γ7
  have hΓ8 : ∀ z, z ∉ irmLocals → Γ8.get z = Γ0.get z := fun z hz => by
    simp only [Γ8]; rw [cnl (by decide) hz]; exact hΓ7 z hz
  have gP := pk Γ8 hΓ8 irP (by decide) _ vP
  refine specR_alloc4I (C := ctxH C H5) (ctxOK_H hok H5) irO _ _ _ _ (cellA C op) (cellA C om) (Enc.idxW us)
    (cellA C opp) (by simp +decide [ctxLocals, irmLocals])
    (fun v => by simp only [sev, sev_vv, Env.get_cons, show irP ≠ irO by decide, ite_false] at gP ⊢; exact gP)
    (fun v => by simp +decide [Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons])
    (fun v => by simp +decide [Γ8, Γ7, Γ6, Γ5, Γ4, sev, Env.get_cons])
    (fun v => by simp +decide [Γ8, sev, Env.get_cons]) (fun H6 ws hp6 hws hroom6 => ?_)
  have hp56 : H5 <+: H6 := hp6
  obtain ⟨g0, g1, g2, g3⟩ := img4_get H6 ws (cellA C op) (cellA C om) (Enc.idxW us) (cellA C opp) hws
  have hI := img4_prefix H6 ws (cellA C op) (cellA C om) (Enc.idxW us) (cellA C opp) hws
  have hHI : H <+: img4 H6 ws (cellA C op) (cellA C om) (Enc.idxW us) (cellA C opp) :=
    (((((hHH2.trans hp23).trans hp4).trans hp45).trans hp56).trans hI)
  have h2I : H2 <+: img4 H6 ws (cellA C op) (cellA C om) (Enc.idxW us) (cellA C opp) :=
    ((((hp23.trans hp4).trans hp45).trans hp56).trans hI)
  exact specR_returnI _ (cellA C H6.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, hHI,
    sr_of_eq ht.sr rfl rfl rfl rfl, fun e => by simp at e, fun rr e => by
      simp only [Option.some.injEq] at e; subst e
      exact ⟨H6.length, rfl, ⟨op, g0, get_prefix hpc hHI, fun j hj => get_prefix (hpre j hj) hHI⟩,
        ⟨om, g1, blkAt_mono hmb h2I⟩, g2,
        ⟨opp, g3, blkAt_mono hpb (hp56.trans hI)⟩,
        fun j hj => by have := hmlt _ (List.getElem_mem hj); omega⟩⟩)

end

end ConPanqueque.T.Ind
