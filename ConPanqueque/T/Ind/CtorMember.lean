import ConPanqueque.T.Ind.RecTarget
import ConRon.Arena.Inductives.Positivity

/-!
# The member a head names, and a constructor's member

`memberIdxAt? names lvls e`: a `const` head at the block's own universe arguments `lvls` (an interned list, so
handle equality) names the member it is among `names`; `none` otherwise.  `ctorMember?`: a constructor's
result head (`stripPis (nP + nF)`, `getAppFn`), read by `memberIdxAt?`.

Both return an index word: the member, or `k` (the member count) for `none`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI

/-- An optional member index as a word's number: the index, or `k` for none. -/
def optIdx (k : Nat) : Option Nat → Nat
  | some t => t
  | none => k

def miP := ofString "mi_p"
def miK := ofString "mi_k"
def miL := ofString "mi_l"
def miE := ofString "mi_e"
def miN := ofString "mi_n"
def miU := ofString "mi_u"
def miR := ofString "mi_r"
def fMemberIdx := ofString "memberIdxAt"

def miParams : List MlS := [miP, miK, miL, miE]
def miLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, miN, miU, miR]

def miBody : ProgHOL 64 := prologue miLocals
  (.ite (tagIsE miE 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv miE)) (.seq eViewP
    (.seq (.assign .local miN (.load .one (vv lRp)))
    (.seq (.assign .local miU (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv miU) (vv miL))
      (.seq (.call (some (some (.local, miR), none)) fNameIdx [vv miP, .const 0, vv miK, vv miN]) (.return (vv miR)))
      (.return (vv miK))))))))
    (.return (vv miK)))

section
variable {σ : Type}

theorem mi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ miLocals → (ctxEnv C ++ miParams.zip vals).get x = none :=
  Knot.params_none C miLocals miParams vals (by decide) (by decide)

/-- `names.findIdx?` as a member index: `nameIdxP` from `0`. -/
theorem findIdx_optIdx (blk : List IConstantInfo) (k : Nat) (hk : k ≤ blk.length) (n : NIdx) :
    optIdx k (((blk.take k).map (fun (c : IConstantInfo) => c.name)).findIdx? (· == n)) = nameIdxP blk k n k 0 := by
  rw [nameIdxP_eq blk k hk n k 0 (by omega) (by omega)]
  simp only [List.drop_zero]
  cases (List.findIdx? (fun x => x == n) (List.map (fun (x : IConstantInfo) => x.name) (List.take k blk))) <;>
    simp [Option.elim, optIdx]

theorem findIdx_lt (blk : List IConstantInfo) (k : Nat) (hk : k ≤ blk.length) (n : NIdx) (t : Nat)
    (h : ((blk.take k).map (fun (c : IConstantInfo) => c.name)).findIdx? (· == n) = some t) : t < k := by
  have := List.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨ht, -⟩ := this
  simp at ht; omega

/-- The post of the member-index functions: the word is `optIdx k`, and a member index is below `k`. -/
def PostMI (C : Ctx) (k : Nat) (a : Option Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  PostN C (optIdx k a) w s' st ∧ ∀ t, a = some t → t < k

/-- **`memberIdxAt?`**. -/
theorem mi_spec (C : Ctx)
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k : Nat) (lvls : LsIdx) (e : EIdx) (hk : k ≤ blk.length) (hlen : blk.length < 2 ^ 59)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hb : IndBlk C H ob blk) :
    SpecR (σ := σ) (Pre (ctxH C H) s (miParams.zip [cellA C ob, BitVec.ofNat 64 k, Enc.idxW lvls, Enc.idxW e])) miBody s
      (memberIdxAt? ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls e) (PostMI (ctxH C H) k) := by
  refine specR_prologue (fun a w s' st L ⟨h1, h2⟩ => ⟨postN_locals _ _ w s' st L h1, h2⟩) (mi_none _ _) ?_
  rw [memberIdxAt?]
  have retK : ∀ (Γ : Env) (M : Mem), Γ.get miK = some (BitVec.ofNat 64 k) →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ miLocals)) (.return (vv miK)) s (pure none) (PostMI (ctxH C H) k) :=
    fun Γ M hK => specR_returnI _ (BitVec.ofNat 64 k) (by simpa [sev] using hK)
      (fun t ht => ⟨⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩, fun _ e => by simp at e⟩)
  refine Knot.specR_tagIteV miE e 3 (by decide) (by decide) (by simp +decide [Env.get, miParams, ctxEnv])
    (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [ite_eq_right (show ¬ (e.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    refine retK _ _ ?_
    simp +decide [Env.get, miParams, ctxEnv]
  rw [ite_eq_left (show (e.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by simp +decide [ctxLocals, miLocals])
    (by simp +decide [Env.get, miParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv miE) (Enc.idxW e) (by simp +decide [ctxLocals, miLocals])
    (by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv]) ?_
  refine ConPanqueque.T.Big.specR_viewP e (by simp) (by simp +decide [Env.get_cons, Env.get, miParams, ctxEnv] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, miParams, ctxEnv] <;> rfl) (by simp +decide [ctxLocals, miLocals])
    (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨cj, us, rfl⟩ := UD.tagN_const h3
  have hvc : s.store.viewConst e = some (cj, us) := ConPanqueque.T.WC.viewConst_of_view (by rw [htc]; rfl) hv
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' miN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cj) (by simp +decide [ctxLocals, miLocals])
    (by simp [sev, Env.get_cons]) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW cj) [Enc.idxW us] []) ?_
  refine specR_loadI' miU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by simp +decide [ctxLocals, miLocals])
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW cj) (Enc.idxW us) [] []) ?_
  by_cases hu : us = lvls
  · subst hu
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ite_true]
    refine specR_congr (m' := (pure (nameIdxP blk k cj k 0) : AM Nat) >>= fun _ =>
        pure (((blk.take k).map (fun (c : IConstantInfo) => c.name)).findIdx? (· == cj))) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) miR fNameIdx niParams [vv miP, .const 0, vv miK, vv miN] niBody
      [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 k, Enc.idxW cj] (by decide) rfl
      (by simp +decide [ctxLocals, miLocals]) hcn
      ⟨by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (fun a w s' st => (pure (nameIdxP blk k cj k 0) : AM Nat) s = .ok (a, s') ∧ PostN (ctxH C H) a w s' st)
      (fun r w _ _ => w = BitVec.ofNat 64 r ∧ r = nameIdxP blk k cj k 0)
      (fun r w s' st ⟨hrun, H', hp', hw, hsr⟩ => by
        have hr : r = nameIdxP blk k cj k 0 := by
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun; exact hrun.1.symm
        exact ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu niParams _ rfl hlk)
        (ni_spec C hcn blk ob k cj hk hlen k 0 H s hp hb (by omega) (by omega))))
      (fun r w s1 H1 hp1 ⟨hw, hr⟩ => ?_)
    subst hw; subst hr
    exact specR_returnI _ (BitVec.ofNat 64 (nameIdxP blk k cj k 0)) (by simp +decide [Env.get])
      (fun t ht => ⟨⟨H1, hp1, by rw [findIdx_optIdx blk k hk cj], sr_of_eq ht.sr rfl rfl rfl rfl⟩,
        fun t' ht' => findIdx_lt blk k hk cj t' ht'⟩)
  · have hne : Enc.idxW us ≠ Enc.idxW lvls := fun h => hu (ConPanqueque.V.Enc.idxW_inj h)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
    have hb' : (us == lvls) = false := by simpa using hu
    simp only [hb', Bool.false_eq_true, ite_false]
    refine retK _ _ ?_
    simp +decide [Env.get_cons, Env.get, miParams, ctxEnv]

end

def cmP := ofString "cm_p"
def cmK := ofString "cm_k"
def cmL := ofString "cm_l"
def cmN := ofString "cm_n"
def cmT := ofString "cm_t"
def cmR := ofString "cm_r"
def cmW := ofString "cm_w"
def cmB := ofString "cm_b"
def cmH := ofString "cm_h"
def fCtorMember := ofString "ctorMember"

def cmParams : List MlS := [cmP, cmK, cmL, cmN, cmT]
def cmLocals : List MlS := [cmR, cmW, cmB, cmH]

def cmBody (_C : Ctx) : ProgHOL 64 := prologue cmLocals
  (.seq (.call (some (some (.local, cmR), none)) fStripPis [vv cmN, vv cmT])
  (.ite (.cmp .equal (vv cmR) (.const 0)) (.return (vv cmK))
  (.seq (.assign .local cmW (.load .one (vv cmR)))
  (.seq (.assign .local cmB (.load .one (.op .add [vv cmR, .shift .lsl (vv cmW) (.const 3)])))
  (.seq (.call (some (some (.local, cmH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv cmB])
  (.seq (.call (some (some (.local, cmR), none)) fMemberIdx [vv cmP, vv cmK, vv cmL, vv cmH])
    (.return (vv cmR))))))))

section
variable {σ : Type}

theorem cm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cmLocals → (ctxEnv C ++ cmParams.zip vals).get x = none :=
  Knot.params_none C cmLocals cmParams vals (by decide) (by decide)

/-- **`ctorMember?`**: the member a constructor's result names. -/
theorem cm_spec (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcm : C.code.lookup fMemberIdx = some (miParams.map (fun p => (p, ShapeHOL.one)), miBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k nP : Nat) (lvls : LsIdx) (c : IConstantVal × Nat) (hk : k ≤ blk.length)
    (hlen : blk.length < 2 ^ 59) (hnP : nP + c.2 < 2 ^ 64)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hb : IndBlk C H ob blk) :
    SpecR (σ := σ) (Pre (ctxH C H) s (cmParams.zip [cellA C ob, BitVec.ofNat 64 k, Enc.idxW lvls,
        BitVec.ofNat 64 (nP + c.2), Enc.idxW c.1.type])) (cmBody C) s
      (ctorMember? ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP c) (PostMI (ctxH C H) k) := by
  refine specR_prologue (fun a w s' st L ⟨h1, h2⟩ => ⟨postN_locals _ _ w s' st L h1, h2⟩) (cm_none _ _) ?_
  rw [ctorMember?]
  refine specR_callNIH (C := ctxH C H) cmR fStripPis [pFu, pH] [vv cmN, vv cmT] (stripBody C fStripPis 6)
    [BitVec.ofNat 64 (nP + c.2), Enc.idxW c.1.type] (by decide) rfl (by simp +decide [ctxLocals, cmLocals]) hcs
    ⟨by simp +decide [sev, Env.get, cmParams, ctxEnv], by simp +decide [sev, Env.get, cmParams, ctxEnv], trivial⟩
    (PostSP (ctxH C H)) (fun o w s' H' => (o = none → w = 0) ∧
      ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact stripPis_spec C hok hcs (nP + c.2) hnP H s c.1.type _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
  have hpH : H <+: H1 := hp1
  have hb1 : IndBlk C H1 ob blk := indBlk_mono hb hpH
  rcases o with _ | ⟨tys, b⟩
  · have e0 := hn rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ (BitVec.ofNat 64 k) (by simp +decide [sev, Env.get_cons, Env.get, cmParams, ctxEnv])
      (fun t ht => ⟨⟨H1, hpH, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩, fun _ e => by simp at e⟩)
  obtain ⟨ob', rfl, hblk⟩ := hsm tys b rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hblk
  have hHN' : H1.length ≤ C.HN := hHN
  have hne : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hl0 : (ctxH C H1).H[ob']? = some (BitVec.ofNat 64 (tys.length + 1)) := by
    show H1[ob']? = _; rw [hblk.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H1) cmW (vv cmR) ob' _ hl0 (by simp +decide [ctxLocals, cmLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  have hbw : (ctxH C H1).H[ob' + 1 + tys.length]? = some (Enc.idxW b) := by
    show H1[ob' + 1 + tys.length]? = _
    have := hblk.2 tys.length (by simp); simpa using this
  refine UD.specR_heapLoadI' (C := ctxH C H1) cmB _ (ob' + 1 + tys.length) _ hbw (by simp +decide [ctxLocals, cmLocals])
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C ob' + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  refine specR_callNIM cmH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cmB]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by simp +decide [ctxLocals, cmLocals]) hcg
    ⟨rfl, by simp [sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel b s1 = .ok (a, s') ∧ Post (ctxH C H1) s1 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H1) hcg coreWalkFuel b s1 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hh w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s1 = s' := hs.symm
  subst hs'
  refine specR_congr (m' := memberIdxAt? ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls hh >>= fun r => pure r)
    (by simp) ?_
  refine specR_callNIH (C := ctxH C H1) cmR fMemberIdx miParams [vv cmP, vv cmK, vv cmL, vv cmH] miBody
    [cellA C ob, BitVec.ofNat 64 k, Enc.idxW lvls, Enc.idxW hh] (by decide) rfl (by simp +decide [ctxLocals, cmLocals]) hcm
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cmParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cmParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostMI (ctxH C H1) k) (fun a w _ _ => w = BitVec.ofNat 64 (optIdx k a) ∧ ∀ t, a = some t → t < k)
    (fun a w s' st ⟨⟨H', hp', hw, hsr⟩, hbd⟩ => ⟨H', hp', ⟨hw, hbd⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu miParams _ rfl hlk)
      (mi_spec C hcn blk ob k lvls hh hk hlen H1 s1 (hp.trans hpH) hb1))
    (fun a w s2 H2 hp2 ⟨hw, hbd⟩ => ?_)
  subst hw
  exact specR_returnI _ (BitVec.ofNat 64 (optIdx k a)) (by simp +decide [Env.get])
    (fun t ht => ⟨⟨H2, hpH.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩, hbd⟩)

end

end ConPanqueque.T.Ind
