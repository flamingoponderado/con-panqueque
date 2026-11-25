import ConPanqueque.T.Core.FindRule
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `iotaVals`: the values an ι reduct substitutes

`args[0:p] ++ margs[q:]` as a fresh heap block: one allocation, two copy loops.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Str
open ConPanqueque.V.Enc

theorem eidxCopyUpto_eq (xs : Array EIdx) (k : Nat) :
    ∀ n i (out : Array EIdx), k - i = n → eidxCopyUpto xs k i out = out ++ ((xs.toList.take k).drop i).toArray := by
  intro n
  induction n with
  | zero =>
    intro i out h
    rw [eidxCopyUpto, dite_eq_right (by omega)]
    have : (xs.toList.take k).drop i = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    rw [this]; simp
  | succ n ih =>
    intro i out h
    by_cases hi : i < xs.size
    · rw [eidxCopyUpto, dite_eq_left ⟨by omega, hi⟩, ih (i + 1) _ (by omega)]
      have hik : i < (xs.toList.take k).length := by simp; omega
      rw [List.drop_eq_getElem_cons hik]
      simp [Array.push, List.getElem_take]
    · rw [eidxCopyUpto, dite_eq_right (by omega)]
      have : (xs.toList.take k).drop i = [] := by
        apply List.drop_eq_nil_of_le; simp; omega
      rw [this]; simp

theorem iotaVals_eq (args : Array EIdx) (p : Nat) (margs : Array EIdx) (q : Nat) :
    iotaVals args p margs q = (args.toList.take p ++ margs.toList.drop q).toArray := by
  unfold iotaVals
  rw [eidxCopyUpto_eq margs margs.size _ q _ rfl, eidxCopyUpto_eq args p _ 0 _ rfl]
  simp [show margs.toList.take margs.size = margs.toList from List.take_of_length_le (by simp)]


def ivA := ofString "iva"
def ivP := ofString "ivp"
def ivM := ofString "ivm"
def ivQ := ofString "ivq"
def ivMl := ofString "ivml"
def ivK := ofString "ivk"
def ivL := ofString "ivl"
def ivO := ofString "ivo"
def fIv := ofString "iotaVals"

@[simp] theorem iv_ivA_ne_ivP : ivA ≠ ivP := by decide
@[simp] theorem iv_ivA_ne_ivM : ivA ≠ ivM := by decide
@[simp] theorem iv_ivA_ne_ivQ : ivA ≠ ivQ := by decide
@[simp] theorem iv_ivA_ne_ivMl : ivA ≠ ivMl := by decide
@[simp] theorem iv_ivA_ne_ivK : ivA ≠ ivK := by decide
@[simp] theorem iv_ivA_ne_ivL : ivA ≠ ivL := by decide
@[simp] theorem iv_ivA_ne_ivO : ivA ≠ ivO := by decide
@[simp] theorem iv_ivA_ne_lSrc : ivA ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivA : lSrc ≠ ivA := by decide
@[simp] theorem iv_ivA_ne_lDst : ivA ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivA : lDst ≠ ivA := by decide
@[simp] theorem iv_ivA_ne_lCi : ivA ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivA : lCi ≠ ivA := by decide
@[simp] theorem iv_ivA_ne_lCz : ivA ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivA : lCz ≠ ivA := by decide
@[simp] theorem iv_ivA_ne_lCn : ivA ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivA : lCn ≠ ivA := by decide
@[simp] theorem iv_ivP_ne_ivA : ivP ≠ ivA := by decide
@[simp] theorem iv_ivP_ne_ivM : ivP ≠ ivM := by decide
@[simp] theorem iv_ivP_ne_ivQ : ivP ≠ ivQ := by decide
@[simp] theorem iv_ivP_ne_ivMl : ivP ≠ ivMl := by decide
@[simp] theorem iv_ivP_ne_ivK : ivP ≠ ivK := by decide
@[simp] theorem iv_ivP_ne_ivL : ivP ≠ ivL := by decide
@[simp] theorem iv_ivP_ne_ivO : ivP ≠ ivO := by decide
@[simp] theorem iv_ivP_ne_lSrc : ivP ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivP : lSrc ≠ ivP := by decide
@[simp] theorem iv_ivP_ne_lDst : ivP ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivP : lDst ≠ ivP := by decide
@[simp] theorem iv_ivP_ne_lCi : ivP ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivP : lCi ≠ ivP := by decide
@[simp] theorem iv_ivP_ne_lCz : ivP ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivP : lCz ≠ ivP := by decide
@[simp] theorem iv_ivP_ne_lCn : ivP ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivP : lCn ≠ ivP := by decide
@[simp] theorem iv_ivM_ne_ivA : ivM ≠ ivA := by decide
@[simp] theorem iv_ivM_ne_ivP : ivM ≠ ivP := by decide
@[simp] theorem iv_ivM_ne_ivQ : ivM ≠ ivQ := by decide
@[simp] theorem iv_ivM_ne_ivMl : ivM ≠ ivMl := by decide
@[simp] theorem iv_ivM_ne_ivK : ivM ≠ ivK := by decide
@[simp] theorem iv_ivM_ne_ivL : ivM ≠ ivL := by decide
@[simp] theorem iv_ivM_ne_ivO : ivM ≠ ivO := by decide
@[simp] theorem iv_ivM_ne_lSrc : ivM ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivM : lSrc ≠ ivM := by decide
@[simp] theorem iv_ivM_ne_lDst : ivM ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivM : lDst ≠ ivM := by decide
@[simp] theorem iv_ivM_ne_lCi : ivM ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivM : lCi ≠ ivM := by decide
@[simp] theorem iv_ivM_ne_lCz : ivM ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivM : lCz ≠ ivM := by decide
@[simp] theorem iv_ivM_ne_lCn : ivM ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivM : lCn ≠ ivM := by decide
@[simp] theorem iv_ivQ_ne_ivA : ivQ ≠ ivA := by decide
@[simp] theorem iv_ivQ_ne_ivP : ivQ ≠ ivP := by decide
@[simp] theorem iv_ivQ_ne_ivM : ivQ ≠ ivM := by decide
@[simp] theorem iv_ivQ_ne_ivMl : ivQ ≠ ivMl := by decide
@[simp] theorem iv_ivQ_ne_ivK : ivQ ≠ ivK := by decide
@[simp] theorem iv_ivQ_ne_ivL : ivQ ≠ ivL := by decide
@[simp] theorem iv_ivQ_ne_ivO : ivQ ≠ ivO := by decide
@[simp] theorem iv_ivQ_ne_lSrc : ivQ ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivQ : lSrc ≠ ivQ := by decide
@[simp] theorem iv_ivQ_ne_lDst : ivQ ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivQ : lDst ≠ ivQ := by decide
@[simp] theorem iv_ivQ_ne_lCi : ivQ ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivQ : lCi ≠ ivQ := by decide
@[simp] theorem iv_ivQ_ne_lCz : ivQ ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivQ : lCz ≠ ivQ := by decide
@[simp] theorem iv_ivQ_ne_lCn : ivQ ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivQ : lCn ≠ ivQ := by decide
@[simp] theorem iv_ivMl_ne_ivA : ivMl ≠ ivA := by decide
@[simp] theorem iv_ivMl_ne_ivP : ivMl ≠ ivP := by decide
@[simp] theorem iv_ivMl_ne_ivM : ivMl ≠ ivM := by decide
@[simp] theorem iv_ivMl_ne_ivQ : ivMl ≠ ivQ := by decide
@[simp] theorem iv_ivMl_ne_ivK : ivMl ≠ ivK := by decide
@[simp] theorem iv_ivMl_ne_ivL : ivMl ≠ ivL := by decide
@[simp] theorem iv_ivMl_ne_ivO : ivMl ≠ ivO := by decide
@[simp] theorem iv_ivMl_ne_lSrc : ivMl ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivMl : lSrc ≠ ivMl := by decide
@[simp] theorem iv_ivMl_ne_lDst : ivMl ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivMl : lDst ≠ ivMl := by decide
@[simp] theorem iv_ivMl_ne_lCi : ivMl ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivMl : lCi ≠ ivMl := by decide
@[simp] theorem iv_ivMl_ne_lCz : ivMl ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivMl : lCz ≠ ivMl := by decide
@[simp] theorem iv_ivMl_ne_lCn : ivMl ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivMl : lCn ≠ ivMl := by decide
@[simp] theorem iv_ivK_ne_ivA : ivK ≠ ivA := by decide
@[simp] theorem iv_ivK_ne_ivP : ivK ≠ ivP := by decide
@[simp] theorem iv_ivK_ne_ivM : ivK ≠ ivM := by decide
@[simp] theorem iv_ivK_ne_ivQ : ivK ≠ ivQ := by decide
@[simp] theorem iv_ivK_ne_ivMl : ivK ≠ ivMl := by decide
@[simp] theorem iv_ivK_ne_ivL : ivK ≠ ivL := by decide
@[simp] theorem iv_ivK_ne_ivO : ivK ≠ ivO := by decide
@[simp] theorem iv_ivK_ne_lSrc : ivK ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivK : lSrc ≠ ivK := by decide
@[simp] theorem iv_ivK_ne_lDst : ivK ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivK : lDst ≠ ivK := by decide
@[simp] theorem iv_ivK_ne_lCi : ivK ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivK : lCi ≠ ivK := by decide
@[simp] theorem iv_ivK_ne_lCz : ivK ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivK : lCz ≠ ivK := by decide
@[simp] theorem iv_ivK_ne_lCn : ivK ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivK : lCn ≠ ivK := by decide
@[simp] theorem iv_ivL_ne_ivA : ivL ≠ ivA := by decide
@[simp] theorem iv_ivL_ne_ivP : ivL ≠ ivP := by decide
@[simp] theorem iv_ivL_ne_ivM : ivL ≠ ivM := by decide
@[simp] theorem iv_ivL_ne_ivQ : ivL ≠ ivQ := by decide
@[simp] theorem iv_ivL_ne_ivMl : ivL ≠ ivMl := by decide
@[simp] theorem iv_ivL_ne_ivK : ivL ≠ ivK := by decide
@[simp] theorem iv_ivL_ne_ivO : ivL ≠ ivO := by decide
@[simp] theorem iv_ivL_ne_lSrc : ivL ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivL : lSrc ≠ ivL := by decide
@[simp] theorem iv_ivL_ne_lDst : ivL ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivL : lDst ≠ ivL := by decide
@[simp] theorem iv_ivL_ne_lCi : ivL ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivL : lCi ≠ ivL := by decide
@[simp] theorem iv_ivL_ne_lCz : ivL ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivL : lCz ≠ ivL := by decide
@[simp] theorem iv_ivL_ne_lCn : ivL ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivL : lCn ≠ ivL := by decide
@[simp] theorem iv_ivO_ne_ivA : ivO ≠ ivA := by decide
@[simp] theorem iv_ivO_ne_ivP : ivO ≠ ivP := by decide
@[simp] theorem iv_ivO_ne_ivM : ivO ≠ ivM := by decide
@[simp] theorem iv_ivO_ne_ivQ : ivO ≠ ivQ := by decide
@[simp] theorem iv_ivO_ne_ivMl : ivO ≠ ivMl := by decide
@[simp] theorem iv_ivO_ne_ivK : ivO ≠ ivK := by decide
@[simp] theorem iv_ivO_ne_ivL : ivO ≠ ivL := by decide
@[simp] theorem iv_ivO_ne_lSrc : ivO ≠ lSrc := by decide
@[simp] theorem iv_lSrc_ne_ivO : lSrc ≠ ivO := by decide
@[simp] theorem iv_ivO_ne_lDst : ivO ≠ lDst := by decide
@[simp] theorem iv_lDst_ne_ivO : lDst ≠ ivO := by decide
@[simp] theorem iv_ivO_ne_lCi : ivO ≠ lCi := by decide
@[simp] theorem iv_lCi_ne_ivO : lCi ≠ ivO := by decide
@[simp] theorem iv_ivO_ne_lCz : ivO ≠ lCz := by decide
@[simp] theorem iv_lCz_ne_ivO : lCz ≠ ivO := by decide
@[simp] theorem iv_ivO_ne_lCn : ivO ≠ lCn := by decide
@[simp] theorem iv_lCn_ne_ivO : lCn ≠ ivO := by decide

def ivParams : List MlS := [ivA, ivP, ivM, ivQ]
def ivLocals : List MlS := [ivMl, ivK, ivL, ivO, lSrc, lDst, lCi, lCz, lCn]

def ivCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local ivMl (.load .one (vv ivM)))
  (.seq (.assign .local ivK (.op .sub [vv ivMl, vv ivQ]))
  (.seq (.assign .local ivL (.op .add [vv ivP, vv ivK]))
  (allocP C ivO (.panop .mul [.op .add [vv ivL, .const 1], .const 8])
  (.seq (.store (vv ivO) (vv ivL))
  (.seq (.assign .local lSrc (.op .add [vv ivA, .const 8]))
  (.seq (.assign .local lDst (.op .add [vv ivO, .const 8]))
  (.seq (.assign .local lCi (.const 0))
  (.seq (.assign .local lCn (vv ivP))
  (.seq copyLoop
  (.seq (.assign .local lSrc (.op .add [vv ivM, .shift .lsl (.op .add [vv ivQ, .const 1]) (.const 3)]))
  (.seq (.assign .local lCi (.const 0))
  (.seq (.assign .local lCn (vv ivK))
  (.seq copyLoop (.return (vv ivO)))))))))))))))

def ivBody (C : Ctx) : ProgHOL 64 := prologue ivLocals (ivCore C)

section
variable {σ : Type}

theorem iv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ivLocals → (ctxEnv C ++ ivParams.zip vals).get x = none :=
  Knot.params_none C ivLocals ivParams vals (by decide) (by decide)

theorem iv_spec (C : Ctx) (hok : CtxOK C) (args margs : List EIdx) (oa om p q : Nat)
    (hba : BlkAt C.H oa (args.map Enc.idxW)) (hbm : BlkAt C.H om (margs.map Enc.idxW))
    (hp : p ≤ args.length) (hq : q ≤ margs.length) (s : AState) :
    SpecR (σ := σ) (Pre C s (ivParams.zip [cellA C oa, BitVec.ofNat 64 p, cellA C om, BitVec.ofNat 64 q])) (ivBody C) s
      (pure () : AM Unit) (PostG C s ((args.take p ++ margs.drop q).map Enc.idxW)) := by
  refine specR_prologue (postG_locals C s _) (iv_none C _) ?_
  unfold ivCore
  refine specR_atEntry fun t0 ht0 => ?_
  have hla := blk_small0 hok ht0.sr hba
  have hlm := blk_small0 hok ht0.sr hbm
  simp only [List.length_map] at hla hlm
  have hea := blkAt_len hba
  have hem := blkAt_len hbm
  simp only [List.length_map] at hea hem
  refine UD.specR_heapLoadI' ivMl (vv ivM) om _ hbm.1 (by decide) (by simp +decide [Env.get, ivParams, ctxEnv]) ?_
  refine specR_assignI ivK _ (BitVec.ofNat 64 (margs.length - q)) (by decide)
    (by simp +decide [sev, Env.get, ivParams, ctxEnv]; exact w_sub _ _ hq (by omega)) ?_
  refine specR_assignI ivL _ (BitVec.ofNat 64 (p + (margs.length - q))) (by decide)
    (by simp +decide [sev, Env.get, ivParams, ctxEnv, BitVec.ofNat_add_ofNat]) ?_
  set L := p + (margs.length - q) with hL
  refine specR_allocI ivO (.panop .mul [.op .add [vv ivL, .const 1], .const 8]) (L + 1) (by omega)
    (by decide) (fun v => by simp [sev, Env.get]; rw [word_add1_eq]; exact CV.mul8_eq _) (fun H3 ws hpre hwl hcap => ?_)
  have hpl := hpre.length_le
  have hj : H3.length < (ctxH C (H3 ++ ws)).H.length := by show H3.length < (H3 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv ivO) (vv ivL) H3.length hj (BitVec.ofNat 64 L) (by simp; rfl) (by simp) ?_
  let B0 := (H3 ++ ws).set H3.length (BitVec.ofNat 64 L)
  have hB0 : B0.length = H3.length + (L + 1) := by simp [B0, hwl]
  have hB0get : ∀ k, k < C.H.length → B0[k]? = C.H[k]? := by
    intro k hk
    show ((H3 ++ ws).set H3.length _)[k]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
    obtain ⟨r, hr⟩ := hpre
    show H3[k]? = _
    rw [← hr, List.getElem?_append_left hk]
  refine specR_assignI lSrc _ (cellA C (oa + 1 + 0)) (by decide)
    (by simp +decide [sev, Env.get, ivParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI lDst _ (cellA C (H3.length + 1 + 0)) (by decide)
    (by simp [sev]; exact cellA_add8 C _) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI lCn (vv ivP) (BitVec.ofNat 64 p) (by decide) (by simp +decide [Env.get, ivParams, ctxEnv]) ?_
  let ws1 := (args.map Enc.idxW).take p
  have hws1 : ws1.length = p := by simp [ws1]; omega
  let Γc : Env := [(lCn, BitVec.ofNat 64 ws1.length), (ivO, cellA C H3.length),
    (ivK, BitVec.ofNat 64 (margs.length - q)), (ivM, cellA C om), (ivQ, BitVec.ofNat 64 q)]
  refine specR_envWeak (Γb := (lCi, BitVec.ofNat 64 0) :: (lDst, cellA C (H3.length + 1 + 0)) ::
    (lSrc, cellA C (oa + 1 + 0)) :: Γc) (fun z v hz => ?_) ?_
  · simp only [Γc, Env.get_cons] at hz ⊢
    by_cases e1 : z = lCi
    · subst e1; simpa using hz
    by_cases e2 : z = lDst
    · subst e2; simpa using hz
    by_cases e3 : z = lSrc
    · subst e3; simpa using hz
    by_cases e4 : z = lCn
    · subst e4; simp at hz ⊢; rw [hws1] at hz; exact hz
    by_cases e5 : z = ivO
    · subst e5; simpa using hz
    by_cases e6 : z = ivK
    · subst e6; simpa using hz
    by_cases e7 : z = ivM
    · subst e7; simp at hz; subst hz; simp +decide [Env.get, ivParams, ctxEnv]
    by_cases e8 : z = ivQ
    · subst e8; simp at hz; subst hz; simp +decide [Env.get, ivParams, ctxEnv]
    simp [e1, e2, e3, e4, e5, e6, e7, e8, Env.get] at hz
  have hsrc1 : ∀ j (hj : j < ws1.length), B0[oa + 1 + j]? = some ws1[j] := by
    intro j hj
    rw [hB0get _ (by omega)]
    have := hba.2 j (by simp; omega)
    rw [this]; simp [ws1]
  refine specR_copyI (C := C) hok B0 ws1 (oa + 1) (H3.length + 1) (by decide) hsrc1 (by omega)
    (by rw [hB0]; omega) (by omega) (by simp [Γc]) (by decide) (by simp [Γc, Env.get]) ?_
  let B1 := fillI B0 ws1 (H3.length + 1) ws1.length
  have hB1 : B1.length = B0.length := fillI_length _ _ _ _
  refine specR_assignI lSrc _ (cellA C (om + 1 + q + 0)) (by decide)
    (by simp [sev, Γc]; first | exact slP_eq' C om q (by omega) | exact slP_eq C om q (by omega)) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI lCn (vv ivK) (BitVec.ofNat 64 (margs.length - q)) (by decide) (by simp [Γc]) ?_
  let ws2 := (margs.map Enc.idxW).drop q
  have hws2 : ws2.length = margs.length - q := by simp [ws2]
  let Γd : Env := [(lCn, BitVec.ofNat 64 ws2.length), (ivO, cellA C H3.length)]
  refine specR_envWeak (Γb := (lCi, BitVec.ofNat 64 0) :: (lDst, cellA C (H3.length + 1 + p + 0)) ::
    (lSrc, cellA C (om + 1 + q + 0)) :: Γd) (fun z v hz => ?_) ?_
  · simp only [Γd, Γc, Env.get_cons] at hz ⊢
    by_cases e1 : z = lCi
    · subst e1; simpa using hz
    by_cases e2 : z = lDst
    · subst e2; simp at hz ⊢; subst hz; rw [hws1]
    by_cases e3 : z = lSrc
    · subst e3; simpa using hz
    by_cases e4 : z = lCn
    · subst e4; simp at hz ⊢; rw [hws2] at hz; exact hz
    by_cases e5 : z = ivO
    · subst e5; simpa using hz
    simp [e1, e2, e3, e4, e5, Env.get] at hz
  have hsrc2 : ∀ j (hj : j < ws2.length), B1[om + 1 + q + j]? = some ws2[j] := by
    intro j hj
    rw [fillI_get?, ite_eq_right (by omega), hB0get _ (by omega)]
    have := hbm.2 (q + j) (by simp; omega)
    rw [show om + 1 + q + j = om + 1 + (q + j) by omega, this]; simp [ws2]
  refine specR_copyI (C := C) hok B1 ws2 (om + 1 + q) (H3.length + 1 + p) (by decide) hsrc2 (by omega)
    (by rw [hB1, hB0]; omega) (by omega) (by simp [Γd]) (by decide) (by simp [Γd, Env.get]) ?_
  refine specR_returnI _ (cellA C H3.length) (by simp [Γd]) (fun t ht => ?_)
  refine ⟨fillI B1 ws2 (H3.length + 1 + p) ws2.length, H3.length, ?_, rfl, ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · exact CV.prefix_fillI _ _ _ C.H (by omega)
      (CV.prefix_fillI _ _ _ C.H (by omega)
        (prefix_set_ge (hpre.trans (List.prefix_append _ _)) _ hpl _) _) _
  · have hlf := fillI_length B1 ws2 (H3.length + 1 + p)
    constructor
    · rw [fillI_get?, ite_eq_right (by omega), fillI_get?, ite_eq_right (by omega)]
      show ((H3 ++ ws).set H3.length _)[H3.length]? = _
      rw [List.getElem?_set_self (by simp; omega)]
      simp [hL, Nat.min_eq_left hp]
    · intro i hi
      rw [← List.getElem?_eq_getElem]
      simp only [List.length_map, List.length_append, List.length_take, List.length_drop] at hi
      by_cases hip : i < p
      · rw [fillI_get?, ite_eq_right (by omega), fillI_get?, ite_eq_left ⟨by omega, by omega, by rw [hB0]; omega⟩]
        rw [List.map_append, List.getElem?_append_left (by simp; omega)]
        simp [ws1, List.getD_eq_getElem?_getD, show H3.length + 1 + i - (H3.length + 1) = i by omega, hip,
          List.getElem?_eq_getElem (show i < args.length by omega)]
      · rw [fillI_get?, ite_eq_left ⟨by omega, by omega, by rw [hB1, hB0]; omega⟩]
        rw [List.map_append, List.getElem?_append_right (by simp; omega)]
        simp only [ws2, List.getD_eq_getElem?_getD, show H3.length + 1 + i - (H3.length + 1 + p) = i - p by omega,
          List.length_map, List.length_take, Nat.min_eq_left hp, List.getElem?_drop, List.getElem?_map]
        rw [List.getElem?_eq_getElem (show q + (i - p) < margs.length by omega)]
        simp
end

end ConPanqueque.T.WC
