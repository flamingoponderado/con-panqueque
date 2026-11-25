import ConPanqueque.T.Core.NatPred
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `defeqOffset`

Two zeros are equal; two literals are left to `quickDefEq`; two successor forms compare their predecessors
(the knot's `defeq`). Answers `LLeq.obW` (`0` none, `1` false, `2` true).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ofA := ofString "ofn_a"
def ofB := ofString "ofn_b"
def ofX := ofString "ofn_x"
def ofY := ofString "ofn_y"
def ofP := ofString "ofn_p"
def ofQ := ofString "ofn_q"
def ofR := ofString "ofn_r"
def fOf := ofString "defeqOffset"

@[simp] theorem of_ofA_ne_ofB : ofA ≠ ofB := by decide
@[simp] theorem of_ofA_ne_ofX : ofA ≠ ofX := by decide
@[simp] theorem of_ofA_ne_ofY : ofA ≠ ofY := by decide
@[simp] theorem of_ofA_ne_ofP : ofA ≠ ofP := by decide
@[simp] theorem of_ofA_ne_ofQ : ofA ≠ ofQ := by decide
@[simp] theorem of_ofA_ne_ofR : ofA ≠ ofR := by decide
@[simp] theorem of_ofA_ne_kFu : ofA ≠ kFu := by decide
@[simp] theorem of_kFu_ne_ofA : kFu ≠ ofA := by decide
@[simp] theorem of_ofA_ne_kD : ofA ≠ kD := by decide
@[simp] theorem of_kD_ne_ofA : kD ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lFl : ofA ≠ lFl := by decide
@[simp] theorem of_lFl_ne_ofA : lFl ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lDh : ofA ≠ lDh := by decide
@[simp] theorem of_lDh_ne_ofA : lDh ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lDt : ofA ≠ lDt := by decide
@[simp] theorem of_lDt_ne_ofA : lDt ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lDg : ofA ≠ lDg := by decide
@[simp] theorem of_lDg_ne_ofA : lDg ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lDi : ofA ≠ lDi := by decide
@[simp] theorem of_lDi_ne_ofA : lDi ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lRp : ofA ≠ lRp := by decide
@[simp] theorem of_lRp_ne_ofA : lRp ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lRn : ofA ≠ lRn := by decide
@[simp] theorem of_lRn_ne_ofA : lRn ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lDir : ofA ≠ lDir := by decide
@[simp] theorem of_lDir_ne_ofA : lDir ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lFle : ofA ≠ lFle := by decide
@[simp] theorem of_lFle_ne_ofA : lFle ≠ ofA := by decide
@[simp] theorem of_ofA_ne_lKb : ofA ≠ lKb := by decide
@[simp] theorem of_lKb_ne_ofA : lKb ≠ ofA := by decide
@[simp] theorem of_ofB_ne_ofA : ofB ≠ ofA := by decide
@[simp] theorem of_ofB_ne_ofX : ofB ≠ ofX := by decide
@[simp] theorem of_ofB_ne_ofY : ofB ≠ ofY := by decide
@[simp] theorem of_ofB_ne_ofP : ofB ≠ ofP := by decide
@[simp] theorem of_ofB_ne_ofQ : ofB ≠ ofQ := by decide
@[simp] theorem of_ofB_ne_ofR : ofB ≠ ofR := by decide
@[simp] theorem of_ofB_ne_kFu : ofB ≠ kFu := by decide
@[simp] theorem of_kFu_ne_ofB : kFu ≠ ofB := by decide
@[simp] theorem of_ofB_ne_kD : ofB ≠ kD := by decide
@[simp] theorem of_kD_ne_ofB : kD ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lFl : ofB ≠ lFl := by decide
@[simp] theorem of_lFl_ne_ofB : lFl ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lDh : ofB ≠ lDh := by decide
@[simp] theorem of_lDh_ne_ofB : lDh ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lDt : ofB ≠ lDt := by decide
@[simp] theorem of_lDt_ne_ofB : lDt ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lDg : ofB ≠ lDg := by decide
@[simp] theorem of_lDg_ne_ofB : lDg ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lDi : ofB ≠ lDi := by decide
@[simp] theorem of_lDi_ne_ofB : lDi ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lRp : ofB ≠ lRp := by decide
@[simp] theorem of_lRp_ne_ofB : lRp ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lRn : ofB ≠ lRn := by decide
@[simp] theorem of_lRn_ne_ofB : lRn ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lDir : ofB ≠ lDir := by decide
@[simp] theorem of_lDir_ne_ofB : lDir ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lFle : ofB ≠ lFle := by decide
@[simp] theorem of_lFle_ne_ofB : lFle ≠ ofB := by decide
@[simp] theorem of_ofB_ne_lKb : ofB ≠ lKb := by decide
@[simp] theorem of_lKb_ne_ofB : lKb ≠ ofB := by decide
@[simp] theorem of_ofX_ne_ofA : ofX ≠ ofA := by decide
@[simp] theorem of_ofX_ne_ofB : ofX ≠ ofB := by decide
@[simp] theorem of_ofX_ne_ofY : ofX ≠ ofY := by decide
@[simp] theorem of_ofX_ne_ofP : ofX ≠ ofP := by decide
@[simp] theorem of_ofX_ne_ofQ : ofX ≠ ofQ := by decide
@[simp] theorem of_ofX_ne_ofR : ofX ≠ ofR := by decide
@[simp] theorem of_ofX_ne_kFu : ofX ≠ kFu := by decide
@[simp] theorem of_kFu_ne_ofX : kFu ≠ ofX := by decide
@[simp] theorem of_ofX_ne_kD : ofX ≠ kD := by decide
@[simp] theorem of_kD_ne_ofX : kD ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lFl : ofX ≠ lFl := by decide
@[simp] theorem of_lFl_ne_ofX : lFl ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lDh : ofX ≠ lDh := by decide
@[simp] theorem of_lDh_ne_ofX : lDh ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lDt : ofX ≠ lDt := by decide
@[simp] theorem of_lDt_ne_ofX : lDt ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lDg : ofX ≠ lDg := by decide
@[simp] theorem of_lDg_ne_ofX : lDg ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lDi : ofX ≠ lDi := by decide
@[simp] theorem of_lDi_ne_ofX : lDi ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lRp : ofX ≠ lRp := by decide
@[simp] theorem of_lRp_ne_ofX : lRp ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lRn : ofX ≠ lRn := by decide
@[simp] theorem of_lRn_ne_ofX : lRn ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lDir : ofX ≠ lDir := by decide
@[simp] theorem of_lDir_ne_ofX : lDir ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lFle : ofX ≠ lFle := by decide
@[simp] theorem of_lFle_ne_ofX : lFle ≠ ofX := by decide
@[simp] theorem of_ofX_ne_lKb : ofX ≠ lKb := by decide
@[simp] theorem of_lKb_ne_ofX : lKb ≠ ofX := by decide
@[simp] theorem of_ofY_ne_ofA : ofY ≠ ofA := by decide
@[simp] theorem of_ofY_ne_ofB : ofY ≠ ofB := by decide
@[simp] theorem of_ofY_ne_ofX : ofY ≠ ofX := by decide
@[simp] theorem of_ofY_ne_ofP : ofY ≠ ofP := by decide
@[simp] theorem of_ofY_ne_ofQ : ofY ≠ ofQ := by decide
@[simp] theorem of_ofY_ne_ofR : ofY ≠ ofR := by decide
@[simp] theorem of_ofY_ne_kFu : ofY ≠ kFu := by decide
@[simp] theorem of_kFu_ne_ofY : kFu ≠ ofY := by decide
@[simp] theorem of_ofY_ne_kD : ofY ≠ kD := by decide
@[simp] theorem of_kD_ne_ofY : kD ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lFl : ofY ≠ lFl := by decide
@[simp] theorem of_lFl_ne_ofY : lFl ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lDh : ofY ≠ lDh := by decide
@[simp] theorem of_lDh_ne_ofY : lDh ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lDt : ofY ≠ lDt := by decide
@[simp] theorem of_lDt_ne_ofY : lDt ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lDg : ofY ≠ lDg := by decide
@[simp] theorem of_lDg_ne_ofY : lDg ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lDi : ofY ≠ lDi := by decide
@[simp] theorem of_lDi_ne_ofY : lDi ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lRp : ofY ≠ lRp := by decide
@[simp] theorem of_lRp_ne_ofY : lRp ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lRn : ofY ≠ lRn := by decide
@[simp] theorem of_lRn_ne_ofY : lRn ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lDir : ofY ≠ lDir := by decide
@[simp] theorem of_lDir_ne_ofY : lDir ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lFle : ofY ≠ lFle := by decide
@[simp] theorem of_lFle_ne_ofY : lFle ≠ ofY := by decide
@[simp] theorem of_ofY_ne_lKb : ofY ≠ lKb := by decide
@[simp] theorem of_lKb_ne_ofY : lKb ≠ ofY := by decide
@[simp] theorem of_ofP_ne_ofA : ofP ≠ ofA := by decide
@[simp] theorem of_ofP_ne_ofB : ofP ≠ ofB := by decide
@[simp] theorem of_ofP_ne_ofX : ofP ≠ ofX := by decide
@[simp] theorem of_ofP_ne_ofY : ofP ≠ ofY := by decide
@[simp] theorem of_ofP_ne_ofQ : ofP ≠ ofQ := by decide
@[simp] theorem of_ofP_ne_ofR : ofP ≠ ofR := by decide
@[simp] theorem of_ofP_ne_kFu : ofP ≠ kFu := by decide
@[simp] theorem of_kFu_ne_ofP : kFu ≠ ofP := by decide
@[simp] theorem of_ofP_ne_kD : ofP ≠ kD := by decide
@[simp] theorem of_kD_ne_ofP : kD ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lFl : ofP ≠ lFl := by decide
@[simp] theorem of_lFl_ne_ofP : lFl ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lDh : ofP ≠ lDh := by decide
@[simp] theorem of_lDh_ne_ofP : lDh ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lDt : ofP ≠ lDt := by decide
@[simp] theorem of_lDt_ne_ofP : lDt ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lDg : ofP ≠ lDg := by decide
@[simp] theorem of_lDg_ne_ofP : lDg ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lDi : ofP ≠ lDi := by decide
@[simp] theorem of_lDi_ne_ofP : lDi ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lRp : ofP ≠ lRp := by decide
@[simp] theorem of_lRp_ne_ofP : lRp ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lRn : ofP ≠ lRn := by decide
@[simp] theorem of_lRn_ne_ofP : lRn ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lDir : ofP ≠ lDir := by decide
@[simp] theorem of_lDir_ne_ofP : lDir ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lFle : ofP ≠ lFle := by decide
@[simp] theorem of_lFle_ne_ofP : lFle ≠ ofP := by decide
@[simp] theorem of_ofP_ne_lKb : ofP ≠ lKb := by decide
@[simp] theorem of_lKb_ne_ofP : lKb ≠ ofP := by decide
@[simp] theorem of_ofQ_ne_ofA : ofQ ≠ ofA := by decide
@[simp] theorem of_ofQ_ne_ofB : ofQ ≠ ofB := by decide
@[simp] theorem of_ofQ_ne_ofX : ofQ ≠ ofX := by decide
@[simp] theorem of_ofQ_ne_ofY : ofQ ≠ ofY := by decide
@[simp] theorem of_ofQ_ne_ofP : ofQ ≠ ofP := by decide
@[simp] theorem of_ofQ_ne_ofR : ofQ ≠ ofR := by decide
@[simp] theorem of_ofQ_ne_kFu : ofQ ≠ kFu := by decide
@[simp] theorem of_kFu_ne_ofQ : kFu ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_kD : ofQ ≠ kD := by decide
@[simp] theorem of_kD_ne_ofQ : kD ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lFl : ofQ ≠ lFl := by decide
@[simp] theorem of_lFl_ne_ofQ : lFl ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lDh : ofQ ≠ lDh := by decide
@[simp] theorem of_lDh_ne_ofQ : lDh ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lDt : ofQ ≠ lDt := by decide
@[simp] theorem of_lDt_ne_ofQ : lDt ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lDg : ofQ ≠ lDg := by decide
@[simp] theorem of_lDg_ne_ofQ : lDg ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lDi : ofQ ≠ lDi := by decide
@[simp] theorem of_lDi_ne_ofQ : lDi ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lRp : ofQ ≠ lRp := by decide
@[simp] theorem of_lRp_ne_ofQ : lRp ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lRn : ofQ ≠ lRn := by decide
@[simp] theorem of_lRn_ne_ofQ : lRn ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lDir : ofQ ≠ lDir := by decide
@[simp] theorem of_lDir_ne_ofQ : lDir ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lFle : ofQ ≠ lFle := by decide
@[simp] theorem of_lFle_ne_ofQ : lFle ≠ ofQ := by decide
@[simp] theorem of_ofQ_ne_lKb : ofQ ≠ lKb := by decide
@[simp] theorem of_lKb_ne_ofQ : lKb ≠ ofQ := by decide
@[simp] theorem of_ofR_ne_ofA : ofR ≠ ofA := by decide
@[simp] theorem of_ofR_ne_ofB : ofR ≠ ofB := by decide
@[simp] theorem of_ofR_ne_ofX : ofR ≠ ofX := by decide
@[simp] theorem of_ofR_ne_ofY : ofR ≠ ofY := by decide
@[simp] theorem of_ofR_ne_ofP : ofR ≠ ofP := by decide
@[simp] theorem of_ofR_ne_ofQ : ofR ≠ ofQ := by decide
@[simp] theorem of_ofR_ne_kFu : ofR ≠ kFu := by decide
@[simp] theorem of_kFu_ne_ofR : kFu ≠ ofR := by decide
@[simp] theorem of_ofR_ne_kD : ofR ≠ kD := by decide
@[simp] theorem of_kD_ne_ofR : kD ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lFl : ofR ≠ lFl := by decide
@[simp] theorem of_lFl_ne_ofR : lFl ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lDh : ofR ≠ lDh := by decide
@[simp] theorem of_lDh_ne_ofR : lDh ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lDt : ofR ≠ lDt := by decide
@[simp] theorem of_lDt_ne_ofR : lDt ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lDg : ofR ≠ lDg := by decide
@[simp] theorem of_lDg_ne_ofR : lDg ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lDi : ofR ≠ lDi := by decide
@[simp] theorem of_lDi_ne_ofR : lDi ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lRp : ofR ≠ lRp := by decide
@[simp] theorem of_lRp_ne_ofR : lRp ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lRn : ofR ≠ lRn := by decide
@[simp] theorem of_lRn_ne_ofR : lRn ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lDir : ofR ≠ lDir := by decide
@[simp] theorem of_lDir_ne_ofR : lDir ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lFle : ofR ≠ lFle := by decide
@[simp] theorem of_lFle_ne_ofR : lFle ≠ ofR := by decide
@[simp] theorem of_ofR_ne_lKb : ofR ≠ lKb := by decide
@[simp] theorem of_lKb_ne_ofR : lKb ≠ ofR := by decide

def ofParams : List MlS := [kFu, kD, ofA, ofB]
def ofLocals : List MlS := [ofX, ofY, ofP, ofQ, ofR]
def ofRest : ProgHOL 64 := (.seq (.call (some (some (.local, ofP), none)) fNp [(vv ofA)]) (.ite (.cmp .equal (vv ofP) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ofQ), none)) fNp [(vv ofB)]) (.ite (.cmp .equal (vv ofQ) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ofR), none)) fD [(vv kFu), (vv kD), (.op .sub [(vv ofP), (.const 1)]), (.op .sub [(vv ofQ), (.const 1)])]) (.return (.op .add [(vv ofR), (.const 1)])))))))
def ofBody : ProgHOL 64 := prologue ofLocals (.seq (.call (some (some (.local, ofX), none)) fIz [(vv ofA)]) (.seq (.call (some (some (.local, ofY), none)) fIz [(vv ofB)]) (.ite (.op .and [vv ofX, vv ofY]) (.return (.const 2)) (.ite (tagIsE ofA 8) (.ite (tagIsE ofB 8) (.return (.const 0)) ofRest) ofRest))))

section
variable {σ : Type}

/-- An `Option Bool` answer (`LLeq.obW`); the heap may have grown. -/
def PostOBH (C : Ctx) (o : Option Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = LLeq.obW o ∧ SR (ctxH C H') s' st

theorem postOBH_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOBH C a w s' st → PostOBH C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem obW_some (b : Bool) : LLeq.obW (some b) = boolW b + 1 := by cases b <;> rfl

theorem of_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C)
    (hiz : C.code.lookup fIz = some ([izE].map (fun p => (p, ShapeHOL.one)), izBody C, .one))
    (hnp : C.code.lookup fNp = some ([npE].map (fun p => (p, ShapeHOL.one)), npBody C, .one))
    (hnl : NlCodes C) (hcd : C.code.lookup fD = some (pmap dParams, dE C, .one))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (s : AState) (d : Nat) (hdd : d < 2 ^ 63) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (ofParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) ofBody s
      (defeqOffset (knot mode C n) d a b) (PostOBH C) := by
  refine specR_prologue (postOBH_locals C) (Knot.params_none C ofLocals ofParams _ (by decide) (by decide)) ?_
  unfold defeqOffset
  have hrest : ∀ (H' : List (BitVec 64)) (s' : AState) (Γ : Env), C.H <+: H' →
      Γ.get ofA = some (Enc.idxW a) → Γ.get ofB = some (Enc.idxW b) → Γ.get kFu = some (BitVec.ofNat 64 n) →
      Γ.get kD = some (BitVec.ofNat 64 d) →
      SpecR (σ := σ) (Inv (ctxH C H') s' Γ [] (ctxLocals ++ ofLocals)) ofRest s'
        (natPred? a >>= fun o => match o with
          | none => pure none
          | some x => natPred? b >>= fun o2 => match o2 with
            | none => pure none
            | some y => (knot mode C n).defeq d x y >>= fun ok => pure (some ok)) (PostOBH C) := by
    intro H' s' Γ hp' hA hB hF hDv
    unfold ofRest
    refine specR_callNIH (C := ctxH C H') ofP fNp [npE] [vv ofA] (npBody C) [Enc.idxW a] (by decide) rfl (by decide)
      hnp ⟨by simp [hA], trivial⟩ (UD.PostO (ctxH C H')) (fun o w _ _ => w = optW o)
      (fun o w s'' st ⟨H'', hp'', hw, hsr⟩ => ⟨H'', hp'', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [npE] _ rfl hlk)
        (np_spec ra (ctxH C H') (ctxOK_H hok H') (nlCodes_H hnl H') s' a))
      (fun o w s1 H1 hp1 hw => ?_)
    subst hw
    rcases o with _ | x
    · refine specR_ifI _ 1 (by simp [sev, optW, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨H1, hp'.trans hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, optW, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne x)
      (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    refine specR_callNIH (C := ctxH C H1) ofQ fNp [npE] [vv ofB] (npBody C) [Enc.idxW b] (by decide) rfl (by decide)
      hnp ⟨by simp [hB], trivial⟩ (UD.PostO (ctxH C H1)) (fun o w _ _ => w = optW o)
      (fun o w s'' st ⟨H'', hp'', hw, hsr⟩ => ⟨H'', hp'', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [npE] _ rfl hlk)
        (np_spec ra (ctxH C H1) (ctxOK_H hok H1) (nlCodes_H hnl H1) s1 b))
      (fun o2 w s2 H2 hp2 hw => ?_)
    subst hw
    rcases o2 with _ | y
    · refine specR_ifI _ 1 (by simp [sev, optW, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (LLeq.obW none) rfl
        (fun t ht => ⟨H2, hp'.trans (hp1.trans hp2), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, optW, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne y)
      (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    refine specR_callNIH (C := ctxH C H2) ofR fD dParams [vv kFu, vv kD, .op .sub [vv ofP, .const 1],
      .op .sub [vv ofQ, .const 1]] (dE C) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl
      (by decide) hcd
      ⟨by simp [hF], by simp [hDv], by simp [sev, optW, optWG]; exact BitVec.add_sub_cancel _ _,
        by simp [sev, optW, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
      (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s'' st ⟨H'', hp'', hw, hsr⟩ => ⟨H'', hp'', hw, hsr⟩)
      (fun u hu _ hlk => hD H2 s2 d x y (hp'.trans (hp1.trans hp2)) hdd u hu (fun i hi _ => hlk i (by omega)))
      (fun ok w s3 H3 hp3 hw => ?_)
    subst hw
    exact specR_returnI _ (LLeq.obW (some ok)) (by simp [sev, obW_some])
      (fun t ht => ⟨H3, hp'.trans (hp1.trans (hp2.trans hp3)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_callNIH (C := C) ofX fIz [izE] [vv ofA] (izBody C) [Enc.idxW a] (by decide) rfl (by decide) hiz
    ⟨by simp +decide [Env.get, ofParams, ctxEnv], trivial⟩ (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [izE] _ rfl hlk) (iz_spec C hok s a))
    (fun za w s1 H1 hp1 hw => ?_)
  subst hw
  refine specR_callNIH (C := ctxH C H1) ofY fIz [izE] [vv ofB] (izBody C) [Enc.idxW b] (by decide) rfl (by decide)
    hiz ⟨by simp +decide [Env.get, ofParams, ctxEnv], trivial⟩ (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [izE] _ rfl hlk) (iz_spec (ctxH C H1) (ctxOK_H hok H1) s1 b))
    (fun zb w s2 H2 hp2 hw => ?_)
  subst hw
  have hp12 : C.H <+: H2 := hp1.trans hp2
  by_cases hz : za = true ∧ zb = true
  · obtain ⟨rfl, rfl⟩ := hz
    refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.and_self, ↓reduceIte]
    exact specR_returnI _ (LLeq.obW (some true)) rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hzf : (za && zb) = false := by cases za <;> cases zb <;> simp_all
  refine specR_ifI _ 0 (by cases za <;> cases zb <;> simp_all [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [hzf, Bool.false_eq_true, ↓reduceIte]
  refine Knot.specR_tagIteV ofA a 8 (by decide) (by decide) (by simp +decide [Env.get, ofParams, ctxEnv]) (fun hta => ?_) (fun hta => ?_)
  · refine Knot.specR_tagIteV ofB b 8 (by decide) (by decide) (by simp +decide [Env.get, ofParams, ctxEnv]) (fun htb => ?_) (fun htb => ?_)
    · rw [ite_eq_left (by simp [hta, htb, ETag.lit])]
      exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [ite_eq_right (by intro h; simp [ETag.lit] at h; exact htb h.2)]
      exact hrest H2 s2 _ hp12 (by simp +decide [Env.get, ofParams, ctxEnv]) (by simp +decide [Env.get, ofParams, ctxEnv]) (by simp +decide [Env.get, ofParams, ctxEnv]) (by simp +decide [Env.get, ofParams, ctxEnv])
  · rw [ite_eq_right (by intro h; simp [ETag.lit] at h; exact hta h.1)]
    exact hrest H2 s2 _ hp12 (by simp +decide [Env.get, ofParams, ctxEnv]) (by simp +decide [Env.get, ofParams, ctxEnv]) (by simp +decide [Env.get, ofParams, ctxEnv]) (by simp +decide [Env.get, ofParams, ctxEnv])

end

end ConPanqueque.T.WC
