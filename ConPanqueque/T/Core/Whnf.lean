import ConPanqueque.T.Big.ReduceNat
import ConPanqueque.T.LoopT
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfBody`: the reduction loop

The twin's `whnfLoop` iterates `whnfStep` — `whnfCore`, then `reduceNat`, then `unfoldDefinition` — on a step
budget of `2^62`. The port runs the same steps in a `while` loop, threading the twin (`specR_whileT`).
-/

namespace ConPanqueque.T.WB

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big

def wE := ofString "wbe"
def wF := ofString "wbf"
def wG := ofString "wbg"
def w1 := ofString "wb1"
def wR := ofString "wbr"
def wU := ofString "wbu"
def fRN := ofString "reduceNat"

@[simp] theorem wb_wE_ne_wF : wE ≠ wF := by decide
@[simp] theorem wb_wE_ne_wG : wE ≠ wG := by decide
@[simp] theorem wb_wE_ne_w1 : wE ≠ w1 := by decide
@[simp] theorem wb_wE_ne_wR : wE ≠ wR := by decide
@[simp] theorem wb_wE_ne_wU : wE ≠ wU := by decide
@[simp] theorem wb_wE_ne_kFu : wE ≠ kFu := by decide
@[simp] theorem wb_kFu_ne_wE : kFu ≠ wE := by decide
@[simp] theorem wb_wE_ne_kD : wE ≠ kD := by decide
@[simp] theorem wb_kD_ne_wE : kD ≠ wE := by decide
@[simp] theorem wb_wE_ne_kE : wE ≠ kE := by decide
@[simp] theorem wb_kE_ne_wE : kE ≠ wE := by decide
@[simp] theorem wb_wE_ne_kC : wE ≠ kC := by decide
@[simp] theorem wb_kC_ne_wE : kC ≠ wE := by decide
@[simp] theorem wb_wE_ne_lFle : wE ≠ lFle := by decide
@[simp] theorem wb_lFle_ne_wE : lFle ≠ wE := by decide
@[simp] theorem wb_wE_ne_lDir : wE ≠ lDir := by decide
@[simp] theorem wb_lDir_ne_wE : lDir ≠ wE := by decide
@[simp] theorem wb_wE_ne_lKb : wE ≠ lKb := by decide
@[simp] theorem wb_lKb_ne_wE : lKb ≠ wE := by decide
@[simp] theorem wb_wE_ne_lFl : wE ≠ lFl := by decide
@[simp] theorem wb_lFl_ne_wE : lFl ≠ wE := by decide
@[simp] theorem wb_wE_ne_lFln : wE ≠ lFln := by decide
@[simp] theorem wb_lFln_ne_wE : lFln ≠ wE := by decide
@[simp] theorem wb_wE_ne_lFll : wE ≠ lFll := by decide
@[simp] theorem wb_lFll_ne_wE : lFll ≠ wE := by decide
@[simp] theorem wb_wE_ne_lFls : wE ≠ lFls := by decide
@[simp] theorem wb_lFls_ne_wE : lFls ≠ wE := by decide
@[simp] theorem wb_wF_ne_wE : wF ≠ wE := by decide
@[simp] theorem wb_wF_ne_wG : wF ≠ wG := by decide
@[simp] theorem wb_wF_ne_w1 : wF ≠ w1 := by decide
@[simp] theorem wb_wF_ne_wR : wF ≠ wR := by decide
@[simp] theorem wb_wF_ne_wU : wF ≠ wU := by decide
@[simp] theorem wb_wF_ne_kFu : wF ≠ kFu := by decide
@[simp] theorem wb_kFu_ne_wF : kFu ≠ wF := by decide
@[simp] theorem wb_wF_ne_kD : wF ≠ kD := by decide
@[simp] theorem wb_kD_ne_wF : kD ≠ wF := by decide
@[simp] theorem wb_wF_ne_kE : wF ≠ kE := by decide
@[simp] theorem wb_kE_ne_wF : kE ≠ wF := by decide
@[simp] theorem wb_wF_ne_kC : wF ≠ kC := by decide
@[simp] theorem wb_kC_ne_wF : kC ≠ wF := by decide
@[simp] theorem wb_wF_ne_lFle : wF ≠ lFle := by decide
@[simp] theorem wb_lFle_ne_wF : lFle ≠ wF := by decide
@[simp] theorem wb_wF_ne_lDir : wF ≠ lDir := by decide
@[simp] theorem wb_lDir_ne_wF : lDir ≠ wF := by decide
@[simp] theorem wb_wF_ne_lKb : wF ≠ lKb := by decide
@[simp] theorem wb_lKb_ne_wF : lKb ≠ wF := by decide
@[simp] theorem wb_wF_ne_lFl : wF ≠ lFl := by decide
@[simp] theorem wb_lFl_ne_wF : lFl ≠ wF := by decide
@[simp] theorem wb_wF_ne_lFln : wF ≠ lFln := by decide
@[simp] theorem wb_lFln_ne_wF : lFln ≠ wF := by decide
@[simp] theorem wb_wF_ne_lFll : wF ≠ lFll := by decide
@[simp] theorem wb_lFll_ne_wF : lFll ≠ wF := by decide
@[simp] theorem wb_wF_ne_lFls : wF ≠ lFls := by decide
@[simp] theorem wb_lFls_ne_wF : lFls ≠ wF := by decide
@[simp] theorem wb_wG_ne_wE : wG ≠ wE := by decide
@[simp] theorem wb_wG_ne_wF : wG ≠ wF := by decide
@[simp] theorem wb_wG_ne_w1 : wG ≠ w1 := by decide
@[simp] theorem wb_wG_ne_wR : wG ≠ wR := by decide
@[simp] theorem wb_wG_ne_wU : wG ≠ wU := by decide
@[simp] theorem wb_wG_ne_kFu : wG ≠ kFu := by decide
@[simp] theorem wb_kFu_ne_wG : kFu ≠ wG := by decide
@[simp] theorem wb_wG_ne_kD : wG ≠ kD := by decide
@[simp] theorem wb_kD_ne_wG : kD ≠ wG := by decide
@[simp] theorem wb_wG_ne_kE : wG ≠ kE := by decide
@[simp] theorem wb_kE_ne_wG : kE ≠ wG := by decide
@[simp] theorem wb_wG_ne_kC : wG ≠ kC := by decide
@[simp] theorem wb_kC_ne_wG : kC ≠ wG := by decide
@[simp] theorem wb_wG_ne_lFle : wG ≠ lFle := by decide
@[simp] theorem wb_lFle_ne_wG : lFle ≠ wG := by decide
@[simp] theorem wb_wG_ne_lDir : wG ≠ lDir := by decide
@[simp] theorem wb_lDir_ne_wG : lDir ≠ wG := by decide
@[simp] theorem wb_wG_ne_lKb : wG ≠ lKb := by decide
@[simp] theorem wb_lKb_ne_wG : lKb ≠ wG := by decide
@[simp] theorem wb_wG_ne_lFl : wG ≠ lFl := by decide
@[simp] theorem wb_lFl_ne_wG : lFl ≠ wG := by decide
@[simp] theorem wb_wG_ne_lFln : wG ≠ lFln := by decide
@[simp] theorem wb_lFln_ne_wG : lFln ≠ wG := by decide
@[simp] theorem wb_wG_ne_lFll : wG ≠ lFll := by decide
@[simp] theorem wb_lFll_ne_wG : lFll ≠ wG := by decide
@[simp] theorem wb_wG_ne_lFls : wG ≠ lFls := by decide
@[simp] theorem wb_lFls_ne_wG : lFls ≠ wG := by decide
@[simp] theorem wb_w1_ne_wE : w1 ≠ wE := by decide
@[simp] theorem wb_w1_ne_wF : w1 ≠ wF := by decide
@[simp] theorem wb_w1_ne_wG : w1 ≠ wG := by decide
@[simp] theorem wb_w1_ne_wR : w1 ≠ wR := by decide
@[simp] theorem wb_w1_ne_wU : w1 ≠ wU := by decide
@[simp] theorem wb_w1_ne_kFu : w1 ≠ kFu := by decide
@[simp] theorem wb_kFu_ne_w1 : kFu ≠ w1 := by decide
@[simp] theorem wb_w1_ne_kD : w1 ≠ kD := by decide
@[simp] theorem wb_kD_ne_w1 : kD ≠ w1 := by decide
@[simp] theorem wb_w1_ne_kE : w1 ≠ kE := by decide
@[simp] theorem wb_kE_ne_w1 : kE ≠ w1 := by decide
@[simp] theorem wb_w1_ne_kC : w1 ≠ kC := by decide
@[simp] theorem wb_kC_ne_w1 : kC ≠ w1 := by decide
@[simp] theorem wb_w1_ne_lFle : w1 ≠ lFle := by decide
@[simp] theorem wb_lFle_ne_w1 : lFle ≠ w1 := by decide
@[simp] theorem wb_w1_ne_lDir : w1 ≠ lDir := by decide
@[simp] theorem wb_lDir_ne_w1 : lDir ≠ w1 := by decide
@[simp] theorem wb_w1_ne_lKb : w1 ≠ lKb := by decide
@[simp] theorem wb_lKb_ne_w1 : lKb ≠ w1 := by decide
@[simp] theorem wb_w1_ne_lFl : w1 ≠ lFl := by decide
@[simp] theorem wb_lFl_ne_w1 : lFl ≠ w1 := by decide
@[simp] theorem wb_w1_ne_lFln : w1 ≠ lFln := by decide
@[simp] theorem wb_lFln_ne_w1 : lFln ≠ w1 := by decide
@[simp] theorem wb_w1_ne_lFll : w1 ≠ lFll := by decide
@[simp] theorem wb_lFll_ne_w1 : lFll ≠ w1 := by decide
@[simp] theorem wb_w1_ne_lFls : w1 ≠ lFls := by decide
@[simp] theorem wb_lFls_ne_w1 : lFls ≠ w1 := by decide
@[simp] theorem wb_wR_ne_wE : wR ≠ wE := by decide
@[simp] theorem wb_wR_ne_wF : wR ≠ wF := by decide
@[simp] theorem wb_wR_ne_wG : wR ≠ wG := by decide
@[simp] theorem wb_wR_ne_w1 : wR ≠ w1 := by decide
@[simp] theorem wb_wR_ne_wU : wR ≠ wU := by decide
@[simp] theorem wb_wR_ne_kFu : wR ≠ kFu := by decide
@[simp] theorem wb_kFu_ne_wR : kFu ≠ wR := by decide
@[simp] theorem wb_wR_ne_kD : wR ≠ kD := by decide
@[simp] theorem wb_kD_ne_wR : kD ≠ wR := by decide
@[simp] theorem wb_wR_ne_kE : wR ≠ kE := by decide
@[simp] theorem wb_kE_ne_wR : kE ≠ wR := by decide
@[simp] theorem wb_wR_ne_kC : wR ≠ kC := by decide
@[simp] theorem wb_kC_ne_wR : kC ≠ wR := by decide
@[simp] theorem wb_wR_ne_lFle : wR ≠ lFle := by decide
@[simp] theorem wb_lFle_ne_wR : lFle ≠ wR := by decide
@[simp] theorem wb_wR_ne_lDir : wR ≠ lDir := by decide
@[simp] theorem wb_lDir_ne_wR : lDir ≠ wR := by decide
@[simp] theorem wb_wR_ne_lKb : wR ≠ lKb := by decide
@[simp] theorem wb_lKb_ne_wR : lKb ≠ wR := by decide
@[simp] theorem wb_wR_ne_lFl : wR ≠ lFl := by decide
@[simp] theorem wb_lFl_ne_wR : lFl ≠ wR := by decide
@[simp] theorem wb_wR_ne_lFln : wR ≠ lFln := by decide
@[simp] theorem wb_lFln_ne_wR : lFln ≠ wR := by decide
@[simp] theorem wb_wR_ne_lFll : wR ≠ lFll := by decide
@[simp] theorem wb_lFll_ne_wR : lFll ≠ wR := by decide
@[simp] theorem wb_wR_ne_lFls : wR ≠ lFls := by decide
@[simp] theorem wb_lFls_ne_wR : lFls ≠ wR := by decide
@[simp] theorem wb_wU_ne_wE : wU ≠ wE := by decide
@[simp] theorem wb_wU_ne_wF : wU ≠ wF := by decide
@[simp] theorem wb_wU_ne_wG : wU ≠ wG := by decide
@[simp] theorem wb_wU_ne_w1 : wU ≠ w1 := by decide
@[simp] theorem wb_wU_ne_wR : wU ≠ wR := by decide
@[simp] theorem wb_wU_ne_kFu : wU ≠ kFu := by decide
@[simp] theorem wb_kFu_ne_wU : kFu ≠ wU := by decide
@[simp] theorem wb_wU_ne_kD : wU ≠ kD := by decide
@[simp] theorem wb_kD_ne_wU : kD ≠ wU := by decide
@[simp] theorem wb_wU_ne_kE : wU ≠ kE := by decide
@[simp] theorem wb_kE_ne_wU : kE ≠ wU := by decide
@[simp] theorem wb_wU_ne_kC : wU ≠ kC := by decide
@[simp] theorem wb_kC_ne_wU : kC ≠ wU := by decide
@[simp] theorem wb_wU_ne_lFle : wU ≠ lFle := by decide
@[simp] theorem wb_lFle_ne_wU : lFle ≠ wU := by decide
@[simp] theorem wb_wU_ne_lDir : wU ≠ lDir := by decide
@[simp] theorem wb_lDir_ne_wU : lDir ≠ wU := by decide
@[simp] theorem wb_wU_ne_lKb : wU ≠ lKb := by decide
@[simp] theorem wb_lKb_ne_wU : lKb ≠ wU := by decide
@[simp] theorem wb_wU_ne_lFl : wU ≠ lFl := by decide
@[simp] theorem wb_lFl_ne_wU : lFl ≠ wU := by decide
@[simp] theorem wb_wU_ne_lFln : wU ≠ lFln := by decide
@[simp] theorem wb_lFln_ne_wU : lFln ≠ wU := by decide
@[simp] theorem wb_wU_ne_lFll : wU ≠ lFll := by decide
@[simp] theorem wb_lFll_ne_wU : lFll ≠ wU := by decide
@[simp] theorem wb_wU_ne_lFls : wU ≠ lFls := by decide
@[simp] theorem wb_lFls_ne_wU : lFls ≠ wU := by decide

def wbStep : ProgHOL 64 :=
  .ite (.cmp .equal (vv wF) (.const 0)) hang
  (.seq (.assign .local wF (.op .sub [vv wF, .const 1]))
  (.seq (.call (some (some (.local, w1), none)) fWC [vv kFu, .const 0, vv kD, vv wE])
  (.seq (.call (some (some (.local, wR), none)) fRN [vv kFu, vv kD, vv w1])
  (.ite (.cmp .notEqual (vv wR) (.const 0))
    (.seq (.assign .local wE (.op .sub [vv wR, .const 1])) (.ite (tagIsE wE 8) (.assign .local wG (.const 0)) .skip))
    (.seq (.call (some (some (.local, wU), none)) UD.fUnfold [vv w1])
      (.ite (.cmp .notEqual (vv wU) (.const 0)) (.assign .local wE (.op .sub [vv wU, .const 1]))
        (.seq (.assign .local wE (vv w1)) (.assign .local wG (.const 0)))))))))

def wbCore : ProgHOL 64 :=
  .seq (.assign .local wE (vv kE)) (.seq (.assign .local wF (.const (BitVec.ofNat 64 whnfLoopFuel)))
  (.seq (.assign .local wG (.const 1)) (.seq (.while (vv wG) wbStep) (.return (vv wE)))))

def wbLocals : List MlS := [wE, wF, wG, w1, wR, wU]
def wbBody : ProgHOL 64 := prologue wbLocals wbCore

section
variable {σ : Type}

theorem step_ifI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {Q : PState σ → Prop}
    {c1 c2 : ProgHOL 64} (e : ExpHOL 64) (w : BitVec 64) (he : sev Γ e = some w)
    (h1 : w ≠ 0 → Step (Inv C s Γ M D) c1 Q) (h2 : w = 0 → Step (Inv C s Γ M D) c2 Q) :
    Step (Inv C s Γ M D) (.ite e c1 c2) Q := by
  intro t ht
  rw [ite_word t e c1 c2 w (inv_ev ht he)]
  by_cases hw : w ≠ 0
  · rw [if_pos hw]; exact h1 hw t ht
  · rw [if_neg hw]; exact h2 (by simpa using hw) t ht

theorem step_hangI {P Q : PState σ → Prop} : Step P hang Q :=
  fun t _ => Or.inl (Or.inl (hang_spec t.clock t rfl))

theorem step_ex {α : Type} {P : α → PState σ → Prop} {Q : PState σ → Prop} {c : ProgHOL 64}
    (h : ∀ a, Step (P a) c Q) : Step (fun t => ∃ a, P a t) c Q :=
  fun t ⟨a, ht⟩ => h a t ht

/-! ## The twin's loop, one step at a time -/

theorem whnfLoop_succ (r : CoreFnsA) (fe : IFEnv) (d f : Nat) (e : EIdx) (s : AState) :
    whnfLoop r fe d (f + 1) e s = (whnfStep r fe d e >>= fun st => match st with
      | .done v => pure v
      | .cont e' => whnfLoop r fe d f e') s := rfl

theorem whnfStep_lit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e e1 e2 : EIdx) (s1 s2 s3 : AState)
    (h1 : r.whnfCore false d e s1 = .ok (e1, s2)) (h2 : reduceNat r fe d e1 s2 = .ok (some e2, s3)) :
    whnfStep r fe d e s1 = .ok (if e2.tag == ETag.lit then .done e2 else .cont e2, s3) := by
  show (Except.bind (r.whnfCore false d e s1) fun x => _) = _
  rw [h1]; simp only [Except.bind]
  show (Except.bind (reduceNat r fe d e1 s2) fun x => _) = _
  rw [h2]; simp only [Except.bind]
  split <;> rfl

theorem whnfStep_unf (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e e1 : EIdx) (o : Option EIdx) (s1 s2 s3 s4 : AState)
    (h1 : r.whnfCore false d e s1 = .ok (e1, s2)) (h2 : reduceNat r fe d e1 s2 = .ok (none, s3))
    (h3 : unfoldDefinition fe e1 s3 = .ok (o, s4)) :
    whnfStep r fe d e s1 = .ok (match o with | some e2 => .cont e2 | none => .done e1, s4) := by
  show (Except.bind (r.whnfCore false d e s1) fun x => _) = _
  rw [h1]; simp only [Except.bind]
  show (Except.bind (reduceNat r fe d e1 s2) fun x => _) = _
  rw [h2]; simp only [Except.bind]
  show (Except.bind (unfoldDefinition fe e1 s3) fun x => _) = _
  cases o <;> (simp only [h3, Except.bind]; rfl)

end

end ConPanqueque.T.WB
