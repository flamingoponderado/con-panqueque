import ConPanqueque.T.Big.LitIntern
import ConPanqueque.T.Big.SizeMath
import ConPanqueque.T.Big.Gcd
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The common tail of a literal operation

`nbTail`: the result block (in `nbr`) against `maxNatSize` — a block of more bytes than allowed declines (halts) —
then the literal is interned from it and returned as `some h` (`h + 1`). `tail_plain` is the twin's
`internE >>= some`; `tail_sized` is its `litNatSized`, whose refusal is exactly the port's halt.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def nA := ofString "nba"
def nB := ofString "nbb"
def nX := ofString "nbx"
def nY := ofString "nby"
def nR := ofString "nbr"
def nL := ofString "nbl"
def nM := ofString "nbm"
def nH := ofString "nbh"
def nC := ofString "nbc"
def nE := ofString "nbe"
def nS := ofString "nbs"
def nT := ofString "nbt"
def fLitB := ofString "litBlk"

@[simp] theorem nb_nA_ne_nB : nA ≠ nB := by decide
@[simp] theorem nb_nA_ne_nX : nA ≠ nX := by decide
@[simp] theorem nb_nA_ne_nY : nA ≠ nY := by decide
@[simp] theorem nb_nA_ne_nR : nA ≠ nR := by decide
@[simp] theorem nb_nA_ne_nL : nA ≠ nL := by decide
@[simp] theorem nb_nA_ne_nM : nA ≠ nM := by decide
@[simp] theorem nb_nA_ne_nH : nA ≠ nH := by decide
@[simp] theorem nb_nA_ne_nC : nA ≠ nC := by decide
@[simp] theorem nb_nA_ne_nE : nA ≠ nE := by decide
@[simp] theorem nb_nA_ne_nS : nA ≠ nS := by decide
@[simp] theorem nb_nA_ne_nT : nA ≠ nT := by decide
@[simp] theorem nb_nA_ne_iLx : nA ≠ iLx := by decide
@[simp] theorem nb_nA_ne_lFle : nA ≠ lFle := by decide
@[simp] theorem nb_nA_ne_lDir : nA ≠ lDir := by decide
@[simp] theorem nb_nA_ne_lKb : nA ≠ lKb := by decide
@[simp] theorem nb_nB_ne_nA : nB ≠ nA := by decide
@[simp] theorem nb_nB_ne_nX : nB ≠ nX := by decide
@[simp] theorem nb_nB_ne_nY : nB ≠ nY := by decide
@[simp] theorem nb_nB_ne_nR : nB ≠ nR := by decide
@[simp] theorem nb_nB_ne_nL : nB ≠ nL := by decide
@[simp] theorem nb_nB_ne_nM : nB ≠ nM := by decide
@[simp] theorem nb_nB_ne_nH : nB ≠ nH := by decide
@[simp] theorem nb_nB_ne_nC : nB ≠ nC := by decide
@[simp] theorem nb_nB_ne_nE : nB ≠ nE := by decide
@[simp] theorem nb_nB_ne_nS : nB ≠ nS := by decide
@[simp] theorem nb_nB_ne_nT : nB ≠ nT := by decide
@[simp] theorem nb_nB_ne_iLx : nB ≠ iLx := by decide
@[simp] theorem nb_nB_ne_lFle : nB ≠ lFle := by decide
@[simp] theorem nb_nB_ne_lDir : nB ≠ lDir := by decide
@[simp] theorem nb_nB_ne_lKb : nB ≠ lKb := by decide
@[simp] theorem nb_nX_ne_nA : nX ≠ nA := by decide
@[simp] theorem nb_nX_ne_nB : nX ≠ nB := by decide
@[simp] theorem nb_nX_ne_nY : nX ≠ nY := by decide
@[simp] theorem nb_nX_ne_nR : nX ≠ nR := by decide
@[simp] theorem nb_nX_ne_nL : nX ≠ nL := by decide
@[simp] theorem nb_nX_ne_nM : nX ≠ nM := by decide
@[simp] theorem nb_nX_ne_nH : nX ≠ nH := by decide
@[simp] theorem nb_nX_ne_nC : nX ≠ nC := by decide
@[simp] theorem nb_nX_ne_nE : nX ≠ nE := by decide
@[simp] theorem nb_nX_ne_nS : nX ≠ nS := by decide
@[simp] theorem nb_nX_ne_nT : nX ≠ nT := by decide
@[simp] theorem nb_nX_ne_iLx : nX ≠ iLx := by decide
@[simp] theorem nb_nX_ne_lFle : nX ≠ lFle := by decide
@[simp] theorem nb_nX_ne_lDir : nX ≠ lDir := by decide
@[simp] theorem nb_nX_ne_lKb : nX ≠ lKb := by decide
@[simp] theorem nb_nY_ne_nA : nY ≠ nA := by decide
@[simp] theorem nb_nY_ne_nB : nY ≠ nB := by decide
@[simp] theorem nb_nY_ne_nX : nY ≠ nX := by decide
@[simp] theorem nb_nY_ne_nR : nY ≠ nR := by decide
@[simp] theorem nb_nY_ne_nL : nY ≠ nL := by decide
@[simp] theorem nb_nY_ne_nM : nY ≠ nM := by decide
@[simp] theorem nb_nY_ne_nH : nY ≠ nH := by decide
@[simp] theorem nb_nY_ne_nC : nY ≠ nC := by decide
@[simp] theorem nb_nY_ne_nE : nY ≠ nE := by decide
@[simp] theorem nb_nY_ne_nS : nY ≠ nS := by decide
@[simp] theorem nb_nY_ne_nT : nY ≠ nT := by decide
@[simp] theorem nb_nY_ne_iLx : nY ≠ iLx := by decide
@[simp] theorem nb_nY_ne_lFle : nY ≠ lFle := by decide
@[simp] theorem nb_nY_ne_lDir : nY ≠ lDir := by decide
@[simp] theorem nb_nY_ne_lKb : nY ≠ lKb := by decide
@[simp] theorem nb_nR_ne_nA : nR ≠ nA := by decide
@[simp] theorem nb_nR_ne_nB : nR ≠ nB := by decide
@[simp] theorem nb_nR_ne_nX : nR ≠ nX := by decide
@[simp] theorem nb_nR_ne_nY : nR ≠ nY := by decide
@[simp] theorem nb_nR_ne_nL : nR ≠ nL := by decide
@[simp] theorem nb_nR_ne_nM : nR ≠ nM := by decide
@[simp] theorem nb_nR_ne_nH : nR ≠ nH := by decide
@[simp] theorem nb_nR_ne_nC : nR ≠ nC := by decide
@[simp] theorem nb_nR_ne_nE : nR ≠ nE := by decide
@[simp] theorem nb_nR_ne_nS : nR ≠ nS := by decide
@[simp] theorem nb_nR_ne_nT : nR ≠ nT := by decide
@[simp] theorem nb_nR_ne_iLx : nR ≠ iLx := by decide
@[simp] theorem nb_nR_ne_lFle : nR ≠ lFle := by decide
@[simp] theorem nb_nR_ne_lDir : nR ≠ lDir := by decide
@[simp] theorem nb_nR_ne_lKb : nR ≠ lKb := by decide
@[simp] theorem nb_nL_ne_nA : nL ≠ nA := by decide
@[simp] theorem nb_nL_ne_nB : nL ≠ nB := by decide
@[simp] theorem nb_nL_ne_nX : nL ≠ nX := by decide
@[simp] theorem nb_nL_ne_nY : nL ≠ nY := by decide
@[simp] theorem nb_nL_ne_nR : nL ≠ nR := by decide
@[simp] theorem nb_nL_ne_nM : nL ≠ nM := by decide
@[simp] theorem nb_nL_ne_nH : nL ≠ nH := by decide
@[simp] theorem nb_nL_ne_nC : nL ≠ nC := by decide
@[simp] theorem nb_nL_ne_nE : nL ≠ nE := by decide
@[simp] theorem nb_nL_ne_nS : nL ≠ nS := by decide
@[simp] theorem nb_nL_ne_nT : nL ≠ nT := by decide
@[simp] theorem nb_nL_ne_iLx : nL ≠ iLx := by decide
@[simp] theorem nb_nL_ne_lFle : nL ≠ lFle := by decide
@[simp] theorem nb_nL_ne_lDir : nL ≠ lDir := by decide
@[simp] theorem nb_nL_ne_lKb : nL ≠ lKb := by decide
@[simp] theorem nb_nM_ne_nA : nM ≠ nA := by decide
@[simp] theorem nb_nM_ne_nB : nM ≠ nB := by decide
@[simp] theorem nb_nM_ne_nX : nM ≠ nX := by decide
@[simp] theorem nb_nM_ne_nY : nM ≠ nY := by decide
@[simp] theorem nb_nM_ne_nR : nM ≠ nR := by decide
@[simp] theorem nb_nM_ne_nL : nM ≠ nL := by decide
@[simp] theorem nb_nM_ne_nH : nM ≠ nH := by decide
@[simp] theorem nb_nM_ne_nC : nM ≠ nC := by decide
@[simp] theorem nb_nM_ne_nE : nM ≠ nE := by decide
@[simp] theorem nb_nM_ne_nS : nM ≠ nS := by decide
@[simp] theorem nb_nM_ne_nT : nM ≠ nT := by decide
@[simp] theorem nb_nM_ne_iLx : nM ≠ iLx := by decide
@[simp] theorem nb_nM_ne_lFle : nM ≠ lFle := by decide
@[simp] theorem nb_nM_ne_lDir : nM ≠ lDir := by decide
@[simp] theorem nb_nM_ne_lKb : nM ≠ lKb := by decide
@[simp] theorem nb_nH_ne_nA : nH ≠ nA := by decide
@[simp] theorem nb_nH_ne_nB : nH ≠ nB := by decide
@[simp] theorem nb_nH_ne_nX : nH ≠ nX := by decide
@[simp] theorem nb_nH_ne_nY : nH ≠ nY := by decide
@[simp] theorem nb_nH_ne_nR : nH ≠ nR := by decide
@[simp] theorem nb_nH_ne_nL : nH ≠ nL := by decide
@[simp] theorem nb_nH_ne_nM : nH ≠ nM := by decide
@[simp] theorem nb_nH_ne_nC : nH ≠ nC := by decide
@[simp] theorem nb_nH_ne_nE : nH ≠ nE := by decide
@[simp] theorem nb_nH_ne_nS : nH ≠ nS := by decide
@[simp] theorem nb_nH_ne_nT : nH ≠ nT := by decide
@[simp] theorem nb_nH_ne_iLx : nH ≠ iLx := by decide
@[simp] theorem nb_nH_ne_lFle : nH ≠ lFle := by decide
@[simp] theorem nb_nH_ne_lDir : nH ≠ lDir := by decide
@[simp] theorem nb_nH_ne_lKb : nH ≠ lKb := by decide
@[simp] theorem nb_nC_ne_nA : nC ≠ nA := by decide
@[simp] theorem nb_nC_ne_nB : nC ≠ nB := by decide
@[simp] theorem nb_nC_ne_nX : nC ≠ nX := by decide
@[simp] theorem nb_nC_ne_nY : nC ≠ nY := by decide
@[simp] theorem nb_nC_ne_nR : nC ≠ nR := by decide
@[simp] theorem nb_nC_ne_nL : nC ≠ nL := by decide
@[simp] theorem nb_nC_ne_nM : nC ≠ nM := by decide
@[simp] theorem nb_nC_ne_nH : nC ≠ nH := by decide
@[simp] theorem nb_nC_ne_nE : nC ≠ nE := by decide
@[simp] theorem nb_nC_ne_nS : nC ≠ nS := by decide
@[simp] theorem nb_nC_ne_nT : nC ≠ nT := by decide
@[simp] theorem nb_nC_ne_iLx : nC ≠ iLx := by decide
@[simp] theorem nb_nC_ne_lFle : nC ≠ lFle := by decide
@[simp] theorem nb_nC_ne_lDir : nC ≠ lDir := by decide
@[simp] theorem nb_nC_ne_lKb : nC ≠ lKb := by decide
@[simp] theorem nb_nE_ne_nA : nE ≠ nA := by decide
@[simp] theorem nb_nE_ne_nB : nE ≠ nB := by decide
@[simp] theorem nb_nE_ne_nX : nE ≠ nX := by decide
@[simp] theorem nb_nE_ne_nY : nE ≠ nY := by decide
@[simp] theorem nb_nE_ne_nR : nE ≠ nR := by decide
@[simp] theorem nb_nE_ne_nL : nE ≠ nL := by decide
@[simp] theorem nb_nE_ne_nM : nE ≠ nM := by decide
@[simp] theorem nb_nE_ne_nH : nE ≠ nH := by decide
@[simp] theorem nb_nE_ne_nC : nE ≠ nC := by decide
@[simp] theorem nb_nE_ne_nS : nE ≠ nS := by decide
@[simp] theorem nb_nE_ne_nT : nE ≠ nT := by decide
@[simp] theorem nb_nE_ne_iLx : nE ≠ iLx := by decide
@[simp] theorem nb_nE_ne_lFle : nE ≠ lFle := by decide
@[simp] theorem nb_nE_ne_lDir : nE ≠ lDir := by decide
@[simp] theorem nb_nE_ne_lKb : nE ≠ lKb := by decide
@[simp] theorem nb_nS_ne_nA : nS ≠ nA := by decide
@[simp] theorem nb_nS_ne_nB : nS ≠ nB := by decide
@[simp] theorem nb_nS_ne_nX : nS ≠ nX := by decide
@[simp] theorem nb_nS_ne_nY : nS ≠ nY := by decide
@[simp] theorem nb_nS_ne_nR : nS ≠ nR := by decide
@[simp] theorem nb_nS_ne_nL : nS ≠ nL := by decide
@[simp] theorem nb_nS_ne_nM : nS ≠ nM := by decide
@[simp] theorem nb_nS_ne_nH : nS ≠ nH := by decide
@[simp] theorem nb_nS_ne_nC : nS ≠ nC := by decide
@[simp] theorem nb_nS_ne_nE : nS ≠ nE := by decide
@[simp] theorem nb_nS_ne_nT : nS ≠ nT := by decide
@[simp] theorem nb_nS_ne_iLx : nS ≠ iLx := by decide
@[simp] theorem nb_nS_ne_lFle : nS ≠ lFle := by decide
@[simp] theorem nb_nS_ne_lDir : nS ≠ lDir := by decide
@[simp] theorem nb_nS_ne_lKb : nS ≠ lKb := by decide
@[simp] theorem nb_nT_ne_nA : nT ≠ nA := by decide
@[simp] theorem nb_nT_ne_nB : nT ≠ nB := by decide
@[simp] theorem nb_nT_ne_nX : nT ≠ nX := by decide
@[simp] theorem nb_nT_ne_nY : nT ≠ nY := by decide
@[simp] theorem nb_nT_ne_nR : nT ≠ nR := by decide
@[simp] theorem nb_nT_ne_nL : nT ≠ nL := by decide
@[simp] theorem nb_nT_ne_nM : nT ≠ nM := by decide
@[simp] theorem nb_nT_ne_nH : nT ≠ nH := by decide
@[simp] theorem nb_nT_ne_nC : nT ≠ nC := by decide
@[simp] theorem nb_nT_ne_nE : nT ≠ nE := by decide
@[simp] theorem nb_nT_ne_nS : nT ≠ nS := by decide
@[simp] theorem nb_nT_ne_iLx : nT ≠ iLx := by decide
@[simp] theorem nb_nT_ne_lFle : nT ≠ lFle := by decide
@[simp] theorem nb_nT_ne_lDir : nT ≠ lDir := by decide
@[simp] theorem nb_nT_ne_lKb : nT ≠ lKb := by decide
@[simp] theorem nb_iLx_ne_nA : iLx ≠ nA := by decide
@[simp] theorem nb_iLx_ne_nB : iLx ≠ nB := by decide
@[simp] theorem nb_iLx_ne_nX : iLx ≠ nX := by decide
@[simp] theorem nb_iLx_ne_nY : iLx ≠ nY := by decide
@[simp] theorem nb_iLx_ne_nR : iLx ≠ nR := by decide
@[simp] theorem nb_iLx_ne_nL : iLx ≠ nL := by decide
@[simp] theorem nb_iLx_ne_nM : iLx ≠ nM := by decide
@[simp] theorem nb_iLx_ne_nH : iLx ≠ nH := by decide
@[simp] theorem nb_iLx_ne_nC : iLx ≠ nC := by decide
@[simp] theorem nb_iLx_ne_nE : iLx ≠ nE := by decide
@[simp] theorem nb_iLx_ne_nS : iLx ≠ nS := by decide
@[simp] theorem nb_iLx_ne_nT : iLx ≠ nT := by decide
@[simp] theorem nb_lFle_ne_nA : lFle ≠ nA := by decide
@[simp] theorem nb_lFle_ne_nB : lFle ≠ nB := by decide
@[simp] theorem nb_lFle_ne_nX : lFle ≠ nX := by decide
@[simp] theorem nb_lFle_ne_nY : lFle ≠ nY := by decide
@[simp] theorem nb_lFle_ne_nR : lFle ≠ nR := by decide
@[simp] theorem nb_lFle_ne_nL : lFle ≠ nL := by decide
@[simp] theorem nb_lFle_ne_nM : lFle ≠ nM := by decide
@[simp] theorem nb_lFle_ne_nH : lFle ≠ nH := by decide
@[simp] theorem nb_lFle_ne_nC : lFle ≠ nC := by decide
@[simp] theorem nb_lFle_ne_nE : lFle ≠ nE := by decide
@[simp] theorem nb_lFle_ne_nS : lFle ≠ nS := by decide
@[simp] theorem nb_lFle_ne_nT : lFle ≠ nT := by decide
@[simp] theorem nb_lDir_ne_nA : lDir ≠ nA := by decide
@[simp] theorem nb_lDir_ne_nB : lDir ≠ nB := by decide
@[simp] theorem nb_lDir_ne_nX : lDir ≠ nX := by decide
@[simp] theorem nb_lDir_ne_nY : lDir ≠ nY := by decide
@[simp] theorem nb_lDir_ne_nR : lDir ≠ nR := by decide
@[simp] theorem nb_lDir_ne_nL : lDir ≠ nL := by decide
@[simp] theorem nb_lDir_ne_nM : lDir ≠ nM := by decide
@[simp] theorem nb_lDir_ne_nH : lDir ≠ nH := by decide
@[simp] theorem nb_lDir_ne_nC : lDir ≠ nC := by decide
@[simp] theorem nb_lDir_ne_nE : lDir ≠ nE := by decide
@[simp] theorem nb_lDir_ne_nS : lDir ≠ nS := by decide
@[simp] theorem nb_lDir_ne_nT : lDir ≠ nT := by decide
@[simp] theorem nb_lKb_ne_nA : lKb ≠ nA := by decide
@[simp] theorem nb_lKb_ne_nB : lKb ≠ nB := by decide
@[simp] theorem nb_lKb_ne_nX : lKb ≠ nX := by decide
@[simp] theorem nb_lKb_ne_nY : lKb ≠ nY := by decide
@[simp] theorem nb_lKb_ne_nR : lKb ≠ nR := by decide
@[simp] theorem nb_lKb_ne_nL : lKb ≠ nL := by decide
@[simp] theorem nb_lKb_ne_nM : lKb ≠ nM := by decide
@[simp] theorem nb_lKb_ne_nH : lKb ≠ nH := by decide
@[simp] theorem nb_lKb_ne_nC : lKb ≠ nC := by decide
@[simp] theorem nb_lKb_ne_nE : lKb ≠ nE := by decide
@[simp] theorem nb_lKb_ne_nS : lKb ≠ nS := by decide
@[simp] theorem nb_lKb_ne_nT : lKb ≠ nT := by decide

section
variable {σ : Type}

/-- Calling a function whose spec is `PostK` (a handle, the heap grown). -/
theorem specR_callKH {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM EIdx} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) Bd s m (Knot.PostK C))
    (hk : ∀ a s' H', C.H <+: H' → SpecR (Inv (ctxH C H') s' ((x, Enc.idxW a) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIH x f ps es Bd vs hnd hl hx hC hes (Knot.PostK C) (fun a w _ _ => w = Enc.idxW a)
    (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ps vs hl hlk) hspec)
    (fun a w s' H' hp hw => by subst hw; exact hk a s' H' hp)

theorem natSizeRefused_run (n : Nat) (s : AState) :
    natSizeRefused n s = .ok (decide (natSizeBytes n > s.pins.maxNatSize), s) := by
  simp [natSizeRefused, maxNatSizeM, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure,
    StateT.pure, Except.bind, Except.pure]

def nbSizeE : ExpHOL 64 :=
  .panop .mul [.op .add [vv nL, .cmp .equal (vv nL) (.const 0)], .const 8]

def nbTail (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local nL (.load .one (vv nR)))
  (.seq (.assign .local nM (.load .one (.const (ecell C (C.PO + pinCount + 3)))))
  (.ite (.cmp .lower (vv nM) nbSizeE) hang
  (.seq (.call (some (some (.local, nH), none)) fLitB [vv nR]) (.return (.op .add [vv nH, .const 1])))))

theorem sev_size (Γ : Env) (len : Nat) (hl : len < 2 ^ 58) (h : Γ.get nL = some (BitVec.ofNat 64 len)) :
    sev Γ nbSizeE = some (BitVec.ofNat 64 (8 * max len 1)) := by
  simp only [nbSizeE, sev, vv, h]
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  apply BitVec.eq_of_toNat_eq
  by_cases h0 : len = 0
  · subst h0; simp
  · have : BitVec.ofNat 64 len ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [this, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.max_eq_left (by omega)]; omega

/-- After the size test passed: intern from the block and return `some h`. -/
theorem tail_call (ra : ConPanqueque.Hash.RuntimeAssumptions) {C0 : Ctx} (hok : CtxOK C0) {H : List (BitVec 64)}
    {s : AState} {Γ : Env} {D : List MlS} (r o : Nat) (hpre : C0.H <+: H) (hb : BlkAt H o (limbs r))
    (hcl : C0.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C0, .one))
    (hR : Γ.get nR = some (cellA C0 o)) (hD : nH ∈ D) :
    SpecR (σ := σ) (Inv (ctxH C0 H) s Γ [] D)
      (.seq (.call (some (some (.local, nH), none)) fLitB [vv nR]) (.return (.op .add [vv nH, .const 1]))) s
      (internE (.lit (.natVal r)) >>= fun x => pure (some x)) (UD.PostO C0) := by
  refine specR_callKH nH fLitB [iLx] [vv nR] (litBlkBody C0) [cellA C0 o] (by decide) rfl hD hcl
    ⟨by simp [hR], trivial⟩ (litBlk_spec ra (ctxH C0 H) (ctxOK_H hok _) s r o hb) (fun a s' H' hp => ?_)
  refine specR_returnI _ (Enc.idxW a + 1) (by simp [sev]) (fun t ht => ?_)
  exact ⟨H', hpre.trans hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

theorem tail_test {α : Type} {C0 : Ctx} (hok : CtxOK C0) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {D : List MlS} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (r o : Nat) (hpre : C0.H <+: H)
    (hb : BlkAt H o (limbs r)) (hR : Γ.get nR = some (cellA C0 o)) (hD : nL ∈ D ∧ nM ∈ D)
    (hok' : ∀ t : PState σ, Inv (ctxH C0 H) s Γ [] D t → (limbs r).length < 2 ^ 58)
    (hk : natSizeBytes r ≤ C0.pins.maxNatSize →
      SpecR (Inv (ctxH C0 H) s ((nM, BitVec.ofNat 64 C0.pins.maxNatSize) ::
        (nL, BitVec.ofNat 64 (limbs r).length) :: Γ) [] D)
      (.seq (.call (some (some (.local, nH), none)) fLitB [vv nR]) (.return (.op .add [vv nH, .const 1]))) s m R) :
    SpecR (Inv (ctxH C0 H) s Γ [] D) (nbTail C0) s m R := by
  refine specR_atEntry fun t0 ht0 => ?_
  have hsm := hok' t0 ht0
  have hl0 : (ctxH C0 H).H[o]? = some (BitVec.ofNat 64 (limbs r).length) := hb.1
  unfold nbTail
  refine UD.specR_heapLoadI' (C := ctxH C0 H) nL (vv nR) o _ hl0 hD.1 (by simp [hR]; rfl) ?_
  have hpm := hok.pinsRel.2.2.2.2.2.1
  refine specR_envLoadI (C := ctxH C0 H) nM _ (C0.PO + pinCount + 3) _ hD.2 rfl hpm.1 ?_
  have hm63 := hpm.2
  have hsz := sev_size ((nM, BitVec.ofNat 64 C0.pins.maxNatSize) :: (nL, BitVec.ofNat 64 (limbs r).length) :: Γ)
    (limbs r).length hsm (by simp)
  have hlt := word_lt_iff C0.pins.maxNatSize (8 * max (limbs r).length 1) (by unfold B; omega)
    (by unfold B; omega)
  have hnb := natSizeBytes_limbs r
  by_cases hc : C0.pins.maxNatSize < 8 * max (limbs r).length 1
  · exact specR_ifI _ 1 (by simp [sev, hsz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.mpr hc])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp [sev, hsz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hlt).mpr hc])
    (fun h => absurd rfl h) (fun _ => hk (by omega))

theorem tail_plain (ra : ConPanqueque.Hash.RuntimeAssumptions) {C0 : Ctx} (hok : CtxOK C0) {H : List (BitVec 64)}
    {s : AState} {Γ : Env} {D : List MlS} (r o : Nat) (hpre : C0.H <+: H) (hb : BlkAt H o (limbs r))
    (hcl : C0.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C0, .one))
    (hR : Γ.get nR = some (cellA C0 o)) (hD : nL ∈ D ∧ nM ∈ D ∧ nH ∈ D) :
    SpecR (σ := σ) (Inv (ctxH C0 H) s Γ [] D) (nbTail C0) s
      (internE (.lit (.natVal r)) >>= fun x => pure (some x)) (UD.PostO C0) :=
  tail_test hok r o hpre hb hR ⟨hD.1, hD.2.1⟩
    (fun t ht => blk_small (C := ctxH C0 H) (ctxOK_H hok _) ht.sr hb)
    (fun _ => tail_call ra hok r o hpre hb hcl (by simp [hR]) hD.2.2)

theorem tail_sized (ra : ConPanqueque.Hash.RuntimeAssumptions) {C0 : Ctx} (hok : CtxOK C0) {H : List (BitVec 64)}
    {s : AState} {Γ : Env} {D : List MlS} (r o : Nat) (hpre : C0.H <+: H) (hb : BlkAt H o (limbs r))
    (hcl : C0.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C0, .one))
    (hR : Γ.get nR = some (cellA C0 o)) (hD : nL ∈ D ∧ nM ∈ D ∧ nH ∈ D) :
    SpecR (σ := σ) (Inv (ctxH C0 H) s Γ [] D) (nbTail C0) s (litNatSized r) (UD.PostO C0) :=
  tail_test hok r o hpre hb hR ⟨hD.1, hD.2.1⟩
    (fun t ht => blk_small (C := ctxH C0 H) (ctxOK_H hok _) ht.sr hb)
    (fun hle => by
      refine specR_atEntry fun t ht => ?_
      have hp : s.pins = C0.pins := ht.sr.pins
      unfold litNatSized
      refine specR_runBind (natSizeRefused_run r s) ?_
      have e : decide (natSizeBytes r > s.pins.maxNatSize) = false := by rw [hp]; simp; omega
      rw [e]; simp only [Bool.false_eq_true, ite_false]
      exact tail_call ra hok r o hpre hb hcl (by simp [hR]) hD.2.2)

end

end ConPanqueque.T.Big
