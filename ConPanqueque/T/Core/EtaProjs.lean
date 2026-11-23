import ConPanqueque.T.Core.ProofIrrel
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `etaFabArgsE`: a structure-η fabrication's argument spine

The major's type's arguments, then `proj T j b` for `j < nF` interned in order (`etaProjs`). A recursive function
accumulating into fresh blocks (`appendWord`), starting from the type's arguments.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def efT := ofString "eft"
def efB := ofString "efb"
def efA := ofString "efa"
def efJ := ofString "efj"
def efN := ofString "efn"
def efP := ofString "efp"
def efQ := ofString "efq"
def efX := ofString "efx"
def fEf := ofString "etaFabArgs"

@[simp] theorem ef_efT_ne_efB : efT ≠ efB := by decide
@[simp] theorem ef_efT_ne_efA : efT ≠ efA := by decide
@[simp] theorem ef_efT_ne_efJ : efT ≠ efJ := by decide
@[simp] theorem ef_efT_ne_efN : efT ≠ efN := by decide
@[simp] theorem ef_efT_ne_efP : efT ≠ efP := by decide
@[simp] theorem ef_efT_ne_efQ : efT ≠ efQ := by decide
@[simp] theorem ef_efT_ne_efX : efT ≠ efX := by decide
@[simp] theorem ef_efT_ne_lKb : efT ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efT : lKb ≠ efT := by decide
@[simp] theorem ef_efB_ne_efT : efB ≠ efT := by decide
@[simp] theorem ef_efB_ne_efA : efB ≠ efA := by decide
@[simp] theorem ef_efB_ne_efJ : efB ≠ efJ := by decide
@[simp] theorem ef_efB_ne_efN : efB ≠ efN := by decide
@[simp] theorem ef_efB_ne_efP : efB ≠ efP := by decide
@[simp] theorem ef_efB_ne_efQ : efB ≠ efQ := by decide
@[simp] theorem ef_efB_ne_efX : efB ≠ efX := by decide
@[simp] theorem ef_efB_ne_lKb : efB ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efB : lKb ≠ efB := by decide
@[simp] theorem ef_efA_ne_efT : efA ≠ efT := by decide
@[simp] theorem ef_efA_ne_efB : efA ≠ efB := by decide
@[simp] theorem ef_efA_ne_efJ : efA ≠ efJ := by decide
@[simp] theorem ef_efA_ne_efN : efA ≠ efN := by decide
@[simp] theorem ef_efA_ne_efP : efA ≠ efP := by decide
@[simp] theorem ef_efA_ne_efQ : efA ≠ efQ := by decide
@[simp] theorem ef_efA_ne_efX : efA ≠ efX := by decide
@[simp] theorem ef_efA_ne_lKb : efA ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efA : lKb ≠ efA := by decide
@[simp] theorem ef_efJ_ne_efT : efJ ≠ efT := by decide
@[simp] theorem ef_efJ_ne_efB : efJ ≠ efB := by decide
@[simp] theorem ef_efJ_ne_efA : efJ ≠ efA := by decide
@[simp] theorem ef_efJ_ne_efN : efJ ≠ efN := by decide
@[simp] theorem ef_efJ_ne_efP : efJ ≠ efP := by decide
@[simp] theorem ef_efJ_ne_efQ : efJ ≠ efQ := by decide
@[simp] theorem ef_efJ_ne_efX : efJ ≠ efX := by decide
@[simp] theorem ef_efJ_ne_lKb : efJ ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efJ : lKb ≠ efJ := by decide
@[simp] theorem ef_efN_ne_efT : efN ≠ efT := by decide
@[simp] theorem ef_efN_ne_efB : efN ≠ efB := by decide
@[simp] theorem ef_efN_ne_efA : efN ≠ efA := by decide
@[simp] theorem ef_efN_ne_efJ : efN ≠ efJ := by decide
@[simp] theorem ef_efN_ne_efP : efN ≠ efP := by decide
@[simp] theorem ef_efN_ne_efQ : efN ≠ efQ := by decide
@[simp] theorem ef_efN_ne_efX : efN ≠ efX := by decide
@[simp] theorem ef_efN_ne_lKb : efN ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efN : lKb ≠ efN := by decide
@[simp] theorem ef_efP_ne_efT : efP ≠ efT := by decide
@[simp] theorem ef_efP_ne_efB : efP ≠ efB := by decide
@[simp] theorem ef_efP_ne_efA : efP ≠ efA := by decide
@[simp] theorem ef_efP_ne_efJ : efP ≠ efJ := by decide
@[simp] theorem ef_efP_ne_efN : efP ≠ efN := by decide
@[simp] theorem ef_efP_ne_efQ : efP ≠ efQ := by decide
@[simp] theorem ef_efP_ne_efX : efP ≠ efX := by decide
@[simp] theorem ef_efP_ne_lKb : efP ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efP : lKb ≠ efP := by decide
@[simp] theorem ef_efQ_ne_efT : efQ ≠ efT := by decide
@[simp] theorem ef_efQ_ne_efB : efQ ≠ efB := by decide
@[simp] theorem ef_efQ_ne_efA : efQ ≠ efA := by decide
@[simp] theorem ef_efQ_ne_efJ : efQ ≠ efJ := by decide
@[simp] theorem ef_efQ_ne_efN : efQ ≠ efN := by decide
@[simp] theorem ef_efQ_ne_efP : efQ ≠ efP := by decide
@[simp] theorem ef_efQ_ne_efX : efQ ≠ efX := by decide
@[simp] theorem ef_efQ_ne_lKb : efQ ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efQ : lKb ≠ efQ := by decide
@[simp] theorem ef_efX_ne_efT : efX ≠ efT := by decide
@[simp] theorem ef_efX_ne_efB : efX ≠ efB := by decide
@[simp] theorem ef_efX_ne_efA : efX ≠ efA := by decide
@[simp] theorem ef_efX_ne_efJ : efX ≠ efJ := by decide
@[simp] theorem ef_efX_ne_efN : efX ≠ efN := by decide
@[simp] theorem ef_efX_ne_efP : efX ≠ efP := by decide
@[simp] theorem ef_efX_ne_efQ : efX ≠ efQ := by decide
@[simp] theorem ef_efX_ne_lKb : efX ≠ lKb := by decide
@[simp] theorem ef_lKb_ne_efX : lKb ≠ efX := by decide

def efParams : List MlS := [efT, efB, efA, efJ, efN]
def efLocals : List MlS := [efP, efQ, efX]

def efBody : ProgHOL 64 := prologue efLocals
  (.ite (.cmp .equal (vv efJ) (vv efN)) (.return (vv efA))
  (.seq (.call (some (some (.local, efP), none)) fInternProj [vv efT, vv efB, vv efJ])
  (.seq (.call (some (some (.local, efQ), none)) ExPre.fAppend [vv efA, vv efP])
  (.seq (.call (some (some (.local, efX), none)) fEf [vv efT, vv efB, vv efQ, .op .add [vv efJ, .const 1], vv efN])
    (.return (vv efX))))))

section
variable {σ : Type}

theorem ef_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ efLocals → (ctxEnv C ++ efParams.zip vals).get x = none :=
  Knot.params_none C efLocals efParams vals (by decide) (by decide)

theorem ef_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C0 : Ctx) (hok0 : CtxOK C0)
    (hcp : C0.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one))
    (hca : C0.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C0, .one))
    (hcf : C0.code.lookup fEf = some (efParams.map (fun p => (p, ShapeHOL.one)), efBody, .one))
    (T : NIdx) (b : EIdx) (n : Nat) (hn : n < 2 ^ 62) :
    ∀ k j (H : List (BitVec 64)) (acc : List EIdx) (oa : Nat) (s : AState), C0.H <+: H → n - j = k → j ≤ n →
      BlkAt H oa (acc.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C0 H) s (efParams.zip [Enc.idxW T, Enc.idxW b, cellA C0 oa, BitVec.ofNat 64 j,
        BitVec.ofNat 64 n])) efBody s (projNodesGo T b k j >>= fun ps => pure (acc ++ ps)) (PostA (ctxH C0 H)) := by
  intro k
  induction k with
  | zero =>
    intro j H acc oa s hp hk hj hb
    have hj' : j = n := by omega
    subst hj'
    refine specR_prologue (postA_locals _) (ef_none _ _) ?_
    rw [projNodesGo]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, efParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [pure_bind, List.append_nil]
    exact specR_returnI _ (cellA C0 oa) (by simp +decide [Env.get, efParams, ctxEnv])
      (fun t ht => ⟨H, oa, List.prefix_refl _, rfl, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j H acc oa s hp hk hj hb
    have hjn : j < n := by omega
    refine specR_prologue (postA_locals _) (ef_none _ _) ?_
    rw [projNodesGo]
    have hne : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 n := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, efParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hok := ctxOK_H hok0 H
    simp only [bind_assoc, pure_bind]
    refine specR_internProjI (C := ctxH C0 H) ra hok hcp efP (vv efT) (vv efB) (vv efJ) T j b (by omega) (by decide)
      (by simp +decide [Env.get, efParams, ctxEnv]) (by simp +decide [Env.get, efParams, ctxEnv])
      (by simp +decide [Env.get, efParams, ctxEnv]) (fun p s1 => ?_)
    refine ExPre.specR_callApp (C := ctxH C0 H) hok hca efQ (vv efA) (vv efP) oa (acc.map Enc.idxW) (Enc.idxW p) (by decide)
      hb (by simp +decide [Env.get, efParams, ctxEnv]; rfl) (by simp) (fun H1 o1 hp1 hb1 => ?_)
    have hb1' : BlkAt H1 o1 ((acc ++ [p]).map Enc.idxW) := by simpa using hb1
    refine specR_congr (m' := (projNodesGo T b k (j + 1) >>= fun ps => pure ((acc ++ [p]) ++ ps)) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C0 H1) efX fEf efParams
      [vv efT, vv efB, vv efQ, .op .add [vv efJ, .const 1], vv efN] efBody
      [Enc.idxW T, Enc.idxW b, cellA C0 o1, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 n] (by decide) rfl (by decide) hcf
      ⟨by simp +decide [Env.get, efParams, ctxEnv], by simp +decide [Env.get, efParams, ctxEnv], by simp; rfl,
        by simp +decide [sev, Env.get, efParams, ctxEnv]; exact word_add1_eq j,
        by simp +decide [Env.get, efParams, ctxEnv], trivial⟩
      (PostA (ctxH C0 H1)) (fun a w _ H2 => ∃ o2, w = cellA C0 o2 ∧ BlkAt H2 o2 (a.map Enc.idxW))
      (fun a w s' st ⟨H2, o2, hp2, hw, hb2, hsr⟩ => ⟨H2, hp2, ⟨o2, hw, hb2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu efParams _ rfl hlk)
        (ih (j + 1) H1 (acc ++ [p]) o1 s1 (hp.trans hp1) (by omega) (by omega) hb1'))
      (fun r w s2 H2 hp2 ⟨o2, hw, hb2⟩ => ?_)
    subst hw
    exact specR_returnI _ (cellA C0 o2) (by simp)
      (fun t ht => ⟨H2, o2, hp1.trans hp2, rfl, by simpa using hb2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
