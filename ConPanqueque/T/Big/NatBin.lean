import ConPanqueque.T.Big.NatBinBase
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `natBinOpResult`, one Pancake function per operation

Each takes the two literal handles (`nba`, `nbb`), copies both literals to heap blocks (`litToHeap`), runs the
verified block operation, and finishes with `nbTail` (the `maxNatSize` test and the intern).
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def fLitH := ofString "bigLit"
def fAdd := ofString "bigAdd"
def fSub := ofString "bigSub"
def fCmp := ofString "bigCmp"

/-- The code the literal operations call. -/
structure BigCodes (C : Ctx) : Prop where
  lit : C.code.lookup fLitH = some ([cH].map (fun p => (p, ShapeHOL.one)), litBody C, .one)
  add : C.code.lookup fAdd = some (addParams.map (fun p => (p, ShapeHOL.one)), addBody C, .one)
  sub : C.code.lookup fSub = some (subParams.map (fun p => (p, ShapeHOL.one)), subBody C, .one)
  mul : C.code.lookup fMul = some (mulParams.map (fun p => (p, ShapeHOL.one)), mulBody C, .one)
  cmp : C.code.lookup fCmp = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody, .one)
  litb : C.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C, .one)

def nbLocals : List MlS := [nX, nY, nR, nL, nM, nH, nC, nE, nS, nT]
def nbParams : List MlS := [nA, nB]

def nbLits (mid : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, nX), none)) fLitH [vv nA])
  (.seq (.call (some (some (.local, nY), none)) fLitH [vv nB]) mid)

section
variable {σ : Type}

theorem nb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nbLocals → (ctxEnv C ++ nbParams.zip vals).get x = none :=
  Knot.params_none C nbLocals nbParams vals (by decide) (by decide)

def nbEnv (C : Ctx) (ha hb : EIdx) : Env := ctxEnv C ++ nbParams.zip [Enc.idxW ha, Enc.idxW hb]

theorem nbEnv_a (C : Ctx) (ha hb : EIdx) : (nbEnv C ha hb).get nA = some (Enc.idxW ha) := by
  simp +decide [nbEnv, Env.get, nbParams, ctxEnv]
theorem nbEnv_b (C : Ctx) (ha hb : EIdx) : (nbEnv C ha hb).get nB = some (Enc.idxW hb) := by
  simp +decide [nbEnv, Env.get, nbParams, ctxEnv]

/-- Both literals copied to heap blocks. -/
theorem nb_lits {α : Type} {C : Ctx} (hok : CtxOK C) (hc : BigCodes C) {s : AState} {Γ : Env} {D : List MlS}
    {mid : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b)))
    (hA : Γ.get nA = some (Enc.idxW ha)) (hB : Γ.get nB = some (Enc.idxW hb)) (hD : nX ∈ D ∧ nY ∈ D)
    (hk : ∀ H ox oy, C.H <+: H → BlkAt H ox (limbs a) → BlkAt H oy (limbs b) →
      SpecR (Inv (ctxH C H) s ((nY, cellA C oy) :: (nX, cellA C ox) :: Γ) [] D) mid s m R) :
    SpecR (Inv C s Γ [] D) (nbLits mid) s m R := by
  unfold nbLits
  refine specR_callPH (k := fun _ => m) nX fLitH [cH] [vv nA] (litBody C) [Enc.idxW ha] a (by decide) rfl hD.1
    hc.lit ⟨by simp [sev, hA], trivial⟩ (lit_spec C hok s ha a hva) (fun H1 o1 hp1 hb1 => ?_)
  refine specR_callPH (C := ctxH C H1) (k := fun _ => m) nY fLitH [cH] [vv nB] (litBody C) [Enc.idxW hb] b
    (by decide) rfl hD.2 hc.lit ⟨by simp [sev, hB], trivial⟩ (lit_spec (ctxH C H1) (ctxOK_H hok _) s hb b hvb)
    (fun H2 o2 hp2 hb2 => ?_)
  exact hk H2 o1 o2 (hp1.trans hp2) (blkAt_mono hb1 hp2) hb2

/-! ## `add` -/

def nbAddMid (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local nS (.load .one (vv nX)))
  (.seq (.assign .local nT (.load .one (vv nY)))
  (.ite (.cmp .lower (vv nS) (vv nT))
    (.seq (.call (some (some (.local, nR), none)) fAdd [vv nY, vv nX]) (nbTail C))
    (.seq (.call (some (some (.local, nR), none)) fAdd [vv nX, vv nY]) (nbTail C))))

def nbAddBody (C : Ctx) : ProgHOL 64 := prologue nbLocals (nbLits (nbAddMid C))

theorem nbAdd_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BigCodes C)
    (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb])) (nbAddBody C) s (natBinOpResult .add a b)
      (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (nb_none C _) ?_
  refine nb_lits hok hc ha hb a b hva hvb (nbEnv_a C ha hb) (nbEnv_b C ha hb) (by decide)
    (fun H ox oy hp hbx hby => ?_)
  unfold nbAddMid
  have hl0 : (ctxH C H).H[ox]? = some (BitVec.ofNat 64 (limbs a).length) := hbx.1
  have hl1 : (ctxH C H).H[oy]? = some (BitVec.ofNat 64 (limbs b).length) := hby.1
  refine UD.specR_heapLoadI' (C := ctxH C H) nS (vv nX) ox _ hl0 (by decide) (by simp; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) nT (vv nY) oy _ hl1 (by decide) (by simp; rfl) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsa := blk_small (C := ctxH C H) (ctxOK_H hok _) ht0.sr hbx
  have hsb := blk_small (C := ctxH C H) (ctxOK_H hok _) ht0.sr hby
  have hlt := word_lt_iff (limbs a).length (limbs b).length (by unfold B; omega) (by unfold B; omega)
  show SpecR _ _ s (litNatSized (a + b)) _
  by_cases hab : (limbs a).length < (limbs b).length
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.mpr hab])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [Nat.add_comm]
    refine specR_callPH (C := ctxH C H) (k := fun r => litNatSized r) nR fAdd addParams _ (addBody C)
      [cellA C oy, cellA C ox] (b + a) (by decide) rfl (by decide) hc.add ⟨by simp, by simp, trivial⟩
      (add_spec (ctxH C H) (ctxOK_H hok _) s b a oy ox hby hbx (by omega) (by omega)) (fun H' o hp' hbr => ?_)
    exact tail_sized ra hok (b + a) o (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)
  · refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hlt).mpr hab])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPH (C := ctxH C H) (k := fun r => litNatSized r) nR fAdd addParams _ (addBody C)
      [cellA C ox, cellA C oy] (a + b) (by decide) rfl (by decide) hc.add ⟨by simp, by simp, trivial⟩
      (add_spec (ctxH C H) (ctxOK_H hok _) s a b ox oy hbx hby (by omega) (by omega)) (fun H' o hp' hbr => ?_)
    exact tail_sized ra hok (a + b) o (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)

end

end ConPanqueque.T.Big
