import ConPanqueque.T.Big.NatBinBase
import ConPanqueque.T.Big.Bit
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
def fShr := ofString "bigShr"
def fGcd := ofString "bigGcd"
def fBit : BitOp → MlS
  | .and => ofString "bigAnd" | .or => ofString "bigOr" | .xor => ofString "bigXor"
def fDm (isMod : Bool) : MlS := if isMod then ofString "bigMod" else ofString "bigDiv"

/-- The code the literal operations call. -/
structure BigCodes (C : Ctx) : Prop where
  lit : C.code.lookup fLitH = some ([cH].map (fun p => (p, ShapeHOL.one)), litBody C, .one)
  add : C.code.lookup fAdd = some (addParams.map (fun p => (p, ShapeHOL.one)), addBody C, .one)
  sub : C.code.lookup fSub = some (subParams.map (fun p => (p, ShapeHOL.one)), subBody C, .one)
  mul : C.code.lookup fMul = some (mulParams.map (fun p => (p, ShapeHOL.one)), mulBody C, .one)
  cmp : C.code.lookup fCmp = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody, .one)
  litb : C.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C, .one)
  bit : ∀ o, C.code.lookup (fBit o) = some (bitParams.map (fun p => (p, ShapeHOL.one)), bitBody o C, .one)
  shr : C.code.lookup fShr = some (shrParams.map (fun p => (p, ShapeHOL.one)), shrBody C, .one)
  dm : ∀ isMod, C.code.lookup (fDm isMod) = some (dmParams.map (fun p => (p, ShapeHOL.one)), dmBody C isMod, .one)
  gcd : C.code.lookup fGcd = some (dmParams.map (fun p => (p, ShapeHOL.one)), gcdBody C, .one)

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

/-! ## `mul` -/

def nbMulBody (C : Ctx) : ProgHOL 64 :=
  prologue nbLocals (nbLits (.seq (.call (some (some (.local, nR), none)) fMul [vv nX, vv nY]) (nbTail C)))

theorem nbMul_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BigCodes C)
    (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb])) (nbMulBody C) s (natBinOpResult .mul a b)
      (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (nb_none C _) ?_
  refine nb_lits hok hc ha hb a b hva hvb (nbEnv_a C ha hb) (nbEnv_b C ha hb) (by decide)
    (fun H ox oy hp hbx hby => ?_)
  refine specR_atEntry fun t0 ht0 => ?_
  have hsa := blk_small (C := ctxH C H) (ctxOK_H hok _) ht0.sr hbx
  have hsb := blk_small (C := ctxH C H) (ctxOK_H hok _) ht0.sr hby
  show SpecR _ _ s (litNatSized (a * b)) _
  refine specR_callPH (C := ctxH C H) (k := fun r => litNatSized r) nR fMul mulParams _ (mulBody C)
    [cellA C ox, cellA C oy] (a * b) (by decide) rfl (by decide) hc.mul ⟨by simp, by simp, trivial⟩
    (mul_spec (ctxH C H) (ctxOK_H hok _) s a b ox oy hbx hby (by omega)) (fun H' o hp' hbr => ?_)
  exact tail_sized ra hok (a * b) o (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)

/-! ## `land`, `lor`, `xor` -/

def BitOp.nb : BitOp → NatBinOp
  | .and => .land | .or => .lor | .xor => .xor

theorem BitOp.f_comm (o : BitOp) (a b : Nat) : o.f a b = o.f b a := by
  cases o
  · exact Nat.and_comm a b
  · exact Nat.or_comm a b
  · exact Nat.xor_comm a b

theorem natBinOpResult_bit (o : BitOp) (a b : Nat) :
    natBinOpResult o.nb a b = (internE (.lit (.natVal (o.f a b))) >>= fun x => pure (some x)) := by
  cases o <;> rfl

def nbBitMid (o : BitOp) (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local nS (.load .one (vv nX)))
  (.seq (.assign .local nT (.load .one (vv nY)))
  (.ite (.cmp .lower (vv nS) (vv nT))
    (.seq (.call (some (some (.local, nR), none)) (fBit o) [vv nY, vv nX]) (nbTail C))
    (.seq (.call (some (some (.local, nR), none)) (fBit o) [vv nX, vv nY]) (nbTail C))))

def nbBitBody (o : BitOp) (C : Ctx) : ProgHOL 64 := prologue nbLocals (nbLits (nbBitMid o C))

theorem nbBit_spec (o : BitOp) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : BigCodes C) (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb])) (nbBitBody o C) s (natBinOpResult o.nb a b)
      (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (nb_none C _) ?_
  rw [natBinOpResult_bit]
  refine nb_lits hok hc ha hb a b hva hvb (nbEnv_a C ha hb) (nbEnv_b C ha hb) (by decide)
    (fun H ox oy hp hbx hby => ?_)
  unfold nbBitMid
  have hl0 : (ctxH C H).H[ox]? = some (BitVec.ofNat 64 (limbs a).length) := hbx.1
  have hl1 : (ctxH C H).H[oy]? = some (BitVec.ofNat 64 (limbs b).length) := hby.1
  refine UD.specR_heapLoadI' (C := ctxH C H) nS (vv nX) ox _ hl0 (by decide) (by simp; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) nT (vv nY) oy _ hl1 (by decide) (by simp; rfl) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsa := blk_small (C := ctxH C H) (ctxOK_H hok _) ht0.sr hbx
  have hsb := blk_small (C := ctxH C H) (ctxOK_H hok _) ht0.sr hby
  have hlt := word_lt_iff (limbs a).length (limbs b).length (by unfold B; omega) (by unfold B; omega)
  by_cases hab : (limbs a).length < (limbs b).length
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.mpr hab])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [BitOp.f_comm]
    refine specR_callPH (C := ctxH C H) (k := fun r => internE (.lit (.natVal r)) >>= fun x => pure (some x))
      nR (fBit o) bitParams _ (bitBody o C) [cellA C oy, cellA C ox] (o.f b a) (by decide) rfl (by decide) (hc.bit o)
      ⟨by simp, by simp, trivial⟩
      (bit_spec o (ctxH C H) (ctxOK_H hok _) s b a oy ox hby hbx (by omega) (by omega)) (fun H' r hp' hbr => ?_)
    exact tail_plain ra hok (o.f b a) r (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)
  · refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hlt).mpr hab])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPH (C := ctxH C H) (k := fun r => internE (.lit (.natVal r)) >>= fun x => pure (some x))
      nR (fBit o) bitParams _ (bitBody o C) [cellA C ox, cellA C oy] (o.f a b) (by decide) rfl (by decide) (hc.bit o)
      ⟨by simp, by simp, trivial⟩
      (bit_spec o (ctxH C H) (ctxOK_H hok _) s a b ox oy hbx hby (by omega) (by omega)) (fun H' r hp' hbr => ?_)
    exact tail_plain ra hok (o.f a b) r (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)

/-! ## `shiftRight`, `div`, `mod`, `gcd`: one call, any operands -/

/-- A literal operation that is one call of a block function answering `f a b`, then the plain tail. -/
theorem nb_one (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C) (hc : BigCodes C)
    {s : AState} (fn : MlS) (ps : List MlS) (Bd : ProgHOL 64) (f : Nat → Nat → Nat) (ha hb : EIdx) (a b : Nat)
    (hnd : ps.Nodup) (hl2 : ps.length = 2)
    (hcode : ∀ H : List (BitVec 64), (ctxH C H).code.lookup fn = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hspec : ∀ H ox oy, C.H <+: H → BlkAt H ox (limbs a) → BlkAt H oy (limbs b) →
      SpecR (σ := σ) (Pre (ctxH C H) s (ps.zip [cellA C ox, cellA C oy])) Bd s (pure (f a b) : AM Nat)
        (PostH (ctxH C H) s))
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb]))
      (prologue nbLocals (nbLits (.seq (.call (some (some (.local, nR), none)) fn [vv nX, vv nY]) (nbTail C)))) s
      (internE (.lit (.natVal (f a b))) >>= fun x => pure (some x)) (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (nb_none C _) ?_
  refine nb_lits hok hc ha hb a b hva hvb (nbEnv_a C ha hb) (nbEnv_b C ha hb) (by decide)
    (fun H ox oy hp hbx hby => ?_)
  refine specR_callPH (C := ctxH C H) (k := fun r => internE (.lit (.natVal r)) >>= fun x => pure (some x))
    nR fn ps _ Bd [cellA C ox, cellA C oy] (f a b) hnd (by simp [hl2]) (by decide) (hcode H)
    ⟨by simp, by simp, trivial⟩ (hspec H ox oy hp hbx hby) (fun H' r hp' hbr => ?_)
  exact tail_plain ra hok (f a b) r (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)

def nbShrBody (C : Ctx) : ProgHOL 64 :=
  prologue nbLocals (nbLits (.seq (.call (some (some (.local, nR), none)) fShr [vv nX, vv nY]) (nbTail C)))

theorem nbShr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BigCodes C)
    (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb])) (nbShrBody C) s
      (natBinOpResult .shiftRight a b) (UD.PostO C) :=
  nb_one ra hok hc fShr shrParams (shrBody C) (fun a b => a >>> b) ha hb a b (by decide) rfl (fun _ => hc.shr)
    (fun H ox oy _ hbx hby => shr_spec (ctxH C H) (ctxOK_H hok _) s a b ox oy hbx hby) hva hvb

def nbDmBody (C : Ctx) (isMod : Bool) : ProgHOL 64 :=
  prologue nbLocals (nbLits (.seq (.call (some (some (.local, nR), none)) (fDm isMod) [vv nX, vv nY]) (nbTail C)))

theorem nbDm_spec (isMod : Bool) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : BigCodes C) (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb])) (nbDmBody C isMod) s
      (natBinOpResult (if isMod then .mod else .div) a b) (UD.PostO C) := by
  have e : natBinOpResult (if isMod then .mod else .div) a b =
      (internE (.lit (.natVal (dmRes isMod a b))) >>= fun x => pure (some x)) := by
    cases isMod <;> rfl
  rw [e]
  exact nb_one ra hok hc (fDm isMod) dmParams (dmBody C isMod) (dmRes isMod) ha hb a b (by decide) rfl
    (fun _ => hc.dm isMod) (fun H ox oy _ hbx hby => dm_spec (ctxH C H) (ctxOK_H hok _) s isMod a b ox oy hbx hby)
    hva hvb

def nbGcdBody (C : Ctx) : ProgHOL 64 :=
  prologue nbLocals (nbLits (.seq (.call (some (some (.local, nR), none)) fGcd [vv nX, vv nY]) (nbTail C)))

theorem nbGcd_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BigCodes C)
    (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb])) (nbGcdBody C) s
      (natBinOpResult .gcd a b) (UD.PostO C) :=
  nb_one ra hok hc fGcd dmParams (gcdBody C) Nat.gcd ha hb a b (by decide) rfl (fun _ => hc.gcd)
    (fun H ox oy _ hbx hby => gcd_spec (ctxH C H) (ctxOK_H hok _) s a b ox oy hbx hby) hva hvb

/-! ## `sub` -/

/-- Calling a function whose spec is `PostW` (a word, nothing else changed). -/
theorem specR_callWH {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Nat → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64)) (r : Nat)
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) Bd s (pure r : AM Nat) (PostW C s))
    (hk : SpecR (Inv C s ((x, BitVec.ofNat 64 r) :: Γ) [] D) rest s (k r) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (k r) R := by
  refine specR_congr (m' := (pure r : AM Nat) >>= k) rfl ?_
  refine specR_callNIH x f ps es Bd vs hnd hl hx hC hes
    (fun tt w s' st => (pure r : AM Nat) s = .ok (tt, s') ∧ PostW C s tt w s' st)
    (fun tt w s' H2 => tt = r ∧ s' = s ∧ w = BitVec.ofNat 64 r ∧ H2 = C.H)
    (fun tt w s' st ⟨hrun, hw, hs, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨C.H, List.prefix_refl _, ⟨rfl, hs, hw, rfl⟩, hs ▸ hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ps vs hl hlk) hspec))
    (fun tt w s' H2 _ ⟨htt, hs, hw, hH⟩ => ?_)
  subst htt hs hw hH
  exact hk

def nbSubMid (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv nC) (.const 0))
    (.seq (.call (some (some (.local, nR), none)) fSub [vv nX, vv nX]) (nbTail C))
    (.seq (.call (some (some (.local, nR), none)) fSub [vv nX, vv nY]) (nbTail C))

def nbSubBody (C : Ctx) : ProgHOL 64 :=
  prologue nbLocals (.seq (.call (some (some (.local, nC), none)) fCmp [vv nA, vv nB]) (nbLits (nbSubMid C)))

theorem limbs_len_mono {a b : Nat} (h : b ≤ a) : (limbs b).length ≤ (limbs a).length := by
  by_contra hc
  have := lt_of_length_lt (Nat.lt_of_not_le hc)
  omega

theorem nbSub_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BigCodes C)
    (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (nbParams.zip [Enc.idxW ha, Enc.idxW hb])) (nbSubBody C) s (natBinOpResult .sub a b)
      (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (nb_none C _) ?_
  show SpecR _ _ s (litNatSized (a - b)) _
  refine specR_callWH (k := fun _ => litNatSized (a - b)) nC fCmp bcParams _ bcBody
    [Enc.idxW ha, Enc.idxW hb] (cmpN a b) (by decide) rfl (by decide) hc.cmp
    ⟨by simp +decide [sev, vv, Env.get, nbParams, ctxEnv], by simp +decide [sev, vv, Env.get, nbParams, ctxEnv], trivial⟩ (bc_spec C s ha hb a b hva hvb) ?_
  refine nb_lits hok hc ha hb a b hva hvb (by simp +decide [Env.get, nbParams, ctxEnv]) (by simp +decide [Env.get, nbParams, ctxEnv])
    (by decide) (fun H ox oy hp hbx hby => ?_)
  unfold nbSubMid
  refine specR_atEntry fun t0 ht0 => ?_
  have hsa := blk_small (C := ctxH C H) (ctxOK_H hok _) ht0.sr hbx
  by_cases hab : a < b
  · have hc0 : cmpN a b = 0 := by simp [cmpN, hab]
    refine specR_ifI _ 1 (by simp [sev, hc0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [show a - b = a - a by omega]
    refine specR_callPH (C := ctxH C H) (k := fun r => litNatSized r) nR fSub subParams _ (subBody C)
      [cellA C ox, cellA C ox] (a - a) (by decide) rfl (by decide) hc.sub ⟨by simp, by simp, trivial⟩
      (sub_spec (ctxH C H) (ctxOK_H hok _) s a a ox ox hbx hbx (Nat.le_refl _) (Nat.le_refl _) (by omega))
      (fun H' o hp' hbr => ?_)
    exact tail_sized ra hok (a - a) o (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)
  · have hc0 : cmpN a b ≠ 0 := by unfold cmpN; split <;> [omega; (split <;> omega)]
    have hw : BitVec.ofNat 64 (cmpN a b) ≠ 0#64 := by
      have : cmpN a b < 3 := by unfold cmpN; split <;> [omega; (split <;> omega)]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPH (C := ctxH C H) (k := fun r => litNatSized r) nR fSub subParams _ (subBody C)
      [cellA C ox, cellA C oy] (a - b) (by decide) rfl (by decide) hc.sub ⟨by simp, by simp, trivial⟩
      (sub_spec (ctxH C H) (ctxOK_H hok _) s a b ox oy hbx hby (by omega) (limbs_len_mono (by omega)) (by omega))
      (fun H' o hp' hbr => ?_)
    exact tail_sized ra hok (a - b) o (hp.trans hp') hbr hc.litb (by simp; rfl) (by decide)

end

end ConPanqueque.T.Big
