import ConPanqueque.T.Ind.GenMotive
import ConPanqueque.T.Ind.CloseLams

/-!
# `classGenRule` for a constructor with ordinary fields (one class)

`fmsBody`: the first minor slot at `(0, cn)` from slot `i` on (none: a hang).  `pvgBody`: the prefix variables'
effects (`slotVar` for the slots; the parameters are read, the result unused when no field recurses).
`cgrBody`: the rule `λ (prefix) f⃗, minor_s f⃗`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## The minor slot of a constructor -/

def fmsS := ofString "fms_s"
def fmsI := ofString "fms_i"
def fmsN := ofString "fms_n"
def fmsCn := ofString "fms_cn"
def fmsP := ofString "fms_p"
def fmsTg := ofString "fms_tg"
def fmsCc := ofString "fms_cc"
def fmsCv := ofString "fms_cv"
def fmsR := ofString "fms_r"
def fFms := ofString "findMinorSlot"

def fmsParams : List MlS := [fmsS, fmsI, fmsN, fmsCn]
def fmsLocals : List MlS := [fmsP, fmsTg, fmsCc, fmsCv, fmsR]

def fmsRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, fmsR), none)) fFms [vv fmsS, .op .add [vv fmsI, .const 1], vv fmsN, vv fmsCn])
    (.return (vv fmsR))

def fmsBody : ProgHOL 64 := prologue fmsLocals
  (.ite (.cmp .lower (vv fmsI) (vv fmsN))
    (.seq (.assign .local fmsP (.load .one (.op .add [vv fmsS, .op .add [.panop .mul [vv fmsI, .const 8], .const 8]])))
    (.seq (.assign .local fmsTg (.load .one (vv fmsP)))
    (.ite (.cmp .equal (vv fmsTg) (.const 1))
      (.seq (.assign .local fmsCc (.load .one (.op .add [vv fmsP, .const 8])))
      (.seq (.assign .local fmsCv (.load .one (.op .add [vv fmsP, .const 16])))
      (.ite (.cmp .equal (vv fmsCc) (.const 0))
        (.ite (.cmp .equal (vv fmsCv) (vv fmsCn)) (.return (vv fmsI)) fmsRec)
        fmsRec)))
      fmsRec)))
    hang)

section
variable {σ : Type}

theorem fms_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fmsLocals → (ctxEnv C ++ fmsParams.zip vals).get x = none :=
  Knot.params_none C fmsLocals fmsParams vals (by decide) (by decide)

/-- The first slot from `i` on that is a hit. -/
def PostFMS (C : Ctx) (sls : List ClassSlot) (cn : NIdx) (i : Nat) (s : AState) (_ : Unit) (w : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ r, w = BitVec.ofNat 64 r ∧ i ≤ r ∧ ∃ hr : r < sls.length, isHitC cn sls[r] = true ∧
    (∀ k (hk : k < sls.length), i ≤ k → k < r → isHitC cn sls[k] = false) ∧ SR C s' st

set_option maxHeartbeats 16000000 in
theorem fms_spec (C : Ctx) (hc : C.code.lookup fFms = some (fmsParams.map (fun p => (p, ShapeHOL.one)), fmsBody, .one))
    (sls : List ClassSlot) (os : Nat) (hsl : sls.length < 2 ^ 58) (cn : NIdx)
    (hcb : ∀ sl ∈ sls, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63) (H : List (BitVec 64))
    (hsb : SlotBlk C H os sls) :
    ∀ f i (s : AState), sls.length - i = f → i ≤ sls.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (fmsParams.zip [cellA C os, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length,
        Enc.idxW cn])) fmsBody s (pure ()) (PostFMS (ctxH C H) sls cn i s) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hsb
  have hpost : ∀ (i : Nat) (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostFMS (ctxH C H) sls cn i s a w s' st → PostFMS (ctxH C H) sls cn i s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ _ ⟨h0, r, h1, h2, h3, h4, h5, h6⟩ => ⟨h0, r, h1, h2, h3, h4, h5, sr_of_eq h6 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (hpost _ s) (fms_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, fmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  | succ f ih =>
    intro i s hf hi
    have hin : i < sls.length := by omega
    refine specR_prologue (hpost _ s) (fms_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, fmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hsr⟩ := hpsr i hin
    have hio : i < ps.length := by omega
    have hpe := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hpi : ps[i] = op := by simpa [List.getElem?_eq_getElem hio] using hop
    rw [hpi] at hpe
    refine UD.specR_heapLoadI' (C := ctxH C H) fmsP _ (os + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, fmsParams, ctxEnv]; exact cellA_mulIdx C os i (by omega)) ?_
    -- the recursive call: the answer from `i + 1` on, and slot `i` no hit
    have hrec : isHitC cn sls[i] = false → ∀ (Γ : Env), Γ.get fmsS = some (cellA C os) →
        Γ.get fmsI = some (BitVec.ofNat 64 i) → Γ.get fmsN = some (BitVec.ofNat 64 sls.length) →
        Γ.get fmsCn = some (Enc.idxW cn) → (∀ y ∈ [fmsR], y ∈ ctxLocals ++ fmsLocals) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ fmsLocals)) fmsRec s (pure ())
          (PostFMS (ctxH C H) sls cn i s) := by
      intro hf0 Γ gS gI gN gC _
      refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) fmsR fFms fmsParams [vv fmsS, .op .add [vv fmsI, .const 1], vv fmsN, vv fmsCn]
        fmsBody [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length, Enc.idxW cn] (by decide) rfl (by decide) hc
        ⟨by simp [sev, gS], by simp [sev, sev_vv, gI]; exact word_add1_eq i, by simp [sev, gN], by simp [sev, gC], trivial⟩
        (PostFMS (ctxH C H) sls cn (i + 1) s)
        (fun _ w s' H' => H' = H ∧ s' = s ∧ ∃ r, w = BitVec.ofNat 64 r ∧ i + 1 ≤ r ∧ ∃ hr : r < sls.length,
          isHitC cn sls[r] = true ∧ ∀ k (hk : k < sls.length), i + 1 ≤ k → k < r → isHitC cn sls[k] = false)
        (fun a w s' st ⟨h0, r, h1, h2, h3, h4, h5, h6⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, r, h1, h2, h3, h4, h5⟩, h6⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmsParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun _ w s3 H3 hp3 ⟨eH, es, r, hw, hr1, hr2, hr3, hr4⟩ => ?_)
      subst eH es hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, r, rfl, by omega, hr2, hr3,
        fun k hk h1 h2 => by
          rcases Nat.lt_or_ge i k with h | h
          · exact hr4 k hk h h2
          · have : k = i := by omega
            subst this; exact hf0, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hsli := List.getElem_mem hin
    generalize hsl : sls[i] = sl at hsr hsli hrec
    cases sl with
    | motive k =>
      obtain ⟨h0, -, -, -⟩ := hsr
      refine UD.specR_heapLoadI' (C := ctxH C H) fmsTg (vv fmsP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      exact hrec (by simp [isHitC]) _ (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv]) (by decide)
    | minor c C' ihs =>
      obtain ⟨h0, h1, h2, oi, h3, hpr⟩ := hsr
      have hc63 := hcb _ hsli c C' ihs rfl
      refine UD.specR_heapLoadI' (C := ctxH C H) fmsTg (vv fmsP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) fmsCc _ (op + 1) _ h1 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) fmsCv _ (op + 2) _ h2 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 2) ?_
      by_cases hc0 : c = 0
      swap
      · have hne : BitVec.ofNat 64 c ≠ 0#64 := fun e => hc0 (by have := congrArg BitVec.toNat e; simp at this; omega)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
        exact hrec (by simp [isHitC, hc0]) _ (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv]) (by decide)
      subst hc0
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases hcv : C' = cn
      swap
      · have hne : Enc.idxW C' ≠ Enc.idxW cn := fun e => hcv (Enc.idxW_inj e)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, fmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        exact hrec (by simp [isHitC, hcv]) _ (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, fmsParams, ctxEnv]) (by decide)
      subst hcv
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, fmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (BitVec.ofNat 64 i) (by simp +decide [sev, Env.get_cons, Env.get, fmsParams, ctxEnv])
        (fun t ht => ⟨rfl, i, rfl, Nat.le_refl _, hin, by rw [hsl]; simp [isHitC],
          fun k hk h1 h2 => absurd h2 (by omega), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The prefix variables -/

def pvgI := ofString "pvg_i"
def pvgR := ofString "pvg_r"
def pvgN := ofString "pvg_n"
def pvgPm := ofString "pvg_pm"
def pvgZ := ofString "pvg_z"
def pvgSz := ofString "pvg_sz"
def pvgV := ofString "pvg_v"
def fPvg := ofString "prefixVarsGo"

def pvgParams : List MlS := [pvgI, pvgR, pvgN, pvgPm]
def pvgLocals : List MlS := gaaLocals ++ [pvgZ, pvgSz, pvgV]

def pvgRec (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, ExS.lY), none)) fPvg [.op .add [vv pvgI, .const 1], vv pvgR, vv pvgN, vv pvgPm])
    (prependP C pvgV)

def pvgBody (C : Ctx) : ProgHOL 64 := prologue pvgLocals
  (.ite (.cmp .lower (vv pvgI) (vv pvgR))
    (.ite (.cmp .lower (vv pvgI) (vv pvgN))
      (.seq (.assign .local pvgV (.load .one (.op .add [vv pvgPm, .op .add [.panop .mul [vv pvgI, .const 8], .const 8]])))
        (pvgRec C))
      (.seq (.assign .local pvgZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
      (.seq (.call (some (some (.local, pvgSz), none)) fInternSort [vv pvgZ])
      (.seq (.call (some (some (.local, pvgV), none)) fInternFVar [vv pvgSz, vv pvgI])
        (pvgRec C)))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure PVGCodes (C : Ctx) : Prop where
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  self : C.code.lookup fPvg = some (pvgParams.map (fun p => (p, ShapeHOL.one)), pvgBody C, .one)

section
variable {σ : Type}

theorem pvg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pvgLocals → (ctxEnv C ++ pvgParams.zip vals).get x = none :=
  Knot.params_none C pvgLocals pvgParams vals (by decide) (by decide)

/-- Any answer, past the value heap. -/
def PostLs {α : Type} (C : Ctx) (_ : α) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postLs_locals {α : Type} (C : Ctx) : ∀ (a : α) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLs C a w s' st → PostLs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hsr⟩ => ⟨H', hp, sr_of_eq hsr rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **The prefix variables** from `i` on: the parameters read, the slots' variables interned; a fresh block. -/
theorem pvg_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PVGCodes C)
    (g : ClassGen) (hpl : g.nP ≤ g.params.length) (rP : Nat) (hrP : rP < 2 ^ 62) (hnP : g.nP < 2 ^ 62)
    (opm : Nat) (hpml : g.params.length < 2 ^ 56) (hpm : BlkAt C.H opm (g.params.map Enc.idxW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState), rP - i = f → i ≤ rP → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (pvgParams.zip [BitVec.ofNat 64 i, BitVec.ofNat 64 rP, BitVec.ofNat 64 g.nP,
          cellA C opm]))
        (pvgBody C) s (((List.range rP).drop i).mapM fun i =>
          if i < g.nP then exprGetD g.params i else g.slotVar (i - g.nP)) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = rP := by omega
    subst hin
    refine specR_prologue (postA_locals _) (pvg_none _ _) ?_
    have hlw := nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pvgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [show (List.range i).drop i = [] by simp, List.mapM_nil]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < rP := by omega
    refine specR_prologue (postA_locals _) (pvg_none _ _) ?_
    have hlw := nd_lt_iff i rP (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pvgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons (by simpa using hin), List.getElem_range, List.mapM_cons]
    -- the recursive call and the prepend, after slot `i`'s variable
    have hrec : ∀ (b : EIdx) (s1 : AState) (Γ : Env) (M : Mem), Γ.get pvgI = some (BitVec.ofNat 64 i) →
        Γ.get pvgR = some (BitVec.ofNat 64 rP) → Γ.get pvgN = some (BitVec.ofNat 64 g.nP) →
        Γ.get pvgPm = some (cellA C opm) → Γ.get pvgV = some (Enc.idxW b) → Γ.get lCz = none →
        SpecR (σ := σ) (Inv (ctxH C H) s1 Γ M (ctxLocals ++ pvgLocals)) (pvgRec C) s1
          ((((List.range rP).drop (i + 1)).mapM fun i =>
            if i < g.nP then exprGetD g.params i else g.slotVar (i - g.nP)) >>= fun bs => pure (b :: bs))
          (PostA (ctxH C H)) := by
      intro b s1 Γ M gI gR gN gP gV gz
      refine specR_callNIH (C := ctxH C H) ExS.lY fPvg pvgParams [.op .add [vv pvgI, .const 1], vv pvgR, vv pvgN, vv pvgPm]
        (pvgBody C) [BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rP, BitVec.ofNat 64 g.nP, cellA C opm] (by decide) rfl
        (by decide) hc.self
        ⟨by simp [sev, sev_vv, gI]; exact word_add1_eq i, by simp [sev, gR], by simp [sev, gN], by simp [sev, gP], trivial⟩
        (PostA (ctxH C H)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
        (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pvgParams _ rfl hlk)
          (ih (i + 1) H s1 (by omega) (by omega) hp))
        (fun rs w s3 H3 hp3 ⟨oy, hw, hry⟩ => ?_)
      subst hw
      have hp3' : H <+: H3 := hp3
      refine ExPre.prepend_spec C hok (H := H3) pvgV (Enc.idxW b) oy (rs.map Enc.idxW) (by decide)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons, gV]) hry (by decide)
        (by simp +decide [Env.get_cons, gz]) (by decide) (fun H' o t hp' hb hsr => ?_)
      exact ⟨H', o, hp3'.trans hp', rfl, by simpa using hb, hsr⟩
    by_cases hlt : i < g.nP
    · have hlw2 := nd_lt_iff i g.nP (by omega) (by omega)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pvgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr hlt])
        (fun _ => ?_) (fun h => absurd h (by decide))
      have hil : i < g.params.length := Nat.lt_of_lt_of_le hlt hpl
      have hx := hpm.2 i (by simp; omega)
      simp only [List.getElem_map] at hx
      refine UD.specR_heapLoadI' (C := ctxH C H) pvgV _ (opm + 1 + i) _ (get_prefix hx hp) (by decide)
        (by simp +decide [sev, Env.get, pvgParams, ctxEnv]; exact cellA_mulIdx C opm i (by omega)) ?_
      simp only [hlt, ↓reduceIte, exprGetD, List.getElem?_eq_getElem hil, pure_bind]
      exact hrec _ s _ _ (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv])
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv])
    · have hlw2 := nd_lt_iff i g.nP (by omega) (by omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pvgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hlt, ↓reduceIte, ClassGen.slotVar, zeroLevel, bind_assoc, Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)]
      have hokH := ctxOK_H hok H
      refine specR_pinXI (C := ctxH C H) hokH pinZeroLevel 1 C.pins.zeroLevel _
        (fun s hp => pinZeroLevel_run (C := ctxH C H) hokH hp) (pin_zeroLevel_cell hokH) pvgZ (by decide) ?_
      refine ILP.callE_spec (C := ctxH C H) pvgSz fInternSort [lEu] [vv pvgZ] sortBody [Enc.idxW C.pins.zeroLevel]
        (by decide) rfl (by decide) hc.srt ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
        (sort_body_spec ra (ctxH C H) hokH s _) (fun sz s6 => ?_)
      refine ILP.specR_internFVarI ra hokH hc.fv pvgV (vv pvgSz) (vv pvgI) sz i (by omega) (by decide)
        (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, Env.get, pvgParams, ctxEnv]) (fun v s7 => ?_)
      exact hrec _ s7 _ _ (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv]) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons, Env.get, pvgParams, ctxEnv])

end

/-! ## `classGenRule.callsGo` (recursive fields at class `0`) -/

def cgoKb := ofString "cgo_kb"
def cgoI := ofString "cgo_i"
def cgoN := ofString "cgo_n"
def cgoFv := ofString "cgo_fv"
def cgoFn := ofString "cgo_fn"
def cgoWs := ofString "cgo_ws"
def cgoWn := ofString "cgo_wn"
def cgoE := ofString "cgo_e"
def cgoNPc := ofString "cgo_npc"
def cgoRn := ofString "cgo_rn"
def cgoRl := ofString "cgo_rl"
def cgoPv := ofString "cgo_pv"
def cgoK := ofString "cgo_k"
def cgoW := ofString "cgo_w"
def cgoX := ofString "cgo_x"
def cgoXs := ofString "cgo_xs"
def cgoLf := ofString "cgo_lf"
def cgoA := ofString "cgo_a"
def cgoAl := ofString "cgo_al"
def cgoF := ofString "cgo_f"
def cgoXl := ofString "cgo_xl"
def cgoFx := ofString "cgo_fx"
def cgoRc := ofString "cgo_rc"
def cgoB1 := ofString "cgo_b1"
def cgoB2 := ofString "cgo_b2"
def cgoB3 := ofString "cgo_b3"
def cgoB3l := ofString "cgo_b3l"
def cgoAp := ofString "cgo_ap"
def cgoBs := ofString "cgo_bs"
def cgoBl := ofString "cgo_bl"
def cgoCl := ofString "cgo_cl"
def fCgo := ofString "ruleCalls"

def cgoParams : List MlS := [cgoKb, cgoI, cgoN, cgoFv, cgoFn, cgoWs, cgoWn, cgoE, cgoNPc, cgoRn, cgoRl, cgoPv]
def cgoLocals : List MlS := gaaLocals ++ [cgoK, cgoW, cgoX, cgoXs, cgoLf, cgoA, cgoAl, cgoF, cgoXl, cgoFx, cgoRc, cgoB1,
  cgoB2, cgoB3, cgoB3l, cgoAp, cgoBs, cgoBl, cgoCl]

def cgoRec : ProgHOL 64 :=
  .call (some (some (.local, ExS.lY), none)) fCgo [vv cgoKb, .op .add [vv cgoI, .const 1], vv cgoN, vv cgoFv, vv cgoFn,
    vv cgoWs, vv cgoWn, vv cgoE, vv cgoNPc, vv cgoRn, vv cgoRl, vv cgoPv]

def cgoBody (C : Ctx) : ProgHOL 64 := prologue cgoLocals
  (.ite (.cmp .lower (vv cgoI) (vv cgoN))
    (.seq (.assign .local cgoK (.load .one (.op .add [vv cgoKb, .op .add [.panop .mul [vv cgoI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv cgoK) (.const 0))
      (.seq cgoRec (.return (vv ExS.lY)))
    (.ite (.cmp .lower (vv cgoI) (vv cgoWn))
    (.ite (.cmp .lower (vv cgoI) (vv cgoFn))
    (.seq (.assign .local cgoK (.op .sub [vv cgoK, .const 1]))
    (.seq (.assign .local cgoW (.load .one (.op .add [vv cgoWs, .op .add [.panop .mul [vv cgoI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, cgoX), none)) fOpenFvars [vv cgoK, vv cgoW, vv cgoE])
    (.ite (.cmp .equal (vv cgoX) (.const 0)) hang
    (.seq (.assign .local cgoXs (.load .one (vv cgoX)))
    (.seq (.assign .local cgoLf (.load .one (.op .add [vv cgoX, .const 8])))
    (.seq (.call (some (some (.local, cgoA), none)) fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), vv cgoLf])
    (.seq (.assign .local cgoAl (.load .one (vv cgoA)))
    (.ite (.cmp .lower (vv cgoAl) (vv cgoNPc)) hang
    (.ite (.cmp .lower (vv cgoAl) (.const (BitVec.ofNat 64 (2 ^ 56))))
    (.seq (.assign .local cgoF (.load .one (.op .add [vv cgoFv, .op .add [.panop .mul [vv cgoI, .const 8], .const 8]])))
    (.seq (.assign .local cgoXl (.load .one (vv cgoXs)))
    (.ite (.cmp .lower (vv cgoXl) (.const (BitVec.ofNat 64 (2 ^ 56))))
    (.seq (.call (some (some (.local, cgoFx), none)) ExK.fMka [vv cgoF, vv cgoXs, .const 0, vv cgoXl])
    (.seq (.call (some (some (.local, cgoRc), none)) fInternConst [vv cgoRn, vv cgoRl])
    (.seq (.call (some (some (.local, cgoB1), none)) fCat [vv cgoPv, vv cgoA, vv cgoNPc])
    (alloc2 C cgoB2 (.const 1) (vv cgoFx)
    (.seq (.call (some (some (.local, cgoB3), none)) fCat [vv cgoB1, vv cgoB2, .const 0])
    (.seq (.assign .local cgoB3l (.load .one (vv cgoB3)))
    (.ite (.cmp .lower (vv cgoB3l) (.const (BitVec.ofNat 64 (2 ^ 56))))
    (.seq (.call (some (some (.local, cgoAp), none)) ExK.fMka [vv cgoRc, vv cgoB3, .const 0, vv cgoB3l])
    (.seq (.call (some (some (.local, cgoBs), none)) fFvtDs [vv cgoXs])
    (.seq (.assign .local cgoBl (.load .one (vv cgoBs)))
    (.ite (.cmp .lower (vv cgoBl) (.const (BitVec.ofNat 64 (2 ^ 56))))
    (.seq (.call (some (some (.local, cgoCl), none)) fClm [vv cgoE, .const 0, vv cgoBs, .const 0, vv cgoAp])
    (.seq cgoRec (prependP C cgoCl)))
    hang))))
    hang)))))))
    hang)))
    hang))))))))))
    hang)
    hang)))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure CGOCodes (C : Ctx) : Prop where
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)
  cat : CatCodes C
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  ftd : C.code.lookup fFvtDs = some (ftdParams.map (fun p => (p, ShapeHOL.one)), ftdBody C, .one)
  ftf : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  clm : CLMCodes C
  self : C.code.lookup fCgo = some (cgoParams.map (fun p => (p, ShapeHOL.one)), cgoBody C, .one)

section
variable {σ : Type}

theorem blk_len_lt' {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} (hHN : H.length ≤ C.HN) {o : Nat}
    {xs : List (BitVec 64)} (h : BlkAt H o xs) : xs.length < 2 ^ 61 := by
  have hlay := hok.heapLay
  have := (List.getElem?_eq_some_iff.mp h.1).1
  rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
  · omega
  · have h1 := h.2 (xs.length - 1) (by omega)
    have := (List.getElem?_eq_some_iff.mp h1).1
    omega

theorem cgo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cgoLocals → (ctxEnv C ++ cgoParams.zip vals).get x = none :=
  Knot.params_none C cgoLocals cgoParams vals (by decide) (by decide)

set_option maxHeartbeats 64000000 in
/-- **`classGenRule.callsGo`** over the fields from field `i` on (recursive fields at class `0`). -/
theorem cgo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CGOCodes C)
    (g : ClassGen) (m : TargetMajor) (hcls : g.cls = [m]) (recCls : List Nat) (cvGs : List IConstantVal)
    (rlvls : LsIdx) (rn : NIdx) (hrn : classRecOf recCls cvGs 0 = some rn)
    (x : ClassCtor) (rP : Nat) (fvs ws pvars : List EIdx) (pk pf pw pv : Nat) (hko : KindsOK x.kinds)
    (hkl : x.kinds.length = x.nF) (hnf : x.nF < 2 ^ 56) (hrP : rP + x.nF < 2 ^ 61) (hnpc : m.nPc < 2 ^ 62)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hkb : BlkAt H0 pk (x.kinds.map cfKindW))
    (hfb : BlkAt H0 pf (fvs.map Enc.idxW)) (hwb : BlkAt H0 pw (ws.map Enc.idxW)) (hpv : BlkAt H0 pv (pvars.map Enc.idxW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState), x.nF - i = f → i ≤ x.nF → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cgoParams.zip [cellA C pk, BitVec.ofNat 64 i, BitVec.ofNat 64 x.nF,
        cellA C pf, BitVec.ofNat 64 fvs.length, cellA C pw, BitVec.ofNat 64 ws.length, BitVec.ofNat 64 (rP + x.nF),
        BitVec.ofNat 64 m.nPc, Enc.idxW rn, Enc.idxW rlvls, cellA C pv])) (cgoBody C) s
        (classGenRule.callsGo g recCls cvGs rlvls x rP fvs ws pvars (x.nF - i) i) (PostIH (ctxH C H) (x.nF - i)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = x.nF := by omega
    subst hin
    refine specR_prologue (postIH_locals _ _) (cgo_none _ _) ?_
    have hlw := nd_lt_iff x.nF x.nF (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Nat.sub_self, classGenRule.callsGo]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws2 hp2 hws => ?_)
    have hg : ((H2 ++ ws2).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws2).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨[], _, H2.length, rfl,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, by simp,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < x.nF := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (postIH_locals _ _) (cgo_none _ _) ?_
    have hlw := nd_lt_iff i x.nF (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hik : i < x.kinds.length := by omega
    have hkx := hkb.2 i (by simp; omega)
    simp only [List.getElem_map] at hkx
    refine UD.specR_heapLoadI' (C := ctxH C H) cgoK _ (pk + 1 + i) _ (get_prefix hkx hp) (by decide)
      (by simp +decide [sev, Env.get, cgoParams, ctxEnv]; exact cellA_mulIdx C pk i (by omega)) ?_
    rw [show x.nF - i = (x.nF - (i + 1)) + 1 by omega, classGenRule.callsGo]
    have hgd : x.kinds.getD i ClassField.ordinary = x.kinds[i] := by simp [List.getD, List.getElem?_eq_getElem hik]
    rw [hgd]
    rcases hko x.kinds[i] (List.getElem_mem hik) with hk | ⟨tele, hk, htele⟩
    · rw [hk] at hkx ⊢
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, cfKindW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      refine specR_congr (m' := classGenRule.callsGo g recCls cvGs rlvls x rP fvs ws pvars (x.nF - (i + 1)) (i + 1) >>=
        fun r => pure r) (by simp) ?_
      unfold cgoRec
      refine specR_callNIH (C := ctxH C H) ExS.lY fCgo cgoParams [vv cgoKb, .op .add [vv cgoI, .const 1], vv cgoN, vv cgoFv,
          vv cgoFn, vv cgoWs, vv cgoWn, vv cgoE, vv cgoNPc, vv cgoRn, vv cgoRl, vv cgoPv] (cgoBody C)
        [cellA C pk, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 x.nF, cellA C pf, BitVec.ofNat 64 fvs.length, cellA C pw,
          BitVec.ofNat 64 ws.length, BitVec.ofNat 64 (rP + x.nF), BitVec.ofNat 64 m.nPc, Enc.idxW rn, Enc.idxW rlvls,
          cellA C pv] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
          trivial⟩
        (PostIH (ctxH C H) (x.nF - (i + 1))) (fun o w _ H' => ∃ ihs ob, o = some ihs ∧ w = cellA C ob ∧
          BlkAt H' ob (ihs.map Enc.idxW) ∧ ihs.length ≤ x.nF - (i + 1))
        (fun o w s' st ⟨ihs, H', ob, h0, hp', hw, hb, hl, hsr⟩ => ⟨H', hp', ⟨ihs, ob, h0, hw, hb, hl⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cgoParams _ rfl hlk)
          (ih (i + 1) H s (by omega) (by omega) hp))
        (fun o w s1 H1 hp1 ⟨ihs, ob, ho, hw, hb, hl⟩ => ?_)
      subst ho hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨ihs, H1, ob, rfl, hp1, rfl, hb, by omega,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [hk] at hkx ⊢
    have hkw : cfKindW (.recursive 0 tele) ≠ 0 := by
      simp only [cfKindW]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hkw)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN0 => ?_)
    have hHN0' : H.length ≤ C.HN := hHN0
    have hlay := hok.heapLay
    have hwl : ws.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos ws.length with h0 | hpos
      · omega
      · have h1 := (blkAt_mono hwb hp).2 (ws.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hfl : fvs.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos fvs.length with h0 | hpos
      · omega
      · have h1 := (blkAt_mono hfb hp).2 (fvs.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hlww := nd_lt_iff i ws.length (by omega) (by omega)
    by_cases hiw : i < ws.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgoParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgoParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlww.mpr hiw]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hlwf := nd_lt_iff i fvs.length (by omega) (by omega)
    by_cases hif : i < fvs.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgoParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgoParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwf.mpr hif]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI cgoK _ (BitVec.ofNat 64 tele) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp [cfKindW]; exact ofNat_succ_sub_one tele) ?_
    have hwx := hwb.2 i (by simp; omega)
    simp only [List.getElem_map] at hwx
    refine UD.specR_heapLoadI' (C := ctxH C H) cgoW _ (pw + 1 + i) _ (get_prefix hwx hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv]; exact cellA_mulIdx C pw i (by omega)) ?_
    simp only [exprGetD, List.getElem?_eq_getElem hiw, pure_bind]
    simp only [ClassGen.ihParts, hcls, List.getElem?_cons_zero, bind_assoc]
    refine specR_callNIH (C := ctxH C H) cgoX fOpenFvars ofParams [vv cgoK, vv cgoW, vv cgoE]
      (ofBody C) [BitVec.ofNat 64 tele, Enc.idxW ws[i], BitVec.ofNat 64 (rP + x.nF)] (by decide) rfl
      (by decide) hc.ofc ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], trivial⟩
      (PostOF (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ xs e', o = some (xs, e') → ∃ ob oa,
        w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (xs.map Enc.idxW))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
        (of_spec ra C hok hc.op tele ws[i] (rP + x.nF) (by omega) (by omega) H hpC s))
      (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
    have hp1' : H <+: H1 := hp1
    rcases o with _ | ⟨xs, lf⟩
    · have e0 := hn rfl
      subst e0
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨ob, oa, rfl, hob, hlf, hxb⟩ := hsm xs lf rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
    have hol : ob < H1.length := (List.getElem?_eq_some_iff.mp hob).1
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [bind_assoc]
    refine UD.specR_heapLoadI' (C := ctxH C H1) cgoXs (vv cgoX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) cgoLf _ (ob + 1) _ hlf (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ob) ?_
    have hxl : xs.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
      · omega
      · have h1 := hxb.2 (xs.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    refine specR_callNIH (C := ctxH C H1) cgoA fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cgoLf] (gaaBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW lf] (by decide) rfl (by decide) hc.gaa
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostA (ctxH C H1)) (fun rr w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rr.map Enc.idxW))
      (fun rr w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H1 lf s1))
      (fun args w s2 H2 hp2 ⟨oar, hw, harb⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    have harl := harb.1
    simp only [List.length_map] at harl
    refine UD.specR_heapLoadI' (C := ctxH C H2) cgoAl (vv cgoA) oar _ harl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN2 => ?_)
    have hHN2' : H2.length ≤ C.HN := hHN2
    have hargl : args.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos args.length with h0 | hpos
      · omega
      · have h1 := harb.2 (args.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hlwn := nd_lt_iff args.length m.nPc (by omega) (by omega)
    by_cases hnr : m.nPc ≤ args.length
    swap
    · exact specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgoParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwn.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgoParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hlwb := nd_lt_iff args.length (2 ^ 56) (by omega) (by omega)
    by_cases hlb : args.length < 2 ^ 56
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [hrn]
    simp only [List.getElem?_eq_getElem hif, pure_bind]
    have hpH2 : H <+: H2 := hp1'.trans hp2'
    have hfx := hfb.2 i (by simp; omega)
    simp only [List.getElem_map] at hfx
    refine UD.specR_heapLoadI' (C := ctxH C H2) cgoF _ (pf + 1 + i) _ (get_prefix hfx (hp.trans hpH2)) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv]; exact cellA_mulIdx C pf i (by omega)) ?_
    have hxb2 := blkAt_mono hxb hp2'
    have hxsl := hxb2.1
    simp only [List.length_map] at hxsl
    refine UD.specR_heapLoadI' (C := ctxH C H2) cgoXl (vv cgoXs) oa _ hxsl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    have hlwx := nd_lt_iff xs.length (2 ^ 56) (by omega) (by omega)
    by_cases hxb56 : xs.length < 2 ^ 56
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine ILP.callE_spec (C := ctxH C H2) cgoFx ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
      [vv cgoF, vv cgoXs, .const 0, vv cgoXl] ExK.mkaBody
      [Enc.idxW fvs[i], cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc.mka
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
        trivial⟩
      (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H2) (ctxOK_H hok H2) hc.mka hc.app oa xs hxb2
            (by omega) 0 (by omega) fvs[i] s2; simp only [List.drop_zero] at h; exact h)
      (fun fx s3 => ?_)
    have hok2 := ctxOK_H hok H2
    refine ILP.callE_spec (C := ctxH C H2) cgoRc fInternConst [lEn, lEus] [vv cgoRn, vv cgoRl] constBody
      [Enc.idxW rn, Enc.idxW rlvls] (by decide) rfl (by decide) hc.ic
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], trivial⟩
      (const_body_spec ra (ctxH C H2) hok2 s3 _ _) (fun rc s4 => ?_)
    refine specR_callPure (C := ctxH C H2) cgoB1 fCat catParams [vv cgoPv, vv cgoA, vv cgoNPc] catBody
      [cellA C pv, cellA C oar, BitVec.ofNat 64 m.nPc] (pvars.map Enc.idxW ++ (args.map Enc.idxW).drop m.nPc) (by decide) rfl
      (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], trivial⟩
      (fun r w s' st => ∃ H' o, H2 <+: H' ∧ s' = s4 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
      (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
      (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
        (cat_spec C hok hc.cat (args.map Enc.idxW) oar (by simp; omega) _ m.nPc _ pv H2 s4 rfl
          (by simp; omega) (blkAt_mono hpv (hp.trans hpH2)) harb))
      (fun w H4 hp4 ⟨o4, hw4, hb4⟩ => ?_)
    subst hw4
    have hp4' : H2 <+: H4 := hp4
    refine specR_alloc2I (ctxOK_H hok H4) cgoB2 (.const 1) (vv cgoFx) (BitVec.ofNat 64 1) (Enc.idxW fx)
      (by decide) (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H5 ws5 hp5 hws5 => ?_)
    obtain ⟨k0, k1⟩ := img2_get H5 ws5 (BitVec.ofNat 64 1) (Enc.idxW fx) hws5
    have hp5' : H4 <+: _ := (hp5 : H4 <+: H5).trans (img2_prefix H5 ws5 (BitVec.ofNat 64 1) (Enc.idxW fx) hws5)
    have hb5 : BlkAt (((H5 ++ ws5).set H5.length (BitVec.ofNat 64 1)).set (H5.length + 1) (Enc.idxW fx)) H5.length
        [Enc.idxW fx] := ⟨by simpa using k0, fun i hi => by simp at hi; subst hi; simpa using k1⟩
    refine specR_callPure (C := ctxH C _) cgoB3 fCat catParams [vv cgoB1, vv cgoB2, .const 0] catBody
      [cellA C o4, cellA C H5.length, BitVec.ofNat 64 0]
      ((pvars.map Enc.idxW ++ (args.map Enc.idxW).drop m.nPc) ++ [Enc.idxW fx].drop 0)
      (by decide) rfl (by decide) hc.cat.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, rfl, trivial⟩
      (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s4 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
      (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
      (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
        (cat_spec C hok hc.cat [Enc.idxW fx] H5.length (by simp) _ 0 _ o4 _ s4 rfl (by simp) (blkAt_mono hb4 hp5')
          hb5))
      (fun w H6 hp6 ⟨o6, hw6, hb6⟩ => ?_)
    subst hw6
    have hp6' : _ <+: H6 := hp6
    have hb6' : BlkAt H6 o6 ((pvars ++ args.drop m.nPc ++ [fx]).map Enc.idxW) := by simpa [List.map_drop] using hb6
    have hl6 := hb6'.1
    simp only [List.length_map] at hl6
    obtain ⟨L3, hL3⟩ : ∃ L3, (pvars ++ args.drop m.nPc ++ [fx]).length = L3 := ⟨_, rfl⟩
    rw [hL3] at hl6
    have hp26 : H2 <+: H6 := hp4'.trans (hp5'.trans hp6')
    refine UD.specR_heapLoadI' (C := ctxH C H6) cgoB3l (vv cgoB3) o6 _ hl6 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN6 => ?_)
    have hHN6' : H6.length ≤ C.HN := hHN6
    have hb3l0 : L3 < 2 ^ 61 := by
      have := blk_len_lt' hok hHN6' hb6'; simp only [List.length_map] at this; omega
    have hlw3 := nd_lt_iff L3 (2 ^ 56) (by omega) (by omega)
    by_cases hb3 : L3 < 2 ^ 56
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine ILP.callE_spec (C := ctxH C H6) cgoAp ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
      [vv cgoRc, vv cgoB3, .const 0, vv cgoB3l] ExK.mkaBody
      [Enc.idxW rc, cellA C o6, BitVec.ofNat 64 0, BitVec.ofNat 64 (pvars ++ args.drop m.nPc ++ [fx]).length] (by decide) rfl
      (by decide) hc.mka
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons]; rw [← hL3]; simp,
        trivial⟩
      (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H6) (ctxOK_H hok H6) hc.mka hc.app o6 (pvars ++ args.drop m.nPc ++ [fx]) hb6'
            (by omega) 0 (by omega) rc s4; simp only [List.drop_zero] at h; exact h)
      (fun app s6 => ?_)
    rw [mapM_binder_eq g xs]
    refine specR_callNIH (C := ctxH C H6) cgoBs fFvtDs ftdParams [vv cgoXs] (ftdBody C) [cellA C oa] (by decide) rfl
      (by decide) hc.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (PostA (ctxH C H6)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
      (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
        (ftd_spec C hok hc.ftd hc.ftf hc.fvt xs oa (by omega) H6 s6 (blkAt_mono hxb2 hp26)))
      (fun bs w s7 H7 hp7 ⟨o7, hw7, hb7⟩ => ?_)
    subst hw7
    have hp7' : H6 <+: H7 := hp7
    have hpC7 : C.H <+: H7 := hpC.trans (hpH2.trans (hp26.trans hp7'))
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN7 => ?_)
    have hHN7' : H7.length ≤ C.HN := hHN7
    have hbsl0 : bs.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos bs.length with h0 | hpos
      · omega
      · have h1 := hb7.2 (bs.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hb7l := hb7.1
    simp only [List.length_map] at hb7l
    refine UD.specR_heapLoadI' (C := ctxH C H7) cgoBl (vv cgoBs) o7 _ hb7l (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    have hlwbs := nd_lt_iff bs.length (2 ^ 56) (by omega) (by omega)
    by_cases hbsl : bs.length < 2 ^ 56
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun _ => ?_) (fun h => absurd h (by decide))
    unfold closeLams
    refine specR_callNIH (C := ctxH C H7) cgoCl fClm clmParams [vv cgoE, .const 0, vv cgoBs, .const 0, vv cgoAp] clmBody
      [BitVec.ofNat 64 (rP + x.nF), BitVec.ofNat 64 0, cellA C o7, BitVec.ofNat 64 0, Enc.idxW app] (by decide) rfl
      (by decide) hc.clm.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostK (ctxH C H7)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu clmParams _ rfl hlk)
        (by have h := clm_spec (σ := σ) ra C hok hc.clm (rP + x.nF) (by omega) bs o7 (by omega) app bs.length 0 0 H7 s7
              (by omega) (by omega) (by omega) hpC7 hb7; simp only [List.drop_zero] at h; exact h))
      (fun cl w s8 H8 hp8 hw => ?_)
    subst hw
    have hp8' : H7 <+: H8 := hp8
    unfold cgoRec
    refine specR_callNIH (C := ctxH C H8) ExS.lY fCgo cgoParams [vv cgoKb, .op .add [vv cgoI, .const 1], vv cgoN, vv cgoFv,
        vv cgoFn, vv cgoWs, vv cgoWn, vv cgoE, vv cgoNPc, vv cgoRn, vv cgoRl, vv cgoPv] (cgoBody C)
      [cellA C pk, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 x.nF, cellA C pf, BitVec.ofNat 64 fvs.length, cellA C pw,
        BitVec.ofNat 64 ws.length, BitVec.ofNat 64 (rP + x.nF), BitVec.ofNat 64 m.nPc, Enc.idxW rn, Enc.idxW rlvls,
        cellA C pv] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgoParams, ctxEnv],
        trivial⟩
      (PostIH (ctxH C H8) (x.nF - (i + 1))) (fun o w _ H' => ∃ ihs ob, o = some ihs ∧ w = cellA C ob ∧
        BlkAt H' ob (ihs.map Enc.idxW) ∧ ihs.length ≤ x.nF - (i + 1))
      (fun o w s' st ⟨ihs, H', ob, h0, hp', hw, hb, hl, hsr⟩ => ⟨H', hp', ⟨ihs, ob, h0, hw, hb, hl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cgoParams _ rfl hlk)
        (ih (i + 1) H8 s8 (by omega) (by omega) (hp.trans (hpH2.trans (hp26.trans (hp7'.trans hp8'))))))
      (fun o w s9 H9 hp9 ⟨ihs, oy, ho, hw, hry, hl⟩ => ?_)
    subst ho hw
    have hp9' : H8 <+: H9 := hp9
    simp only
    refine ExPre.prepend_spec C hok (H := H9) cgoCl (Enc.idxW cl) oy (ihs.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hry (by decide)
      (by simp +decide [Env.get_cons, Env.get, cgoParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨cl :: ihs, H', o, rfl, hpH2.trans (hp26.trans (hp7'.trans (hp8'.trans (hp9'.trans hp')))), rfl,
      by simpa using hb, by simp; omega, hsr⟩

end

/-! ## The generated rule -/

def cgrCc := ofString "cgr_cc"
def cgrRp := ofString "cgr_rp"
def cgrNp := ofString "cgr_np"
def cgrPm := ofString "cgr_pm"
def cgrSl := ofString "cgr_sl"
def cgrPr := ofString "cgr_pr"
def cgrNf := ofString "cgr_nf"
def cgrTd := ofString "cgr_td"
def cgrTn := ofString "cgr_tn"
def cgrCvp := ofString "cgr_cvp"
def cgrNm := ofString "cgr_nm"
def cgrLp := ofString "cgr_lp"
def cgrNs := ofString "cgr_ns"
def cgrS := ofString "cgr_s"
def cgrX := ofString "cgr_x"
def cgrFv := ofString "cgr_fv"
def cgrLf := ofString "cgr_lf"
def cgrW := ofString "cgr_w"
def cgrD := ofString "cgr_d"
def cgrZ := ofString "cgr_z"
def cgrSz := ofString "cgr_sz"
def cgrSv := ofString "cgr_sv"
def cgrBd := ofString "cgr_bd"
def cgrFb := ofString "cgr_fb"
def cgrLb := ofString "cgr_lb"
def cgrCt := ofString "cgr_ct"
def cgrR := ofString "cgr_r"
def cgrNpc := ofString "cgr_npc"
def cgrRn := ofString "cgr_rn"
def cgrRl := ofString "cgr_rl"
def cgrKb := ofString "cgr_kb"
def cgrWl := ofString "cgr_wl"
def cgrIh := ofString "cgr_ih"
def cgrCa := ofString "cgr_ca"
def cgrCal := ofString "cgr_cal"
def fCgr := ofString "classGenRule"

def cgrParams : List MlS := [cgrCc, cgrRp, cgrNp, cgrPm, cgrSl, cgrPr, cgrNpc, cgrRn, cgrRl]
def cgrLocals : List MlS := [cgrNf, cgrTd, cgrTn, cgrCvp, cgrNm, cgrLp, cgrNs, cgrS, cgrX, cgrFv, cgrLf, cgrW, cgrD, cgrZ,
  cgrSz, cgrSv, cgrBd, cgrFb, cgrLb, cgrCt, cgrR, cgrKb, cgrWl, cgrIh, cgrCa, cgrCal]

def cgrBody (C : Ctx) : ProgHOL 64 := prologue cgrLocals
  (.seq (.assign .local cgrNf (.load .one (.op .add [(vv cgrCc), .const 8])))
  (.seq (.assign .local cgrTd (.load .one (.op .add [(vv cgrCc), .const 16])))
  (.seq (.assign .local cgrTn (.load .one (.op .add [(vv cgrCc), .const 24])))
  (.seq (.assign .local cgrCvp (.load .one (vv cgrCc)))
  (.seq (.assign .local cgrNm (.load .one (vv cgrCvp)))
  (.seq (.assign .local cgrLp (.load .one (vv cgrPm)))
  (.ite (.cmp .lower (vv cgrLp) (vv cgrNp))
  hang
  (.seq (.assign .local cgrNs (.load .one (vv cgrSl)))
  (.seq (.call (some (some (.local, cgrS), none)) fFms [(vv cgrSl), .const 0, (vv cgrNs), (vv cgrNm)])
  (.seq (.call (some (some (.local, cgrX), none)) fOpenFvars [(vv cgrNf), (vv cgrTd), (vv cgrRp)])
  (.ite (.cmp .equal (vv cgrX) (.const 0))
  hang
  (.seq (.assign .local cgrFv (.load .one (vv cgrX)))
  (.seq (.assign .local cgrLf (.load .one (vv cgrFv)))
  (.ite (.cmp .equal (vv cgrLf) (vv cgrNf))
  (.seq (.call (some (some (.local, cgrW), none)) fTpw [(vv cgrFv), .const 0, (vv cgrLf), (vv cgrTn)])
  (.seq (.call (some (some (.local, cgrD), none)) fPvg [.const 0, (vv cgrRp), (vv cgrNp), (vv cgrPm)])
  (.seq (.assign .local cgrKb (.load .one (.op .add [(vv cgrCc), .const 40])))
  (.seq (.assign .local cgrWl (.load .one (vv cgrW)))
  (.seq (.call (some (some (.local, cgrIh), none)) fCgo [(vv cgrKb), .const 0, (vv cgrNf), (vv cgrFv), (vv cgrLf),
      (vv cgrW), (vv cgrWl), .op .add [(vv cgrRp), (vv cgrNf)], (vv cgrNpc), (vv cgrRn), (vv cgrRl), (vv cgrD)])
  (.seq (.assign .local cgrZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, cgrSz), none)) fInternSort [(vv cgrZ)])
  (.seq (.call (some (some (.local, cgrSv), none)) fInternFVar [(vv cgrSz), (.op .add [(vv cgrNp), (vv cgrS)])])
  (.seq (.call (some (some (.local, cgrCa), none)) fCat [(vv cgrFv), (vv cgrIh), .const 0])
  (.seq (.assign .local cgrCal (.load .one (vv cgrCa)))
  (.seq (.call (some (some (.local, cgrBd), none)) ExK.fMka [(vv cgrSv), (vv cgrCa), .const 0, (vv cgrCal)])
  (.seq (.call (some (some (.local, cgrFb), none)) fFvtDs [(vv cgrFv)])
  (.seq (.assign .local cgrLb (.load .one (vv cgrFb)))
  (.ite (.cmp .equal (vv cgrLb) (vv cgrNf))
  (.seq (.call (some (some (.local, cgrCt), none)) fCat [(vv cgrPr), (vv cgrFb), .const 0])
  (.seq (.call (some (some (.local, cgrR), none)) fClm [.const 0, .const 0, (vv cgrCt), .const 0, (vv cgrBd)])
  (.return (vv cgrR))))
  hang))))))))))))))
  hang))))))))))))))

structure CGRCodes (C : Ctx) : Prop where
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  tpw : TPWCodes C
  fms : C.code.lookup fFms = some (fmsParams.map (fun p => (p, ShapeHOL.one)), fmsBody, .one)
  pvg : PVGCodes C
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  ftd : C.code.lookup fFvtDs = some (ftdParams.map (fun p => (p, ShapeHOL.one)), ftdBody C, .one)
  ftf : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  cat : CatCodes C
  clm : CLMCodes C
  cgo : CGOCodes C
  self : C.code.lookup fCgr = some (cgrParams.map (fun p => (p, ShapeHOL.one)), cgrBody C, .one)

section
variable {σ : Type}

theorem cgr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cgrLocals → (ctxEnv C ++ cgrParams.zip vals).get x = none :=
  Knot.params_none C cgrLocals cgrParams vals (by decide) (by decide)

theorem find_zip_hit (sls : List ClassSlot) (cn : NIdx) (p : Nat × ClassSlot → Bool) (hp : ∀ q, p q = isHitC cn q.2)
    (r : Nat) (hr : r < sls.length) (h1 : isHitC cn sls[r] = true)
    (h2 : ∀ k (hk : k < sls.length), k < r → isHitC cn sls[k] = false) :
    ((List.range sls.length).zip sls).find? p = some (r, sls[r]) := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by rw [hp]; exact h1, r, by simp; exact hr, by simp [List.getElem_zip], fun j hj => ?_⟩
  rw [hp]; simp only [List.getElem_zip, List.getElem_range]
  rw [h2 j (by omega) hj]; rfl

set_option maxHeartbeats 32000000 in
/-- **`classGenRule g _ _ _ 0 x`** for a constructor of the one class (recursive fields at class `0`). -/
theorem cgr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CGRCodes C)
    (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal) (rlvls : LsIdx)
    (m : TargetMajor) (hcls : g.cls = [m]) (hnpc : m.nPc < 2 ^ 62) (rn : NIdx) (hrn : classRecOf recCls cvGs 0 = some rn)
    (x : ClassCtor) (oc : Nat) (hcc : CCRep C C.H oc x) (hnf : x.nF < 2 ^ 56)
    (opm : Nat) (hpm : BlkAt C.H opm (g.params.map Enc.idxW)) (hpml : g.params.length < 2 ^ 56)
    (os : Nat) (hsb : SlotBlk C C.H os g.slots) (hsl : g.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (opr : Nat) (hpr : BlkAt C.H opr (g.pre.map Enc.idxW)) (hprl : g.pre.length < 2 ^ 56) (hnP : g.nP < 2 ^ 56)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (cgrParams.zip [cellA C oc, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP,
        cellA C opm, cellA C os, cellA C opr, BitVec.ofNat 64 m.nPc, Enc.idxW rn, Enc.idxW rlvls])) (cgrBody C) s
      (classGenRule g recCls cvGs rlvls 0 x) (PostSomeH C) := by
  refine specR_prologue (postSomeH_locals _) (cgr_none _ _) ?_
  obtain ⟨⟨ocv, hocv, hcv⟩, hnfw, htd, htn, -, ⟨okb, hokb, hkb⟩, hko, hkl⟩ := hcc
  unfold classGenRule
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine UD.specR_heapLoadI' (C := ctxH C C.H) cgrNf _ (oc + 1) _ hnfw (by decide) (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; exact cellA_add8 C oc) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) cgrTd _ (oc + 2) _ htd (by decide) (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) cgrTn _ (oc + 3) _ htn (by decide) (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; exact cellA_add_ofNat C oc 3) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) cgrCvp _ oc _ hocv (by decide) (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) cgrNm (vv cgrCvp) ocv _ hcv.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  -- the parameters must be there (their reads then pure)
  refine UD.specR_heapLoadI' (C := ctxH C C.H) cgrLp _ opm _ hpm.1 (by decide) (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; rfl) ?_
  simp only [List.length_map]
  have hlwp := nd_lt_iff g.params.length g.nP (by omega) (by omega)
  by_cases hpl : g.nP ≤ g.params.length
  swap
  · exact specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        hlwp.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cgrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    (fun h => absurd rfl h) (fun _ => ?_)
  -- the minor slot
  have hsb0 := hsb
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hsb0
  have hns : C.H[os]? = some (BitVec.ofNat 64 g.slots.length) := by simpa [hpsl] using hpsb.1
  refine UD.specR_heapLoadI' (C := ctxH C C.H) cgrNs _ os _ hns (by decide) (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; rfl) ?_
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
  refine specR_callNIH (C := ctxH C C.H) cgrS fFms fmsParams [vv cgrSl, .const 0, vv cgrNs, vv cgrNm] fmsBody
    [cellA C os, BitVec.ofNat 64 0, BitVec.ofNat 64 g.slots.length, Enc.idxW x.cv.name] (by decide) rfl (by decide) hc.fms
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostFMS (ctxH C C.H) g.slots x.cv.name 0 s)
    (fun _ w s' H' => H' = C.H ∧ s' = s ∧ ∃ r, w = BitVec.ofNat 64 r ∧ ∃ hr : r < g.slots.length,
      isHitC x.cv.name g.slots[r] = true ∧ ∀ k (hk : k < g.slots.length), k < r → isHitC x.cv.name g.slots[k] = false)
    (fun a w s' st ⟨h0, r, h1, h2, h3, h4, h5, h6⟩ => ⟨C.H, List.prefix_refl _,
      ⟨rfl, h0, r, h1, h3, h4, fun k hk h => h5 k hk (Nat.zero_le _) h⟩, h6⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmsParams _ rfl hlk)
      (fms_spec C hc.fms g.slots os (by omega) x.cv.name hcb C.H hsb g.slots.length 0 s (by omega) (by omega)))
    (fun _ w s1 H1 hp1 ⟨eH, es, r, hw, hr, hh, hb⟩ => ?_)
  subst eH es hw
  have e : ∀ p : Nat × ClassSlot → Bool, (∀ q, p q = isHitC x.cv.name q.2) →
      ((List.range g.slots.length).zip g.slots).find? p = some (r, g.slots[r]) :=
    fun p hp => find_zip_hit g.slots x.cv.name p hp r hr hh hb
  rw [e _ (fun q => by rcases q with ⟨_, sl⟩; cases sl <;> rfl)]
  simp only
  refine specR_callNIH (C := ctxH C C.H) cgrX fOpenFvars ofParams [vv cgrNf, vv cgrTd, vv cgrRp]
    (ofBody C) [BitVec.ofNat 64 x.nF, Enc.idxW x.tyD, BitVec.ofNat 64 g.pre.length] (by decide) rfl
    (by decide) hc.ofc ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], trivial⟩
    (PostOF (ctxH C C.H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op x.nF x.tyD g.pre.length (by omega) (by omega) C.H hp0 s1))
    (fun o w s2 H1 hp1 ⟨hn, hsm⟩ => ?_)
  have hp1' : C.H <+: H1 := hp1
  rcases o with _ | ⟨fvs, res⟩
  · have e0 := hn rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, oa, rfl, hob, hres, hfb⟩ := hsm fvs res rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol : ob < H1.length := (List.getElem?_eq_some_iff.mp hob).1
  have hHN' : H1.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H1) cgrFv (vv cgrX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfl : H1[oa]? = some (BitVec.ofNat 64 fvs.length) := by simpa using hfb.1
  refine UD.specR_heapLoadI' (C := ctxH C H1) cgrLf (vv cgrFv) oa _ hfl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfvl0 : fvs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos fvs.length with h0 | hpos
    · omega
    · have h1 := hfb.2 (fvs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hfn : fvs.length = x.nF
  swap
  · have hne2 : BitVec.ofNat 64 fvs.length ≠ BitVec.ofNat 64 x.nF := fun e => hfn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfn]) (fun _ => ?_) (fun h => absurd h (by decide))
  have hfvl : fvs.length < 2 ^ 56 := by omega
  refine specR_callNIH (C := ctxH C H1) cgrW fTpw tpwParams [vv cgrFv, .const 0, vv cgrLf, vv cgrTn] (tpwBody C)
    [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, Enc.idxW x.tyN] (by decide) rfl (by decide) hc.tpw.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], trivial⟩
    (PostSL (ctxH C H1)) (fun o w _ H' => ∃ ds ow, o = some ds ∧ w = cellA C ow ∧ BlkAt H' ow (ds.map Enc.idxW))
    (fun o w s' st ⟨ds, H', ow, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, ow, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tpwParams _ rfl hlk)
      (by have h := tpw_spec (σ := σ) ra C hok hc.tpw fvs oa H1 hp1' hfb fvs.length 0 H1 s2 x.tyN (by omega) (by omega) (List.prefix_refl _); simp only [List.drop_zero] at h; exact h))
    (fun o w s3 H2 hp2 ⟨ws, ow, ho, hw, hwb⟩ => ?_)
  subst ho hw
  have hp2' : H1 <+: H2 := hp2
  simp only
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  refine specR_callNIH (C := ctxH C H2) cgrD fPvg pvgParams [.const 0, vv cgrRp, vv cgrNp, vv cgrPm] (pvgBody C)
    [BitVec.ofNat 64 0, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm] (by decide) rfl (by decide) hc.pvg.self
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], trivial⟩
    (PostA (ctxH C H2)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
    (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pvgParams _ rfl hlk)
      (by have h := pvg_spec (σ := σ) ra C hok hc.pvg g hpl g.pre.length (by omega) (by omega) opm hpml hpm g.pre.length 0 H2 s3 (by omega) (by omega) hpC2; simp only [List.drop_zero] at h; exact h))
    (fun pvars w s4 H3 hp3 ⟨opv, hw, hpvb⟩ => ?_)
  subst hw
  have hp3a : H2 <+: H3 := hp3
  refine UD.specR_heapLoadI' (C := ctxH C H3) cgrKb _ (oc + 5) _ (get_prefix hokb (hpC2.trans hp3a)) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; exact cellA_add_ofNat C oc 5) ?_
  have hwl0 := (blkAt_mono hwb hp3a).1
  simp only [List.length_map] at hwl0
  refine UD.specR_heapLoadI' (C := ctxH C H3) cgrWl (vv cgrW) ow _ hwl0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_callNIH (C := ctxH C H3) cgrIh fCgo cgoParams [vv cgrKb, .const 0, vv cgrNf, vv cgrFv, vv cgrLf,
      vv cgrW, vv cgrWl, .op .add [vv cgrRp, vv cgrNf], vv cgrNpc, vv cgrRn, vv cgrRl, vv cgrD] (cgoBody C)
    [cellA C okb, BitVec.ofNat 64 0, BitVec.ofNat 64 x.nF, cellA C oa, BitVec.ofNat 64 fvs.length, cellA C ow,
      BitVec.ofNat 64 ws.length, BitVec.ofNat 64 (g.pre.length + x.nF), BitVec.ofNat 64 m.nPc, Enc.idxW rn,
      Enc.idxW rlvls, cellA C opv] (by decide) rfl (by decide) hc.cgo.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; simp only [BitVec.ofNat_add],
      by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostIH (ctxH C H3) (x.nF - 0)) (fun o w _ H' => ∃ ihs ob, o = some ihs ∧ w = cellA C ob ∧
      BlkAt H' ob (ihs.map Enc.idxW) ∧ ihs.length ≤ x.nF - 0)
    (fun o w s' st ⟨ihs, H', ob, h0, hp', hw, hb, hl, hsr⟩ => ⟨H', hp', ⟨ihs, ob, h0, hw, hb, hl⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cgoParams _ rfl hlk)
      (by have h := cgo_spec (σ := σ) ra C hok hc.cgo g m hcls recCls cvGs rlvls rn hrn x g.pre.length fvs ws pvars okb oa ow
            opv hko hkl hnf (by omega) hnpc H3 (hpC2.trans hp3a) (blkAt_mono hkb (hpC2.trans hp3a))
            (blkAt_mono hfb (hp2'.trans hp3a)) (blkAt_mono hwb hp3a) hpvb x.nF 0 H3 s4 (by omega) (by omega)
            (List.prefix_refl _)
          simp only [Nat.sub_zero] at h ⊢; exact h))
    (fun o w s4 H3 hp3x ⟨ihs, oih, ho, hw, hihb, hihl⟩ => ?_)
  subst ho hw
  simp only
  have hp3' : H2 <+: H3 := hp3a.trans hp3x
  have hpC3 : C.H <+: H3 := hpC2.trans hp3'
  simp only [ClassGen.slotVar, zeroLevel, bind_assoc]
  have hok3 := ctxOK_H hok H3
  refine specR_pinXI (C := ctxH C H3) hok3 pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H3) hok3 hp) (pin_zeroLevel_cell hok3) cgrZ (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H3) cgrSz fInternSort [lEu] [vv cgrZ] sortBody [Enc.idxW C.pins.zeroLevel]
    (by decide) rfl (by decide) hc.pvg.srt ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
    (sort_body_spec ra (ctxH C H3) hok3 s4 _) (fun sz s5 => ?_)
  refine ILP.specR_internFVarI ra hok3 hc.pvg.fv cgrSv (vv cgrSz) (.op .add [vv cgrNp, vv cgrS]) sz (g.nP + r) (by omega) (by decide)
    (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv]; rw [BitVec.ofNat_add]) (fun sv s6 => ?_)
  refine specR_callPure (C := ctxH C H3) cgrCa fCat catParams [vv cgrFv, vv cgrIh, .const 0] catBody
    [cellA C oa, cellA C oih, BitVec.ofNat 64 0] (fvs.map Enc.idxW ++ (ihs.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H3 <+: H' ∧ s' = s6 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (ihs.map Enc.idxW) oih (by simp; omega) _ 0 _ oa H3 s6 rfl (by omega)
        (blkAt_mono hfb (hp2'.trans hp3')) hihb))
    (fun w H3c hp3c ⟨o3c, hw3c, hb3c⟩ => ?_)
  subst hw3c
  have hb3c' : BlkAt H3c o3c ((fvs ++ ihs).map Enc.idxW) := by simpa using hb3c
  have hl3c := hb3c'.1
  simp only [List.length_map] at hl3c
  refine UD.specR_heapLoadI' (C := ctxH C H3c) cgrCal (vv cgrCa) o3c _ hl3c (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine ILP.callE_spec (C := ctxH C H3c) cgrBd ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv cgrSv, vv cgrCa, .const 0, vv cgrCal] ExK.mkaBody
    [Enc.idxW sv, cellA C o3c, BitVec.ofNat 64 0, BitVec.ofNat 64 (fvs ++ ihs).length] (by decide) rfl (by decide) hc.mka
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H3c) (ctxOK_H hok H3c) hc.mka hc.app o3c (fvs ++ ihs) hb3c' (by simp; omega) 0 (by omega) sv s6; simp only [List.drop_zero] at h; exact h)
    (fun body s7 => ?_)
  have hp3c' : H3 <+: H3c := hp3c
  have hp3'' : H2 <+: H3c := hp3'.trans hp3c'
  have hpC3' : C.H <+: H3c := hpC2.trans hp3''
  rw [mapM_binder_eq g fvs]
  refine specR_callNIH (C := ctxH C H3c) cgrFb fFvtDs ftdParams [vv cgrFv] (ftdBody C) [cellA C oa] (by decide) rfl
    (by decide) hc.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H3c)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
    (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
      (ftd_spec C hok hc.ftd hc.ftf hc.fvt fvs oa (by omega) H3c s7 (blkAt_mono hfb (hp2'.trans hp3''))))
    (fun fbs w s8 H4 hp4 ⟨o4, hw4, hb4⟩ => ?_)
  subst hw4
  have hp4' : H3c <+: H4 := hp4
  have hb4l := hb4.1
  simp only [List.length_map] at hb4l
  refine UD.specR_heapLoadI' (C := ctxH C H4) cgrLb (vv cgrFb) o4 _ hb4l (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN4 => ?_)
  have hHN4' : H4.length ≤ C.HN := hHN4
  have hfbl0 : fbs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos fbs.length with h0 | hpos
    · omega
    · have h1 := hb4.2 (fbs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hfbn : fbs.length = x.nF
  swap
  · have hne3 : BitVec.ofNat 64 fbs.length ≠ BitVec.ofNat 64 x.nF := fun e => hfbn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne3) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfbn]) (fun _ => ?_) (fun h => absurd h (by decide))
  have hpC4 : C.H <+: H4 := hpC3'.trans hp4'
  refine specR_callPure (C := ctxH C H4) cgrCt fCat catParams [vv cgrPr, vv cgrFb, .const 0] catBody
    [cellA C opr, cellA C o4, BitVec.ofNat 64 0] (g.pre.map Enc.idxW ++ (fbs.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H4 <+: H' ∧ s' = s8 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (fbs.map Enc.idxW) o4 (by simp; omega) _ 0 _ opr H4 s8 rfl (by omega)
        (blkAt_mono hpr hpC4) hb4))
    (fun w H5 hp5 ⟨o5, hw5, hb5⟩ => ?_)
  subst hw5
  have hp5' : H4 <+: H5 := hp5
  have hb5' : BlkAt H5 o5 ((g.pre ++ fbs).map Enc.idxW) := by simpa using hb5
  unfold closeLams
  refine specR_callNIH (C := ctxH C H5) cgrR fClm clmParams [.const 0, .const 0, vv cgrCt, .const 0, vv cgrBd] clmBody
    [BitVec.ofNat 64 0, BitVec.ofNat 64 0, cellA C o5, BitVec.ofNat 64 0, Enc.idxW body] (by decide) rfl (by decide)
    hc.clm.self ⟨rfl, rfl, by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostK (ctxH C H5)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu clmParams _ rfl hlk)
      (by have h := clm_spec (σ := σ) ra C hok hc.clm 0 (by omega) (g.pre ++ fbs) o5 (by simp; omega) body (g.pre ++ fbs).length 0 0 H5 s8 (by omega) (by omega) (by simp; omega) (hpC4.trans hp5') hb5'; simp only [List.drop_zero] at h; exact h))
    (fun rr w s10 H6 hp6 hw => ?_)
  subst hw
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H6, rr, (hpC4.trans hp5').trans hp6, rfl, rfl,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
