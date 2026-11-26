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

/-! ## The prefix variables' effects -/

def pvgI := ofString "pvg_i"
def pvgR := ofString "pvg_r"
def pvgN := ofString "pvg_n"
def pvgZ := ofString "pvg_z"
def pvgSz := ofString "pvg_sz"
def pvgV := ofString "pvg_v"
def pvgX := ofString "pvg_x"
def fPvg := ofString "prefixVarsGo"

def pvgParams : List MlS := [pvgI, pvgR, pvgN]
def pvgLocals : List MlS := [pvgZ, pvgSz, pvgV, pvgX]

def pvgRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, pvgX), none)) fPvg [.op .add [vv pvgI, .const 1], vv pvgR, vv pvgN])
    (.return (.const 0))

def pvgBody (C : Ctx) : ProgHOL 64 := prologue pvgLocals
  (.ite (.cmp .lower (vv pvgI) (vv pvgR))
    (.ite (.cmp .lower (vv pvgI) (vv pvgN))
      pvgRec
      (.seq (.assign .local pvgZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
      (.seq (.call (some (some (.local, pvgSz), none)) fInternSort [vv pvgZ])
      (.seq (.call (some (some (.local, pvgV), none)) fInternFVar [vv pvgSz, vv pvgI])
        pvgRec))))
    (.return (.const 0)))

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
/-- **The prefix variables** from `i` on: the parameters read, the slots' variables interned. -/
theorem pvg_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PVGCodes C)
    (g : ClassGen) (hpl : g.nP ≤ g.params.length) (rP : Nat) (hrP : rP < 2 ^ 62) (hnP : g.nP < 2 ^ 62) :
    ∀ f i (H : List (BitVec 64)) (s : AState), rP - i = f → i ≤ rP → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (pvgParams.zip [BitVec.ofNat 64 i, BitVec.ofNat 64 rP, BitVec.ofNat 64 g.nP]))
        (pvgBody C) s (((List.range rP).drop i).mapM fun i =>
          if i < g.nP then exprGetD g.params i else g.slotVar (i - g.nP)) (PostLs (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = rP := by omega
    subst hin
    refine specR_prologue (postLs_locals _) (pvg_none _ _) ?_
    have hlw := nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pvgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [show (List.range i).drop i = [] by simp]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < rP := by omega
    refine specR_prologue (postLs_locals _) (pvg_none _ _) ?_
    have hlw := nd_lt_iff i rP (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pvgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons (by simpa using hin), List.getElem_range, List.mapM_cons]
    -- the recursive call and the return, after slot `i`'s effects
    have hrec : ∀ (b : EIdx) (s1 : AState) (Γ : Env) (M : Mem), Γ.get pvgI = some (BitVec.ofNat 64 i) →
        Γ.get pvgR = some (BitVec.ofNat 64 rP) → Γ.get pvgN = some (BitVec.ofNat 64 g.nP) →
        pvgX ∈ ctxLocals ++ pvgLocals →
        SpecR (σ := σ) (Inv (ctxH C H) s1 Γ M (ctxLocals ++ pvgLocals)) pvgRec s1
          ((((List.range rP).drop (i + 1)).mapM fun i =>
            if i < g.nP then exprGetD g.params i else g.slotVar (i - g.nP)) >>= fun bs => pure (b :: bs))
          (PostLs (ctxH C H)) := by
      intro b s1 Γ M gI gR gN hx
      refine specR_callNIH (C := ctxH C H) pvgX fPvg pvgParams [.op .add [vv pvgI, .const 1], vv pvgR, vv pvgN]
        (pvgBody C) [BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rP, BitVec.ofNat 64 g.nP] (by decide) rfl hx hc.self
        ⟨by simp [sev, sev_vv, gI]; exact word_add1_eq i, by simp [sev, gR], by simp [sev, gN], trivial⟩
        (PostLs (ctxH C H)) (fun _ _ _ _ => True)
        (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pvgParams _ rfl hlk)
          (ih (i + 1) H s1 (by omega) (by omega) hp))
        (fun _ w s3 H3 hp3 _ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    by_cases hlt : i < g.nP
    · have hlw2 := nd_lt_iff i g.nP (by omega) (by omega)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pvgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr hlt])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [hlt, ↓reduceIte, exprGetD, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hlt hpl), pure_bind]
      exact hrec _ s _ _ (by simp +decide [Env.get, pvgParams, ctxEnv]) (by simp +decide [Env.get, pvgParams, ctxEnv])
        (by simp +decide [Env.get, pvgParams, ctxEnv]) (by decide)
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
        (by decide)

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
def fCgr := ofString "classGenRuleOrd"

def cgrParams : List MlS := [cgrCc, cgrRp, cgrNp, cgrPm, cgrSl, cgrPr]
def cgrLocals : List MlS := [cgrNf, cgrTd, cgrTn, cgrCvp, cgrNm, cgrLp, cgrNs, cgrS, cgrX, cgrFv, cgrLf, cgrW, cgrD, cgrZ,
  cgrSz, cgrSv, cgrBd, cgrFb, cgrLb, cgrCt, cgrR]

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
  (.seq (.call (some (some (.local, cgrD), none)) fPvg [.const 0, (vv cgrRp), (vv cgrNp)])
  (.seq (.assign .local cgrZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, cgrSz), none)) fInternSort [(vv cgrZ)])
  (.seq (.call (some (some (.local, cgrSv), none)) fInternFVar [(vv cgrSz), (.op .add [(vv cgrNp), (vv cgrS)])])
  (.seq (.call (some (some (.local, cgrBd), none)) ExK.fMka [(vv cgrSv), (vv cgrFv), .const 0, (vv cgrLf)])
  (.seq (.call (some (some (.local, cgrFb), none)) fFvtDs [(vv cgrFv)])
  (.seq (.assign .local cgrLb (.load .one (vv cgrFb)))
  (.ite (.cmp .equal (vv cgrLb) (vv cgrNf))
  (.seq (.call (some (some (.local, cgrCt), none)) fCat [(vv cgrPr), (vv cgrFb), .const 0])
  (.seq (.call (some (some (.local, cgrR), none)) fClm [.const 0, .const 0, (vv cgrCt), .const 0, (vv cgrBd)])
  (.return (vv cgrR))))
  hang)))))))))
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
  self : C.code.lookup fCgr = some (cgrParams.map (fun p => (p, ShapeHOL.one)), cgrBody C, .one)

section
variable {σ : Type}

theorem cgr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cgrLocals → (ctxEnv C ++ cgrParams.zip vals).get x = none :=
  Knot.params_none C cgrLocals cgrParams vals (by decide) (by decide)

theorem callsGo_ord (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal) (rlvls : LsIdx) (x : ClassCtor)
    (hko : ∀ k ∈ x.kinds, k = .ordinary) (rP : Nat) (fvs ws pvars : List EIdx) :
    ∀ n i, classGenRule.callsGo g recCls cvGs rlvls x rP fvs ws pvars n i = pure (some [])
  | 0, i => by simp only [classGenRule.callsGo]
  | n + 1, i => by
    have hget : x.kinds.getD i .ordinary = .ordinary := by
      rcases h : x.kinds[i]? with _ | k
      · simp [List.getD, h]
      · simp [List.getD, h]; exact hko k (List.mem_of_getElem? h)
    simp only [classGenRule.callsGo, hget]
    exact callsGo_ord g recCls cvGs rlvls x hko rP fvs ws pvars n (i + 1)

theorem find_zip_hit (sls : List ClassSlot) (cn : NIdx) (p : Nat × ClassSlot → Bool) (hp : ∀ q, p q = isHitC cn q.2)
    (r : Nat) (hr : r < sls.length) (h1 : isHitC cn sls[r] = true)
    (h2 : ∀ k (hk : k < sls.length), k < r → isHitC cn sls[k] = false) :
    ((List.range sls.length).zip sls).find? p = some (r, sls[r]) := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by rw [hp]; exact h1, r, by simp; exact hr, by simp [List.getElem_zip], fun j hj => ?_⟩
  rw [hp]; simp only [List.getElem_zip, List.getElem_range]
  rw [h2 j (by omega) hj]; rfl

set_option maxHeartbeats 32000000 in
/-- **`classGenRule g _ _ _ 0 x`** for a constructor with ordinary fields of the one class. -/
theorem cgr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CGRCodes C)
    (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal) (rlvls : LsIdx)
    (x : ClassCtor) (oc : Nat) (hcc : CCRep C C.H oc x) (hnf : x.nF < 2 ^ 56)
    (opm : Nat) (hpm : BlkAt C.H opm (g.params.map Enc.idxW)) (hpml : g.params.length < 2 ^ 56)
    (os : Nat) (hsb : SlotBlk C C.H os g.slots) (hsl : g.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (opr : Nat) (hpr : BlkAt C.H opr (g.pre.map Enc.idxW)) (hprl : g.pre.length < 2 ^ 56) (hnP : g.nP < 2 ^ 56)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (cgrParams.zip [cellA C oc, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP,
        cellA C opm, cellA C os, cellA C opr])) (cgrBody C) s (classGenRule g recCls cvGs rlvls 0 x) (PostSomeH C) := by
  refine specR_prologue (postSomeH_locals _) (cgr_none _ _) ?_
  obtain ⟨⟨ocv, hocv, hcv⟩, hnfw, htd, htn, hkl, hko⟩ := hcc
  unfold classGenRule
  simp only [callsGo_ord g recCls cvGs rlvls x hko, pure_bind, List.append_nil]
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
  refine specR_callNIH (C := ctxH C H2) cgrD fPvg pvgParams [.const 0, vv cgrRp, vv cgrNp] (pvgBody C)
    [BitVec.ofNat 64 0, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP] (by decide) rfl (by decide) hc.pvg.self
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cgrParams, ctxEnv], trivial⟩
    (PostLs (ctxH C H2)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pvgParams _ rfl hlk)
      (by have h := pvg_spec (σ := σ) ra C hok hc.pvg g hpl g.pre.length (by omega) (by omega) g.pre.length 0 H2 s3 (by omega) (by omega) hpC2; simp only [List.drop_zero] at h; exact h))
    (fun pvars w s4 H3 hp3 _ => ?_)
  have hp3' : H2 <+: H3 := hp3
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
  refine ILP.callE_spec (C := ctxH C H3) cgrBd ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv cgrSv, vv cgrFv, .const 0, vv cgrLf] ExK.mkaBody
    [Enc.idxW sv, cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length] (by decide) rfl (by decide) hc.mka
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H3) hok3 hc.mka hc.app oa fvs (blkAt_mono hfb (hp2'.trans hp3')) (by omega) 0 (by omega) sv s6; simp only [List.drop_zero] at h; exact h)
    (fun body s7 => ?_)
  rw [mapM_binder_eq g fvs]
  refine specR_callNIH (C := ctxH C H3) cgrFb fFvtDs ftdParams [vv cgrFv] (ftdBody C) [cellA C oa] (by decide) rfl
    (by decide) hc.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H3)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
    (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
      (ftd_spec C hok hc.ftd hc.ftf hc.fvt fvs oa (by omega) H3 s7 (blkAt_mono hfb (hp2'.trans hp3'))))
    (fun fbs w s8 H4 hp4 ⟨o4, hw4, hb4⟩ => ?_)
  subst hw4
  have hp4' : H3 <+: H4 := hp4
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
  have hpC4 : C.H <+: H4 := hpC3.trans hp4'
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
