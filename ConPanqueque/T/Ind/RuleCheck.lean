import ConPanqueque.T.Ind.GenRule
import ConPanqueque.T.Ind.ClassConst
import ConPanqueque.T.Ind.BlockIsRec

/-!
# `classRuleCheck`

`draBody`: the λ-domains of a generated rule, each resolving and naming none of the pushed recursors (else a
hang).  `crcBody`: the rule closed, its level parameters the recursor's, resolving, typed (the flush leaving
the inference), and its λ-telescope's domains as above.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

section
variable {σ : Type}

/-- `if c then fail else K` against a hang on a nonzero condition. -/
theorem specR_hangIteT {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {c : Bool} {F K : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (cond : ExpHOL 64) (v : BitVec 64)
    (hv : sev Γ cond = some v) (hvt : c = true → v ≠ 0) (hvf : c = false → v = 0)
    (hk : c = false → SpecR (Inv C s Γ M D) rest s K R) :
    SpecR (Inv C s Γ M D) (.ite cond hang rest) s (if c = true then F else K) R := by
  cases c
  · rw [ite_eq_right (by decide)]; exact specR_ifI _ v hv (fun h => absurd (hvf rfl) h) (fun _ => hk rfl)
  · rw [ite_eq_left rfl]; exact specR_ifI _ v hv (fun _ => specR_hangI) (fun h => absurd h (hvt rfl))

/-- `if c then K else fail` against a hang on a nonzero condition. -/
theorem specR_hangIteF {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {c : Bool} {F K : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (cond : ExpHOL 64) (v : BitVec 64)
    (hv : sev Γ cond = some v) (hvt : c = true → v = 0) (hvf : c = false → v ≠ 0)
    (hk : c = true → SpecR (Inv C s Γ M D) rest s K R) :
    SpecR (Inv C s Γ M D) (.ite cond hang rest) s (if c = true then K else F) R := by
  cases c
  · rw [ite_eq_right (by decide)]; exact specR_ifI _ v hv (fun _ => specR_hangI) (fun h => absurd h (hvf rfl))
  · rw [ite_eq_left rfl]; exact specR_ifI _ v hv (fun h => absurd (hvt rfl) h) (fun _ => hk rfl)

end

/-! ## The domains -/

def draB := ofString "dra_b"
def draI := ofString "dra_i"
def draN := ofString "dra_n"
def draPn := ofString "dra_pn"
def draPl := ofString "dra_pl"
def draE := ofString "dra_e"
def draR := ofString "dra_r"
def draK := ofString "dra_k"
def draM := ofString "dra_m"
def draX := ofString "dra_x"
def fDra := ofString "ruleDomainsOk"

def draParams : List MlS := [draB, draI, draN, draPn, draPl]
def draLocals : List MlS := [draE, draR, draK, draM, draX]

def draBody (C : Ctx) : ProgHOL 64 := prologue draLocals
  (.ite (.cmp .lower (vv draI) (vv draN))
    (.seq (.assign .local draE (.load .one (.op .add [vv draB, .op .add [.panop .mul [vv draI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, draR), none)) fCrff [vv draE])
    (.ite (.cmp .equal (vv draR) (.const 0)) hang
    (.seq (.call (some (some (.local, draK), none)) WC.fMx
        [.const (BitVec.ofNat 64 coreWalkFuel), vv draPn, vv draPl, vv draE, .const 0])
    (.seq (.assign .local draM (.load .one (vv draK)))
    (.ite (.cmp .notEqual (vv draM) (.const 0)) hang
    (.seq (.call (some (some (.local, draX), none)) fDra
        [vv draB, .op .add [vv draI, .const 1], vv draN, vv draPn, vv draPl])
      (.return (.const 1)))))))))
    (.return (.const 1)))

structure DRACodes (C : Ctx) : Prop where
  crff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)
  crf : CrfCodes C
  mx : WC.MxCodes C
  self : C.code.lookup fDra = some (draParams.map (fun p => (p, ShapeHOL.one)), draBody C, .one)

section
variable {σ : Type}

theorem dra_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ draLocals → (ctxEnv C ++ draParams.zip vals).get x = none :=
  Knot.params_none C draLocals draParams vals (by decide) (by decide)

/-- A true answer, past the value heap. -/
def PostT (C : Ctx) (r : Bool) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  r = true ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postT_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostT C a w s' st → PostT C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, H', hp, hsr⟩ => ⟨h0, H', hp, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem allM_cons_ite {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (p : α → m Bool) (a : α) (l : List α) :
    (a :: l).allM p = p a >>= fun c => if c then l.allM p else pure false := by
  simp only [List.allM]
  congr 1; funext c; cases c <;> rfl

set_option maxHeartbeats 16000000 in
/-- **The rule's domains** from `i` on: each resolving at the context's environment, naming none of `names`. -/
theorem dra_spec (C : Ctx) (hok : CtxOK C) (hc : DRACodes C) (names : List NIdx) (pn : Nat)
    (hl : names.length < 2 ^ 59) (hns : Elems C.H pn names) (tys : List EIdx) (b : EIdx) (ob : Nat)
    (htl : tys.length < 2 ^ 61) :
    ∀ f i (H : List (BitVec 64)) (s : AState), tys.length - i = f → i ≤ tys.length → C.H <+: H →
      BlkAt H ob (tys.map Enc.idxW ++ [Enc.idxW b]) →
      SpecR (σ := σ) (Pre (ctxH C H) s (draParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 tys.length,
        cellA C pn, BitVec.ofNat 64 names.length])) (draBody C) s
        ((tys.drop i).allM fun b => do
          if ← constsResolveFFast C.fe b then pure !(← mentionsAnyConst names b) else pure false)
        (PostT (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp hb
    have hin : i = tys.length := by omega
    subst hin
    refine specR_prologue (postT_locals _) (dra_none _ _) ?_
    have hlw := nd_lt_iff tys.length tys.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, draParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp hb
    have hin : i < tys.length := by omega
    refine specR_prologue (postT_locals _) (dra_none _ _) ?_
    have hlw := nd_lt_iff i tys.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, draParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have he := hb.2 i (by simp; omega)
    rw [List.getElem_append_left (by simpa using hin), List.getElem_map] at he
    refine UD.specR_heapLoadI' (C := ctxH C H) draE _ (ob + 1 + i) _ he (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin, allM_cons_ite, bind_assoc]
    have hokH := ctxOK_H hok H
    refine specR_callNIH (C := ctxH C H) draR fCrff [crffE] [vv draE] crffBody [Enc.idxW tys[i]] (by decide) rfl
      (by decide) hc.crff ⟨by simp +decide [sev, Env.get_cons], trivial⟩ (PostB (ctxH C H)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
        (crff_spec (ctxH C H) hokH (by ctx_tr hc.crf) s tys[i]))
      (fun c w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases c
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_true, mentionsAnyConst, bind_assoc, pure_bind]
    refine specR_callNIH (C := ctxH C H1) draK WC.fMx WC.mxParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv draPn, vv draPl, vv draE, .const 0] (WC.mxBody C)
      [BitVec.ofNat 64 coreWalkFuel, cellA C pn, BitVec.ofNat 64 names.length, Enc.idxW tys[i], 0] (by decide) rfl
      (by decide) hc.mx.self
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (WC.PostLb (ctxH C H1) s1)
      (fun rm w s' H' => s' = s1 ∧ ∃ o pm', w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
        WC.LbRep C H' pm' rm.2)
      (fun rm w s' st ⟨h1, H', o, pm', hp', hw, h0, h1', hrep', hsr⟩ =>
        ⟨H', hp', ⟨h1, o, pm', hw, h0, h1', WC.lbRep_ofH hrep'⟩, by subst h1; exact hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu WC.mxParams _ rfl hlk)
        (WC.mx_spec C hok hc.mx names pn hl hns coreWalkFuel CV.coreWalkFuel_lt tys[i] ∅ H1 s1 0 (hp.trans hp1')
          (WC.lbRep_empty C H1)))
      (fun rm w s' H2 hp2 ⟨hs', o, pm', hw, h0, h1', hrep'⟩ => ?_)
    subst s'; subst hw
    have hp2' : H1 <+: H2 := hp2
    refine UD.specR_heapLoadI' (C := ctxH C H2) draM (vv draK) o (boolW rm.1) h0 (by decide) (by simp [Env.get]; rfl) ?_
    cases hr : rm.1
    · refine specR_ifI _ 0 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.not_false, ite_true]
      refine specR_congr (m' := ((tys.drop (i + 1)).allM fun b => do
          if ← constsResolveFFast C.fe b then pure !(← mentionsAnyConst names b) else pure false) >>= fun r => pure r)
        (by simp only [bind_pure, mentionsAnyConst, bind_assoc, pure_bind]) ?_
      refine specR_callNIH (C := ctxH C H2) draX fDra draParams
        [vv draB, .op .add [vv draI, .const 1], vv draN, vv draPn, vv draPl] (draBody C)
        [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 tys.length, cellA C pn, BitVec.ofNat 64 names.length]
        (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, draParams, ctxEnv], trivial⟩
        (PostT (ctxH C H2)) (fun r _ _ _ => r = true) (fun r w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu draParams _ rfl hlk)
          (ih (i + 1) H2 s1 (by omega) (by omega) (hp.trans (hp1'.trans hp2')) (blkAt_mono hb (hp1'.trans hp2'))))
        (fun r w s3 H3 hp3 hr3 => ?_)
      subst hr3
      exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H3, hp1'.trans (hp2'.trans hp3), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · exact specR_ifI _ 1 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))

end

/-! ## The check of one rule -/

def crcG := ofString "crc_g"
def crcL := ofString "crc_l"
def crcLn := ofString "crc_ln"
def crcN := ofString "crc_n"
def crcPn := ofString "crc_pn"
def crcPl := ofString "crc_pl"
def crcR := ofString "crc_r"
def crcX := ofString "crc_x"
def crcY := ofString "crc_y"
def crcK := ofString "crc_k"
def crcBl := ofString "crc_bl"
def fCrc := ofString "classRuleCheck"

def crcParams : List MlS := [crcG, crcL, crcLn, crcN, crcPn, crcPl]
def crcLocals : List MlS := [crcR, crcX, crcY, crcK, crcBl, lJ0]

def crcBody (C : Ctx) : ProgHOL 64 := prologue crcLocals
  (callR crcR ExM.fLBB [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv crcG]
  (.ite (.cmp .equal (vv crcR) (.const 0)) hang
  (callR crcR ExM.fHasFvar [.const (BitVec.ofNat 64 coreWalkFuel), vv crcG]
  (.ite (.cmp .notEqual (vv crcR) (.const 0)) hang
  (callR crcR fAt [vv crcG, vv crcL, vv crcLn]
  (.ite (.cmp .equal (vv crcR) (.const 0)) hang
  (callR crcR fCrff [vv crcG]
  (.ite (.cmp .equal (vv crcR) (.const 0)) hang
  (callR crcX fI [.const (BitVec.ofNat 64 checkFuel), .const 0, vv crcG]
  (flushCode C (flushRegions false)
  (callR crcY fStripLams [vv crcN, vv crcG]
  (.ite (.cmp .equal (vv crcY) (.const 0)) hang
  (.seq (.assign .local crcBl (.load .one (vv crcY)))
  (callR crcK fDra [vv crcY, .const 0, .op .sub [vv crcBl, .const 1], vv crcPn, vv crcPl]
  (.return (.const 0))))))))))))))))

structure CRCCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  lbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one)
  cB : ExB.CodesB C (ExB.bodyB C)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  hf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one)
  cF : ExF.CodesF C (ExF.bodyF C)
  fvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)
  atc : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)
  al : AlCodes C
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  strip : C.code.lookup fStripLams = some ([(pFu, .one), (pH, .one)], stripBody C fStripLams 5, .one)
  dra : DRACodes C
  self : C.code.lookup fCrc = some (crcParams.map (fun p => (p, ShapeHOL.one)), crcBody C, .one)

section
variable {σ : Type}

theorem crc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crcLocals → (ctxEnv C ++ crcParams.zip vals).get x = none :=
  Knot.params_none C crcLocals crcParams vals (by decide) (by decide)

set_option maxHeartbeats 32000000 in
/-- **`classRuleCheck`** at the context's environment. -/
theorem crc_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CRCCodes mode C)
    (feR : IFEnv) (hfe : feR = C.fe) (pushed : List NIdx) (pn : Nat) (hpsl : pushed.length < 2 ^ 59)
    (hpn : Elems C.H pn pushed) (cvR : IConstantVal) (o : Nat) (hb : BlkAt C.H o (cvR.levelParams.map Enc.idxW))
    (hlen : cvR.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = cvR.levelParams.length)
    (hks : ∀ j (hj : j < cvR.levelParams.length), denoteN C.St.ns cvR.levelParams[j] = some (ks[j]'(by omega)))
    (n : Nat) (hn : n < 2 ^ 62) (gen : EIdx) (s : AState) :
    SpecR (σ := σ) (Pre C s (crcParams.zip [Enc.idxW gen, cellA C o, BitVec.ofNat 64 cvR.levelParams.length,
        BitVec.ofNat 64 n, cellA C pn, BitVec.ofNat 64 pushed.length])) (crcBody C) s
      (classRuleCheck mode feR pushed cvR n gen) (Decl.PostU C) := by
  refine specR_prologue (Decl.postU_locals C) (crc_none C _) ?_
  unfold classRuleCheck
  dsimp only
  subst hfe
  refine specR_callNIH (C := ctxH C C.H) crcR ExM.fLBB [pFu, ExM.pKb, pH]
    [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv crcG] ExM.lbbBody
    [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 0, Enc.idxW gen] (by decide) rfl (by decide) hc.lbb
    ⟨rfl, rfl, (by simp +decide [Env.get, crcParams, ctxEnv]), trivial⟩ (ExM.PostB (ctxH C C.H)) (fun b w _ H' => H' = C.H ∧ w = boolW b)
    (fun b w s' st ⟨hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, ExM.pKb, pH] _ rfl hlk)
      (ExM.lbb_spec (ctxH C C.H) (ctxOK_H hok C.H) (by ctx_tr hc.cB) hc.bvb s coreWalkFuel 0 gen CV.coreWalkFuel_lt (by decide)))
    (fun b w s1 H1 hp1 ⟨eH1, hw⟩ => ?_)
  subst hw; subst H1
  refine specR_hangIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  try simp only [pure_bind]
  have hok0 := ctxOK_H hok C.H
  refine specR_callNIH (C := ctxH C C.H) crcR ExM.fHasFvar [pFu, pH]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv crcG] ExM.hasFvarBody
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW gen] (by decide) rfl (by decide) hc.hf
    ⟨rfl, (by simp +decide [Env.get, crcParams, ctxEnv]), trivial⟩ (ExM.PostB (ctxH C C.H)) (fun b w _ H' => H' = C.H ∧ w = boolW b)
    (fun b w s' st ⟨hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExM.hasFvar_spec (ctxH C C.H) hok0 (by ctx_tr hc.cF) hc.fvb s1 coreWalkFuel gen CV.coreWalkFuel_lt))
    (fun b w s2 H2 hp2 ⟨eH2, hw⟩ => ?_)
  subst hw; subst H2
  refine specR_hangIteT (c := b) _ (boolW b) (by simp +decide [sev, Env.get]; exact nez_b b)
    (boolW_ne _) (boolW_eq _) (fun _ => ?_)
  refine specR_atEntry fun t2 ht2 => ?_
  have hL : LpsAt (ctxH C C.H) s2 o cvR.levelParams ks :=
    ⟨hb, hkl, fun j hj => denoteN_ext (hks j hj) ht2.sr.floor, hlen⟩
  refine specR_callNIH (C := ctxH C C.H) crcR fAt atParams [vv crcG, vv crcL, vv crcLn] atBody
    [Enc.idxW gen, cellA C o, BitVec.ofNat 64 cvR.levelParams.length] (by decide) rfl (by decide) hc.atc
    ⟨(by simp +decide [Env.get, crcParams, ctxEnv]), (by simp +decide [Env.get, crcParams, ctxEnv]), by simp +decide [Env.get, crcParams, ctxEnv], trivial⟩ (PostB (ctxH C C.H)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu atParams _ rfl hlk)
      (at_spec (ctxH C C.H) hok0 (by ctx_tr hc.al) s2 gen hL))
    (fun b w s3 H3 hp3 hw => ?_)
  subst hw
  have hp3' : C.H <+: H3 := hp3
  refine specR_hangIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  try simp only [pure_bind]
  have hok3 := ctxOK_H hok H3
  refine specR_callNIH (C := ctxH C H3) crcR fCrff [crffE] [vv crcG] crffBody [Enc.idxW gen] (by decide) rfl
    (by decide) hc.dra.crff ⟨(by simp +decide [Env.get, crcParams, ctxEnv]), trivial⟩ (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
      (crff_spec (ctxH C H3) hok3 (by ctx_tr hc.dra.crf) s3 gen))
    (fun b w s4 H4 hp4 hw => ?_)
  subst hw
  have hp4' : H3 <+: H4 := hp4
  refine specR_hangIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  try simp only [pure_bind]
  have hpC4 : C.H <+: H4 := hp3'.trans hp4'
  have hok4 := ctxOK_H hok H4
  have hk4 := kcodes_H hc.k H4
  have hac4 := allCodes_H hc.ac H4
  refine Big.specR_callKC (C := ctxH C H4) crcX fI kParams [.const (BitVec.ofNat 64 checkFuel), .const 0, vv crcG]
    (inferE (ctxH C H4) fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW gen] (by decide) rfl
    (by decide) hk4.ei ⟨rfl, rfl, by simp +decide [sev, Env.get_cons, Env.get, crcParams, ctxEnv], trivial⟩
    (Comp.inferTop ra mode hok4 hk4 hac4 hs s4 0 (by decide) gen)
    (fun st s5 H5 hp5 _ => ?_)
  have hp5' : H4 <+: H5 := hp5
  have hpC5 : C.H <+: H5 := hpC4.trans hp5'
  refine specR_flushTopI (ctxOK_H hok H5) hpl false flushCaches rfl (by decide) ?_
  refine specR_callNIH (C := ctxH C H5) crcY fStripLams [pFu, pH] [vv crcN, vv crcG] (stripBody C fStripLams 5)
    [BitVec.ofNat 64 n, Enc.idxW gen] (by decide) rfl (by decide) hc.strip
    ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, crcParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, crcParams, ctxEnv], trivial⟩
    (PostSP (ctxH C H5)) (fun o w s' H' => (o = none → w = 0) ∧
      ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact stripLams_spec C hok hc.strip n (by omega) H5 (flushedS false s5) gen _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun o w s6 H6 hp6 ⟨hn0, hsm⟩ => ?_)
  have hp6' : H5 <+: H6 := hp6
  rcases o with _ | ⟨tys, bb⟩
  · have e0 := hn0 rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob', rfl, hblk⟩ := hsm tys bb rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hblk
  have hHN' : H6.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hne : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  have hl0 : (ctxH C H6).H[ob']? = some (BitVec.ofNat 64 (tys.length + 1)) := by
    show H6[ob']? = _; rw [hblk.1]; simp
  have htl : tys.length < 2 ^ 61 := by
    have := hblk.2 tys.length (by simp)
    have := (List.getElem?_eq_some_iff.mp this).1
    omega
  refine UD.specR_heapLoadI' (C := ctxH C H6) crcBl (vv crcY) ob' _ hl0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hsub : BitVec.ofNat 64 (tys.length + 1) - 1#64 = BitVec.ofNat 64 tys.length := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  refine specR_callNIH (C := ctxH C H6) crcK fDra draParams
    [vv crcY, .const 0, .op .sub [vv crcBl, .const 1], vv crcPn, vv crcPl] (draBody C)
    [cellA C ob', BitVec.ofNat 64 0, BitVec.ofNat 64 tys.length, cellA C pn, BitVec.ofNat 64 pushed.length]
    (by decide) rfl (by decide) hc.dra.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons]; exact hsub,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, crcParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, crcParams, ctxEnv], trivial⟩
    (PostT (ctxH C H6)) (fun r _ _ _ => r = true) (fun r w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu draParams _ rfl hlk)
      (by have h := dra_spec (σ := σ) C hok hc.dra pushed pn hpsl hpn tys bb ob' htl tys.length 0 H6 s6 (by omega) (by omega) (hpC5.trans hp6') hblk; simp only [List.drop_zero] at h; exact h))
    (fun r w s7 H7 hp7 hr => ?_)
  subst hr
  simp only [ite_true]
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H7, hpC5.trans (hp6'.trans hp7), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## A class's rules (`classRulesOk`, class `0`) -/

def crlCs := ofString "crl_cs"
def crlI := ofString "crl_i"
def crlK := ofString "crl_k"
def crlRp := ofString "crl_rp"
def crlNp := ofString "crl_np"
def crlPm := ofString "crl_pm"
def crlSl := ofString "crl_sl"
def crlPr := ofString "crl_pr"
def crlLp := ofString "crl_lp"
def crlLn := ofString "crl_ln"
def crlN0 := ofString "crl_n0"
def crlPn := ofString "crl_pn"
def crlPl := ofString "crl_pl"
def crlCc := ofString "crl_cc"
def crlLv := ofString "crl_lv"
def crlG := ofString "crl_g"
def crlNf := ofString "crl_nf"
def crlX := ofString "crl_x"
def fCrl := ofString "classRulesOk"

def crlParams : List MlS := [crlCs, crlI, crlK, crlRp, crlNp, crlPm, crlSl, crlPr, crlLp, crlLn, crlN0, crlPn, crlPl]
def crlLocals : List MlS := gaaLocals ++ [crlCc, crlLv, crlG, crlNf, crlX]

def crlBody (C : Ctx) : ProgHOL 64 := prologue crlLocals
  (.ite (.cmp .lower (vv crlI) (vv crlK))
    (.seq (.assign .local crlCc (.load .one (.op .add [vv crlCs, .op .add [.panop .mul [vv crlI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, crlLv), none)) fParamLevels [vv crlLp])
    (.seq (.call (some (some (.local, crlG), none)) fCgr [vv crlCc, vv crlRp, vv crlNp, vv crlPm, vv crlSl, vv crlPr])
    (.seq (.assign .local crlNf (.load .one (.op .add [vv crlCc, .const 8])))
    (.seq (.call (some (some (.local, crlX), none)) fCrc
        [vv crlG, vv crlLp, vv crlLn, .op .add [vv crlN0, vv crlNf], vv crlPn, vv crlPl])
    (.seq (.call (some (some (.local, ExS.lY), none)) fCrl
        [vv crlCs, .op .add [vv crlI, .const 1], vv crlK, vv crlRp, vv crlNp, vv crlPm, vv crlSl, vv crlPr, vv crlLp,
          vv crlLn, vv crlN0, vv crlPn, vv crlPl])
      (prependP C crlG)))))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure CRLCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  lp : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  cgr : CGRCodes C
  crc : CRCCodes mode C
  self : C.code.lookup fCrl = some (crlParams.map (fun p => (p, ShapeHOL.one)), crlBody C, .one)

section
variable {σ : Type}

theorem crl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crlLocals → (ctxEnv C ++ crlParams.zip vals).get x = none :=
  Knot.params_none C crlLocals crlParams vals (by decide) (by decide)

/-- A block of handles, past the value heap. -/
def PostRs (C : Ctx) (rs : List EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW) ∧ SR (ctxH C H') s' st

theorem postRs_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRs C a w s' st → PostRs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

set_option maxHeartbeats 32000000 in
/-- **`classRulesOk`** for the one class's constructors from `i` on, at the context's environment. -/
theorem crl_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CRLCodes mode C)
    (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (opm : Nat) (hpm : BlkAt C.H opm (g.params.map Enc.idxW)) (hpml : g.params.length < 2 ^ 56)
    (os : Nat) (hsb : SlotBlk C C.H os g.slots) (hsl : g.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (opr : Nat) (hpr : BlkAt C.H opr (g.pre.map Enc.idxW)) (hprl : g.pre.length < 2 ^ 56) (hnP : g.nP < 2 ^ 56)
    (pushed : List NIdx) (pn : Nat) (hpsl : pushed.length < 2 ^ 59)
    (cvR : IConstantVal) (o : Nat) (hb : BlkAt C.H o (cvR.levelParams.map Enc.idxW))
    (hlen : cvR.levelParams.length < 2 ^ 59) (ks : List ConLeche.Name) (hkl : ks.length = cvR.levelParams.length)
    (hks : ∀ j (hj : j < cvR.levelParams.length), denoteN C.St.ns cvR.levelParams[j] = some (ks[j]'(by omega)))
    (xs : List ClassCtor) (ocs : Nat) (hcs : PRep C C.H ocs (fun H o cc => CCRep C H o cc) xs)
    (hxl : xs.length < 2 ^ 58) (hnf : ∀ x ∈ xs, x.nF < 2 ^ 56) :
    ∀ f i (H : List (BitVec 64)) (s : AState), xs.length - i = f → i ≤ xs.length → C.H <+: H → Elems H pn pushed →
      SpecR (σ := σ) (Pre (ctxH C H) s (crlParams.zip [cellA C ocs, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length,
        BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr, cellA C o,
        BitVec.ofNat 64 cvR.levelParams.length, BitVec.ofNat 64 (g.nP + g.slots.length), cellA C pn,
        BitVec.ofNat 64 pushed.length])) (crlBody C) s
        (classRulesOk mode C.fe pushed g recCls cvGs cvR 0 (xs.drop i)) (PostRs (ctxH C H)) := by
  obtain ⟨oss, hossl, hossb, hossr⟩ := hcs
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp hpn
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postRs_locals _) (crl_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    simp only [classRulesOk]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp hpn
    have hin : i < xs.length := by omega
    refine specR_prologue (postRs_locals _) (crl_none _ _) ?_
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : i < oss.length := by omega
    have hpe := hossb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hcc := ccRep_mono hp (hossr i hin hio)
    refine UD.specR_heapLoadI' (C := ctxH C H) crlCc _ (ocs + 1 + i) _ (get_prefix hpe hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv]; exact cellA_mulIdx C ocs i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin]
    simp only [classRulesOk, classRuleOk, bind_assoc, pure_bind]
    refine specR_callNIH (C := ctxH C H) crlLv fParamLevels plParams [vv crlLp] (plBody C) [cellA C o] (by decide) rfl
      (by decide) hc.pl ⟨by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], trivial⟩
      (PostLsH (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', _, hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
        (pl_spec ra C hok hc.pl hc.pf hc.lp hc.ls cvR.levelParams o (by omega) H s (blkAt_mono hb hp)))
      (fun rlvls w s1 H1 hp1 _ => ?_)
    have hp1' : H <+: H1 := hp1
    have hpC1 : C.H <+: H1 := hp.trans hp1'
    have hcc1 := ccRep_mono hp1' hcc
    refine specR_callNIH (C := ctxH C H1) crlG fCgr cgrParams [vv crlCc, vv crlRp, vv crlNp, vv crlPm, vv crlSl, vv crlPr]
      (cgrBody C) [cellA C oss[i], BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr]
      (by decide) rfl (by decide) hc.cgr.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], trivial⟩
      (PostSomeH (ctxH C H1)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
      (fun o w s' st ⟨H', t, hp', ho, hw, hsr⟩ => ⟨H', hp', ⟨t, ho, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cgrParams _ rfl hlk)
        (cgr_spec ra (ctxH C H1) (ctxOK_H hok H1) (by ctx_tr hc.cgr) g recCls cvGs rlvls xs[i] oss[i] hcc1
          (hnf _ (List.getElem_mem hin)) opm (blkAt_mono hpm hpC1) hpml os (slotBlk_mono hpC1 hsb) hsl hcb opr
          (blkAt_mono hpr hpC1) hprl hnP s1))
      (fun og w s2 H2 hp2 ⟨gen, hog, hw⟩ => ?_)
    subst hog hw
    have hp2' : H1 <+: H2 := hp2
    have hpC2 : C.H <+: H2 := hpC1.trans hp2'
    simp only
    have hcc2 := ccRep_mono hp2' hcc1
    refine UD.specR_heapLoadI' (C := ctxH C H2) crlNf _ (oss[i] + 1) _ hcc2.2.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oss[i]) ?_
    have hnfi := hnf _ (List.getElem_mem hin)
    refine specR_callNIH (C := ctxH C H2) crlX fCrc crcParams
      [vv crlG, vv crlLp, vv crlLn, .op .add [vv crlN0, vv crlNf], vv crlPn, vv crlPl] (crcBody C)
      [Enc.idxW gen, cellA C o, BitVec.ofNat 64 cvR.levelParams.length, BitVec.ofNat 64 (g.nP + g.slots.length + xs[i].nF),
        cellA C pn, BitVec.ofNat 64 pushed.length] (by decide) rfl (by decide) hc.crc.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv]; simp only [BitVec.ofNat_add],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H2)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crcParams _ rfl hlk)
        (crc_spec mode ra (ctxH C H2) (ctxOK_H hok H2) hs hpl (by ctx_tr hc.crc) C.fe rfl pushed pn hpsl
          (fun j hj => get_prefix (hpn j hj) (hp1'.trans hp2')) cvR o (blkAt_mono hb hpC2) (by omega) ks hkl hks
          (g.nP + g.slots.length + xs[i].nF) (by omega) gen s2))
      (fun _ w s3 H3 hp3 _ => ?_)
    have hp3' : H2 <+: H3 := hp3
    refine specR_callNIH (C := ctxH C H3) ExS.lY fCrl crlParams
      [vv crlCs, .op .add [vv crlI, .const 1], vv crlK, vv crlRp, vv crlNp, vv crlPm, vv crlSl, vv crlPr, vv crlLp,
        vv crlLn, vv crlN0, vv crlPn, vv crlPl] (crlBody C)
      [cellA C ocs, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP,
        cellA C opm, cellA C os, cellA C opr, cellA C o, BitVec.ofNat 64 cvR.levelParams.length,
        BitVec.ofNat 64 (g.nP + g.slots.length), cellA C pn, BitVec.ofNat 64 pushed.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crlParams, ctxEnv], trivial⟩
      (PostRs (ctxH C H3)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
      (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crlParams _ rfl hlk)
        (ih (i + 1) H3 s3 (by omega) (by omega) (hpC2.trans hp3') (fun j hj => get_prefix (hpn j hj) (hp1'.trans (hp2'.trans hp3')))))
      (fun rs w s4 H4 hp4 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp4' : H3 <+: H4 := hp4
    refine ExPre.prepend_spec C hok (H := H4) crlG (Enc.idxW gen) oy (rs.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hry (by decide)
      (by simp +decide [Env.get_cons, Env.get, crlParams, ctxEnv]) (by decide) (fun H' o' t hp' hb' hsr => ?_)
    exact ⟨H', o', hp1'.trans (hp2'.trans (hp3'.trans (hp4'.trans hp'))), rfl, by simpa using hb', hsr⟩

end

end ConPanqueque.T.Ind
