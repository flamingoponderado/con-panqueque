import ConPanqueque.T.Ind.GenRecCheck
import ConPanqueque.T.Ind.ClassCtorRec
import ConPanqueque.T.Ind.LargeElim
import ConPanqueque.T.Ind.StreamRecsAll

/-!
# `genRecCheck`'s head (one member, one recursor, one class)

The recursor pins, the stream's recursor type checked, the elimination guard, the class's normal forms and
constructors, the minor-premise count, the elimination level; then `genRecB`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

theorem classCtorOf_nF {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {fts : List EIdx} {rd : ClassRead}
    {ms : List TargetMajor} {c : Nat} {ctor : IConstantVal × Nat} {s s' : AState} {x : ClassCtor}
    (h : classCtorOf mode fe p fts rd ms c ctor s = .ok (x, s')) : x.nF = ctor.2 := by
  unfold classCtorOf at h
  obtain ⟨m, s1, -, h⟩ := AM.bind_ok h
  dsimp only at h
  generalize List.filter _ m.nfs = es at h
  cases es with
  | nil => exact (AM.fail_ok h).elim
  | cons e0 es' =>
  dsimp only at h
  obtain ⟨q, s2, -, h⟩ := AM.bind_ok h
  obtain ⟨o, s3, -, h⟩ := AM.bind_ok h
  split at h
  · exact (AM.fail_ok h).elim
  obtain ⟨kinds, s4, -, h⟩ := AM.bind_ok h
  obtain ⟨_, s5, -, h⟩ := AM.bind_ok h
  obtain ⟨t0, s6, -, h⟩ := AM.bind_ok h
  obtain ⟨o2, s7, -, h⟩ := AM.bind_ok h
  split at h
  · exact (AM.fail_ok h).elim
  obtain ⟨rfl, -⟩ := AM.pure_ok h
  rfl

theorem classCtorsOf_nF {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {fts : List EIdx} {rd : ClassRead}
    {ms : List TargetMajor} {c : Nat} : ∀ (cs : List (IConstantVal × Nat)) {s s' : AState} {xs : List ClassCtor},
    classCtorsOf mode fe p fts rd ms c cs s = .ok (xs, s') → ∀ x ∈ xs, ∃ ct ∈ cs, x.nF = ct.2
  | [], s, s', xs, h => by
    simp only [classCtorsOf] at h
    obtain ⟨rfl, -⟩ := AM.pure_ok h
    intro x hx; cases hx
  | ct :: cs, s, s', xs, h => by
    simp only [classCtorsOf] at h
    obtain ⟨x0, s1, h1, h⟩ := AM.bind_ok h
    obtain ⟨xs', s2, h2, h⟩ := AM.bind_ok h
    obtain ⟨rfl, -⟩ := AM.pure_ok h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨ct, List.mem_cons_self .., classCtorOf_nF h1⟩
    · obtain ⟨c', hc', he⟩ := classCtorsOf_nF cs h2 x hx
      exact ⟨c', List.mem_cons_of_mem _ hc', he⟩

theorem classCtorsOf_len {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {fts : List EIdx} {rd : ClassRead}
    {ms : List TargetMajor} {c : Nat} : ∀ (cs : List (IConstantVal × Nat)) {s s' : AState} {xs : List ClassCtor},
    classCtorsOf mode fe p fts rd ms c cs s = .ok (xs, s') → xs.length = cs.length
  | [], s, s', xs, h => by
    simp only [classCtorsOf] at h
    obtain ⟨rfl, -⟩ := AM.pure_ok h
    rfl
  | ct :: cs, s, s', xs, h => by
    simp only [classCtorsOf] at h
    obtain ⟨x0, s1, h1, h⟩ := AM.bind_ok h
    obtain ⟨xs', s2, h2, h⟩ := AM.bind_ok h
    obtain ⟨rfl, -⟩ := AM.pure_ok h
    simp [classCtorsOf_len cs h2]

theorem postGR_H {m0 : TargetMajor} {C : Ctx} {H : List (BitVec 64)} (hp : C.H <+: H) :
    ∀ a w s' (st : PState σ), PostGR m0 (ctxH C H) a w s' st → PostGR m0 C a w s' st := by
  intro a w s' st ⟨EH, envM, H', o, h1, h2, h3, h4, h5⟩
  exact ⟨EH, envM, H', o, h1, hp.trans h2, h3, h4, h5⟩

/-! ## The minor premises counted -/

def cmcS := ofString "cmc_s"
def cmcI := ofString "cmc_i"
def cmcN := ofString "cmc_n"
def cmcP := ofString "cmc_p"
def cmcTg := ofString "cmc_tg"
def cmcR := ofString "cmc_r"
def fCmc := ofString "minorCount"

def cmcParams : List MlS := [cmcS, cmcI, cmcN]
def cmcLocals : List MlS := [cmcP, cmcTg, cmcR]

def cmcBody : ProgHOL 64 := prologue cmcLocals
  (.ite (.cmp .lower (vv cmcI) (vv cmcN))
    (.seq (.assign .local cmcP (.load .one (.op .add [vv cmcS, .op .add [.panop .mul [vv cmcI, .const 8], .const 8]])))
    (.seq (.assign .local cmcTg (.load .one (vv cmcP)))
    (.seq (.call (some (some (.local, cmcR), none)) fCmc [vv cmcS, .op .add [vv cmcI, .const 1], vv cmcN])
    (.ite (.cmp .equal (vv cmcTg) (.const 1)) (.return (.op .add [vv cmcR, .const 1])) (.return (vv cmcR))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem cmc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cmcLocals → (ctxEnv C ++ cmcParams.zip vals).get x = none :=
  Knot.params_none C cmcLocals cmcParams vals (by decide) (by decide)

def PostCMC (C : Ctx) (s : AState) (r : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = BitVec.ofNat 64 r ∧ SR C s' st

set_option maxHeartbeats 16000000 in
theorem cmc_spec (C : Ctx) (hc : C.code.lookup fCmc = some (cmcParams.map (fun p => (p, ShapeHOL.one)), cmcBody, .one))
    (sls : List ClassSlot) (os : Nat) (hsl : sls.length < 2 ^ 58) (H : List (BitVec 64))
    (hsb : SlotBlk C H os sls) :
    ∀ f i (s : AState), sls.length - i = f → i ≤ sls.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cmcParams.zip [cellA C os, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length]))
        cmcBody s (pure ((sls.drop i).filter ClassSlot.isMinor).length) (PostCMC (ctxH C H) s) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hsb
  have hpost : ∀ (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostCMC (ctxH C H) s a w s' st → PostCMC (ctxH C H) s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ ⟨h0, h1, h2⟩ => ⟨h0, h1, sr_of_eq h2 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (hpost s) (cmc_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cmcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < sls.length := by omega
    refine specR_prologue (hpost s) (cmc_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cmcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hsr⟩ := hpsr i hin
    have hio : i < ps.length := by omega
    have hpe := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hpi : ps[i] = op := by simpa [List.getElem?_eq_getElem hio] using hop
    rw [hpi] at hpe
    refine UD.specR_heapLoadI' (C := ctxH C H) cmcP _ (os + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cmcParams, ctxEnv]; exact cellA_mulIdx C os i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin]
    have hcall : ∀ (Γ : Env), Γ.get cmcS = some (cellA C os) → Γ.get cmcI = some (BitVec.ofNat 64 i) →
        Γ.get cmcN = some (BitVec.ofNat 64 sls.length) → ∀ (k : Nat → Nat) (rest : ProgHOL 64),
        (∀ r, SpecR (σ := σ) (Inv (ctxH C H) s ((cmcR, BitVec.ofNat 64 r) :: Γ) [] (ctxLocals ++ cmcLocals)) rest s
          (pure (k r)) (PostCMC (ctxH C H) s)) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ cmcLocals))
          (.seq (.call (some (some (.local, cmcR), none)) fCmc [vv cmcS, .op .add [vv cmcI, .const 1], vv cmcN]) rest) s
          ((pure ((sls.drop (i + 1)).filter ClassSlot.isMinor).length : AM Nat) >>= fun r => pure (k r))
          (PostCMC (ctxH C H) s) := by
      intro Γ gS gI gN k rest hk
      exact specR_callNIH (C := ctxH C H) cmcR fCmc cmcParams [vv cmcS, .op .add [vv cmcI, .const 1], vv cmcN]
        cmcBody [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length] (by decide) rfl (by decide) hc
        ⟨by simp [sev, gS], by simp [sev, sev_vv, gI]; exact word_add1_eq i, by simp [sev, gN], trivial⟩
        (PostCMC (ctxH C H) s) (fun r w s' H' => H' = H ∧ s' = s ∧ w = BitVec.ofNat 64 r)
        (fun r w s' st ⟨h0, h1, h2⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, h1⟩, h2⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmcParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun r w s3 H3 hp3 ⟨eH, es, hw⟩ => by subst eH es hw; exact hk r)
    generalize hsl' : sls[i] = sl at hsr
    cases sl with
    | motive k =>
      refine UD.specR_heapLoadI' (C := ctxH C H) cmcTg (vv cmcP) op _ hsr.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_congr (m' := (pure ((sls.drop (i + 1)).filter ClassSlot.isMinor).length : AM Nat) >>= fun r =>
        pure (id r)) (by simp [List.filter_cons, ClassSlot.isMinor]) ?_
      refine hcall _ (by simp +decide [Env.get_cons, Env.get, cmcParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cmcParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, cmcParams, ctxEnv]) id _ (fun r => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ (BitVec.ofNat 64 r) (by simp [sev, Env.get_cons])
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | minor c C' ihs =>
      refine UD.specR_heapLoadI' (C := ctxH C H) cmcTg (vv cmcP) op _ hsr.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_congr (m' := (pure ((sls.drop (i + 1)).filter ClassSlot.isMinor).length : AM Nat) >>= fun r =>
        pure (r + 1)) (by simp [List.filter_cons, ClassSlot.isMinor]) ?_
      refine hcall _ (by simp +decide [Env.get_cons, Env.get, cmcParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cmcParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, cmcParams, ctxEnv]) (· + 1) _ (fun r => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (BitVec.ofNat 64 (r + 1)) (by simp [sev, Env.get_cons]; exact word_add1_eq r)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The elimination guard and the elimination level -/

def lgdL := ofString "lgd_l"
def lgdR := ofString "lgd_r"
def lgdN := ofString "lgd_n"
def lgdX := ofString "lgd_x"
def lgdK := ofString "lgd_k"
def fLgd := ofString "largeGuard"

def lgdParams : List MlS := [lgdL, lgdR, lgdN, lgdK]
def lgdLocals : List MlS := [lgdX]

def lgdBody : ProgHOL 64 := prologue lgdLocals
  (.ite (.cmp .notEqual (vv lgdL) (.const 0))
    (.seq (.call (some (some (.local, lgdX), none)) fLea [vv lgdR, vv lgdN, vv lgdK]) (.return (.const 0)))
    (.return (.const 0)))

def elvL := ofString "elv_l"
def elvE := ofString "elv_e"
def elvX := ofString "elv_x"
def fElv := ofString "elimLevel"

def elvParams : List MlS := [elvL, elvE]
def elvLocals : List MlS := [elvX]

def elvBody : ProgHOL 64 := prologue elvLocals
  (.ite (.cmp .notEqual (vv elvL) (.const 0))
    (.seq (.call (some (some (.local, elvX), none)) fInternLParam [vv elvE]) (.return (vv elvX)))
    (.seq (.call (some (some (.local, elvX), none)) fInternLZero []) (.return (vv elvX))))

section
variable {σ : Type}

theorem lgd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lgdLocals → (ctxEnv C ++ lgdParams.zip vals).get x = none :=
  Knot.params_none C lgdLocals lgdParams vals (by decide) (by decide)

theorem elv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ elvLocals → (ctxEnv C ++ elvParams.zip vals).get x = none :=
  Knot.params_none C elvLocals elvParams vals (by decide) (by decide)

/-- **The elimination guard** of an unnested block of any member count. -/
theorem lgd_spec (C : Ctx) (hcz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one))
    (hcl : C.code.lookup fLea = some (leaParams.map (fun p => (p, ShapeHOL.one)), leaBody, .one))
    (p : BlockShape) (hkb : p.k < 2 ^ 63) (lsr : ConLeche.Level)
    (hSd : denoteL C.St.ls p.resSort = some lsr) (hnc : p.numCtors < 2 ^ 63) (X : CheckError) (s : AState) :
    SpecR (σ := σ) (Pre C s (lgdParams.zip [boolW p.large, Enc.idxW p.resSort, BitVec.ofNat 64 p.numCtors,
        BitVec.ofNat 64 p.k])) lgdBody s
      (if p.large then (blockLargeElimAllowed p false >>= fun b => if b then pure () else fail X) else pure ())
      (Decl.PostU C) := by
  refine specR_prologue (Decl.postU_locals C) (lgd_none C _) ?_
  cases hl : p.large
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lgdParams, ctxEnv, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, lgdParams, ctxEnv, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [ite_true]
  refine specR_congr (m' := (blockLargeElimAllowed p false >>= fun b => if b then pure () else fail X) >>= fun r => pure r)
    (by simp only [bind_pure]) ?_
  refine specR_callNIH (C := C) lgdX fLea leaParams [vv lgdR, vv lgdN, vv lgdK] leaBody
    [Enc.idxW p.resSort, BitVec.ofNat 64 p.numCtors, BitVec.ofNat 64 p.k] (by decide) rfl (by decide) hcl
    ⟨by simp +decide [sev, Env.get, lgdParams, ctxEnv], by simp +decide [sev, Env.get, lgdParams, ctxEnv],
      by simp +decide [sev, Env.get, lgdParams, ctxEnv], trivial⟩
    (Decl.PostU C) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu leaParams _ rfl hlk)
      (lea_spec C hcz p hl hkb lsr hSd hnc X s))
    (fun _ w s1 H1 hp1 _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **The elimination level** (`structElimLevel`). -/
theorem elv_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (hcZ : C.code.lookup fInternLZero = some ([], internLZeroBody, .one))
    (el : NIdx) (lg : Bool) (s : AState) :
    SpecR (σ := σ) (Pre C s (elvParams.zip [boolW lg, Enc.idxW el])) elvBody s (structElimLevel el lg)
      (PostL C) := by
  refine specR_prologue (postL_locals C) (elv_none C _) ?_
  unfold structElimLevel
  cases lg
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, elvParams, ctxEnv, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ite_false]
    refine specR_congr (m' := internLNode .zero >>= pure) (by simp) ?_
    refine callLN (C := C) elvX fInternLZero [] [] internLZeroBody [] (by decide) rfl (by decide) hcZ trivial
      .zero (internLZero_body_spec ra C hok s) (fun h s2 hr => ?_)
    exact specR_returnI _ (Enc.idxW h) (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, elvParams, ctxEnv, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [ite_true]
    refine specR_congr (m' := internLNode (.param el) >>= pure) (by simp) ?_
    refine callLN (C := C) elvX fInternLParam [lEn] [vv elvE] internLParamBody [Enc.idxW el] (by decide) rfl (by decide)
      hcP ⟨by simp +decide [sev, Env.get, elvParams, ctxEnv], trivial⟩
      (.param el) (internLParam_body_spec ra C hok s el) (fun h s2 hr => ?_)
    exact specR_returnI _ (Enc.idxW h) (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The head -/

def genRecA (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (params : List EIdx) (tbl : List NestCtorNf)
    (rd : ClassRead) (cls : List TargetMajor) (block : List IConstantInfo) :
    AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) := do
  targetRecPins p block
  let cvRis ← classStreamRecs mode fe p.recs
  (if p.large then (blockLargeElimAllowed p false >>= fun b => if b then pure () else
    fail (.invalid "generated recursor: large eliminator on a block whose sort may be Prop (official: elim_only_at_universe_zero)"))
    else pure ())
  let ms2 ← classesNfs mode fe p (p.formers.map (·.type)) tbl cls
  let ctors ← classesCtors mode fe p (p.formers.map (·.type)) rd ms2 0 ms2
  (if ((rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum) = true then pure () else
    fail (.invalid "generated recursor: the recursors' prefix has a minor premise for no constructor of a class (official: invalid recursor)"))
  let formerTysC ← ms2.mapM (classFormerTy mode fe p.formers)
  let elim ← structElimLevel p.elim p.large
  genRecB mode fe p ⟨p.nP, params, ms2, formerTysC, rd.slots, ctors, elim, []⟩ cvRis rd.recCls

/-- `genRecA` up to the generator's record (the generator and the stream's checked recursor types). -/
def gaPre (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (params : List EIdx) (tbl : List NestCtorNf)
    (rd : ClassRead) (m : TargetMajor) (block : List IConstantInfo) : AM (ClassGen × List IConstantVal) := do
  targetRecPins p block
  let cvRis ← classStreamRecs mode fe p.recs
  (if p.large then (blockLargeElimAllowed p false >>= fun b => if b then pure () else
    fail (.invalid "generated recursor: large eliminator on a block whose sort may be Prop (official: elim_only_at_universe_zero)"))
    else pure ())
  let ms2 ← classesNfs mode fe p (p.formers.map (·.type)) tbl [m]
  let ctors ← classesCtors mode fe p (p.formers.map (·.type)) rd ms2 0 ms2
  (if ((rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum) = true then pure () else
    fail (.invalid "generated recursor: the recursors' prefix has a minor premise for no constructor of a class (official: invalid recursor)"))
  let formerTysC ← ms2.mapM (classFormerTy mode fe p.formers)
  let elim ← structElimLevel p.elim p.large
  pure (⟨p.nP, params, ms2, formerTysC, rd.slots, ctors, elim, []⟩, cvRis)

/-- `genRecCheck` of an unnested block with at least one member, every class at a member. -/
theorem genRecCheck_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (params : List EIdx)
    (tbl : List NestCtorNf) (rd : ClassRead) (cls : List TargetMajor) (block : List IConstantInfo)
    (hk : p.k ≠ 0) (hmm : ∀ m ∈ cls, m.member.isSome = true) :
    genRecCheck mode fe p false params tbl rd cls block = genRecA mode fe p params tbl rd cls block := by
  have hk0 : (p.k == 0) = false := by simp [hk]
  have hnb : (false || cls.any fun x => x.member.isNone) = false := by
    simp only [Bool.false_or, List.any_eq_false, Option.isNone_iff_eq_none]
    intro x hx he; have := hmm x hx; rw [he] at this; exact absurd this (by decide)
  unfold genRecCheck genRecA genRecB genRules
  simp only [hk0, hnb, Bool.false_eq_true, ite_false, pure_bind]
  congr 1; funext _; congr 1; funext cvRis
  cases p.large
  · simp only [Bool.false_eq_true, ite_false, pure_bind]
    congr 1; funext ms2; congr 1; funext ctors
    split <;> rfl
  · simp only [ite_true, bind_assoc]
    congr 1; funext b
    split
    · simp only [pure_bind]
      congr 1; funext ms2; congr 1; funext ctors
      split <;> rfl
    · rfl


def gaSh := ofString "ga_sh"
def gaOrr := ofString "ga_orr"
def gaPm := ofString "ga_pm"
def gaOt := ofString "ga_ot"
def gaNt := ofString "ga_nt"
def gaOq := ofString "ga_oq"
def gaNq := ofString "ga_nq"
def gaLv := ofString "ga_lv"
def gaOlp := ofString "ga_olp"
def gaTy0 := ofString "ga_ty0"
def gaPp := ofString "ga_pp"
def gaNpp := ofString "ga_npp"
def gaPa := ofString "ga_pa"
def gaNd := ofString "ga_nd"
def gaNm := ofString "ga_nm"
def gaOsl := ofString "ga_osl"
def gaNsl := ofString "ga_nsl"
def gaOm := ofString "ga_om"
def gaNc := ofString "ga_nc"
def gaNi := ofString "ga_ni"
def gaInd := ofString "ga_ind"
def gaNpc := ofString "ga_npc"
def gaX := ofString "ga_x"
def gaQ := ofString "ga_q"
def gaLg := ofString "ga_lg"
def gaRsrt := ofString "ga_rsrt"
def gaNp := ofString "ga_np"
def gaNk := ofString "ga_nk"
def gaCs := ofString "ga_cs"
def gaNcs := ofString "ga_ncs"
def gaMc := ofString "ga_mc"
def gaEl := ofString "ga_el"
def gaEv := ofString "ga_ev"
def gaRs := ofString "ga_rs"
def gaK := ofString "ga_k"
def gaOrl := ofString "ga_orl"
def gaNrl := ofString "ga_nrl"
def gaOms := ofString "ga_oms"
def gaNcl := ofString "ga_ncl"
def gaCss := ofString "ga_css"
def gaSum := ofString "ga_sum"
def gaFts := ofString "ga_fts"
def gaOrc := ofString "ga_orc"
def fGa := ofString "genRecCheck"

def gaParams : List MlS := [gaSh, gaOrr, gaPm, gaOt, gaNt, gaOq, gaNq, gaLv, gaOlp, gaTy0, gaPp, gaNpp, gaPa, gaNd, gaNm, gaOsl, gaNsl, gaOm, gaNc, gaNi, gaInd, gaNpc, gaOms, gaNcl, gaOrc]
def gaLocals : List MlS := [gaX, gaQ, gaLg, gaRsrt, gaNp, gaNk, gaCs, gaNcs, gaMc, gaEl, gaEv, gaRs, gaK, gaOrl, gaNrl,
  gaCss, gaSum, gaFts]

def gaBody (C : Ctx) : ProgHOL 64 := prologue gaLocals
  (.seq (.call (some (some (.local, gaX), none)) fTrp [vv gaSh])
  (.seq (.assign .local gaOrl (.load .one (.op .add [vv gaSh, .const 8])))
  (.seq (.assign .local gaNrl (.load .one (vv gaOrl)))
  (.seq (.call (some (some (.local, gaX), none)) fCsr [vv gaOrl, .const 0, vv gaNrl])
  (.seq (.assign .local gaLg (.load .one (.op .add [vv gaSh, .const 40])))
  (.seq (.assign .local gaRsrt (.load .one (.op .add [vv gaSh, .const 32])))
  (.seq (.assign .local gaK (.load .one (vv gaOm)))
  (.seq (.call (some (some (.local, gaX), none)) fLgd [vv gaLg, vv gaRsrt, vv gaNc, vv gaK])
  (.seq (.call (some (some (.local, gaX), none)) fCns [vv gaOms, .const 0, vv gaNcl, vv gaOt, vv gaNt, vv gaOlp, vv gaOm, vv gaPp, vv gaNpp])
  (.seq (.assign .local gaNp (.load .one (.op .add [vv gaSh, .const 16])))
  (.seq (.assign .local gaNk (.op .add [vv gaNp, vv gaK]))
  (.seq (.call (some (some (.local, gaCss), none)) fCcs [vv gaOms, .const 0, vv gaNcl, vv gaOt, vv gaNt, vv gaOsl, vv gaNsl,
      vv gaNk, vv gaOm, vv gaOlp, vv gaTy0, vv gaPp, vv gaNpp, vv gaNm])
  (.seq (.call (some (some (.local, gaSum), none)) fSll [vv gaCss, .const 0, vv gaNcl, .const 0])
  (.seq (.call (some (some (.local, gaMc), none)) fCmc [vv gaOsl, .const 0, vv gaNsl])
  (.ite (.cmp .equal (vv gaMc) (vv gaSum))
  (.seq (.assign .local gaCs (.load .one (.op .add [vv gaCss, .const 8])))
  (.seq (.assign .local gaNcs (.load .one (vv gaCs)))
  (.seq (.assign .local gaEl (.load .one (.op .add [vv gaSh, .const 24])))
  (.seq (.call (some (some (.local, gaEv), none)) fElv [vv gaLg, vv gaEl])
  (alloc2 C gaFts (.const 1) (vv gaTy0)
  (.seq (.call (some (some (.local, gaRs), none)) fGb [vv gaPm, vv gaOsl, vv gaNsl, vv gaNp, vv gaCs, vv gaNcs, vv gaNi,
      vv gaEv, vv gaOrr, vv gaOms, vv gaCss, vv gaFts, vv gaOrl, vv gaOrc])
  (.return (vv gaRs))))))))
  hang)))))))))))))))

structure GACodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  trp : TRPCodes C
  trpS : C.code.lookup fTrp = some (trpParams.map (fun p => (p, ShapeHOL.one)), trpBody C, .one)
  gcc : GCCCodes C
  ccv : C.code.lookup fCcv = some (ccvParams.map (fun p => (p, ShapeHOL.one)), ccvBody C, .one)
  csr : C.code.lookup fCsr = some (csrParams.map (fun p => (p, ShapeHOL.one)), csrBody C, .one)
  nz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)
  lea : C.code.lookup fLea = some (leaParams.map (fun p => (p, ShapeHOL.one)), leaBody, .one)
  lgd : C.code.lookup fLgd = some (lgdParams.map (fun p => (p, ShapeHOL.one)), lgdBody, .one)
  cns : CNSCodes mode C
  ccs : CCSCodes mode C
  sll : C.code.lookup fSll = some (sllParams.map (fun p => (p, ShapeHOL.one)), sllBody, .one)
  cmc : C.code.lookup fCmc = some (cmcParams.map (fun p => (p, ShapeHOL.one)), cmcBody, .one)
  lp : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  lz : C.code.lookup fInternLZero = some ([], internLZeroBody, .one)
  elv : C.code.lookup fElv = some (elvParams.map (fun p => (p, ShapeHOL.one)), elvBody, .one)
  gb : GBCodes mode C
  self : C.code.lookup fGa = some (gaParams.map (fun p => (p, ShapeHOL.one)), gaBody C, .one)

section
variable {σ : Type}

theorem ga_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gaLocals → (ctxEnv C ++ gaParams.zip vals).get x = none :=
  Knot.params_none C gaLocals gaParams vals (by decide) (by decide)

/-- `classesCtors` over one class is that class's `classCtorsOf`. -/
theorem classesCtors_one {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {fts : List EIdx} {rd : ClassRead}
    {m : TargetMajor} {s s' : AState} {xss : List (List ClassCtor)}
    (h : classesCtors mode fe p fts rd [m] 0 [m] s = .ok (xss, s')) :
    ∃ xs, classCtorsOf mode fe p fts rd [m] 0 m.ctors s = .ok (xs, s') ∧ xss = [xs] := by
  simp only [classesCtors] at h
  obtain ⟨xs, s1, h1, h⟩ := AM.bind_ok h
  obtain ⟨xss', s2, h2, h⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  exact ⟨xs, h1, rfl⟩

set_option maxHeartbeats 64000000 in
/-- **`genRecCheck`**, one member, one recursor, one class (no nesting). -/
theorem ga_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : GACodes mode C) (hf : ConPanqueque.Front.FrontOK C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (p : BlockShape) (ms0 : MemberShape) (hms : p.members = [ms0]) (block : List IConstantInfo)
    (hsp : SplitOK p block) (osh : Nat) (hsh : ShapeRep C C.H osh p)
    (hlq : ms0.cvT.levelParams.length < 2 ^ 58) (hlr : ∀ rc ∈ p.recs, rc.cvR.levelParams.length < 2 ^ 59)
    (rc : RecShape) (hrecs : p.recs = [rc]) (orr : Nat) (hrr : RecRep C C.H orr rc)
    (ks : List ConLeche.Name) (hkl : ks.length = rc.cvR.levelParams.length)
    (hks : ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (ks[j]'(by omega)))
    (lsr : ConLeche.Level) (hSd : denoteL C.St.ls p.resSort = some lsr) (hnc : p.numCtors < 2 ^ 63)
    (params : List EIdx) (opm : Nat) (hpm : BlkAt C.H opm (params.map Enc.idxW)) (hpml : params.length < 2 ^ 56)
    (tbl : List NestCtorNf) (ot : Nat) (htb : PRep C C.H ot (fun H o nf => NfRep C H o nf) tbl)
    (htl : tbl.length < 2 ^ 58) (hel : ∀ e ∈ tbl, e.ds.length < 2 ^ 61)
    (m : TargetMajor) (hmm : m.member = some 0) (oq : Nat) (hcr : CtorsRep C C.H oq m.ctors)
    (hcsl : m.ctors.length < 2 ^ 58) (hnfc : ∀ c ∈ m.ctors, c.2 < 2 ^ 56)
    (olp : Nat) (hlp : EBlk C.H olp (ms0.cvT.levelParams.map Enc.idxW)) (pp : Nat)
    (hpf : BlkAt C.H pp (m.pfvs.map Enc.idxW)) (hppl : m.pfvs.length < 2 ^ 58) (pa : Nat)
    (hA : BlkAt C.H pa (m.ds.map Enc.idxW)) (hdl : m.ds.length < 2 ^ 56)
    (rd : ClassRead) (osl : Nat) (hsb : SlotBlk C C.H osl rd.slots) (hsl : rd.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ rd.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63) (k0 : ClassKey)
    (hsl0 : rd.slots[0]? = some (.motive k0))
    (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members) (hnk : p.nP + p.k < 2 ^ 56)
    (hni : m.nIdx < 2 ^ 56) (hnpc : m.nPc < 2 ^ 62)
    (hrc0 : rd.recCls = [0]) (orc : Nat) (hRC : BlkAt C.H orc (rd.recCls.map (BitVec.ofNat 64)))
    (oms : Nat) (hT : TMBlk C C.H oms m.pfvs [m]) (s : AState) (hpins : s.pins = C.pins)
    (hcvd : ∀ (g0 : ClassGen) (cvRis : List IConstantVal) (s7 : AState) (pre : List EIdx) s1 s' cv,
      gaPre mode C.fe p params tbl rd m block s = .ok ((g0, cvRis), s7) → g0.prefixBinders s7 = .ok (some pre, s1) →
      classRecTyOk mode C.fe { g0 with pre := pre } p.k rc rc.cvR 0 s1 = .ok (cv, s') →
      (denoteE s'.store cv.type).isSome = true) :
    SpecR (σ := σ) (Pre C s (gaParams.zip [cellA C osh, cellA C orr, cellA C opm, cellA C ot,
        BitVec.ofNat 64 tbl.length, cellA C oq, BitVec.ofNat 64 m.ctors.length, Enc.idxW m.lvls, cellA C olp,
        Enc.idxW ms0.cvT.type, cellA C pp, BitVec.ofNat 64 m.pfvs.length, cellA C pa, BitVec.ofNat 64 m.ds.length,
        Enc.idxW ms0.cvT.name, cellA C osl, BitVec.ofNat 64 rd.slots.length, cellA C om, BitVec.ofNat 64 p.numCtors,
        BitVec.ofNat 64 m.nIdx, Enc.idxW m.ind, BitVec.ofNat 64 m.nPc, cellA C oms, BitVec.ofNat 64 1, cellA C orc])) (gaBody C) s
      (genRecCheck mode C.fe p false params tbl rd [m] block) (PostGR { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) } C) := by
  refine specR_prologue (postGR_locals _ C) (ga_none C _) ?_
  have hk : p.k ≠ 0 := by simp [BlockShape.k, hms]
  rw [genRecCheck_eq mode C.fe p params tbl rd [m] block hk (by simp [hmm])]
  unfold genRecA
  refine specR_callNIH (C := C) gaX fTrp trpParams [vv gaSh] (trpBody C) [cellA C osh] (by decide) rfl (by decide) hc.trpS
    ⟨by simp +decide [sev, Env.get, gaParams, ctxEnv], trivial⟩
    (fun a w s' st => targetRecPins p block s = .ok (a, s') ∧ Decl.PostU C a w s' st)
    (fun a _ s' _ => targetRecPins p block s = .ok (a, s'))
    (fun a w s' st ⟨hr, H', hp', hsr⟩ => ⟨H', hp', hr, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu trpParams _ rfl hlk)
      (trp_spec ra C hok hf hc.trp p ms0 hms block hsp osh hsh hlq hlr s hpins)))
    (fun _ w s1 H1 hp1 htrp => ?_)
  have hp1' : C.H <+: H1 := hp1
  have hrr0 := hrr
  obtain ⟨orl, horl, hRl⟩ := hsh.2.1
  refine UD.specR_heapLoadI' (C := ctxH C H1) gaOrl _ (osh + 1) _ (get_prefix horl hp1') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv]; exact cellA_add_ofNat C osh 1) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) gaNrl (vv gaOrl) orl _ (get_prefix hRl.1 hp1') (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  have hrl : rc.cvR.levelParams.length < 2 ^ 59 := hlr rc (by rw [hrecs]; exact List.mem_cons_self ..)
  have hcsrC : CSRCodes mode C :=
    ⟨hc.gcc, hc.trp.pim, hc.gb.crs.cro.k, hc.gb.crs.cro.ac, hc.ccv, hc.csr⟩
  refine specR_callNIH (C := ctxH C H1) gaX fCsr csrParams [vv gaOrl, .const 0, vv gaNrl] (csrBody C)
    [cellA C orl, BitVec.ofNat 64 0, BitVec.ofNat 64 p.recs.length] (by decide) rfl (by decide) hc.csr
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => classStreamRecs mode C.fe p.recs s1 = .ok (a, s') ∧
      PostCSR (ctxH C H1) (p.recs.map (·.cvR)) a w s' st)
    (fun a _ s' _ => classStreamRecs mode C.fe p.recs s1 = .ok (a, s') ∧ a = p.recs.map (·.cvR))
    (fun a w s' st ⟨hr, h0, H', hp', hsr⟩ => ⟨H', hp', ⟨hr, h0⟩, hsr⟩)
    (fun u hu _ hlk => specR_run <| Knot.specR_of_pre u (pre_of_lookups hu csrParams _ rfl hlk)
      (by
        have h := csr_spec (σ := σ) mode ra C hok hs hcsrC p.recs orl hRl (by rw [hrecs]; simp) hlr
          (fun r hr => by
            rw [hrecs, List.mem_singleton] at hr; subst hr; exact ⟨ks, hkl, hks⟩)
          _ 0 H1 s1 rfl (Nat.zero_le _) hp1'
        rw [List.drop_zero] at h
        exact h))
    (fun cvRis w s2 H2 hp2 ⟨hccv, hcvs⟩ => ?_)
  rw [hrecs] at hcvs hccv
  simp only [List.map_cons, List.map_nil] at hcvs
  subst hcvs
  have hp2' : H1 <+: H2 := hp2
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  obtain ⟨-, -, ⟨hnPw, hnPb⟩, helw, hrsw, hlgw, -⟩ := hsh
  refine UD.specR_heapLoadI' (C := ctxH C H2) gaLg _ (osh + 5) _ (get_prefix hlgw hpC2) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv]; exact cellA_add_ofNat C osh 5) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) gaRsrt _ (osh + 4) _ (get_prefix hrsw hpC2) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv]; exact cellA_add_ofNat C osh 4) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) gaK (vv gaOm) om _ (get_prefix hM.1 hpC2) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv]; rfl) ?_
  have hkb : p.k < 2 ^ 63 := by omega
  refine specR_callNIH (C := ctxH C H2) gaX fLgd lgdParams [vv gaLg, vv gaRsrt, vv gaNc, vv gaK] lgdBody
    [boolW p.large, Enc.idxW p.resSort, BitVec.ofNat 64 p.numCtors, BitVec.ofNat 64 p.k] (by decide) rfl (by decide) hc.lgd
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
    (fun a w s' st => (if p.large then (blockLargeElimAllowed p false >>= fun b => if b then pure () else
      fail (.invalid "generated recursor: large eliminator on a block whose sort may be Prop (official: elim_only_at_universe_zero)"))
      else pure ()) s2 = .ok (a, s') ∧ Decl.PostU (ctxH C H2) a w s' st)
    (fun a _ s' _ => (if p.large then (blockLargeElimAllowed p false >>= fun b => if b then pure () else
      fail (.invalid "generated recursor: large eliminator on a block whose sort may be Prop (official: elim_only_at_universe_zero)"))
      else pure ()) s2 = .ok (a, s'))
    (fun a w s' st ⟨hr, H', hp', hsr⟩ => ⟨H', hp', hr, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu lgdParams _ rfl hlk)
      (lgd_spec (ctxH C H2) hc.nz hc.lea p hkb lsr hSd hnc _ s2)))
    (fun _ w s3 H3 hp3 hlgdr => ?_)
  have hp3' : H2 <+: H3 := hp3
  have hpC3 : C.H <+: H3 := hpC2.trans hp3'
  have hfts : List.map (fun x => x.type) p.formers = [ms0.cvT.type] := by simp [BlockShape.formers, hms]
  have hlps : p.lps = ms0.cvT.levelParams := by simp [BlockShape.lps, hms]
  rw [hfts]
  have hcnsC : CNSCodes mode C := hc.cns
  refine specR_callNIH (C := ctxH C H3) gaX fCns cnsParams
    [vv gaOms, .const 0, vv gaNcl, vv gaOt, vv gaNt, vv gaOlp, vv gaOm, vv gaPp, vv gaNpp]
    cnsBody [cellA C oms, BitVec.ofNat 64 0, BitVec.ofNat 64 [m].length, cellA C ot, BitVec.ofNat 64 tbl.length,
      cellA C olp, cellA C om, cellA C pp, BitVec.ofNat 64 m.pfvs.length] (by decide) rfl (by decide) hcnsC.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], trivial⟩
    (fun r w s' st => classesNfs mode C.fe p [ms0.cvT.type] tbl ([m].drop 0) s3 = .ok (r, s') ∧
      r = ([m].drop 0).map (fun m => { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }) ∧
      Decl.PostU (ctxH C H3) () w s' st)
    (fun r _ s' _ => classesNfs mode C.fe p [ms0.cvT.type] tbl [m] s3 = .ok (r, s') ∧
      r = [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }])
    (fun r w s' st ⟨hrr, hr, H', hp', hsr⟩ => ⟨H', hp', ⟨by simpa using hrr, by simpa using hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run <| Knot.specR_of_pre u (pre_of_lookups hu cnsParams _ rfl hlk)
      (cns_spec mode ra C hok hs hcnsC p [ms0.cvT.type] hfts.symm m.pfvs [m] tbl oms olp om pp ot
        (by rw [hlps]; omega) (by rw [hms]; simp) hppl htl hel (by simp)
        (by intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ⟨hcsl, by omega⟩)
        C.H (List.prefix_refl _) hT (by rw [hlps]; exact hlp) hM hpf htb 1 0 H3 s3 (by simp) (by simp) hpC3))
    (fun es w s4 H4 hp4 ⟨htmnr, hes⟩ => ?_)
  subst es
  have hp4' : H3 <+: H4 := hp4
  have hpC4 : C.H <+: H4 := hpC3.trans hp4'
  refine UD.specR_heapLoadI' (C := ctxH C H4) gaNp _ (osh + 2) _ (get_prefix hnPw hpC4) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv]; exact cellA_add_ofNat C osh 2) ?_
  refine specR_assignI gaNk _ (BitVec.ofNat 64 (p.nP + p.k)) (by decide)
    (by simp +decide [sev, Env.get_cons]; rw [BitVec.ofNat_add]; rfl) ?_
  have hcb2 := hcb
  refine specR_callNIH (C := ctxH C H4) gaCss fCcs ccsParams
    [vv gaOms, .const 0, vv gaNcl, vv gaOt, vv gaNt, vv gaOsl, vv gaNsl, vv gaNk, vv gaOm, vv gaOlp, vv gaTy0, vv gaPp,
      vv gaNpp, vv gaNm] (ccsBody C)
    [cellA C oms, BitVec.ofNat 64 0, BitVec.ofNat 64 [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }].length, cellA C ot, BitVec.ofNat 64 tbl.length, cellA C osl,
      BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 (p.nP + p.k), cellA C om, cellA C olp, Enc.idxW ms0.cvT.type,
      cellA C pp, BitVec.ofNat 64 m.pfvs.length, Enc.idxW ms0.cvT.name] (by decide) rfl (by decide) hc.ccs.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], trivial⟩
    (fun a w s' st => classesCtors mode C.fe p [ms0.cvT.type] rd [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }] 0 ([{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }].drop 0) s4 = .ok (a, s') ∧
      PostCCss (ctxH C H4) a w s' st)
    (fun xss w s' H' => classesCtors mode C.fe p [ms0.cvT.type] rd [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }] 0 ([{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }].drop 0) s4 = .ok (xss, s') ∧
      ∃ o, w = cellA C o ∧ PRep C H' o (fun H o xs => PRep C H o (fun H o cc => CCRep C H o cc) xs) xss)
    (fun a w s' st ⟨hrun, H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ccsParams _ rfl hlk)
      (ccs_spec mode ra C hok hs hc.ccs p [ms0.cvT.type] hfts.symm (by rw [hms]; simp) (Enc.idxW ms0.cvT.type)
        (Enc.idxW ms0.cvT.name) rd [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }] oms
        (tmBlkR_nfs (fun m => tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor))) (tmBlkR_of_tmBlk hT))
        m.pfvs (by simp) (by simp) (by simp [hmm]) (by simp; exact ⟨hcsl, by omega⟩) (by simpa using hnfc)
        om hM ot osl tbl htl htb (by simpa using (fun c hc => nfs_filter_ctor tbl m.ctors c hc)) (by omega) hcb hsb hnk
        olp pp (by rw [hlps]; omega) hppl (by rw [hlps]; exact hlp) hpf 1 0 H4 s4 (by simp) (by simp) hpC4)))
    (fun xss w s5 H5 hp5 ⟨hrunS, ocss, hw, hcss⟩ => ?_)
  subst hw
  have hp5' : H4 <+: H5 := hp5
  have hpC5 : C.H <+: H5 := hpC4.trans hp5'
  obtain ⟨xs, hrun5, rfl⟩ := classesCtors_one hrunS
  have hcss0 := hcss
  obtain ⟨oss1, hoss1l, hoss1b, hoss1r⟩ := hcss0
  have hoss1l' : oss1.length = 1 := by simpa using hoss1l
  have hcs' := hoss1r 0 (by simp) (by omega)
  generalize hocs : oss1[0]'(by omega) = ocs at hcs'
  have hcs : PRep C H5 ocs (fun H o cc => CCRep C H o cc) xs := hcs'
  have hxl : xs.length = m.ctors.length := by simpa using classCtorsOf_len _ hrun5
  have hxnf : ∀ x ∈ xs, x.nF < 2 ^ 56 := fun x hx => by
    obtain ⟨ct, hct, he⟩ := classCtorsOf_nF _ hrun5 x hx
    rw [he]; exact hnfc ct (by simpa using hct)
  have hcs0 := hcs
  obtain ⟨oss, hossl, hossb, -⟩ := hcs0
  have hncs : H5[ocs]? = some (BitVec.ofNat 64 xs.length) := by simpa [hossl] using hossb.1
  refine specR_callPure (C := ctxH C H5) gaSum fSll sllParams [vv gaCss, .const 0, vv gaNcl, .const 0] sllBody
    [cellA C ocss, BitVec.ofNat 64 0, BitVec.ofNat 64 [xs].length, BitVec.ofNat 64 0] xs.length (by decide) rfl
    (by decide) hc.sll ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], rfl, trivial⟩
    (PostSLL (ctxH C H5) s5) (fun r w s' H' => H' = H5 ∧ w = BitVec.ofNat 64 r)
    (fun r w s' st ⟨_, hw, hsr⟩ => ⟨H5, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sllParams _ rfl hlk)
      (specR_congr (m' := pure (0 + (([xs].drop 0).map List.length).sum)) (by simp)
        (sll_spec C hok hc.sll [xs] ocss H5 hcss (by simp) 1 0 0 s5 (by simp) (by simp) (by decide))))
    (fun wsum H5s _ ⟨eH, hwsum⟩ => ?_)
  subst H5s hwsum
  refine specR_congr (m' := (pure ((rd.slots.drop 0).filter ClassSlot.isMinor).length : AM Nat) >>= fun c =>
    (if (c == (List.map List.length [xs]).sum) = true then pure () else
      fail (CheckError.invalid "generated recursor: the recursors' prefix has a minor premise for no constructor of a class (official: invalid recursor)")) >>= fun _ => _)
    (by rw [pure_bind, List.drop_zero]) ?_
  refine specR_callNIH (C := ctxH C H5) gaMc fCmc cmcParams [vv gaOsl, .const 0, vv gaNsl] cmcBody
    [cellA C osl, BitVec.ofNat 64 0, BitVec.ofNat 64 rd.slots.length] (by decide) rfl (by decide) hc.cmc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure ((rd.slots.drop 0).filter ClassSlot.isMinor).length : AM Nat) s5 = .ok (a, s') ∧
      PostCMC (ctxH C H5) s5 a w s' st)
    (fun r w s' H' => (pure ((rd.slots.drop 0).filter ClassSlot.isMinor).length : AM Nat) s5 = .ok (r, s') ∧
      H' = H5 ∧ s' = s5 ∧ w = BitVec.ofNat 64 r)
    (fun r w s' st ⟨hrun, h0, h1, h2⟩ => ⟨H5, List.prefix_refl _, ⟨hrun, rfl, h0, h1⟩, h2⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cmcParams _ rfl hlk)
      (cmc_spec C hc.cmc rd.slots osl (by omega) H5 (slotBlk_mono hpC5 hsb) rd.slots.length 0 s5 (by omega) (by omega))))
    (fun cnt w s6 H6 hp6 ⟨hrun, eH, es, hw⟩ => ?_)
  subst H6 es hw
  have hcntb : cnt ≤ rd.slots.length := by
    obtain ⟨rfl, -⟩ := AM.pure_ok hrun
    have := List.length_filter_le ClassSlot.isMinor (rd.slots.drop 0); simp at this ⊢; omega
  have hxlb : xs.length < 2 ^ 58 := by omega
  by_cases hce : cnt = xs.length
  swap
  · have hne : BitVec.ofNat 64 cnt ≠ BitVec.ofNat 64 xs.length := fun e => hce (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hce])
    (fun _ => ?_) (fun h => absurd h (by decide))
  have hq0 : H5[ocss + 1 + 0]? = some (cellA C ocs) := by
    have := hoss1b.2 0 (by simp; omega); simpa [← hocs] using this
  refine UD.specR_heapLoadI' (C := ctxH C H5) gaCs _ (ocss + 1 + 0) _ hq0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ocss) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H5) gaNcs (vv gaCs) ocs _ hncs (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  simp only [hce, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, beq_self_eq_true, ite_true,
    pure_bind]
  have hft' : List.mapM (classFormerTy mode C.fe p.formers) [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }] = pure [ms0.cvT.type] := by
    simp [classFormerTy, hmm, BlockShape.formers, hms]
  rw [hft', pure_bind]
  refine UD.specR_heapLoadI' (C := ctxH C H5) gaEl _ (osh + 3) _ (get_prefix helw hpC5) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv]; exact cellA_add_ofNat C osh 3) ?_
  refine specR_callNIH (C := ctxH C H5) gaEv fElv elvParams [vv gaLg, vv gaEl] elvBody [boolW p.large, Enc.idxW p.elim]
    (by decide) rfl (by decide) hc.elv ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (fun e w s' st => structElimLevel p.elim p.large s6 = .ok (e, s') ∧ PostL (ctxH C H5) e w s' st)
    (fun e w s' _ => structElimLevel p.elim p.large s6 = .ok (e, s') ∧ w = Enc.idxW e)
    (fun e w s' st ⟨hr, hw, hsr⟩ => ⟨H5, List.prefix_refl _, ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu elvParams _ rfl hlk)
      (elv_spec ra (ctxH C H5) (ctxOK_H hok H5) hc.lp hc.lz p.elim p.large s6)))
    (fun elim w s7 H7 hp7 ⟨helvr, hw⟩ => ?_)
  subst hw
  have hp7' : H5 <+: H7 := hp7
  have hpC7 : C.H <+: H7 := hpC5.trans hp7'
  have hgaPre : gaPre mode C.fe p params tbl rd m block s = .ok ((⟨p.nP, params, [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }],
      [ms0.cvT.type], rd.slots, [xs], elim, []⟩, [rc.cvR]), s7) := by
    have hcnt : (rd.slots.filter ClassSlot.isMinor).length = xs.length := by
      obtain ⟨e, -⟩ := AM.pure_ok hrun; rw [← hce]; simpa using e.symm
    unfold gaPre
    rw [am_bind_run htrp, hrecs, am_bind_run hccv, am_bind_run hlgdr, hfts, am_bind_run htmnr]
    simp only [classesCtors, bind_assoc, pure_bind]
    rw [am_bind_run (by simpa using hrun5)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hcnt, beq_self_eq_true,
      ite_true, pure_bind, hft']
    rw [am_bind_run helvr]; rfl
  rw [hrc0]
  refine specR_congr (m' := _ >>= fun r => pure r) (by rw [bind_pure]) ?_
  refine specR_alloc2I (ctxOK_H hok H7) gaFts (.const 1) (vv gaTy0) 1 (Enc.idxW ms0.cvT.type) (by decide) (fun _ => rfl)
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv]) (fun H8 ws8 hp8 hws8 => ?_)
  obtain ⟨f0, f1⟩ := img2_get H8 ws8 (1 : BitVec 64) (Enc.idxW ms0.cvT.type) hws8
  have hp8' : H7 <+: _ := (hp8 : H7 <+: H8).trans (img2_prefix H8 ws8 (1 : BitVec 64) (Enc.idxW ms0.cvT.type) hws8)
  have hftb : BlkAt (((H8 ++ ws8).set H8.length (1 : BitVec 64)).set (H8.length + 1) (Enc.idxW ms0.cvT.type)) H8.length
      ([ms0.cvT.type].map Enc.idxW) := ⟨by simpa using f0, fun i hi => by simp at hi; subst hi; simpa using f1⟩
  generalize ((H8 ++ ws8).set H8.length (1 : BitVec 64)).set (H8.length + 1) (Enc.idxW ms0.cvT.type) = H9 at hp8' hftb ⊢
  have hpC9 : C.H <+: H9 := hpC7.trans hp8'
  have hp9 : H5 <+: H9 := hp7'.trans hp8'
  refine specR_callNC (C := ctxH C H9) (D := ctxLocals ++ gaLocals) gaRs fGb gbParams
    [vv gaPm, vv gaOsl, vv gaNsl, vv gaNp, vv gaCs, vv gaNcs, vv gaNi, vv gaEv, vv gaOrr, vv gaOms, vv gaCss, vv gaFts,
      vv gaOrl, vv gaOrc] gbBody
    [cellA C opm, cellA C osl, BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 p.nP, cellA C ocs,
      BitVec.ofNat 64 xs.length, BitVec.ofNat 64 m.nIdx, Enc.idxW elim, cellA C orr, cellA C oms, cellA C ocss,
      cellA C H8.length, cellA C orl, cellA C orc] (by decide) rfl (by decide)
    hc.gb.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, gaParams, ctxEnv], trivial⟩
    (PostGR { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) } (ctxH C H9))
    (fun r w s' C' => ∃ EH envM H o, C' = ctxNew (ctxH C H9) r.1 EH envM H ∧ C.EH <+: EH ∧ H9 <+: H ∧
      CtxOK (ctxNew (ctxH C H9) r.1 EH envM H) ∧ TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C.pins ∧
      (∀ n, r.1.find? n = C.fe.find? n) ∧ (∀ n, r.1.findTable? n = C.fe.findTable? n) ∧
      ∃ cv rhss orh oc, r.2 = [(cv, { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }, rhss)] ∧ w = cellA C o ∧ H[o]? = some (cellA C orh) ∧
      H[o + 1]? = some (cellA C oc) ∧ BlkAt H orh (rhss.map Enc.idxW) ∧ CVRep C H oc cv)
    (fun r w s' st ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, o, rfl, h1, h2, h3, h5⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gbParams _ rfl hlk)
      (gb_spec mode ra (ctxH C H9) (ctxOK_H hok H9) hs hpl (by ctx_tr hc.gb) hg hF hL p rc hrecs orr
        (recRep_mono hpC9 hrr0) hrl ks hkl hks
        ⟨p.nP, params, [{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }], [ms0.cvT.type], rd.slots, [xs], elim, []⟩ { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) } rfl hmm
        xs rfl opm osl ocs hpml (blkAt_mono hpm hpC9) hsl (slotBlk_mono hpC9 hsb) hxlb
        (pRep_mono hp9 (fun _ _ => ccRep_mono hp9) hcs) hxnf hni (by show p.nP < _; omega)
        (fun sl h c C' ihs e => (hcb sl h c C' ihs e).1) oms
        (tmBlkR_mono hpC9 (tmBlkR_nfs (fun m => tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor))) (tmBlkR_of_tmBlk hT)))
        ocss H8.length (pRep_mono hp9 (fun _ _ h => pRep_mono hp9 (fun _ _ => ccRep_mono hp9) h) hcss) hftb
        orl (ptrsRep_mono hpC9 (fun _ _ => recRep_mono hpC9) hRl) orc (by rw [← hrc0]; exact blkAt_mono hRC hpC9) s7
        (fun pre s1 s' cv hpb h => hcvd _ [rc.cvR] s7 pre s1 s' cv hgaPre hpb h)))
    (fun r w s8 C8 ⟨EH, envM, H, o, eC, h1, h2, h3, h4⟩ => ?_)
  subst eC
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨EH, envM, H, o, h1, hpC9.trans h2, h3,
    sr_of_eq ht.sr rfl rfl rfl rfl, h4⟩)

end

end ConPanqueque.T.Ind
