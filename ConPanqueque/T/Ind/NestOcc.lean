import ConPanqueque.T.Ind.ClassPass

/-!
# `nestOcc`: does a member or a hole occur (the positivity walk's question)

A pure memoised read; the port mirrors the twin's `HashMap` memo as an association list of cells
`[key, boolW value, next]`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

section
variable {σ : Type}

/-- An optional Boolean as `optWG boolW`; the heap kept. -/
def PostOB2 (C : Ctx) (o : Option Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = optWG boolW o ∧ SR C s' st

theorem postOB2_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOB2 C a w s' st → PostOB2 C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

end

/-- An association list of cells at word `w` (`0` is the empty list). -/
def MemoListB (HB : BitVec 64) (H : List (BitVec 64)) : BitVec 64 → List (EIdx × Bool) → Prop
  | w, [] => w = 0
  | w, (k, v) :: L => ∃ o w', w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some (Enc.idxW k) ∧ H[o + 1]? = some (boolW v) ∧
      H[o + 2]? = some w' ∧ MemoListB HB H w' L

theorem memoListB_mono {HB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') :
    ∀ (L : List (EIdx × Bool)) (w : BitVec 64), MemoListB HB H w L → MemoListB HB H' w L
  | [], _, h => h
  | (_, _) :: L, _, ⟨o, w', h1, h2, h3, h4, h5⟩ =>
    ⟨o, w', h1, get_prefix h2 hp, get_prefix h3 hp, get_prefix h4 hp, memoListB_mono hp L w' h5⟩

/-- A memo at word `w`: an association list whose lookups are the map's. -/
def MemoRepB (HB : BitVec 64) (H : List (BitVec 64)) (w : BitVec 64) (m : Std.HashMap EIdx Bool) : Prop :=
  ∃ L, MemoListB HB H w L ∧ ∀ k, m[k]? = L.lookup k

theorem memoRepB_mono {HB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') {w : BitVec 64}
    {m : Std.HashMap EIdx Bool} (h : MemoRepB HB H w m) : MemoRepB HB H' w m :=
  let ⟨L, h1, h2⟩ := h; ⟨L, memoListB_mono hp L w h1, h2⟩

def mbfW := ofString "mbf_w"
def mbfK := ofString "mbf_k"
def mbfX := ofString "mbf_x"
def mbfR := ofString "mbf_r"
def fMemoFindB := ofString "memoFindB"

def mbfParams : List MlS := [mbfW, mbfK]
def mbfLocals : List MlS := [mbfX, mbfR]

def mbfBody : ProgHOL 64 := prologue mbfLocals
  (.ite (.cmp .equal (vv mbfW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local mbfX (.load .one (vv mbfW)))
  (.ite (.cmp .equal (vv mbfX) (vv mbfK))
    (.seq (.assign .local mbfR (.load .one (.op .add [vv mbfW, .const 8]))) (.return (.op .add [vv mbfR, .const 1])))
    (.seq (.assign .local mbfX (.load .one (.op .add [vv mbfW, .const 16])))
    (.seq (.call (some (some (.local, mbfR), none)) fMemoFindB [vv mbfX, vv mbfK]) (.return (vv mbfR)))))))

section
variable {σ : Type}

theorem mbf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mbfLocals → (ctxEnv C ++ mbfParams.zip vals).get x = none :=
  Knot.params_none C mbfLocals mbfParams vals (by decide) (by decide)

/-- **`memoFind`**: the list's lookup as `optWG idxW`. -/
theorem mbf_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMemoFindB = some (mbfParams.map (fun p => (p, ShapeHOL.one)), mbfBody, .one))
    (H : List (BitVec 64)) (k : EIdx) :
    ∀ (L : List (EIdx × Bool)) (w : BitVec 64) (s : AState), MemoListB C.HB H w L →
      SpecR (σ := σ) (Pre (ctxH C H) s (mbfParams.zip [w, Enc.idxW k])) mbfBody s (pure (L.lookup k))
        (PostOB2 (ctxH C H)) := by
  intro L
  induction L with
  | nil =>
    intro w s hw
    refine specR_prologue (postOB2_locals _) (mbf_none _ _) ?_
    simp only [MemoListB] at hw; subst hw
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mbfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons kv L ih =>
    intro w s hw
    obtain ⟨k0, v0⟩ := kv
    obtain ⟨o, w', rfl, h0, h1, h2, hL⟩ := hw
    refine specR_prologue (postOB2_locals _) (mbf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hol : o < H.length := (List.getElem?_eq_some_iff.mp h0).1
    have hHN' : H.length ≤ C.HN := hHN
    have hne : cellA C o ≠ 0 := cellA_ne0 C hok o (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mbfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H) mbfX (vv mbfW) o _ h0 (by decide)
      (by simp +decide [sev, Env.get, mbfParams, ctxEnv]; rfl) ?_
    by_cases he : k0 = k
    · subst he
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) mbfR _ (o + 1) _ h1 (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv]; exact cellA_add8 C o) ?_
      exact specR_returnI _ (boolW v0 + 1) (by simp [sev, Env.get_cons]) (fun t ht => ⟨by simp [optWG, List.lookup], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hw : Enc.idxW k0 ≠ Enc.idxW k := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H) mbfX _ (o + 2) _ h2 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv]; exact cellA_add_ofNat C o 2) ?_
    have hlk : ((k0, v0) :: L).lookup k = L.lookup k := by
      have hb : (k == k0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he e.symm
      simp only [List.lookup, hb]
    rw [hlk]
    refine specR_congr (m' := (pure (L.lookup k) : AM (Option Bool)) >>= fun r => pure r) (by simp) ?_
    refine specR_callNIM mbfR fMemoFindB mbfParams [vv mbfX, vv mbfK] mbfBody [w', Enc.idxW k] (by decide) rfl (by decide) hc
      ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv], trivial⟩
      (PostOB2 (ctxH C H)) (fun _ _ _ _ h => h.2)
      (fun u hu _ hlk' => Knot.specR_of_pre u (pre_of_lookups hu mbfParams _ rfl hlk') (ih w' s hL))
      (fun r w2 s1 st ⟨hw2, _⟩ => ?_)
    subst hw2
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def nocM := ofString "noc_m"
def nocMs := ofString "noc_ms"
def nocLo := ofString "noc_lo"
def nocHi := ofString "noc_hi"
def nocB := ofString "noc_b"
def nocK := ofString "noc_k"
def nocX := ofString "noc_x"
def nocN := ofString "noc_n"
def nocA1 := ofString "noc_a1"
def nocA2 := ofString "noc_a2"
def nocA3 := ofString "noc_a3"
def nocQ := ofString "noc_q"
def nocY := ofString "noc_y"
def nocZ := ofString "noc_z"
def nocV := ofString "noc_v"
def nocM1 := ofString "noc_m1"
def nocM2 := ofString "noc_m2"
def nocM3 := ofString "noc_m3"
def nocW := ofString "noc_w"
def nocR := ofString "noc_r"
def fNestOcc := ofString "nestOccGo"

def nocParams : List MlS := [pFu, pH, nocM, nocMs, nocLo, nocHi]
def nocLocals : List MlS := gaaLocals ++ [nocB, nocK, nocX, nocN, nocA1, nocA2, nocA3, nocQ, nocY, nocZ, nocV, nocM1,
  nocM2, nocM3, nocW, nocR]

/-- Return the pair `[answer, memo]` (the answer a word expression). -/
def nocRet (C : Ctx) (r : ExpHOL 64) (m : MlS) : ProgHOL 64 := alloc2 C nocR r (vv m) (.return (vv nocR))

/-- One child walked into `y` (answer) and `m'` (memo). -/
def nocCall (child memo y m' : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, nocQ), none)) fNestOcc
      [.op .sub [vv pFu, .const 1], vv child, vv memo, vv nocMs, vv nocLo, vv nocHi])
  (.seq (.assign .local y (.load .one (vv nocQ)))
  (.seq (.assign .local m' (.load .one (.op .add [vv nocQ, .const 8]))) rest))

/-- Memoise `h ↦ v` (in `nocW`) over the memo in `m`, and return. -/
def nocSet (C : Ctx) (m : MlS) : ProgHOL 64 :=
  alloc3 C nocM3 (vv pH) (vv nocW) (vv m) (nocRet C (vv nocW) nocM3)

def nocBin (C : Ctx) : ProgHOL 64 :=
  nocCall nocA1 nocM nocY nocM1
    (.ite (.cmp .equal (vv nocY) (.const 0))
      (nocCall nocA2 nocM1 nocZ nocM2 (.seq (.assign .local nocW (vv nocZ)) (nocSet C nocM2)))
      (.seq (.assign .local nocW (.const 1)) (nocSet C nocM1)))

def nocLet (C : Ctx) : ProgHOL 64 :=
  nocCall nocA1 nocM nocY nocM1
    (.ite (.cmp .equal (vv nocY) (.const 0))
      (nocCall nocA2 nocM1 nocZ nocM2
        (.ite (.cmp .equal (vv nocZ) (.const 0))
          (nocCall nocA3 nocM2 nocV nocM1 (.seq (.assign .local nocW (vv nocV)) (nocSet C nocM1)))
          (.seq (.assign .local nocW (.const 1)) (nocSet C nocM2))))
      (.seq (.assign .local nocW (.const 1)) (nocSet C nocM1)))

def nocProj (C : Ctx) : ProgHOL 64 :=
  nocCall nocA2 nocM nocY nocM1 (.seq (.assign .local nocW (vv nocY)) (nocSet C nocM1))

def nocMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, nocX), none)) fMemoFindB [vv nocM, vv pH])
  (.ite (.cmp .equal (vv nocX) (.const 0)) arm
    (.seq (.assign .local nocX (.op .sub [vv nocX, .const 1])) (nocRet C (vv nocX) nocM)))

def nocNode (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local nocA1 (.load .one (vv lRp)))
  (.seq (.assign .local nocA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local nocA3 (.load .one (.op .add [vv lRp, .const 16]))) (nocMemo C (nocLet C)))
  (.ite (.cmp .equal (vv lDg) (.const 9)) (nocMemo C (nocProj C)) (nocMemo C (nocBin C)))))

def nocFvarIdx (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv nocB) (vv nocLo)) (nocRet C (.const 0) nocM)
    (.ite (.cmp .lower (vv nocB) (vv nocHi)) (nocRet C (.const 1) nocM) (nocRet C (.const 0) nocM))

def nocFvar (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local nocB (.const 0)) (nocFvarIdx C))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local nocB (.load .one (.op .add [vv lRp, .const 8]))) (nocFvarIdx C))
      (nocRet C (.const 0) nocM))

def nocConst (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local nocN (.load .one (vv lRp)))
  (.seq (.assign .local nocK (.load .one (vv nocMs)))
  (.seq (.call (some (some (.local, nocX), none)) fMemNameIn [vv nocMs, vv nocN, .const 0, vv nocK])
    (nocRet C (vv nocX) nocM)))

def nocBody (C : Ctx) : ProgHOL 64 := prologue nocLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (nocFvar C)
  (.ite (.cmp .equal (vv lDg) (.const 3)) (nocConst C)
  (.ite (.cmp .lower (vv lDg) (.const 4)) (nocRet C (.const 0) nocM)
  (.ite (.cmp .equal (vv lDg) (.const 8)) (nocRet C (.const 0) nocM) (nocNode C)))))))))

/-- The code `nestOccGo` runs. -/
structure NOCCodes (C : Ctx) : Prop where
  self : C.code.lookup fNestOcc = some (nocParams.map (fun p => (p, ShapeHOL.one)), nocBody C, .one)
  mbf : C.code.lookup fMemoFindB = some (mbfParams.map (fun p => (p, ShapeHOL.one)), mbfBody, .one)
  mnc : C.code.lookup fMemNameIn = some (mncParams.map (fun p => (p, ShapeHOL.one)), mncBody, .one)

section
variable {σ : Type}

theorem noc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nocLocals → (ctxEnv C ++ nocParams.zip vals).get x = none :=
  Knot.params_none C nocLocals nocParams vals (by decide) (by decide)

/-- The walk's answer: a pair `[boolW b, memo]`, the memo represented. -/
def PostNO (C : Ctx) (r : Bool × Std.HashMap EIdx Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' op mw', C.H <+: H' ∧ w = cellA C op ∧ H'[op]? = some (boolW r.1) ∧ H'[op + 1]? = some mw' ∧
    MemoRepB C.HB H' mw' r.2 ∧ SR (ctxH C H') s' st

theorem postNO_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNO C a w s' st → PostNO C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', op, mw', hp, hw, h1, h2, h3, hs⟩ => ⟨H', op, mw', hp, hw, h1, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

/-- Return `[b, memo]`. -/
theorem noc_ret (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64)) (hbH : Hb <+: H)
    (r : ExpHOL 64) (b : Bool) (m : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hm : MemoRepB C.HB H mw memo) (hr : ∀ v, sev ((nocR, v) :: Γ) r = some (boolW b))
    (gM : ∀ v, sev ((nocR, v) :: Γ) (vv m) = some mw) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ nocLocals)) (nocRet C r m) s (pure (b, memo))
      (PostNO (ctxH C Hb)) := by
  unfold nocRet
  refine specR_alloc2I (ctxOK_H hok H) nocR r (vv m) (boolW b) mw (by decide) hr gM (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1⟩ := img2_get H2 ws (boolW b) mw hws
  have h2 := img2_prefix H2 ws (boolW b) mw hws
  exact specR_returnI (vv nocR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, H2.length, mw, hbH.trans ((hp2 : H <+: H2).trans h2), rfl, g0, g1,
      memoRepB_mono ((hp2 : H <+: H2).trans h2) hm, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem memoRepB_insert {HB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {mw : BitVec 64}
    {m : Std.HashMap EIdx Bool} (h : EIdx) (r : Bool) (hm : MemoRepB HB H mw m)
    (h0 : H[o]? = some (Enc.idxW h)) (h1 : H[o + 1]? = some (boolW r)) (h2 : H[o + 2]? = some mw) :
    MemoRepB HB H (HB + BitVec.ofNat 64 (8 * o)) (m.insert h r) := by
  obtain ⟨L, hL, hlk⟩ := hm
  refine ⟨(h, r) :: L, ⟨o, mw, rfl, h0, h1, h2, hL⟩, fun k => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  by_cases hk : h = k
  · subst hk; simp [List.lookup]
  · have e1 : (h == k) = false := by simpa using hk
    have e2 : (k == h) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hk e.symm
    simp only [e1, Bool.false_eq_true, ite_false, List.lookup, e2, hlk]

/-- Memoise `h ↦ r` (in `nocW`) over the memo in `m`, and return `[r, memo']`. -/
theorem noc_set (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h : EIdx) (r : Bool) (m : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx Bool) (hbH : Hb <+: H)
    (hm : MemoRepB C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get nocW = some (boolW r))
    (gM : Γ.get m = some mw) (hmt : m ≠ nocM3) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ nocLocals)) (nocSet C m) s (pure (r, memo.insert h r))
      (PostNO (ctxH C Hb)) := by
  unfold nocSet
  refine specR_alloc3I (ctxOK_H hok H) nocM3 (vv pH) (vv nocW) (vv m) (Enc.idxW h) (boolW r) mw (by decide)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gH)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg hmt]; exact gM) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW h) (boolW r) mw hws
  have h3 := img3_prefix H2 ws (Enc.idxW h) (boolW r) mw hws
  have hp23 : H <+: _ := (hp2 : H <+: H2).trans h3
  have hm3 := memoRepB_insert h r (memoRepB_mono hp23 hm) g0 g1 g2
  exact noc_ret C hok _ Hb (hbH.trans hp23) (vv nocW) r nocM3 _ _ hm3
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; simp; rfl)

/-- The walk at fuel `n`, from any heap over the base. -/
def NORec (C : Ctx) (ms : List MemberShape) (om lo hi n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx Bool) (mw : BitVec 64) (H : List (BitVec 64)) (s : AState), C.H <+: H →
    MemoRepB C.HB H mw memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (nocParams.zip [BitVec.ofNat 64 n, Enc.idxW h, mw, cellA C om,
      BitVec.ofNat 64 lo, BitVec.ofNat 64 hi])) (nocBody C) s
      (nestOccGo (ms.map (·.cvT.name)) lo hi memo n h) (PostNO (ctxH C H))

/-- One child walked (`nocCall`). -/
theorem noc_call {β : Type} (C : Ctx) (hc : NOCCodes C) (ms : List MemberShape) (om lo hi n : Nat)
    (ih : NORec (σ := σ) C ms om lo hi n)
    {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : Bool × Std.HashMap EIdx Bool → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (hp : C.H <+: H)
    (child memo y m' : MlS)
    (hx : y ∈ ctxLocals ++ nocLocals ∧ m' ∈ ctxLocals ++ nocLocals)
    (hne : y ≠ nocQ ∧ m' ≠ nocQ ∧ m' ≠ y)
    (c : EIdx) (memo0 : Std.HashMap EIdx Bool) (mw : BitVec 64) (hm : MemoRepB C.HB H mw memo0)
    (gF : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (gC : Γ.get child = some (Enc.idxW c))
    (gM : Γ.get memo = some mw) (gMs : Γ.get nocMs = some (cellA C om))
    (gLo : Γ.get nocLo = some (BitVec.ofNat 64 lo)) (gHi : Γ.get nocHi = some (BitVec.ofNat 64 hi))
    (hk : ∀ (r : Bool × Std.HashMap EIdx Bool) (H' : List (BitVec 64)) (op : Nat) (mw' : BitVec 64) (s' : AState),
      H <+: H' → MemoRepB C.HB H' mw' r.2 →
      SpecR (Inv (ctxH C H') s' ((m', mw') :: (y, boolW r.1) :: (nocQ, cellA C op) :: Γ) [] (ctxLocals ++ nocLocals))
        rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ nocLocals)) (nocCall child memo y m' rest) s
      (nestOccGo (ms.map (·.cvT.name)) lo hi memo0 n c >>= k) R := by
  unfold nocCall
  refine specR_callNIH (C := ctxH C H) nocQ fNestOcc nocParams
    [.op .sub [vv pFu, .const 1], vv child, vv memo, vv nocMs, vv nocLo, vv nocHi]
    (nocBody C) [BitVec.ofNat 64 n, Enc.idxW c, mw, cellA C om, BitVec.ofNat 64 lo, BitVec.ofNat 64 hi] (by decide) rfl
    (by decide) hc.self
    ⟨by simp only [sev, sev_vv, gF]; simp; exact ofNat_succ_sub_one n, by simp [sev, gC], by simp [sev, gM],
      by simp [sev, gMs], by simp [sev, gLo], by simp [sev, gHi], trivial⟩
    (PostNO (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (boolW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRepB C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nocParams _ rfl hlk) (ih c memo0 mw H s hp hm))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, h2, h3⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) y (vv nocQ) op _ h1 hx.1 (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) m' _ (op + 1) _ h2 hx.2
    (by simp only [sev, sev_vv, Env.get_cons, if_neg (show nocQ ≠ y from fun e => hne.1 e.symm), if_true]; simp; exact cellA_add8 C op) ?_
  exact hk r H1 op mw' s1 hp1 h3

end

section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`nestOccGo`** at the block's member names. -/
theorem noc_spec (C : Ctx) (hok : CtxOK C) (hc : NOCCodes C) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59) (lo hi : Nat)
    (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64) : ∀ n, n < 2 ^ 64 → NORec (σ := σ) C ms om lo hi n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo mw H s hp hm
    refine specR_prologue (postNO_locals _) (noc_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, nocParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro hn h memo mw H s hp hm
    have ih' := ih (by omega)
    have hM' : PtrsRep C H om (MemberRep C H) ms := ptrsRep_mono hp (fun _ _ => memberRep_mono hp) hM
    refine specR_prologue (postNO_locals _) (noc_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, nocParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [nestOccGo]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, nocParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s = .ok (v, s) by rw [view_run, hv]) ?_
    have hleaf : ∀ (Γ : Env) (M : Mem), Γ.get nocM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ nocLocals)) (nocRet C (.const 0) nocM) s (pure (false, memo))
          (PostNO (ctxH C H)) := fun Γ M gM =>
      noc_ret C hok H H (List.prefix_refl _) (.const 0) false nocM mw memo hm (fun _ => by simp [sev, boolW])
        (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gM)
    -- the memo step of a compound node
    have hmemo : ∀ (arm : ProgHOL 64) (mnone : AM (Bool × Std.HashMap EIdx Bool)) (Γ : Env) (M : Mem),
        Γ.get nocM = some mw → Γ.get pH = some (Enc.idxW h) →
        (memo[h]? = none → SpecR (σ := σ) (Inv (ctxH C H) s ((nocX, 0) :: Γ) [] (ctxLocals ++ nocLocals)) arm s mnone
          (PostNO (ctxH C H))) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ nocLocals)) (nocMemo C arm) s
          (match memo[h]? with
            | some r => pure (r, memo)
            | none => mnone) (PostNO (ctxH C H)) := by
      intro arm mnone Γ M gM gH harm
      obtain ⟨L, hL, hlk⟩ := id hm
      unfold nocMemo
      rw [hlk h]
      refine specR_pureBind (L.lookup h) ?_
      refine specR_callNIM nocX fMemoFindB mbfParams [vv nocM, vv pH] mbfBody [mw, Enc.idxW h] (by decide) rfl (by decide)
        hc.mbf ⟨by simp [sev, gM], by simp [sev, gH], trivial⟩
        (fun a w s' st => (pure (L.lookup h) : AM (Option Bool)) s = .ok (a, s') ∧ PostOB2 (ctxH C H) a w s' st)
        (fun _ _ _ _ h => h.2.2)
        (fun u hu _ hlk' => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mbfParams _ rfl hlk')
          (mbf_spec C hok hc.mbf H h L mw s hL)))
        (fun a w s1 st ⟨hrun, hw, _⟩ => ?_)
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hra, hs1⟩ := hrun
      subst hw; subst hs1; subst hra
      rcases hfo : L.lookup h with _ | r
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact harm (by rw [hlk h, hfo])
      have hr1 : boolW r + 1 ≠ 0#64 := by cases r <;> decide
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hr1)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_assignI nocX _ (boolW r) (by decide)
        (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      exact noc_ret C hok H H (List.prefix_refl _) (vv nocX) r nocM mw memo hm (fun _ => by simp +decide [sev, Env.get_cons])
        (fun _ => by simp +decide [sev, Env.get_cons, gM])
    cases v with
    | bvar i =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv])
    | sort u =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv])
    | lit l =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv])
    | const c us =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold nocConst
      refine specR_loadI' nocN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) nocK (vv nocMs) om _ hM'.1 (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, nocParams, ctxEnv]; rfl) ?_
      simp only
      refine specR_pureBind (((ms.drop 0).map (·.cvT.name)).contains c) ?_
      refine specR_callNIH (C := ctxH C H) nocX fMemNameIn mncParams [vv nocMs, vv nocN, .const 0, vv nocK] mncBody
        [cellA C om, Enc.idxW c, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc.mnc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, nocParams, ctxEnv], by simp +decide [sev, Env.get_cons],
          rfl, by simp +decide [sev, Env.get_cons], trivial⟩
        (fun a w s' st => (pure (((ms.drop 0).map (·.cvT.name)).contains c) : AM Bool) s = .ok (a, s') ∧
          PostB (ctxH C H) a w s' st)
        (fun a w s' _ => (pure (((ms.drop 0).map (·.cvT.name)).contains c) : AM Bool) s = .ok (a, s') ∧ w = boolW a)
        (fun a w s' st ⟨hrun, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hrun, hw⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mncParams _ rfl hlk)
          (mnc_spec C hok hc.mnc ms c om H hM' hml _ 0 s rfl (by omega))))
        (fun a w s1 H1 hp1 ⟨hrun, hw⟩ => ?_)
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hra, hs1⟩ := hrun
      subst hw; subst hs1
      have hp1' : H <+: H1 := hp1
      simp only [List.drop_zero] at hra
      simp only [hra]
      exact noc_ret C hok H1 H hp1' (vv nocX) a nocM mw memo (memoRepB_mono hp1' hm)
        (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, Env.get, nocParams, ctxEnv])
    | fvar i ty =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      try simp only
      unfold nocFvar
      have hlen1 : (encEView (.fvar i ty)).length = 1 + (Enc.limbs i).length := by simp [encEView, Enc.encFVar]; omega
      have hidx : ∀ (Γ : Env) (M : Mem), i < 2 ^ 64 → Γ.get nocB = some (BitVec.ofNat 64 i) →
          Γ.get nocLo = some (BitVec.ofNat 64 lo) → Γ.get nocHi = some (BitVec.ofNat 64 hi) → Γ.get nocM = some mw →
          SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ nocLocals)) (nocFvarIdx C) s
            (pure (decide (lo ≤ i) && decide (i < hi), memo)) (PostNO (ctxH C H)) := by
        intro Γ M hib gB gLo gHi gM
        unfold nocFvarIdx
        by_cases hl : i < lo
        · refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [gB, gLo, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (ConPanqueque.T.Decl.nd_lt_iff i lo hib hlo).mpr hl])
            (fun _ => ?_) (fun h => absurd h (by decide))
          have e : (decide (lo ≤ i) && decide (i < hi)) = false := by simp; omega
          rw [e]
          exact noc_ret C hok H H (List.prefix_refl _) (.const 0) false nocM mw memo hm (fun _ => by simp [sev, boolW])
            (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gM)
        refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [gB, gLo, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (ConPanqueque.T.Decl.nd_lt_iff i lo hib hlo).not.mpr hl])
          (fun h => absurd rfl h) (fun _ => ?_)
        by_cases hh : i < hi
        · refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [gB, gHi, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (ConPanqueque.T.Decl.nd_lt_iff i hi hib hhi).mpr hh])
            (fun _ => ?_) (fun h => absurd h (by decide))
          have e : (decide (lo ≤ i) && decide (i < hi)) = true := by simp; omega
          rw [e]
          exact noc_ret C hok H H (List.prefix_refl _) (.const 1) true nocM mw memo hm (fun _ => by simp [sev, boolW])
            (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gM)
        refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [gB, gHi, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (ConPanqueque.T.Decl.nd_lt_iff i hi hib hhi).not.mpr hh])
          (fun h => absurd rfl h) (fun _ => ?_)
        have e : (decide (lo ≤ i) && decide (i < hi)) = false := by simp; omega
        rw [e]
        exact noc_ret C hok H H (List.prefix_refl _) (.const 0) false nocM mw memo hm (fun _ => by simp [sev, boolW])
          (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gM)
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI nocB (.const 0) 0 (by decide) rfl ?_
        exact hidx _ _ (by decide) (by simp) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv])
      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' nocB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 i) [] (M := [])
              simpa [encEView, Enc.encFVar, hl] using this) ?_
        exact hidx _ _ ib (by simp) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv])
      have hge : 2 ≤ (Enc.limbs i).length := by
        have := (Big.limbs_length_lt_iff i 1).not.mpr (by simp [Big.B]; omega); omega
      have hsh' : 1 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen1]; exact hlen
      have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 1#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 2#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn1)
        (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn2)
        (fun hw => absurd rfl hw) (fun _ => ?_)
      have e : (decide (lo ≤ i) && decide (i < hi)) = false := by simp; omega
      rw [e]
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv])
    | app a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      unfold nocNode
      refine specR_loadI' nocA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' nocA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun _ => ?_)
      unfold nocBin
      simp only [bind_assoc]
      refine noc_call C hc ms om lo hi n ih' H hp nocA1 nocM nocY nocM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨b1, m1⟩ := r1
      cases b1
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine noc_call C hc ms om lo hi n ih' H1 (hp.trans hp1) nocA2 nocM1 nocZ nocM2 (by decide) (by decide) b m1 mw1 hm1
          (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
        obtain ⟨b2, m2⟩ := r2
        try simp only [pure_bind]
        refine specR_assignI nocW (vv nocZ) (boolW b2) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
        exact noc_set C hok H2 H h b2 nocM2 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
      · simp only [↓reduceIte, pure_bind]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI nocW (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
        exact noc_set C hok H1 H h true nocM1 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
    | lam a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      unfold nocNode
      refine specR_loadI' nocA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' nocA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun _ => ?_)
      unfold nocBin
      simp only [bind_assoc]
      refine noc_call C hc ms om lo hi n ih' H hp nocA1 nocM nocY nocM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨b1, m1⟩ := r1
      cases b1
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine noc_call C hc ms om lo hi n ih' H1 (hp.trans hp1) nocA2 nocM1 nocZ nocM2 (by decide) (by decide) b m1 mw1 hm1
          (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
        obtain ⟨b2, m2⟩ := r2
        try simp only [pure_bind]
        refine specR_assignI nocW (vv nocZ) (boolW b2) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
        exact noc_set C hok H2 H h b2 nocM2 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
      · simp only [↓reduceIte, pure_bind]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI nocW (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
        exact noc_set C hok H1 H h true nocM1 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
    | forallE a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      unfold nocNode
      refine specR_loadI' nocA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' nocA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun _ => ?_)
      unfold nocBin
      simp only [bind_assoc]
      refine noc_call C hc ms om lo hi n ih' H hp nocA1 nocM nocY nocM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨b1, m1⟩ := r1
      cases b1
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine noc_call C hc ms om lo hi n ih' H1 (hp.trans hp1) nocA2 nocM1 nocZ nocM2 (by decide) (by decide) b m1 mw1 hm1
          (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
        obtain ⟨b2, m2⟩ := r2
        try simp only [pure_bind]
        refine specR_assignI nocW (vv nocZ) (boolW b2) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
        exact noc_set C hok H2 H h b2 nocM2 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
      · simp only [↓reduceIte, pure_bind]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI nocW (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
        exact noc_set C hok H1 H h true nocM1 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
    | letE ty v b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      unfold nocNode
      refine specR_loadI' nocA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW v, Enc.idxW b] []) ?_
      refine specR_loadI' nocA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' nocA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v) (Enc.idxW b) [] []) ?_
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun _ => ?_)
      unfold nocLet
      simp only [bind_assoc]
      refine noc_call C hc ms om lo hi n ih' H hp nocA1 nocM nocY nocM1 (by decide) (by decide) ty memo mw hm
        (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨b1, m1⟩ := r1
      cases b1
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine noc_call C hc ms om lo hi n ih' H1 (hp.trans hp1) nocA2 nocM1 nocZ nocM2 (by decide) (by decide) v m1 mw1 hm1
          (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
        obtain ⟨b2, m2⟩ := r2
        cases b2
        · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          refine noc_call C hc ms om lo hi n ih' H2 ((hp.trans hp1).trans hp2) nocA3 nocM2 nocV nocM1 (by decide) (by decide) b m2 mw2 hm2
            (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r3 H3 op3 mw3 s3 hp3 hm3 => ?_)
          obtain ⟨b3, m3⟩ := r3
          try simp only [pure_bind]
          refine specR_assignI nocW (vv nocV) (boolW b3) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
          exact noc_set C hok H3 H h b3 nocM1 mw3 m3 ((hp1.trans hp2).trans hp3) hm3 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
        · simp only [↓reduceIte, pure_bind]
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
          refine specR_assignI nocW (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
          exact noc_set C hok H2 H h true nocM2 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
      · simp only [↓reduceIte, pure_bind]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI nocW (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
        exact noc_set C hok H1 H h true nocM1 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)
    | proj nm i e =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      unfold nocNode
      refine specR_loadI' nocA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW nm) (Enc.idxW e :: Enc.limbs i) []) ?_
      refine specR_loadI' nocA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW nm) (Enc.idxW e) (Enc.limbs i) []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun _ => ?_) (fun h => absurd h (by decide))
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun _ => ?_)
      unfold nocProj
      refine noc_call C hc ms om lo hi n ih' H hp nocA2 nocM nocY nocM1 (by decide) (by decide) e memo mw hm
        (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨b1, m1⟩ := r1
      try simp only [pure_bind]
      refine specR_assignI nocW (vv nocY) (boolW b1) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
      exact noc_set C hok H1 H h b1 nocM1 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, nocParams, ctxEnv]) (by decide)

end

end ConPanqueque.T.Ind
