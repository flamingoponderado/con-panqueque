import ConPanqueque.T.Ind.ClassRead
import ConRon.Arena.Inductives.Positivity

/-!
# `replaceFVars` at the canonical map (`targetCanonParams`)

The twin threads a fresh `Std.HashMap` memo through one DAG walk.  The port keeps the same memo as an
allocation-only association list of cells `[key, value, next]` (latest first), so both intern the same
nodes in the same order.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- An association list of cells at word `w` (`0` is the empty list). -/
def MemoList (HB : BitVec 64) (H : List (BitVec 64)) : BitVec 64 → List (EIdx × EIdx) → Prop
  | w, [] => w = 0
  | w, (k, v) :: L => ∃ o w', w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some (Enc.idxW k) ∧ H[o + 1]? = some (Enc.idxW v) ∧
      H[o + 2]? = some w' ∧ MemoList HB H w' L

theorem memoList_mono {HB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') :
    ∀ (L : List (EIdx × EIdx)) (w : BitVec 64), MemoList HB H w L → MemoList HB H' w L
  | [], _, h => h
  | (_, _) :: L, _, ⟨o, w', h1, h2, h3, h4, h5⟩ =>
    ⟨o, w', h1, get_prefix h2 hp, get_prefix h3 hp, get_prefix h4 hp, memoList_mono hp L w' h5⟩

/-- A memo at word `w`: an association list whose lookups are the map's. -/
def MemoRep (HB : BitVec 64) (H : List (BitVec 64)) (w : BitVec 64) (m : Std.HashMap EIdx EIdx) : Prop :=
  ∃ L, MemoList HB H w L ∧ ∀ k, m[k]? = L.lookup k

theorem memoRep_mono {HB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') {w : BitVec 64}
    {m : Std.HashMap EIdx EIdx} (h : MemoRep HB H w m) : MemoRep HB H' w m :=
  let ⟨L, h1, h2⟩ := h; ⟨L, memoList_mono hp L w h1, h2⟩

def mmfW := ofString "mmf_w"
def mmfK := ofString "mmf_k"
def mmfX := ofString "mmf_x"
def mmfR := ofString "mmf_r"
def fMemoFind := ofString "memoFind"

def mmfParams : List MlS := [mmfW, mmfK]
def mmfLocals : List MlS := [mmfX, mmfR]

def mmfBody : ProgHOL 64 := prologue mmfLocals
  (.ite (.cmp .equal (vv mmfW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local mmfX (.load .one (vv mmfW)))
  (.ite (.cmp .equal (vv mmfX) (vv mmfK))
    (.seq (.assign .local mmfR (.load .one (.op .add [vv mmfW, .const 8]))) (.return (.op .add [vv mmfR, .const 1])))
    (.seq (.assign .local mmfX (.load .one (.op .add [vv mmfW, .const 16])))
    (.seq (.call (some (some (.local, mmfR), none)) fMemoFind [vv mmfX, vv mmfK]) (.return (vv mmfR)))))))

section
variable {σ : Type}

theorem mmf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mmfLocals → (ctxEnv C ++ mmfParams.zip vals).get x = none :=
  Knot.params_none C mmfLocals mmfParams vals (by decide) (by decide)

/-- **`memoFind`**: the list's lookup as `optWG idxW`. -/
theorem mmf_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMemoFind = some (mmfParams.map (fun p => (p, ShapeHOL.one)), mmfBody, .one))
    (H : List (BitVec 64)) (k : EIdx) :
    ∀ (L : List (EIdx × EIdx)) (w : BitVec 64) (s : AState), MemoList C.HB H w L →
      SpecR (σ := σ) (Pre (ctxH C H) s (mmfParams.zip [w, Enc.idxW k])) mmfBody s (pure (L.lookup k))
        (PostOE (ctxH C H)) := by
  intro L
  induction L with
  | nil =>
    intro w s hw
    refine specR_prologue (postOE_locals _) (mmf_none _ _) ?_
    simp only [MemoList] at hw; subst hw
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mmfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons kv L ih =>
    intro w s hw
    obtain ⟨k0, v0⟩ := kv
    obtain ⟨o, w', rfl, h0, h1, h2, hL⟩ := hw
    refine specR_prologue (postOE_locals _) (mmf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hol : o < H.length := (List.getElem?_eq_some_iff.mp h0).1
    have hHN' : H.length ≤ C.HN := hHN
    have hne : cellA C o ≠ 0 := cellA_ne0 C hok o (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mmfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H) mmfX (vv mmfW) o _ h0 (by decide)
      (by simp +decide [sev, Env.get, mmfParams, ctxEnv]; rfl) ?_
    by_cases he : k0 = k
    · subst he
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mmfParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) mmfR _ (o + 1) _ h1 (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, mmfParams, ctxEnv]; exact cellA_add8 C o) ?_
      exact specR_returnI _ (Enc.idxW v0 + 1) (by simp [sev, Env.get_cons]) (fun t ht => ⟨by simp [optWG, List.lookup], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hw : Enc.idxW k0 ≠ Enc.idxW k := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, mmfParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H) mmfX _ (o + 2) _ h2 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, mmfParams, ctxEnv]; exact cellA_add_ofNat C o 2) ?_
    have hlk : ((k0, v0) :: L).lookup k = L.lookup k := by
      have hb : (k == k0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he e.symm
      simp only [List.lookup, hb]
    rw [hlk]
    refine specR_congr (m' := (pure (L.lookup k) : AM (Option EIdx)) >>= fun r => pure r) (by simp) ?_
    refine specR_callNIM mmfR fMemoFind mmfParams [vv mmfX, vv mmfK] mmfBody [w', Enc.idxW k] (by decide) rfl (by decide) hc
      ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mmfParams, ctxEnv], trivial⟩
      (PostOE (ctxH C H)) (fun _ _ _ _ h => h.2)
      (fun u hu _ hlk' => Knot.specR_of_pre u (pre_of_lookups hu mmfParams _ rfl hlk') (ih w' s hL))
      (fun r w2 s1 st ⟨hw2, _⟩ => ?_)
    subst hw2
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def rfwM := ofString "rfw_m"
def rfwP := ofString "rfw_p"
def rfwB := ofString "rfw_b"
def rfwK := ofString "rfw_k"
def rfwX := ofString "rfw_x"
def rfwA1 := ofString "rfw_a1"
def rfwA2 := ofString "rfw_a2"
def rfwA3 := ofString "rfw_a3"
def rfwQ := ofString "rfw_q"
def rfwY := ofString "rfw_y"
def rfwZ := ofString "rfw_z"
def rfwV := ofString "rfw_v"
def rfwM1 := ofString "rfw_m1"
def rfwM2 := ofString "rfw_m2"
def rfwM3 := ofString "rfw_m3"
def rfwW := ofString "rfw_w"
def rfwR := ofString "rfw_r"
def fRfv := ofString "replaceFVarsCanon"

def rfwParams : List MlS := [pFu, pH, rfwM, rfwP]
def rfwLocals : List MlS := gaaLocals ++ [rfwB, rfwK, rfwX, rfwA1, rfwA2, rfwA3, rfwQ, rfwY, rfwZ, rfwV, rfwM1, rfwM2,
  rfwM3, rfwW, rfwR]

/-- Return the pair `[r, memo]`. -/
def rfwRet (C : Ctx) (r m : MlS) : ProgHOL 64 := alloc2 C rfwR (vv r) (vv m) (.return (vv rfwR))

/-- One child walked: `Q := rfv(child, memo)`, then its result in `y` and the memo in `m'`. -/
def rfwCall (x child memo y m' : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, x), none)) fRfv [.op .sub [vv pFu, .const 1], vv child, vv memo, vv rfwP])
  (.seq (.assign .local y (.load .one (vv x)))
  (.seq (.assign .local m' (.load .one (.op .add [vv x, .const 8]))) rest))

/-- Memoise `h ↦ w` over the memo in `m`, and return. -/
def rfwSet (C : Ctx) (m : MlS) : ProgHOL 64 :=
  alloc3 C rfwM3 (vv pH) (vv rfwW) (vv m) (rfwRet C rfwW rfwM3)

def rfwBin (C : Ctx) (f : MlS) : ProgHOL 64 :=
  rfwCall rfwQ rfwA1 rfwM rfwY rfwM1 (rfwCall rfwQ rfwA2 rfwM1 rfwZ rfwM2
    (.seq (.call (some (some (.local, rfwW), none)) f [vv rfwY, vv rfwZ]) (rfwSet C rfwM2)))

def rfwLet (C : Ctx) : ProgHOL 64 :=
  rfwCall rfwQ rfwA1 rfwM rfwY rfwM1 (rfwCall rfwQ rfwA2 rfwM1 rfwZ rfwM2 (rfwCall rfwQ rfwA3 rfwM2 rfwV rfwM3
    (.seq (.call (some (some (.local, rfwW), none)) fInternLet [vv rfwY, vv rfwZ, vv rfwV])
      (alloc3 C rfwM2 (vv pH) (vv rfwW) (vv rfwM3) (rfwRet C rfwW rfwM2)))))

def rfwProj (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .notLower (vv rfwB) (.const (BitVec.ofNat 64 (2 ^ 63)))) hang
  (rfwCall rfwQ rfwA2 rfwM rfwY rfwM1
    (.seq (.call (some (some (.local, rfwW), none)) fInternProj [vv rfwA1, vv rfwY, vv rfwB]) (rfwSet C rfwM1)))

/-- The fvar arm: the index (one limb at most, else past every opener), then the opener or `h`. -/
def rfwFvarIdx (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rfwK (.load .one (vv rfwP)))
  (.ite (.cmp .lower (vv rfwB) (vv rfwK))
    (.seq (.assign .local rfwX (.load .one (.op .add [vv rfwP, .op .add [.panop .mul [vv rfwB, .const 8], .const 8]])))
      (rfwRet C rfwX rfwM))
    (rfwRet C pH rfwM))

def rfwFvar (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local rfwB (.const 0)) (rfwFvarIdx C))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local rfwB (.load .one (.op .add [vv lRp, .const 8]))) (rfwFvarIdx C))
      (rfwRet C pH rfwM))

/-- A compound node: the view's children loaded, then the memo, then the arm. -/
def rfwNode (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rfwA1 (.load .one (vv lRp)))
  (.seq (.assign .local rfwA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lDg) (.const 7)) (.seq (.assign .local rfwA3 (.load .one (.op .add [vv lRp, .const 16])))
      (rfwMemo C (rfwLet C)))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local rfwB (.const 0)) (rfwMemo C (rfwProj C)))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local rfwB (.load .one (.op .add [vv lRp, .const 16]))) (rfwMemo C (rfwProj C))) hang))
  (rfwMemo C (.ite (.cmp .equal (vv lDg) (.const 4)) (rfwBin C fInternApp)
    (.ite (.cmp .equal (vv lDg) (.const 5)) (rfwBin C fInternLam) (rfwBin C fInternForallE)))))))
where
  rfwMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
    .seq (.call (some (some (.local, rfwX), none)) fMemoFind [vv rfwM, vv pH])
    (.ite (.cmp .equal (vv rfwX) (.const 0)) arm
      (.seq (.assign .local rfwX (.op .sub [vv rfwX, .const 1])) (rfwRet C rfwX rfwM)))

def rfwBody (C : Ctx) : ProgHOL 64 := prologue rfwLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (rfwFvar C)
  (.ite (.cmp .lower (vv lDg) (.const 4)) (rfwRet C pH rfwM)
  (.ite (.cmp .equal (vv lDg) (.const 8)) (rfwRet C pH rfwM) (rfwNode C))))))))

/-- The code `replaceFVarsCanon` runs. -/
structure RFWCodes (C : Ctx) : Prop where
  self : C.code.lookup fRfv = some (rfwParams.map (fun p => (p, ShapeHOL.one)), rfwBody C, .one)
  mf : C.code.lookup fMemoFind = some (mmfParams.map (fun p => (p, ShapeHOL.one)), mmfBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  lam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  fa : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  lt : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  pj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)

section
variable {σ : Type}

theorem rfw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rfwLocals → (ctxEnv C ++ rfwParams.zip vals).get x = none :=
  Knot.params_none C rfwLocals rfwParams vals (by decide) (by decide)

/-- The walk's answer: a pair `[r, memo]`, the memo represented. -/
def PostRF (C : Ctx) (r : EIdx × Std.HashMap EIdx EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' op mw', C.H <+: H' ∧ w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧ H'[op + 1]? = some mw' ∧
    MemoRep C.HB H' mw' r.2 ∧ SR (ctxH C H') s' st

theorem postRF_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRF C a w s' st → PostRF C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', op, mw', hp, hw, h1, h2, h3, hs⟩ => ⟨H', op, mw', hp, hw, h1, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

/-- The walk at fuel `n`, from any heap holding the openers' block. -/
def RFRec (C : Ctx) (pfvs : List EIdx) (pp n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx EIdx) (mw : BitVec 64) (H : List (BitVec 64)) (s : AState), C.H <+: H →
    BlkAt H pp (pfvs.map Enc.idxW) → MemoRep C.HB H mw memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (rfwParams.zip [BitVec.ofNat 64 n, Enc.idxW h, mw, cellA C pp])) (rfwBody C) s
      (replaceFVarsGo (.canon pfvs) memo n h) (PostRF (ctxH C H))

/-- One child walked (`rfwCall`). -/
theorem rfw_call {β : Type} (C : Ctx) (hc : RFWCodes C) (pfvs : List EIdx) (pp n : Nat) (ih : RFRec (σ := σ) C pfvs pp n)
    {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx × Std.HashMap EIdx EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (hp : C.H <+: H)
    (hpf : BlkAt H pp (pfvs.map Enc.idxW)) (x child memo y m' : MlS)
    (hx : x ∈ ctxLocals ++ rfwLocals ∧ y ∈ ctxLocals ++ rfwLocals ∧ m' ∈ ctxLocals ++ rfwLocals)
    (hne : y ≠ x ∧ m' ≠ x ∧ m' ≠ y)
    (c : EIdx) (memo0 : Std.HashMap EIdx EIdx) (mw : BitVec 64) (hm : MemoRep C.HB H mw memo0)
    (gF : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (gC : Γ.get child = some (Enc.idxW c))
    (gM : Γ.get memo = some mw) (gP : Γ.get rfwP = some (cellA C pp))
    (hk : ∀ (r : EIdx × Std.HashMap EIdx EIdx) (H' : List (BitVec 64)) (op : Nat) (mw' : BitVec 64) (s' : AState),
      H <+: H' → MemoRep C.HB H' mw' r.2 →
      SpecR (Inv (ctxH C H') s' ((m', mw') :: (y, Enc.idxW r.1) :: (x, cellA C op) :: Γ) [] (ctxLocals ++ rfwLocals))
        rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ rfwLocals)) (rfwCall x child memo y m' rest) s
      (replaceFVarsGo (.canon pfvs) memo0 n c >>= k) R := by
  unfold rfwCall
  refine specR_callNIH (C := ctxH C H) x fRfv rfwParams [.op .sub [vv pFu, .const 1], vv child, vv memo, vv rfwP]
    (rfwBody C) [BitVec.ofNat 64 n, Enc.idxW c, mw, cellA C pp] (by decide) rfl hx.1 hc.self
    ⟨by simp only [sev, sev_vv, gF]; simp; exact ofNat_succ_sub_one n, by simp [sev, gC], by simp [sev, gM],
      by simp [sev, gP], trivial⟩
    (PostRF (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRep C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rfwParams _ rfl hlk) (ih c memo0 mw H s hp hpf hm))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, h2, h3⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) y (vv x) op _ h1 hx.2.1 (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) m' _ (op + 1) _ h2 hx.2.2
    (by simp only [sev, sev_vv, Env.get_cons, if_neg (show x ≠ y from fun e => hne.1 e.symm), if_true]; simp; exact cellA_add8 C op) ?_
  exact hk r H1 op mw' s1 hp1 h3

end

section
variable {σ : Type}

section
variable {σ : Type}

theorem memoRep_insert {HB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {mw : BitVec 64}
    {m : Std.HashMap EIdx EIdx} (h r : EIdx) (hm : MemoRep HB H mw m)
    (h0 : H[o]? = some (Enc.idxW h)) (h1 : H[o + 1]? = some (Enc.idxW r)) (h2 : H[o + 2]? = some mw) :
    MemoRep HB H (HB + BitVec.ofNat 64 (8 * o)) (m.insert h r) := by
  obtain ⟨L, hL, hlk⟩ := hm
  refine ⟨(h, r) :: L, ⟨o, mw, rfl, h0, h1, h2, hL⟩, fun k => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  by_cases hk : h = k
  · subst hk; simp [List.lookup]
  · have e1 : (h == k) = false := by simpa using hk
    have e2 : (k == h) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hk e.symm
    simp only [e1, Bool.false_eq_true, ite_false, List.lookup, e2, hlk]

/-- Memoise `h ↦ r` over the memo in `m` (into `t`), and return `[r, memo']`. -/
theorem rfw_set (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h r : EIdx) (m t : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx EIdx) (hbH : Hb <+: H)
    (hm : MemoRep C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get rfwW = some (Enc.idxW r))
    (gM : Γ.get m = some mw) (ht : t ∈ ctxLocals ++ rfwLocals) (htW : t ≠ rfwW ∧ t ≠ rfwR) (hmt : m ≠ t) (htH : t ≠ pH) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfwLocals))
      (alloc3 C t (vv pH) (vv rfwW) (vv m) (rfwRet C rfwW t)) s (pure (r, memo.insert h r)) (PostRF (ctxH C Hb)) := by
  refine specR_alloc3I (ctxOK_H hok H) t (vv pH) (vv rfwW) (vv m) (Enc.idxW h) (Enc.idxW r) mw ht
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htH e.symm)]; exact gH)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg hmt]; exact gM) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have h3 := img3_prefix H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have hp23 : H <+: _ := (hp2 : H <+: H2).trans h3
  have hm3 := memoRep_insert h r (memoRep_mono hp23 hm) g0 g1 g2
  unfold rfwRet
  refine specR_alloc2I (ctxOK_H hok _) rfwR (vv rfwW) (vv t) (Enc.idxW r) (cellA C H2.length) (by decide)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide), if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.2 e)]; simp; rfl)
    (fun H4 ws4 hp4 hws4 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  have h4 := img2_prefix H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  exact specR_returnI (vv rfwR) (cellA C H4.length) (by simp [sev, Env.get_cons]; rfl) (fun tt htt =>
    ⟨_, H4.length, cellA C H2.length, hbH.trans (hp23.trans ((hp4 : _ <+: H4).trans h4)), rfl, k0, k1,
      memoRep_mono ((hp4 : _ <+: H4).trans h4) hm3, sr_of_eq htt.sr rfl rfl rfl rfl⟩)

end

set_option maxHeartbeats 16000000 in
/-- **`replaceFVarsGo` at the canonical map**. -/
theorem rfw_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RFWCodes C)
    (pfvs : List EIdx) (pp : Nat) : ∀ n, n < 2 ^ 64 → RFRec (σ := σ) C pfvs pp n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo mw H s hp hpf hm
    refine specR_prologue (postRF_locals _) (rfw_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rfwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro hn h memo mw H s hp hpf hm
    have ih' := ih (by omega)
    refine specR_prologue (postRF_locals _) (rfw_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rfwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [replaceFVarsGo]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, rfwParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s = .ok (v, s) by rw [view_run, hv]) ?_
    -- the leaves
    have hleaf : ∀ (Γ : Env) (M : Mem), Γ.get pH = some (Enc.idxW h) → Γ.get rfwM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfwLocals)) (rfwRet C pH rfwM) s (pure (h, memo))
          (PostRF (ctxH C H)) := by
      intro Γ M gH gM
      unfold rfwRet
      refine specR_alloc2I (ctxOK_H hok H) rfwR (vv pH) (vv rfwM) (Enc.idxW h) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons, gH]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW h) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW h) mw hws
      exact specR_returnI (vv rfwR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hpH : ∀ (Γ0 : Env), Γ0 = ctxEnv (ctxH C H) ++ rfwParams.zip [BitVec.ofNat 64 (n + 1), Enc.idxW h, mw, cellA C pp] →
        True := fun _ _ => trivial
    -- the memo step of a compound node
    have hmemo : ∀ (arm : ProgHOL 64) (mnone : AM (EIdx × Std.HashMap EIdx EIdx)) (Γ : Env) (M : Mem),
        Γ.get rfwM = some mw → Γ.get pH = some (Enc.idxW h) →
        (memo[h]? = none → SpecR (σ := σ) (Inv (ctxH C H) s ((rfwX, 0) :: Γ) [] (ctxLocals ++ rfwLocals)) arm s mnone
          (PostRF (ctxH C H))) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfwLocals)) (rfwNode.rfwMemo C arm) s
          (match memo[h]? with
            | some r => pure (r, memo)
            | none => mnone) (PostRF (ctxH C H)) := by
      intro arm mnone Γ M gM gH harm
      obtain ⟨L, hL, hlk⟩ := id hm
      unfold rfwNode.rfwMemo
      rw [hlk h]
      refine specR_pureBind (L.lookup h) ?_
      refine specR_callNIM rfwX fMemoFind mmfParams [vv rfwM, vv pH] mmfBody [mw, Enc.idxW h] (by decide) rfl (by decide)
        hc.mf ⟨by simp [sev, gM], by simp [sev, gH], trivial⟩
        (fun a w s' st => (pure (L.lookup h) : AM (Option EIdx)) s = .ok (a, s') ∧ PostOE (ctxH C H) a w s' st)
        (fun _ _ _ _ h => h.2.2)
        (fun u hu _ hlk' => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mmfParams _ rfl hlk')
          (mmf_spec C hok hc.mf H h L mw s hL)))
        (fun a w s1 st ⟨hrun, hw, _⟩ => ?_)
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hra, hs1⟩ := hrun
      subst hw; subst hs1; subst hra
      rcases hfo : L.lookup h with _ | r
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact harm (by rw [hlk h, hfo])
      have hr1 : Enc.idxW r + 1 ≠ 0#64 := by
        intro e; have := congrArg BitVec.toNat e
        have hlt : (Enc.idxW r).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact r.word.toNat_lt
        simp [BitVec.toNat_add] at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hr1)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_assignI rfwX _ (Enc.idxW r) (by decide)
        (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      unfold rfwRet
      refine specR_alloc2I (ctxOK_H hok H) rfwR (vv rfwX) (vv rfwM) (Enc.idxW r) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW r) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW r) mw hws
      exact specR_returnI (vv rfwR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    cases v with
    | bvar i =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
    | sort u =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
    | const c us =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
    | lit l =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
    | fvar i ty =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      rw [fvMapAt]
      simp only [pure_bind]
      unfold rfwFvar
      have hlen1 : (encEView (.fvar i ty)).length = 1 + (Enc.limbs i).length := by simp [encEView, Enc.encFVar]; omega
      have hpl := blkAt_len_le hpf
      simp only [List.length_map] at hpl
      refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
      have hHN' : H.length ≤ C.HN := hHN
      have hlay := hok.heapLay
      -- the opener at a small index, or `h`
      have hidx : ∀ (Γ : Env) (M : Mem), i < 2 ^ 64 → Γ.get rfwB = some (BitVec.ofNat 64 i) →
          Γ.get pH = some (Enc.idxW h) → Γ.get rfwM = some mw → Γ.get rfwP = some (cellA C pp) →
          SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfwLocals)) (rfwFvarIdx C) s
            (match pfvs[i]? with
              | some r => pure (r, memo)
              | none => pure (h, memo)) (PostRF (ctxH C H)) := by
        intro Γ M hi gB gH gM gP
        unfold rfwFvarIdx
        refine UD.specR_heapLoadI' (C := ctxH C H) rfwK (vv rfwP) pp _ hpf.1 (by decide) (by simp [sev, gP]; rfl) ?_
        have hlw := ConPanqueque.T.Decl.nd_lt_iff i pfvs.length hi (by omega)
        by_cases hlt : i < pfvs.length
        · rw [List.getElem?_eq_getElem hlt]
          refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [gB, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hlt])
            (fun _ => ?_) (fun h => absurd h (by decide))
          have hx := hpf.2 i (by simp; omega)
          simp only [List.getElem_map] at hx
          refine UD.specR_heapLoadI' (C := ctxH C H) rfwX _ (pp + 1 + i) _ hx (by decide)
            (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [gB, gP]; exact cellA_mulIdx C pp i (by omega)) ?_
          unfold rfwRet
          refine specR_alloc2I (ctxOK_H hok H) rfwR (vv rfwX) (vv rfwM) (Enc.idxW pfvs[i]) mw (by decide)
            (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
            (fun H2 ws hp2 hws => ?_)
          obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW pfvs[i]) mw hws
          have h2 := img2_prefix H2 ws (Enc.idxW pfvs[i]) mw hws
          exact specR_returnI (vv rfwR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
            ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
              sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · rw [List.getElem?_eq_none (by omega)]
          refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [gB, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
            (fun h => absurd rfl h) (fun _ => ?_)
          exact hleaf _ _ (by simp +decide [Env.get_cons, gH]) (by simp +decide [Env.get_cons, gM])
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI rfwB (.const 0) 0 (by decide) rfl ?_
        exact hidx _ _ (by decide) (by simp) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' rfwB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 i) [] (M := [])
              simpa [encEView, Enc.encFVar, hl] using this) ?_
        exact hidx _ _ ib (by simp) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
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
      rw [List.getElem?_eq_none (by omega)]
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
    | app a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfwNode
      refine specR_loadI' rfwA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rfwA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rfwBin
      simp only [bind_assoc]
      refine rfw_call C hc pfvs pp n ih' H hp hpf rfwQ rfwA1 rfwM rfwY rfwM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rfw_call C hc pfvs pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rfwQ rfwA2 rfwM1 rfwZ rfwM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internAppI ra (ctxOK_H hok H2) hc.app rfwW (vv rfwY) (vv rfwZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rfwSet
      exact rfw_set C hok H2 H h w rfwM2 rfwM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | lam a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfwNode
      refine specR_loadI' rfwA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rfwA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rfwBin
      simp only [bind_assoc]
      refine rfw_call C hc pfvs pp n ih' H hp hpf rfwQ rfwA1 rfwM rfwY rfwM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rfw_call C hc pfvs pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rfwQ rfwA2 rfwM1 rfwZ rfwM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internLamI ra (ctxOK_H hok H2) hc.lam rfwW (vv rfwY) (vv rfwZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rfwSet
      exact rfw_set C hok H2 H h w rfwM2 rfwM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | forallE a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfwNode
      refine specR_loadI' rfwA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rfwA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfwBin
      simp only [bind_assoc]
      refine rfw_call C hc pfvs pp n ih' H hp hpf rfwQ rfwA1 rfwM rfwY rfwM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rfw_call C hc pfvs pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rfwQ rfwA2 rfwM1 rfwZ rfwM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internForallEI ra (ctxOK_H hok H2) hc.fa rfwW (vv rfwY) (vv rfwZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rfwSet
      exact rfw_set C hok H2 H h w rfwM2 rfwM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | letE ty v b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfwNode
      refine specR_loadI' rfwA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW v, Enc.idxW b] []) ?_
      refine specR_loadI' rfwA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' rfwA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v) (Enc.idxW b) [] []) ?_
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun _ => ?_)
      unfold rfwLet
      simp only [bind_assoc]
      refine rfw_call C hc pfvs pp n ih' H hp hpf rfwQ rfwA1 rfwM rfwY rfwM1 (by decide) (by decide) ty memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨t2, m1⟩ := r1
      simp only
      refine rfw_call C hc pfvs pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rfwQ rfwA2 rfwM1 rfwZ rfwM2 (by decide)
        (by decide) v m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨v2, m2⟩ := r2
      simp only
      refine rfw_call C hc pfvs pp n ih' H2 ((hp.trans hp1).trans hp2) (blkAt_mono hpf (hp1.trans hp2)) rfwQ rfwA3 rfwM2
        rfwV rfwM3 (by decide) (by decide) b m2 mw2 hm2 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r3 H3 op3 mw3 s3 hp3 hm3 => ?_)
      obtain ⟨b2, m3⟩ := r3
      simp only
      refine specR_internLetI ra (ctxOK_H hok H3) hc.lt rfwW (vv rfwY) (vv rfwZ) (vv rfwV) t2 v2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv])
        (fun w s4 => ?_)
      simp only [pure_bind]
      exact rfw_set C hok H3 H h w rfwM3 rfwM2 mw3 m3 ((hp1.trans hp2).trans hp3) hm3 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by decide)
        ⟨by decide, by decide⟩ (by decide) (by decide)
    | proj nm i e =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfwNode
      have hlenp : (encEView (.proj nm i e)).length = 2 + (Enc.limbs i).length := by simp [encEView, Enc.encProj]; omega
      refine specR_loadI' rfwA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW nm) (Enc.idxW e :: Enc.limbs i) []) ?_
      refine specR_loadI' rfwA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW nm) (Enc.idxW e) (Enc.limbs i) []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_assignI rfwB (.const 0) 0 (by decide) rfl ?_
        refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun _ => ?_)
        unfold rfwProj
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only [bind_assoc]
        refine rfw_call C hc pfvs pp n ih' H hp hpf rfwQ rfwA2 rfwM rfwY rfwM1 (by decide) (by decide) e memo mw hm
          (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
        obtain ⟨u2, m1⟩ := r1
        simp only
        refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rfwW (vv rfwA1) (vv rfwY) (vv rfwB) nm _ u2 (by decide) (by decide)
          (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun w s2 => ?_)
        simp only [pure_bind]
        unfold rfwSet
        exact rfw_set C hok H1 H h w rfwM1 rfwM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
          (by decide) (by decide)

      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_loadI' rfwB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev, Env.get_cons]) rfl
          (by simpa [encEView, Enc.encProj, hl] using wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] []) ?_
        by_cases h63 : i < 2 ^ 63
        · have hi63 : i < 2 ^ 63 := h63
          refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun _ => ?_)
          unfold rfwProj
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
            (fun h => absurd rfl h) (fun _ => ?_)
          simp only [bind_assoc]
          refine rfw_call C hc pfvs pp n ih' H hp hpf rfwQ rfwA2 rfwM rfwY rfwM1 (by decide) (by decide) e memo mw hm
            (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
          obtain ⟨u2, m1⟩ := r1
          simp only
          refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rfwW (vv rfwA1) (vv rfwY) (vv rfwB) nm _ u2 (hi63) (by decide)
            (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun w s2 => ?_)
          simp only [pure_bind]
          unfold rfwSet
          exact rfw_set C hok H1 H h w rfwM1 rfwM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
            (by decide) (by decide)

        · refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfwParams, ctxEnv]) (fun _ => ?_)
          unfold rfwProj
          exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
            (fun _ => specR_hangI) (fun h => absurd h (by decide))
      have hge : 2 ≤ (Enc.limbs i).length := by
        have := (Big.limbs_length_lt_iff i 1).not.mpr (by simp [Big.B]; omega); omega
      have hsh' : 2 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlenp]; exact hlen
      have hn2 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 2#64 := by
        intro e'; have := congrArg BitVec.toNat e'; simp at this; omega
      have hn3 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 3#64 := by
        intro e'; have := congrArg BitVec.toNat e'; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn2)
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn3)
        (fun h => absurd rfl h) (fun _ => specR_hangI)

end

/-! ## `targetCanonParams` -/

def tcpE := ofString "tcp_e"
def tcpP := ofString "tcp_p"
def tcpQ := ofString "tcp_q"
def tcpR := ofString "tcp_r"
def fTcp := ofString "targetCanonParams"

def tcpParams : List MlS := [tcpE, tcpP]
def tcpLocals : List MlS := [tcpQ, tcpR]

def tcpBody : ProgHOL 64 := prologue tcpLocals
  (.seq (.call (some (some (.local, tcpQ), none)) fRfv [.const (BitVec.ofNat 64 coreWalkFuel), vv tcpE, .const 0, vv tcpP])
  (.seq (.assign .local tcpR (.load .one (vv tcpQ))) (.return (vv tcpR))))

section
variable {σ : Type}

theorem tcp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tcpLocals → (ctxEnv C ++ tcpParams.zip vals).get x = none :=
  Knot.params_none C tcpLocals tcpParams vals (by decide) (by decide)

/-- **`targetCanonParams pfvs e`** (the openers' block at `pp`). -/
theorem tcp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RFWCodes C)
    (hct : C.code.lookup fTcp = some (tcpParams.map (fun p => (p, ShapeHOL.one)), tcpBody, .one))
    (pfvs : List EIdx) (pp : Nat) (H : List (BitVec 64)) (hp : C.H <+: H) (hpf : BlkAt H pp (pfvs.map Enc.idxW))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre (ctxH C H) s (tcpParams.zip [Enc.idxW e, cellA C pp])) tcpBody s (targetCanonParams pfvs e)
      (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (tcp_none _ _) ?_
  unfold targetCanonParams replaceFVars
  refine specR_callNIH (C := ctxH C H) tcpQ fRfv rfwParams [.const (BitVec.ofNat 64 coreWalkFuel), vv tcpE, .const 0, vv tcpP]
    (rfwBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0, cellA C pp] (by decide) rfl (by decide) hc.self
    ⟨rfl, by simp +decide [sev, Env.get, tcpParams, ctxEnv], rfl, by simp +decide [sev, Env.get, tcpParams, ctxEnv], trivial⟩
    (PostRF (ctxH C H)) (fun r w _ H' => ∃ op, w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1))
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, _, _, hsr⟩ => ⟨H', hp', ⟨op, hw, h1⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rfwParams _ rfl hlk)
      (rfw_spec ra C hok hc pfvs pp coreWalkFuel CV.coreWalkFuel_lt e ∅ 0 H s hp hpf
        ⟨[], rfl, fun k => by simp⟩))
    (fun r w s1 H1 hp1 ⟨op, hw, h1⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) tcpR (vv tcpQ) op _ h1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
