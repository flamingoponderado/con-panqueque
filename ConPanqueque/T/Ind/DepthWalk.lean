import ConPanqueque.T.Ind.NestOcc

/-!
# `depth`: the longest root-to-leaf path, memoised (the fuel of the positivity walk)

The twin's `HashMap` memo mirrored as cells `[key, value, next]`; the memo lookup is `memoFindB`'s code
at Nat values.  Pancake hangs once a depth reaches `2^62 - 1` (soundness only).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- An association list of Nat values. -/
def MemoListN (HB : BitVec 64) (H : List (BitVec 64)) : BitVec 64 → List (EIdx × Nat) → Prop
  | w, [] => w = 0
  | w, (k, v) :: L => ∃ o w', w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some (Enc.idxW k) ∧
      H[o + 1]? = some (BitVec.ofNat 64 v) ∧ H[o + 2]? = some w' ∧ MemoListN HB H w' L

theorem memoListN_mono {HB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') :
    ∀ (L : List (EIdx × Nat)) (w : BitVec 64), MemoListN HB H w L → MemoListN HB H' w L
  | [], _, h => h
  | (_, _) :: L, _, ⟨o, w', h1, h2, h3, h4, h5⟩ =>
    ⟨o, w', h1, get_prefix h2 hp, get_prefix h3 hp, get_prefix h4 hp, memoListN_mono hp L w' h5⟩

/-- A memo of depths, each below `2^62`. -/
def MemoRepN (HB : BitVec 64) (H : List (BitVec 64)) (w : BitVec 64) (m : Std.HashMap EIdx Nat) : Prop :=
  ∃ L, MemoListN HB H w L ∧ (∀ k, m[k]? = L.lookup k) ∧ ∀ p ∈ L, p.2 < 2 ^ 62

theorem memoRepN_mono {HB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') {w : BitVec 64}
    {m : Std.HashMap EIdx Nat} (h : MemoRepN HB H w m) : MemoRepN HB H' w m :=
  let ⟨L, h1, h2, h3⟩ := h; ⟨L, memoListN_mono hp L w h1, h2, h3⟩

theorem lookup_mem {L : List (EIdx × Nat)} {k : EIdx} {v : Nat} (h : L.lookup k = some v) : (k, v) ∈ L := by
  induction L with
  | nil => simp [List.lookup] at h
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have hb : (k == a) = false := by simpa using hk
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

section
variable {σ : Type}

/-- An optional Nat as `optWG ofNat`; the heap kept. -/
def PostON2 (C : Ctx) (o : Option Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = optWG (BitVec.ofNat 64) o ∧ SR C s' st

theorem postON2_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostON2 C a w s' st → PostON2 C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

/-- **`memoFindB`'s code at Nat values**: the list's lookup as `optWG ofNat`. -/
theorem mbn_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMemoFindB = some (mbfParams.map (fun p => (p, ShapeHOL.one)), mbfBody, .one))
    (H : List (BitVec 64)) (k : EIdx) :
    ∀ (L : List (EIdx × Nat)) (w : BitVec 64) (s : AState), MemoListN C.HB H w L →
      SpecR (σ := σ) (Pre (ctxH C H) s (mbfParams.zip [w, Enc.idxW k])) mbfBody s (pure (L.lookup k))
        (PostON2 (ctxH C H)) := by
  intro L
  induction L with
  | nil =>
    intro w s hw
    refine specR_prologue (postON2_locals _) (mbf_none _ _) ?_
    simp only [MemoListN] at hw; subst hw
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mbfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons kv L ih =>
    intro w s hw
    obtain ⟨k0, v0⟩ := kv
    obtain ⟨o, w', rfl, h0, h1, h2, hL⟩ := hw
    refine specR_prologue (postON2_locals _) (mbf_none _ _) ?_
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
      exact specR_returnI _ (BitVec.ofNat 64 v0 + 1) (by simp [sev, Env.get_cons])
        (fun t ht => ⟨by simp [optWG, List.lookup], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hw : Enc.idxW k0 ≠ Enc.idxW k := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H) mbfX _ (o + 2) _ h2 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv]; exact cellA_add_ofNat C o 2) ?_
    have hlk : ((k0, v0) :: L).lookup k = L.lookup k := by
      have hb : (k == k0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he e.symm
      simp only [List.lookup, hb]
    rw [hlk]
    refine specR_congr (m' := (pure (L.lookup k) : AM (Option Nat)) >>= fun r => pure r) (by simp) ?_
    refine specR_callNIM mbfR fMemoFindB mbfParams [vv mbfX, vv mbfK] mbfBody [w', Enc.idxW k] (by decide) rfl (by decide) hc
      ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mbfParams, ctxEnv], trivial⟩
      (PostON2 (ctxH C H)) (fun _ _ _ _ h => h.2)
      (fun u hu _ hlk' => Knot.specR_of_pre u (pre_of_lookups hu mbfParams _ rfl hlk') (ih w' s hL))
      (fun r w2 s1 st ⟨hw2, _⟩ => ?_)
    subst hw2
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def dptM := ofString "dpt_m"
def dptX := ofString "dpt_x"
def dptA1 := ofString "dpt_a1"
def dptA2 := ofString "dpt_a2"
def dptA3 := ofString "dpt_a3"
def dptQ := ofString "dpt_q"
def dptY := ofString "dpt_y"
def dptZ := ofString "dpt_z"
def dptV := ofString "dpt_v"
def dptM1 := ofString "dpt_m1"
def dptM2 := ofString "dpt_m2"
def dptM3 := ofString "dpt_m3"
def dptW := ofString "dpt_w"
def dptR := ofString "dpt_r"
def fDepth := ofString "depthGo"

def dptParams : List MlS := [pFu, pH, dptM]
def dptLocals : List MlS := gaaLocals ++ [dptX, dptA1, dptA2, dptA3, dptQ, dptY, dptZ, dptV, dptM1, dptM2, dptM3, dptW,
  dptR]

def dptRet (C : Ctx) (r : ExpHOL 64) (m : MlS) : ProgHOL 64 := alloc2 C dptR r (vv m) (.return (vv dptR))

def dptCall (child memo y m' : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, dptQ), none)) fDepth [.op .sub [vv pFu, .const 1], vv child, vv memo])
  (.seq (.assign .local y (.load .one (vv dptQ)))
  (.seq (.assign .local m' (.load .one (.op .add [vv dptQ, .const 8]))) rest))

def dptSet (C : Ctx) (m : MlS) : ProgHOL 64 :=
  alloc3 C dptM3 (vv pH) (vv dptW) (vv m) (dptRet C (vv dptW) dptM3)

/-- `W + 1` memoised, hanging at the bound. -/
def dptInc (C : Ctx) (m : MlS) : ProgHOL 64 :=
  .ite (.cmp .notLower (vv dptW) (.const (BitVec.ofNat 64 (2 ^ 62 - 1)))) hang
    (.seq (.assign .local dptW (.op .add [vv dptW, .const 1])) (dptSet C m))

/-- `W := max a b`, then `rest`. -/
def maxInto (a b : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower (vv a) (vv b)) (.seq (.assign .local dptW (vv b)) rest) (.seq (.assign .local dptW (vv a)) rest)

def dptBin (C : Ctx) : ProgHOL 64 :=
  dptCall dptA1 dptM dptY dptM1 (dptCall dptA2 dptM1 dptZ dptM2 (maxInto dptY dptZ (dptInc C dptM2)))

def dptLet (C : Ctx) : ProgHOL 64 :=
  dptCall dptA1 dptM dptY dptM1 (dptCall dptA2 dptM1 dptZ dptM2 (dptCall dptA3 dptM2 dptV dptM1
    (maxInto dptY dptZ (.seq (.assign .local dptY (vv dptW)) (maxInto dptY dptV (dptInc C dptM1))))))

def dptProj (C : Ctx) : ProgHOL 64 :=
  dptCall dptA2 dptM dptY dptM1 (.seq (.assign .local dptW (vv dptY)) (dptInc C dptM1))

def dptMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, dptX), none)) fMemoFindB [vv dptM, vv pH])
  (.ite (.cmp .equal (vv dptX) (.const 0)) arm
    (.seq (.assign .local dptX (.op .sub [vv dptX, .const 1])) (dptRet C (vv dptX) dptM)))

def dptNode (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local dptA1 (.load .one (vv lRp)))
  (.seq (.assign .local dptA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local dptA3 (.load .one (.op .add [vv lRp, .const 16]))) (dptMemo C (dptLet C)))
  (.ite (.cmp .equal (vv lDg) (.const 9)) (dptMemo C (dptProj C)) (dptMemo C (dptBin C)))))

def dptBody (C : Ctx) : ProgHOL 64 := prologue dptLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
  (.ite (.cmp .lower (vv lDg) (.const 4)) (dptRet C (.const 1) dptM)
  (.ite (.cmp .equal (vv lDg) (.const 8)) (dptRet C (.const 1) dptM) (dptNode C)))))))

/-- The code `depthGo` runs. -/
structure DPTCodes (C : Ctx) : Prop where
  self : C.code.lookup fDepth = some (dptParams.map (fun p => (p, ShapeHOL.one)), dptBody C, .one)
  mbf : C.code.lookup fMemoFindB = some (mbfParams.map (fun p => (p, ShapeHOL.one)), mbfBody, .one)

section
variable {σ : Type}

theorem dpt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dptLocals → (ctxEnv C ++ dptParams.zip vals).get x = none :=
  Knot.params_none C dptLocals dptParams vals (by decide) (by decide)

/-- The walk's answer: a pair `[depth, memo]`. -/
def PostDW (C : Ctx) (r : Nat × Std.HashMap EIdx Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' op mw', C.H <+: H' ∧ w = cellA C op ∧ H'[op]? = some (BitVec.ofNat 64 r.1) ∧ r.1 < 2 ^ 62 ∧
    H'[op + 1]? = some mw' ∧ MemoRepN C.HB H' mw' r.2 ∧ SR (ctxH C H') s' st

theorem postDW_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostDW C a w s' st → PostDW C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', op, mw', hp, hw, h1, hb, h2, h3, hs⟩ =>
    ⟨H', op, mw', hp, hw, h1, hb, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

theorem dpt_ret (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64)) (hbH : Hb <+: H)
    (r : ExpHOL 64) (d : Nat) (hd : d < 2 ^ 62) (m : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx Nat)
    (hm : MemoRepN C.HB H mw memo) (hr : ∀ v, sev ((dptR, v) :: Γ) r = some (BitVec.ofNat 64 d))
    (gM : ∀ v, sev ((dptR, v) :: Γ) (vv m) = some mw) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ dptLocals)) (dptRet C r m) s (pure (d, memo))
      (PostDW (ctxH C Hb)) := by
  unfold dptRet
  refine specR_alloc2I (ctxOK_H hok H) dptR r (vv m) (BitVec.ofNat 64 d) mw (by decide) hr gM (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1⟩ := img2_get H2 ws (BitVec.ofNat 64 d) mw hws
  have h2 := img2_prefix H2 ws (BitVec.ofNat 64 d) mw hws
  exact specR_returnI (vv dptR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, H2.length, mw, hbH.trans ((hp2 : H <+: H2).trans h2), rfl, g0, hd, g1,
      memoRepN_mono ((hp2 : H <+: H2).trans h2) hm, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem memoRepN_insert {HB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {mw : BitVec 64}
    {m : Std.HashMap EIdx Nat} (h : EIdx) (r : Nat) (hr : r < 2 ^ 62) (hm : MemoRepN HB H mw m)
    (h0 : H[o]? = some (Enc.idxW h)) (h1 : H[o + 1]? = some (BitVec.ofNat 64 r)) (h2 : H[o + 2]? = some mw) :
    MemoRepN HB H (HB + BitVec.ofNat 64 (8 * o)) (m.insert h r) := by
  obtain ⟨L, hL, hlk, hb⟩ := hm
  refine ⟨(h, r) :: L, ⟨o, mw, rfl, h0, h1, h2, hL⟩, fun k => ?_, fun p hp => ?_⟩
  · rw [Std.HashMap.getElem?_insert]
    by_cases hk : h = k
    · subst hk; simp [List.lookup]
    · have e1 : (h == k) = false := by simpa using hk
      have e2 : (k == h) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hk e.symm
      simp only [e1, Bool.false_eq_true, ite_false, List.lookup, e2, hlk]
  · rcases List.mem_cons.mp hp with e | e
    · subst e; exact hr
    · exact hb p e

/-- Memoise `h ↦ d` (in `dptW`) over the memo in `m`, and return. -/
theorem dpt_set (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 62) (m : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx Nat) (hbH : Hb <+: H)
    (hm : MemoRepN C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get dptW = some (BitVec.ofNat 64 d))
    (gM : Γ.get m = some mw) (hmt : m ≠ dptM3) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ dptLocals)) (dptSet C m) s (pure (d, memo.insert h d))
      (PostDW (ctxH C Hb)) := by
  unfold dptSet
  refine specR_alloc3I (ctxOK_H hok H) dptM3 (vv pH) (vv dptW) (vv m) (Enc.idxW h) (BitVec.ofNat 64 d) mw (by decide)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gH)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg hmt]; exact gM) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW h) (BitVec.ofNat 64 d) mw hws
  have h3 := img3_prefix H2 ws (Enc.idxW h) (BitVec.ofNat 64 d) mw hws
  have hp23 : H <+: _ := (hp2 : H <+: H2).trans h3
  have hm3 := memoRepN_insert h d hd (memoRepN_mono hp23 hm) g0 g1 g2
  exact dpt_ret C hok _ Hb (hbH.trans hp23) (vv dptW) d hd dptM3 _ _ hm3
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; simp; rfl)

/-- `W + 1`, memoised (the bound's hang aside). -/
theorem dpt_inc (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 62) (m : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx Nat) (hbH : Hb <+: H)
    (hm : MemoRepN C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get dptW = some (BitVec.ofNat 64 d))
    (gM : Γ.get m = some mw) (hmt : m ≠ dptM3 ∧ m ≠ dptW) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ dptLocals)) (dptInc C m) s
      (pure (d + 1, memo.insert h (d + 1))) (PostDW (ctxH C Hb)) := by
  unfold dptInc
  have hlt := ConPanqueque.T.Decl.nd_lt_iff d (2 ^ 62 - 1) (by omega) (by omega)
  have e1 : BitVec.ofNat 64 d + 1 = BitVec.ofNat 64 (d + 1) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  by_cases hb : d < 2 ^ 62 - 1
  · refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [gW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI dptW _ (BitVec.ofNat 64 (d + 1)) (by decide)
      (by simp [sev, gW]; exact e1) ?_
    exact dpt_set C hok H Hb h (d + 1) (by omega) m mw memo hbH hm
      (by simp only [Env.get_cons]; rw [if_neg (by decide)]; exact gH)
      (by simp [Env.get_cons]) (by simp only [Env.get_cons]; rw [if_neg hmt.2]; exact gM) hmt.1
  · refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [gW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
      (fun _ => specR_hangI) (fun h => absurd h (by decide))

theorem max_into {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (a b : MlS) (x y : Nat) (hx : x < 2 ^ 62) (hy : y < 2 ^ 62)
    (ga : Γ.get a = some (BitVec.ofNat 64 x)) (gb : Γ.get b = some (BitVec.ofNat 64 y))
    (hk : SpecR (Inv C s ((dptW, BitVec.ofNat 64 (max x y)) :: Γ) M (ctxLocals ++ dptLocals)) rest s m R) :
    SpecR (Inv C s Γ M (ctxLocals ++ dptLocals)) (maxInto a b rest) s m R := by
  unfold maxInto
  have hlt := ConPanqueque.T.Decl.nd_lt_iff x y (by omega) (by omega)
  by_cases hl : x < y
  · refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [ga, gb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.mpr hl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [show max x y = y by omega] at hk
    exact specR_assignI dptW _ _ (by decide) (by simp [sev, gb]) hk
  · refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [ga, gb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.not.mpr hl])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [show max x y = x by omega] at hk
    exact specR_assignI dptW _ _ (by decide) (by simp [sev, ga]) hk

/-- The walk at fuel `n`. -/
def DPRec (C : Ctx) (n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx Nat) (mw : BitVec 64) (H : List (BitVec 64)) (s : AState), C.H <+: H →
    MemoRepN C.HB H mw memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (dptParams.zip [BitVec.ofNat 64 n, Enc.idxW h, mw])) (dptBody C) s
      (depthGo memo n h) (PostDW (ctxH C H))

theorem dpt_call {β : Type} (C : Ctx) (hc : DPTCodes C) (n : Nat) (ih : DPRec (σ := σ) C n)
    {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : Nat × Std.HashMap EIdx Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (hp : C.H <+: H)
    (child memo y m' : MlS)
    (hx : y ∈ ctxLocals ++ dptLocals ∧ m' ∈ ctxLocals ++ dptLocals)
    (hne : y ≠ dptQ ∧ m' ≠ dptQ ∧ m' ≠ y)
    (c : EIdx) (memo0 : Std.HashMap EIdx Nat) (mw : BitVec 64) (hm : MemoRepN C.HB H mw memo0)
    (gF : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (gC : Γ.get child = some (Enc.idxW c))
    (gM : Γ.get memo = some mw)
    (hk : ∀ (r : Nat × Std.HashMap EIdx Nat) (H' : List (BitVec 64)) (op : Nat) (mw' : BitVec 64) (s' : AState),
      H <+: H' → r.1 < 2 ^ 62 → MemoRepN C.HB H' mw' r.2 →
      SpecR (Inv (ctxH C H') s' ((m', mw') :: (y, BitVec.ofNat 64 r.1) :: (dptQ, cellA C op) :: Γ) []
        (ctxLocals ++ dptLocals)) rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ dptLocals)) (dptCall child memo y m' rest) s
      (depthGo memo0 n c >>= k) R := by
  unfold dptCall
  refine specR_callNIH (C := ctxH C H) dptQ fDepth dptParams [.op .sub [vv pFu, .const 1], vv child, vv memo]
    (dptBody C) [BitVec.ofNat 64 n, Enc.idxW c, mw] (by decide) rfl (by decide) hc.self
    ⟨by simp only [sev, sev_vv, gF]; simp; exact ofNat_succ_sub_one n, by simp [sev, gC], by simp [sev, gM], trivial⟩
    (PostDW (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (BitVec.ofNat 64 r.1) ∧
      r.1 < 2 ^ 62 ∧ H'[op + 1]? = some mw' ∧ MemoRepN C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, hb, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, hb, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dptParams _ rfl hlk) (ih c memo0 mw H s hp hm))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, hb, h2, h3⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) y (vv dptQ) op _ h1 hx.1 (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) m' _ (op + 1) _ h2 hx.2
    (by simp only [sev, sev_vv, Env.get_cons, if_neg (show dptQ ≠ y from fun e => hne.1 e.symm), if_true]; simp; exact cellA_add8 C op) ?_
  exact hk r H1 op mw' s1 hp1 hb h3

end

section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`depthGo`**. -/
theorem dpt_spec (C : Ctx) (hok : CtxOK C) (hc : DPTCodes C) : ∀ n, n < 2 ^ 64 → DPRec (σ := σ) C n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo mw H s hp hm
    refine specR_prologue (postDW_locals _) (dpt_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dptParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro hn h memo mw H s hp hm
    have ih' := ih (by omega)
    refine specR_prologue (postDW_locals _) (dpt_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dptParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [depthGo]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, dptParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s = .ok (v, s) by rw [view_run, hv]) ?_
    have hleaf : ∀ (Γ : Env) (M : Mem), Γ.get dptM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ dptLocals)) (dptRet C (.const 1) dptM) s (pure (1, memo))
          (PostDW (ctxH C H)) := fun Γ M gM =>
      dpt_ret C hok H H (List.prefix_refl _) (.const 1) 1 (by decide) dptM mw memo hm (fun _ => by simp [sev])
        (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide)]; exact gM)
    have hmemo : ∀ (arm : ProgHOL 64) (mnone : AM (Nat × Std.HashMap EIdx Nat)) (Γ : Env) (M : Mem),
        Γ.get dptM = some mw → Γ.get pH = some (Enc.idxW h) →
        (memo[h]? = none → SpecR (σ := σ) (Inv (ctxH C H) s ((dptX, 0) :: Γ) [] (ctxLocals ++ dptLocals)) arm s mnone
          (PostDW (ctxH C H))) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ dptLocals)) (dptMemo C arm) s
          (match memo[h]? with
            | some r => pure (r, memo)
            | none => mnone) (PostDW (ctxH C H)) := by
      intro arm mnone Γ M gM gH harm
      obtain ⟨L, hL, hlk, hbd⟩ := id hm
      unfold dptMemo
      rw [hlk h]
      refine specR_pureBind (L.lookup h) ?_
      refine specR_callNIM dptX fMemoFindB mbfParams [vv dptM, vv pH] mbfBody [mw, Enc.idxW h] (by decide) rfl (by decide)
        hc.mbf ⟨by simp [sev, gM], by simp [sev, gH], trivial⟩
        (fun a w s' st => (pure (L.lookup h) : AM (Option Nat)) s = .ok (a, s') ∧ PostON2 (ctxH C H) a w s' st)
        (fun _ _ _ _ h => h.2.2)
        (fun u hu _ hlk' => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mbfParams _ rfl hlk')
          (mbn_spec C hok hc.mbf H h L mw s hL)))
        (fun a w s1 st ⟨hrun, hw, _⟩ => ?_)
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hra, hs1⟩ := hrun
      subst hw; subst hs1; subst hra
      rcases hfo : L.lookup h with _ | r
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact harm (by rw [hlk h, hfo])
      have hrb : r < 2 ^ 62 := hbd _ (lookup_mem hfo)
      have hr1 : BitVec.ofNat 64 r + 1 ≠ 0#64 := by
        intro e; have := congrArg BitVec.toNat e; simp [BitVec.toNat_add] at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hr1)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_assignI dptX _ (BitVec.ofNat 64 r) (by decide)
        (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      exact dpt_ret C hok H H (List.prefix_refl _) (vv dptX) r hrb dptM mw memo hm (fun _ => by simp +decide [sev, Env.get_cons])
        (fun _ => by simp +decide [sev, Env.get_cons, gM])
    cases v with
    | bvar i =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv])
    | fvar i ty =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv])
    | sort u =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv])
    | const c us =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv])
    | lit l =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv])
    | app a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold dptNode
      refine specR_loadI' dptA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' dptA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun _ => ?_)
      unfold dptBin
      simp only [bind_assoc]
      refine dpt_call C hc n ih' H hp dptA1 dptM dptY dptM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hb1 hm1 => ?_)
      obtain ⟨d1, m1⟩ := r1
      have hb1' : d1 < 2 ^ 62 := hb1
      try simp only [pure_bind]
      refine dpt_call C hc n ih' H1 (hp.trans hp1) dptA2 dptM1 dptZ dptM2 (by decide) (by decide) b m1 mw1 hm1
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hb2 hm2 => ?_)
      obtain ⟨d2, m2⟩ := r2
      have hb2' : d2 < 2 ^ 62 := hb2
      try simp only [pure_bind]
      refine max_into dptY dptZ d1 d2 hb1' hb2' (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ?_
      exact dpt_inc C hok H2 H h (max d1 d2) (by omega) dptM2 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ⟨by decide, by decide⟩
    | lam a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold dptNode
      refine specR_loadI' dptA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' dptA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun _ => ?_)
      unfold dptBin
      simp only [bind_assoc]
      refine dpt_call C hc n ih' H hp dptA1 dptM dptY dptM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hb1 hm1 => ?_)
      obtain ⟨d1, m1⟩ := r1
      have hb1' : d1 < 2 ^ 62 := hb1
      try simp only [pure_bind]
      refine dpt_call C hc n ih' H1 (hp.trans hp1) dptA2 dptM1 dptZ dptM2 (by decide) (by decide) b m1 mw1 hm1
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hb2 hm2 => ?_)
      obtain ⟨d2, m2⟩ := r2
      have hb2' : d2 < 2 ^ 62 := hb2
      try simp only [pure_bind]
      refine max_into dptY dptZ d1 d2 hb1' hb2' (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ?_
      exact dpt_inc C hok H2 H h (max d1 d2) (by omega) dptM2 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ⟨by decide, by decide⟩
    | forallE a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold dptNode
      refine specR_loadI' dptA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' dptA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun _ => ?_)
      unfold dptBin
      simp only [bind_assoc]
      refine dpt_call C hc n ih' H hp dptA1 dptM dptY dptM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hb1 hm1 => ?_)
      obtain ⟨d1, m1⟩ := r1
      have hb1' : d1 < 2 ^ 62 := hb1
      try simp only [pure_bind]
      refine dpt_call C hc n ih' H1 (hp.trans hp1) dptA2 dptM1 dptZ dptM2 (by decide) (by decide) b m1 mw1 hm1
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hb2 hm2 => ?_)
      obtain ⟨d2, m2⟩ := r2
      have hb2' : d2 < 2 ^ 62 := hb2
      try simp only [pure_bind]
      refine max_into dptY dptZ d1 d2 hb1' hb2' (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ?_
      exact dpt_inc C hok H2 H h (max d1 d2) (by omega) dptM2 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ⟨by decide, by decide⟩
    | letE ty v b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold dptNode
      refine specR_loadI' dptA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW v, Enc.idxW b] []) ?_
      refine specR_loadI' dptA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' dptA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v) (Enc.idxW b) [] []) ?_
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun _ => ?_)
      unfold dptLet
      simp only [bind_assoc]
      refine dpt_call C hc n ih' H hp dptA1 dptM dptY dptM1 (by decide) (by decide) ty memo mw hm
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hb1 hm1 => ?_)
      obtain ⟨d1, m1⟩ := r1
      have hb1' : d1 < 2 ^ 62 := hb1
      try simp only [pure_bind]
      refine dpt_call C hc n ih' H1 (hp.trans hp1) dptA2 dptM1 dptZ dptM2 (by decide) (by decide) v m1 mw1 hm1
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hb2 hm2 => ?_)
      obtain ⟨d2, m2⟩ := r2
      have hb2' : d2 < 2 ^ 62 := hb2
      try simp only [pure_bind]
      refine dpt_call C hc n ih' H2 ((hp.trans hp1).trans hp2) dptA3 dptM2 dptV dptM1 (by decide) (by decide) b m2 mw2 hm2
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r3 H3 op3 mw3 s3 hp3 hb3 hm3 => ?_)
      obtain ⟨d3, m3⟩ := r3
      have hb3' : d3 < 2 ^ 62 := hb3
      try simp only [pure_bind]
      refine max_into dptY dptZ d1 d2 hb1' hb2' (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ?_
      refine specR_assignI dptY (vv dptW) (BitVec.ofNat 64 (max d1 d2)) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
      refine max_into dptY dptV (max d1 d2) d3 (by omega) hb3' (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ?_
      exact dpt_inc C hok H3 H h (max (max d1 d2) d3) (by omega) dptM1 mw3 m3 ((hp1.trans hp2).trans hp3) hm3 (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ⟨by decide, by decide⟩
    | proj nm i e =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold dptNode
      refine specR_loadI' dptA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW nm) (Enc.idxW e :: Enc.limbs i) []) ?_
      refine specR_loadI' dptA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW nm) (Enc.idxW e) (Enc.limbs i) []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun _ => ?_)
      unfold dptProj
      refine dpt_call C hc n ih' H hp dptA2 dptM dptY dptM1 (by decide) (by decide) e memo mw hm
        (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hb1 hm1 => ?_)
      obtain ⟨d1, m1⟩ := r1
      have hb1' : d1 < 2 ^ 62 := hb1
      try simp only [pure_bind]
      refine specR_assignI dptW (vv dptY) (BitVec.ofNat 64 d1) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
      exact dpt_inc C hok H1 H h (d1) (by omega) dptM1 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, dptParams, ctxEnv]) ⟨by decide, by decide⟩

end

end ConPanqueque.T.Ind
