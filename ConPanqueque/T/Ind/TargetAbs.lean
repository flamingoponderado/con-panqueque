import ConPanqueque.T.Ind.Crest

/-!
# `targetAbsGo` for a single-member block

The member abstraction (`RecCheck.lean`): the member at the block's levels becomes its hole; variables are
leaves (their annotations are not entered).  Derived from the hole-image walk (`RFHole.lean`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def tabM := ofString "tab_m"
def tabB := ofString "tab_b"
def tabK := ofString "tab_k"
def tabX := ofString "tab_x"
def tabA1 := ofString "tab_a1"
def tabA2 := ofString "tab_a2"
def tabA3 := ofString "tab_a3"
def tabQ := ofString "tab_q"
def tabY := ofString "tab_y"
def tabZ := ofString "tab_z"
def tabV := ofString "tab_v"
def tabM1 := ofString "tab_m1"
def tabM2 := ofString "tab_m2"
def tabM3 := ofString "tab_m3"
def tabW := ofString "tab_w"
def tabR := ofString "tab_r"
def fTab := ofString "targetAbs"

def tabMs := ofString "tab_ms"
def tabUs := ofString "tab_us"
def tabHb := ofString "tab_hb"
def tabCn := ofString "tab_cn"
def tabCu := ofString "tab_cu"
def tabKn := ofString "tab_kn"
def tabTi := ofString "tab_ti"
def tabHx := ofString "tab_hx"

def tabParams : List MlS := [pFu, pH, tabM, tabMs, tabUs, tabHb]
def tabLocals : List MlS := gaaLocals ++ [tabB, tabK, tabX, tabA1, tabA2, tabA3, tabQ, tabY, tabZ, tabV, tabM1, tabM2,
  tabM3, tabW, tabR, tabCn, tabCu, tabKn, tabTi, tabHx]

/-- Return the pair `[r, memo]`. -/
def tabRet (C : Ctx) (r m : MlS) : ProgHOL 64 := alloc2 C tabR (vv r) (vv m) (.return (vv tabR))

/-- One child walked: `Q := rfv(child, memo)`, then its result in `y` and the memo in `m'`. -/
def tabCall (x child memo y m' : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, x), none)) fTab [.op .sub [vv pFu, .const 1], vv child, vv memo, vv tabMs, vv tabUs, vv tabHb])
  (.seq (.assign .local y (.load .one (vv x)))
  (.seq (.assign .local m' (.load .one (.op .add [vv x, .const 8]))) rest))

/-- Memoise `h ↦ w` over the memo in `m`, and return. -/
def tabSet (C : Ctx) (m : MlS) : ProgHOL 64 :=
  alloc3 C tabM3 (vv pH) (vv tabW) (vv m) (tabRet C tabW tabM3)

def tabBin (C : Ctx) (f : MlS) : ProgHOL 64 :=
  tabCall tabQ tabA1 tabM tabY tabM1 (tabCall tabQ tabA2 tabM1 tabZ tabM2
    (.seq (.call (some (some (.local, tabW), none)) f [vv tabY, vv tabZ]) (tabSet C tabM2)))

def tabLet (C : Ctx) : ProgHOL 64 :=
  tabCall tabQ tabA1 tabM tabY tabM1 (tabCall tabQ tabA2 tabM1 tabZ tabM2 (tabCall tabQ tabA3 tabM2 tabV tabM3
    (.seq (.call (some (some (.local, tabW), none)) fInternLet [vv tabY, vv tabZ, vv tabV])
      (alloc3 C tabM2 (vv pH) (vv tabW) (vv tabM3) (tabRet C tabW tabM2)))))

def tabProj (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .notLower (vv tabB) (.const (BitVec.ofNat 64 (2 ^ 63)))) hang
  (tabCall tabQ tabA2 tabM tabY tabM1
    (.seq (.call (some (some (.local, tabW), none)) fInternProj [vv tabA1, vv tabY, vv tabB]) (tabSet C tabM1)))

/-- The const arm: a member (pointer block `tabMs`) at the block's levels is its hole (block `tabHb`), anything else
itself. -/
def tabConst (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local tabCn (.load .one (vv lRp)))
  (.seq (.assign .local tabCu (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv tabCu) (vv tabUs))
    (.seq (.assign .local tabKn (.load .one (vv tabMs)))
    (.seq (.call (some (some (.local, tabTi), none)) fMemFindIdx [vv tabMs, vv tabCn, .const 0, vv tabKn])
    (.ite (.cmp .equal (vv tabTi) (.const 0)) (tabRet C pH tabM)
      (.seq (.assign .local tabTi (.op .sub [vv tabTi, .const 1]))
      (.seq (.assign .local tabHx (.load .one (.op .add [vv tabHb, .op .add [.panop .mul [vv tabTi, .const 8], .const 8]])))
        (tabRet C tabHx tabM))))))
    (tabRet C pH tabM)))

/-- A compound node: the view's children loaded, then the memo, then the arm. -/
def tabNode (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local tabA1 (.load .one (vv lRp)))
  (.seq (.assign .local tabA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lDg) (.const 7)) (.seq (.assign .local tabA3 (.load .one (.op .add [vv lRp, .const 16])))
      (tabMemo C (tabLet C)))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local tabB (.const 0)) (tabMemo C (tabProj C)))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local tabB (.load .one (.op .add [vv lRp, .const 16]))) (tabMemo C (tabProj C))) hang))
  (tabMemo C (.ite (.cmp .equal (vv lDg) (.const 4)) (tabBin C fInternApp)
    (.ite (.cmp .equal (vv lDg) (.const 5)) (tabBin C fInternLam) (tabBin C fInternForallE)))))))
where
  tabMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
    .seq (.call (some (some (.local, tabX), none)) fMemoFind [vv tabM, vv pH])
    (.ite (.cmp .equal (vv tabX) (.const 0)) arm
      (.seq (.assign .local tabX (.op .sub [vv tabX, .const 1])) (tabRet C tabX tabM)))

def tabBody (C : Ctx) : ProgHOL 64 := prologue tabLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (tabRet C pH tabM)
  (.ite (.cmp .equal (vv lDg) (.const 3)) (tabConst C)
  (.ite (.cmp .lower (vv lDg) (.const 4)) (tabRet C pH tabM)
  (.ite (.cmp .equal (vv lDg) (.const 8)) (tabRet C pH tabM) (tabNode C)))))))))

/-- The code `targetAbs` runs. -/
structure TABCodes (C : Ctx) : Prop where
  self : C.code.lookup fTab = some (tabParams.map (fun p => (p, ShapeHOL.one)), tabBody C, .one)
  mf : C.code.lookup fMemoFind = some (mmfParams.map (fun p => (p, ShapeHOL.one)), mmfBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  lam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  fa : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  lt : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  pj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)
  mfi : C.code.lookup fMemFindIdx = some (mfiParams.map (fun p => (p, ShapeHOL.one)), mfiBody, .one)

section
variable {σ : Type}

theorem tab_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tabLocals → (ctxEnv C ++ tabParams.zip vals).get x = none :=
  Knot.params_none C tabLocals tabParams vals (by decide) (by decide)

/-- The walk's answer: a pair `[r, memo]`, the memo represented. -/
def PostTAB (C : Ctx) (r : EIdx × Std.HashMap EIdx EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' op mw', C.H <+: H' ∧ w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧ H'[op + 1]? = some mw' ∧
    MemoRep C.HB H' mw' r.2 ∧ SR (ctxH C H') s' st

theorem postTAB_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostTAB C a w s' st → PostTAB C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', op, mw', hp, hw, h1, h2, h3, hs⟩ => ⟨H', op, mw', hp, hw, h1, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

/-- The walk at fuel `n`, from any heap holding the openers' block. -/
def TABRec (C : Ctx) (ms : List MemberShape) (om : Nat) (tus : LsIdx) (holes : List EIdx) (ohb : Nat) (n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx EIdx) (mw : BitVec 64) (H : List (BitVec 64)) (s : AState), C.H <+: H →
    MemoRep C.HB H mw memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (tabParams.zip [BitVec.ofNat 64 n, Enc.idxW h, mw, cellA C om, Enc.idxW tus,
      cellA C ohb])) (tabBody C) s
      (targetAbsGo (ms.map (·.cvT.name)) tus holes memo n h) (PostTAB (ctxH C H))

/-- One child walked (`tabCall`). -/
theorem tab_call {β : Type} (C : Ctx) (hc : TABCodes C) (ms : List MemberShape) (om : Nat) (tus : LsIdx) (holes : List EIdx)
    (ohb : Nat) (n : Nat) (ih : TABRec (σ := σ) C ms om tus holes ohb n)
    {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx × Std.HashMap EIdx EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (hp : C.H <+: H)
    (x child memo y m' : MlS)
    (hx : x ∈ ctxLocals ++ tabLocals ∧ y ∈ ctxLocals ++ tabLocals ∧ m' ∈ ctxLocals ++ tabLocals)
    (hne : y ≠ x ∧ m' ≠ x ∧ m' ≠ y)
    (c : EIdx) (memo0 : Std.HashMap EIdx EIdx) (mw : BitVec 64) (hm : MemoRep C.HB H mw memo0)
    (gF : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (gC : Γ.get child = some (Enc.idxW c))
    (gM : Γ.get memo = some mw) (gNm : Γ.get tabMs = some (cellA C om))
    (gUs : Γ.get tabUs = some (Enc.idxW tus)) (gHl : Γ.get tabHb = some (cellA C ohb))
    (hk : ∀ (r : EIdx × Std.HashMap EIdx EIdx) (H' : List (BitVec 64)) (op : Nat) (mw' : BitVec 64) (s' : AState),
      H <+: H' → MemoRep C.HB H' mw' r.2 →
      SpecR (Inv (ctxH C H') s' ((m', mw') :: (y, Enc.idxW r.1) :: (x, cellA C op) :: Γ) [] (ctxLocals ++ tabLocals))
        rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ tabLocals)) (tabCall x child memo y m' rest) s
      (targetAbsGo (ms.map (·.cvT.name)) tus holes memo0 n c >>= k) R := by
  unfold tabCall
  refine specR_callNIH (C := ctxH C H) x fTab tabParams [.op .sub [vv pFu, .const 1], vv child, vv memo, vv tabMs, vv tabUs, vv tabHb]
    (tabBody C) [BitVec.ofNat 64 n, Enc.idxW c, mw, cellA C om, Enc.idxW tus, cellA C ohb] (by decide) rfl hx.1 hc.self
    ⟨by simp only [sev, sev_vv, gF]; simp; exact ofNat_succ_sub_one n, by simp [sev, gC], by simp [sev, gM],
      by simp [sev, gNm], by simp [sev, gUs], by simp [sev, gHl], trivial⟩
    (PostTAB (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRep C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tabParams _ rfl hlk) (ih c memo0 mw H s hp hm))
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

/-- Memoise `h ↦ r` over the memo in `m` (into `t`), and return `[r, memo']`. -/
theorem tab_set (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h r : EIdx) (m t : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx EIdx) (hbH : Hb <+: H)
    (hm : MemoRep C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get tabW = some (Enc.idxW r))
    (gM : Γ.get m = some mw) (ht : t ∈ ctxLocals ++ tabLocals) (htW : t ≠ tabW ∧ t ≠ tabR) (hmt : m ≠ t) (htH : t ≠ pH) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ tabLocals))
      (alloc3 C t (vv pH) (vv tabW) (vv m) (tabRet C tabW t)) s (pure (r, memo.insert h r)) (PostTAB (ctxH C Hb)) := by
  refine specR_alloc3I (ctxOK_H hok H) t (vv pH) (vv tabW) (vv m) (Enc.idxW h) (Enc.idxW r) mw ht
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htH e.symm)]; exact gH)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg hmt]; exact gM) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have h3 := img3_prefix H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have hp23 : H <+: _ := (hp2 : H <+: H2).trans h3
  have hm3 := memoRep_insert h r (memoRep_mono hp23 hm) g0 g1 g2
  unfold tabRet
  refine specR_alloc2I (ctxOK_H hok _) tabR (vv tabW) (vv t) (Enc.idxW r) (cellA C H2.length) (by decide)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide), if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.2 e)]; simp; rfl)
    (fun H4 ws4 hp4 hws4 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  have h4 := img2_prefix H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  exact specR_returnI (vv tabR) (cellA C H4.length) (by simp [sev, Env.get_cons]; rfl) (fun tt htt =>
    ⟨_, H4.length, cellA C H2.length, hbH.trans (hp23.trans ((hp4 : _ <+: H4).trans h4)), rfl, k0, k1,
      memoRep_mono ((hp4 : _ <+: H4).trans h4) hm3, sr_of_eq htt.sr rfl rfl rfl rfl⟩)

end

set_option maxHeartbeats 16000000 in
/-- **`targetAbsGo`** for a single-member block. -/
theorem tab_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : TABCodes C)
    (ms : List MemberShape) (om : Nat) (tus : LsIdx) (holes : List EIdx) (ohb : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59)
    (hhb : BlkAt C.H ohb (holes.map Enc.idxW)) (hhl : holes.length = ms.length) :
    ∀ n, n < 2 ^ 64 → TABRec (σ := σ) C ms om tus holes ohb n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo mw H s hp hm
    refine specR_prologue (postTAB_locals _) (tab_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tabParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro hn h memo mw H s hp hm
    have ih' := ih (by omega)
    refine specR_prologue (postTAB_locals _) (tab_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, tabParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [targetAbsGo]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, tabParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s = .ok (v, s) by rw [view_run, hv]) ?_
    -- the leaves
    have hleaf : ∀ (Γ : Env) (M : Mem), Γ.get pH = some (Enc.idxW h) → Γ.get tabM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ tabLocals)) (tabRet C pH tabM) s (pure (h, memo))
          (PostTAB (ctxH C H)) := by
      intro Γ M gH gM
      unfold tabRet
      refine specR_alloc2I (ctxOK_H hok H) tabR (vv pH) (vv tabM) (Enc.idxW h) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons, gH]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW h) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW h) mw hws
      exact specR_returnI (vv tabR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hleafX : ∀ (tx : EIdx) (Γ : Env) (M : Mem), Γ.get tabHx = some (Enc.idxW tx) → Γ.get tabM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ tabLocals)) (tabRet C tabHx tabM) s (pure (tx, memo))
          (PostTAB (ctxH C H)) := by
      intro tx Γ M gH gM
      unfold tabRet
      refine specR_alloc2I (ctxOK_H hok H) tabR (vv tabHx) (vv tabM) (Enc.idxW tx) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons, gH]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW tx) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW tx) mw hws
      exact specR_returnI (vv tabR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    -- the memo step of a compound node
    have hmemo : ∀ (arm : ProgHOL 64) (mnone : AM (EIdx × Std.HashMap EIdx EIdx)) (Γ : Env) (M : Mem),
        Γ.get tabM = some mw → Γ.get pH = some (Enc.idxW h) →
        (memo[h]? = none → SpecR (σ := σ) (Inv (ctxH C H) s ((tabX, 0) :: Γ) [] (ctxLocals ++ tabLocals)) arm s mnone
          (PostTAB (ctxH C H))) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ tabLocals)) (tabNode.tabMemo C arm) s
          (match memo[h]? with
            | some r => pure (r, memo)
            | none => mnone) (PostTAB (ctxH C H)) := by
      intro arm mnone Γ M gM gH harm
      obtain ⟨L, hL, hlk⟩ := id hm
      unfold tabNode.tabMemo
      rw [hlk h]
      refine specR_pureBind (L.lookup h) ?_
      refine specR_callNIM tabX fMemoFind mmfParams [vv tabM, vv pH] mmfBody [mw, Enc.idxW h] (by decide) rfl (by decide)
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
      refine specR_assignI tabX _ (Enc.idxW r) (by decide)
        (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      unfold tabRet
      refine specR_alloc2I (ctxOK_H hok H) tabR (vv tabX) (vv tabM) (Enc.idxW r) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW r) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW r) mw hws
      exact specR_returnI (vv tabR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    cases v with
    | bvar i =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
    | sort u =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
    | lit l =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
    | fvar i ty =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
    | const c us =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      unfold tabConst
      refine specR_loadI' tabCn (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
      refine specR_loadI' tabCu _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
      by_cases hu : us = tus
      · subst hu
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tabParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        have hMH : PtrsRep C H om (MemberRep C H) ms := ptrsRep_mono hp (fun _ _ h => memberRep_mono hp h) hM
        refine UD.specR_heapLoadI' (C := ctxH C H) tabKn (vv tabMs) om _ hMH.1 (by decide)
          (by simp +decide [sev, Env.get_cons, Env.get, tabParams, ctxEnv]; rfl) ?_
        simp only [beq_self_eq_true, ite_true]
        refine specR_congr (m' := (pure ((((ms.map (·.cvT.name)).drop 0).findIdx? (· == c)).map (· + 0)) :
          AM (Option Nat)) >>= fun o => match o with
            | some t => match holes[t]? with
              | some x => pure (x, memo)
              | none => pure (h, memo)
            | none => pure (h, memo)) (by simp <;> rfl) ?_
        refine specR_callNIM tabTi fMemFindIdx mfiParams [vv tabMs, vv tabCn, .const 0, vv tabKn] mfiBody
          [cellA C om, Enc.idxW c, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc.mfi
          ⟨by simp +decide [sev, Env.get_cons, Env.get, tabParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl,
            by simp +decide [sev, Env.get_cons], trivial⟩
          (fun a w s' st => (pure ((((ms.map (·.cvT.name)).drop 0).findIdx? (· == c)).map (· + 0)) : AM (Option Nat)) s =
            .ok (a, s') ∧ PostON (ctxH C H) a w s' st) (fun _ _ _ _ h => h.2.2.2)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mfiParams _ rfl hlk)
            (mfi_spec C hok hc.mfi ms c om H hMH hml _ 0 s rfl (by omega))))
          (fun a w s2 st ⟨hrun, hw, hb, _⟩ => ?_)
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hra, hs2⟩ := hrun
        subst hw; subst hs2
        rcases a with _ | t
        · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun h => absurd h (by decide))
          exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
        have ht63 := hb t rfl
        have htl : t < ms.length := by
          have h1 : ((ms.map (·.cvT.name)).drop 0).findIdx? (· == c) = some t := by
            have := hra; simp only [Option.map_eq_some_iff] at this; obtain ⟨a, ha, he⟩ := this; simp at he; rw [← he]; exact ha
          have := List.findIdx?_eq_some_iff_getElem.mp h1
          obtain ⟨hlt, -⟩ := this; simpa using hlt
        have hnt : BitVec.ofNat 64 (t + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnt)
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI tabTi _ (BitVec.ofNat 64 t) (by decide)
          (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (t + 1) 1 (by omega) (by omega)) ?_
        have hth : t < holes.length := by omega
        have hx := hhb.2 t (by simp; omega)
        simp only [List.getElem_map] at hx
        refine UD.specR_heapLoadI' (C := ctxH C H) tabHx _ (ohb + 1 + t) _ (get_prefix hx hp) (by decide)
          (by simp +decide [sev, Env.get_cons, Env.get, tabParams, ctxEnv]; exact cellA_mulIdx C ohb t (by omega)) ?_
        simp only [List.getElem?_eq_getElem hth]
        exact hleafX _ _ _ (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
      · have hne : Enc.idxW us ≠ Enc.idxW tus := fun e => hu (Enc.idxW_inj e)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tabParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        simp [hu]
        exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
    | app a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold tabNode
      refine specR_loadI' tabA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' tabA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold tabBin
      simp only [bind_assoc]
      refine tab_call C hc ms om tus holes ohb n ih' H hp tabQ tabA1 tabM tabY tabM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine tab_call C hc ms om tus holes ohb n ih' H1 (hp.trans hp1) tabQ tabA2 tabM1 tabZ tabM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internAppI ra (ctxOK_H hok H2) hc.app tabW (vv tabY) (vv tabZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold tabSet
      exact tab_set C hok H2 H h w tabM2 tabM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | lam a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold tabNode
      refine specR_loadI' tabA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' tabA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold tabBin
      simp only [bind_assoc]
      refine tab_call C hc ms om tus holes ohb n ih' H hp tabQ tabA1 tabM tabY tabM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine tab_call C hc ms om tus holes ohb n ih' H1 (hp.trans hp1) tabQ tabA2 tabM1 tabZ tabM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internLamI ra (ctxOK_H hok H2) hc.lam tabW (vv tabY) (vv tabZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold tabSet
      exact tab_set C hok H2 H h w tabM2 tabM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | forallE a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold tabNode
      refine specR_loadI' tabA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' tabA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold tabBin
      simp only [bind_assoc]
      refine tab_call C hc ms om tus holes ohb n ih' H hp tabQ tabA1 tabM tabY tabM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine tab_call C hc ms om tus holes ohb n ih' H1 (hp.trans hp1) tabQ tabA2 tabM1 tabZ tabM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internForallEI ra (ctxOK_H hok H2) hc.fa tabW (vv tabY) (vv tabZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold tabSet
      exact tab_set C hok H2 H h w tabM2 tabM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | letE ty v b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold tabNode
      refine specR_loadI' tabA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW v, Enc.idxW b] []) ?_
      refine specR_loadI' tabA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' tabA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v) (Enc.idxW b) [] []) ?_
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun _ => ?_)
      unfold tabLet
      simp only [bind_assoc]
      refine tab_call C hc ms om tus holes ohb n ih' H hp tabQ tabA1 tabM tabY tabM1 (by decide) (by decide) ty memo mw hm
        (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨t2, m1⟩ := r1
      simp only
      refine tab_call C hc ms om tus holes ohb n ih' H1 (hp.trans hp1) tabQ tabA2 tabM1 tabZ tabM2 (by decide)
        (by decide) v m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨v2, m2⟩ := r2
      simp only
      refine tab_call C hc ms om tus holes ohb n ih' H2 ((hp.trans hp1).trans hp2) tabQ tabA3 tabM2
        tabV tabM3 (by decide) (by decide) b m2 mw2 hm2 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r3 H3 op3 mw3 s3 hp3 hm3 => ?_)
      obtain ⟨b2, m3⟩ := r3
      simp only
      refine specR_internLetI ra (ctxOK_H hok H3) hc.lt tabW (vv tabY) (vv tabZ) (vv tabV) t2 v2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv])
        (fun w s4 => ?_)
      simp only [pure_bind]
      exact tab_set C hok H3 H h w tabM3 tabM2 mw3 m3 ((hp1.trans hp2).trans hp3) hm3 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by decide)
        ⟨by decide, by decide⟩ (by decide) (by decide)
    | proj nm i e =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold tabNode
      have hlenp : (encEView (.proj nm i e)).length = 2 + (Enc.limbs i).length := by simp [encEView, Enc.encProj]; omega
      refine specR_loadI' tabA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW nm) (Enc.idxW e :: Enc.limbs i) []) ?_
      refine specR_loadI' tabA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW nm) (Enc.idxW e) (Enc.limbs i) []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_assignI tabB (.const 0) 0 (by decide) rfl ?_
        refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun _ => ?_)
        unfold tabProj
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only [bind_assoc]
        refine tab_call C hc ms om tus holes ohb n ih' H hp tabQ tabA2 tabM tabY tabM1 (by decide) (by decide) e memo mw hm
          (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
        obtain ⟨u2, m1⟩ := r1
        simp only
        refine specR_internProjI ra (ctxOK_H hok H1) hc.pj tabW (vv tabA1) (vv tabY) (vv tabB) nm _ u2 (by decide) (by decide)
          (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun w s2 => ?_)
        simp only [pure_bind]
        unfold tabSet
        exact tab_set C hok H1 H h w tabM1 tabM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
          (by decide) (by decide)

      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_loadI' tabB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev, Env.get_cons]) rfl
          (by simpa [encEView, Enc.encProj, hl] using wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] []) ?_
        by_cases h63 : i < 2 ^ 63
        · have hi63 : i < 2 ^ 63 := h63
          refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun _ => ?_)
          unfold tabProj
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
            (fun h => absurd rfl h) (fun _ => ?_)
          simp only [bind_assoc]
          refine tab_call C hc ms om tus holes ohb n ih' H hp tabQ tabA2 tabM tabY tabM1 (by decide) (by decide) e memo mw hm
            (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
          obtain ⟨u2, m1⟩ := r1
          simp only
          refine specR_internProjI ra (ctxOK_H hok H1) hc.pj tabW (vv tabA1) (vv tabY) (vv tabB) nm _ u2 (hi63) (by decide)
            (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun w s2 => ?_)
          simp only [pure_bind]
          unfold tabSet
          exact tab_set C hok H1 H h w tabM1 tabM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
            (by decide) (by decide)

        · refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, tabParams, ctxEnv]) (fun _ => ?_)
          unfold tabProj
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



/-! ## `targetAbs` -/

def taE := ofString "ta_e"
def taMs := ofString "ta_ms"
def taUs := ofString "ta_us"
def taHb := ofString "ta_hb"
def taQ := ofString "ta_q"
def taR := ofString "ta_r"
def fTa := ofString "targetAbsTop"

def taParams : List MlS := [taE, taMs, taUs, taHb]
def taLocals : List MlS := [taQ, taR]

def taBody : ProgHOL 64 := prologue taLocals
  (.seq (.call (some (some (.local, taQ), none)) fTab
      [.const (BitVec.ofNat 64 coreWalkFuel), vv taE, .const 0, vv taMs, vv taUs, vv taHb])
  (.seq (.assign .local taR (.load .one (vv taQ))) (.return (vv taR))))

section
variable {σ : Type}

theorem ta_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ taLocals → (ctxEnv C ++ taParams.zip vals).get x = none :=
  Knot.params_none C taLocals taParams vals (by decide) (by decide)

/-- **`targetAbs names us holes e`**, the names the members' (pointer block `om`), the holes a block at `ohb`. -/
theorem ta_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : TABCodes C)
    (hct : C.code.lookup fTa = some (taParams.map (fun p => (p, ShapeHOL.one)), taBody, .one))
    (ms : List MemberShape) (om : Nat) (tus : LsIdx) (holes : List EIdx) (ohb : Nat) (H : List (BitVec 64))
    (hp : C.H <+: H) (hM : PtrsRep C H om (MemberRep C H) ms) (hml : ms.length < 2 ^ 59)
    (hhb : BlkAt H ohb (holes.map Enc.idxW)) (hhl : holes.length = ms.length) (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre (ctxH C H) s (taParams.zip [Enc.idxW e, cellA C om, Enc.idxW tus, cellA C ohb])) taBody s
      (targetAbs (ms.map (·.cvT.name)) tus holes e) (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (ta_none _ _) ?_
  unfold targetAbs
  refine specR_callNIH (C := ctxH C H) taQ fTab tabParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv taE, .const 0, vv taMs, vv taUs, vv taHb]
    (tabBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0, cellA C om, Enc.idxW tus, cellA C ohb] (by decide) rfl
    (by decide) hc.self
    ⟨rfl, by simp +decide [sev, Env.get, taParams, ctxEnv], rfl, by simp +decide [sev, Env.get, taParams, ctxEnv],
      by simp +decide [sev, Env.get, taParams, ctxEnv], by simp +decide [sev, Env.get, taParams, ctxEnv], trivial⟩
    (PostTAB (ctxH C H)) (fun r w _ H' => ∃ op, w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1))
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, _, _, hsr⟩ => ⟨H', hp', ⟨op, hw, h1⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tabParams _ rfl hlk)
      (tab_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc) ms om tus holes ohb hM hml hhb hhl coreWalkFuel
        CV.coreWalkFuel_lt e ∅ 0 H s (List.prefix_refl _) ⟨[], rfl, fun k => by simp⟩))
    (fun r w s1 H1 hp1 ⟨op, hw, h1⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) taR (vv taQ) op _ h1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
