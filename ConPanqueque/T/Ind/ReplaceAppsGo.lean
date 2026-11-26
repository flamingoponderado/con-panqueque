import ConPanqueque.T.Ind.ReplaceApps
import ConPanqueque.T.Ind.ReplaceFVars

/-!
# `replaceAppsGo`: the whole-application replacement walk (memoised, pre-order)

Derived from the `replaceFVars` walk: free variables are leaves, a constant or an application that is a whole
member application (`appHole?`) is replaced by its hole.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def rapM := ofString "rap_m"
def rapB := ofString "rap_b"
def rapK := ofString "rap_k"
def rapX := ofString "rap_x"
def rapA1 := ofString "rap_a1"
def rapA2 := ofString "rap_a2"
def rapA3 := ofString "rap_a3"
def rapQ := ofString "rap_q"
def rapY := ofString "rap_y"
def rapZ := ofString "rap_z"
def rapV := ofString "rap_v"
def rapM1 := ofString "rap_m1"
def rapM2 := ofString "rap_m2"
def rapM3 := ofString "rap_m3"
def rapW := ofString "rap_w"
def rapR := ofString "rap_r"
def rapMs := ofString "rap_ms"
def rapUs := ofString "rap_us"
def rapBb := ofString "rap_bb"
def rapNn := ofString "rap_nn"
def fRepApps := ofString "replaceAppsGo"

def rapParams : List MlS := [pFu, pH, rapM, rapMs, rapUs, rapBb, rapNn]
def rapLocals : List MlS := gaaLocals ++ [rapB, rapK, rapX, rapA1, rapA2, rapA3, rapQ, rapY, rapZ, rapV, rapM1, rapM2,
  rapM3, rapW, rapR]

/-- Return the pair `[r, memo]`. -/
def rapRet (C : Ctx) (r m : MlS) : ProgHOL 64 := alloc2 C rapR (vv r) (vv m) (.return (vv rapR))

def rapCall (x child memo y m' : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, x), none)) fRepApps
      [.op .sub [vv pFu, .const 1], vv child, vv memo, vv rapMs, vv rapUs, vv rapBb, vv rapNn])
  (.seq (.assign .local y (.load .one (vv x)))
  (.seq (.assign .local m' (.load .one (.op .add [vv x, .const 8]))) rest))

/-- `X := appHole?(h)` (as `optWG idxW`). -/
def rapHole (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, rapX), none)) fAppHole [vv rapBb, vv pH, vv rapNn, vv rapMs, vv rapUs]) rest

/-- Memoise `h ↦ w` over the memo in `m`, and return. -/
def rapSet (C : Ctx) (m : MlS) : ProgHOL 64 :=
  alloc3 C rapM3 (vv pH) (vv rapW) (vv m) (rapRet C rapW rapM3)

def rapBin (C : Ctx) (f : MlS) : ProgHOL 64 :=
  rapCall rapQ rapA1 rapM rapY rapM1 (rapCall rapQ rapA2 rapM1 rapZ rapM2
    (.seq (.call (some (some (.local, rapW), none)) f [vv rapY, vv rapZ]) (rapSet C rapM2)))

def rapLet (C : Ctx) : ProgHOL 64 :=
  rapCall rapQ rapA1 rapM rapY rapM1 (rapCall rapQ rapA2 rapM1 rapZ rapM2 (rapCall rapQ rapA3 rapM2 rapV rapM3
    (.seq (.call (some (some (.local, rapW), none)) fInternLet [vv rapY, vv rapZ, vv rapV])
      (alloc3 C rapM2 (vv pH) (vv rapW) (vv rapM3) (rapRet C rapW rapM2)))))

def rapProj (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .notLower (vv rapB) (.const (BitVec.ofNat 64 (2 ^ 63)))) hang
  (rapCall rapQ rapA2 rapM rapY rapM1
    (.seq (.call (some (some (.local, rapW), none)) fInternProj [vv rapA1, vv rapY, vv rapB]) (rapSet C rapM1)))


/-- The application arm: a whole member application is its hole, else both children. -/
def rapAppArm (C : Ctx) : ProgHOL 64 :=
  rapHole (.ite (.cmp .equal (vv rapX) (.const 0)) (rapBin C fInternApp)
    (.seq (.assign .local rapW (.op .sub [vv rapX, .const 1])) (rapSet C rapM)))

/-- The constant arm: its hole, else itself (not memoised). -/
def rapConst (C : Ctx) : ProgHOL 64 :=
  rapHole (.ite (.cmp .equal (vv rapX) (.const 0)) (rapRet C pH rapM)
    (.seq (.assign .local rapX (.op .sub [vv rapX, .const 1])) (rapRet C rapX rapM)))

/-- A compound node: the view's children loaded, then the memo, then the arm. -/
def rapNode (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rapA1 (.load .one (vv lRp)))
  (.seq (.assign .local rapA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lDg) (.const 7)) (.seq (.assign .local rapA3 (.load .one (.op .add [vv lRp, .const 16])))
      (rapMemo C (rapLet C)))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local rapB (.const 0)) (rapMemo C (rapProj C)))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local rapB (.load .one (.op .add [vv lRp, .const 16]))) (rapMemo C (rapProj C))) hang))
  (rapMemo C (.ite (.cmp .equal (vv lDg) (.const 4)) (rapAppArm C)
    (.ite (.cmp .equal (vv lDg) (.const 5)) (rapBin C fInternLam) (rapBin C fInternForallE)))))))
where
  rapMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
    .seq (.call (some (some (.local, rapX), none)) fMemoFind [vv rapM, vv pH])
    (.ite (.cmp .equal (vv rapX) (.const 0)) arm
      (.seq (.assign .local rapX (.op .sub [vv rapX, .const 1])) (rapRet C rapX rapM)))

def rapBody (C : Ctx) : ProgHOL 64 := prologue rapLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 3)) (rapConst C)
  (.ite (.cmp .lower (vv lDg) (.const 4)) (rapRet C pH rapM)
  (.ite (.cmp .equal (vv lDg) (.const 8)) (rapRet C pH rapM) (rapNode C))))))))

/-- The code `replaceFVarsCanon` runs. -/
structure RAPCodes (C : Ctx) : Prop where
  self : C.code.lookup fRepApps = some (rapParams.map (fun p => (p, ShapeHOL.one)), rapBody C, .one)
  mf : C.code.lookup fMemoFind = some (mmfParams.map (fun p => (p, ShapeHOL.one)), mmfBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  lam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  fa : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  lt : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  ah : AHCodes C
  pj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)

section
variable {σ : Type}

theorem rap_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rapLocals → (ctxEnv C ++ rapParams.zip vals).get x = none :=
  Knot.params_none C rapLocals rapParams vals (by decide) (by decide)

/-- The walk's answer: a pair `[r, memo]`, the memo represented. -/
def PostRA (C : Ctx) (r : EIdx × Std.HashMap EIdx EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' op mw', C.H <+: H' ∧ w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧ H'[op + 1]? = some mw' ∧
    MemoRep C.HB H' mw' r.2 ∧ SR (ctxH C H') s' st

theorem postRA_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRA C a w s' st → PostRA C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', op, mw', hp, hw, h1, h2, h3, hs⟩ => ⟨H', op, mw', hp, hw, h1, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

/-- The walk at fuel `n`. -/
def RARec (C : Ctx) (ms : List MemberShape) (om : Nat) (us : LsIdx) (bb nn n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx EIdx) (mw : BitVec 64) (H : List (BitVec 64)) (s : AState), C.H <+: H →
    MemoRep C.HB H mw memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (rapParams.zip [BitVec.ofNat 64 n, Enc.idxW h, mw, cellA C om, Enc.idxW us,
      BitVec.ofNat 64 bb, BitVec.ofNat 64 nn])) (rapBody C) s
      (replaceAppsGo (ms.map (·.cvT.name)) us bb nn memo n h) (PostRA (ctxH C H))

/-- One child walked (`rapCall`). -/
theorem rap_call {β : Type} (C : Ctx) (hc : RAPCodes C) (ms : List MemberShape) (om : Nat) (us : LsIdx) (bb nn n : Nat)
    (ih : RARec (σ := σ) C ms om us bb nn n)
    {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx × Std.HashMap EIdx EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (hp : C.H <+: H)
    (x child memo y m' : MlS)
    (hx : x ∈ ctxLocals ++ rapLocals ∧ y ∈ ctxLocals ++ rapLocals ∧ m' ∈ ctxLocals ++ rapLocals)
    (hne : y ≠ x ∧ m' ≠ x ∧ m' ≠ y)
    (c : EIdx) (memo0 : Std.HashMap EIdx EIdx) (mw : BitVec 64) (hm : MemoRep C.HB H mw memo0)
    (gF : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (gC : Γ.get child = some (Enc.idxW c))
    (gM : Γ.get memo = some mw) (gMs : Γ.get rapMs = some (cellA C om))
    (gUs : Γ.get rapUs = some (Enc.idxW us)) (gBb : Γ.get rapBb = some (BitVec.ofNat 64 bb))
    (gNn : Γ.get rapNn = some (BitVec.ofNat 64 nn))
    (hk : ∀ (r : EIdx × Std.HashMap EIdx EIdx) (H' : List (BitVec 64)) (op : Nat) (mw' : BitVec 64) (s' : AState),
      H <+: H' → MemoRep C.HB H' mw' r.2 →
      SpecR (Inv (ctxH C H') s' ((m', mw') :: (y, Enc.idxW r.1) :: (x, cellA C op) :: Γ) [] (ctxLocals ++ rapLocals))
        rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ rapLocals)) (rapCall x child memo y m' rest) s
      (replaceAppsGo (ms.map (·.cvT.name)) us bb nn memo0 n c >>= k) R := by
  unfold rapCall
  refine specR_callNIH (C := ctxH C H) x fRepApps rapParams [.op .sub [vv pFu, .const 1], vv child, vv memo, vv rapMs, vv rapUs, vv rapBb, vv rapNn]
    (rapBody C) [BitVec.ofNat 64 n, Enc.idxW c, mw, cellA C om, Enc.idxW us, BitVec.ofNat 64 bb, BitVec.ofNat 64 nn] (by decide) rfl hx.1 hc.self
    ⟨by simp only [sev, sev_vv, gF]; simp; exact ofNat_succ_sub_one n, by simp [sev, gC], by simp [sev, gM],
      by simp [sev, gMs], by simp [sev, gUs], by simp [sev, gBb], by simp [sev, gNn], trivial⟩
    (PostRA (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRep C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rapParams _ rfl hlk) (ih c memo0 mw H s hp hm))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, h2, h3⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) y (vv x) op _ h1 hx.2.1 (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) m' _ (op + 1) _ h2 hx.2.2
    (by simp only [sev, sev_vv, Env.get_cons, if_neg (show x ≠ y from fun e => hne.1 e.symm), if_true]; simp; exact cellA_add8 C op) ?_
  exact hk r H1 op mw' s1 hp1 h3

end

section
variable {σ : Type}

/-- Memoise `h ↦ r` over the memo in `m` (into `t`), and return `[r, memo']`. -/
theorem rap_set (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h r : EIdx) (m t : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx EIdx) (hbH : Hb <+: H)
    (hm : MemoRep C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get rapW = some (Enc.idxW r))
    (gM : Γ.get m = some mw) (ht : t ∈ ctxLocals ++ rapLocals) (htW : t ≠ rapW ∧ t ≠ rapR) (hmt : m ≠ t) (htH : t ≠ pH) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rapLocals))
      (alloc3 C t (vv pH) (vv rapW) (vv m) (rapRet C rapW t)) s (pure (r, memo.insert h r)) (PostRA (ctxH C Hb)) := by
  refine specR_alloc3I (ctxOK_H hok H) t (vv pH) (vv rapW) (vv m) (Enc.idxW h) (Enc.idxW r) mw ht
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htH e.symm)]; exact gH)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg hmt]; exact gM) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have h3 := img3_prefix H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have hp23 : H <+: _ := (hp2 : H <+: H2).trans h3
  have hm3 := memoRep_insert h r (memoRep_mono hp23 hm) g0 g1 g2
  unfold rapRet
  refine specR_alloc2I (ctxOK_H hok _) rapR (vv rapW) (vv t) (Enc.idxW r) (cellA C H2.length) (by decide)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide), if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.2 e)]; simp; rfl)
    (fun H4 ws4 hp4 hws4 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  have h4 := img2_prefix H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  exact specR_returnI (vv rapR) (cellA C H4.length) (by simp [sev, Env.get_cons]; rfl) (fun tt htt =>
    ⟨_, H4.length, cellA C H2.length, hbH.trans (hp23.trans ((hp4 : _ <+: H4).trans h4)), rfl, k0, k1,
      memoRep_mono ((hp4 : _ <+: H4).trans h4) hm3, sr_of_eq htt.sr rfl rfl rfl rfl⟩)


/-- Return `[r, memo]` from the variables `x` and `m`. -/
theorem rap_ret (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64)) (hbH : Hb <+: H)
    (x m : MlS) (r : EIdx) (mw : BitVec 64) (memo : Std.HashMap EIdx EIdx) (hm : MemoRep C.HB H mw memo)
    (gx : ∀ v, sev ((rapR, v) :: Γ) (vv x) = some (Enc.idxW r)) (gM : ∀ v, sev ((rapR, v) :: Γ) (vv m) = some mw) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rapLocals)) (rapRet C x m) s (pure (r, memo))
      (PostRA (ctxH C Hb)) := by
  unfold rapRet
  refine specR_alloc2I (ctxOK_H hok H) rapR (vv x) (vv m) (Enc.idxW r) mw (by decide) gx gM (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW r) mw hws
  have h2 := img2_prefix H2 ws (Enc.idxW r) mw hws
  exact specR_returnI (vv rapR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, H2.length, mw, hbH.trans ((hp2 : H <+: H2).trans h2), rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end


section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`replaceAppsGo`**. -/
theorem rap_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RAPCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 59) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (us : LsIdx) (bb nn : Nat) (hbn : bb + nn < 2 ^ 62) : ∀ n, n < 2 ^ 64 → RARec (σ := σ) C ms om us bb nn n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo mw H s hp hm
    refine specR_prologue (postRA_locals _) (rap_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rapParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro hn h memo mw H s hp hm
    have ih' := ih (by omega)
    refine specR_prologue (postRA_locals _) (rap_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rapParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [replaceAppsGo]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, rapParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s = .ok (v, s) by rw [view_run, hv]) ?_
    -- the leaves
    have hleaf : ∀ (Γ : Env) (M : Mem), Γ.get pH = some (Enc.idxW h) → Γ.get rapM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rapLocals)) (rapRet C pH rapM) s (pure (h, memo))
          (PostRA (ctxH C H)) := by
      intro Γ M gH gM
      unfold rapRet
      refine specR_alloc2I (ctxOK_H hok H) rapR (vv pH) (vv rapM) (Enc.idxW h) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons, gH]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW h) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW h) mw hws
      exact specR_returnI (vv rapR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    -- the memo step of a compound node
    have hmemo : ∀ (arm : ProgHOL 64) (mnone : AM (EIdx × Std.HashMap EIdx EIdx)) (Γ : Env) (M : Mem),
        Γ.get rapM = some mw → Γ.get pH = some (Enc.idxW h) →
        (memo[h]? = none → SpecR (σ := σ) (Inv (ctxH C H) s ((rapX, 0) :: Γ) [] (ctxLocals ++ rapLocals)) arm s mnone
          (PostRA (ctxH C H))) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rapLocals)) (rapNode.rapMemo C arm) s
          (match memo[h]? with
            | some r => pure (r, memo)
            | none => mnone) (PostRA (ctxH C H)) := by
      intro arm mnone Γ M gM gH harm
      obtain ⟨L, hL, hlk⟩ := id hm
      unfold rapNode.rapMemo
      rw [hlk h]
      refine specR_pureBind (L.lookup h) ?_
      refine specR_callNIM rapX fMemoFind mmfParams [vv rapM, vv pH] mmfBody [mw, Enc.idxW h] (by decide) rfl (by decide)
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
      refine specR_assignI rapX _ (Enc.idxW r) (by decide)
        (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      unfold rapRet
      refine specR_alloc2I (ctxOK_H hok H) rapR (vv rapX) (vv rapM) (Enc.idxW r) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW r) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW r) mw hws
      exact specR_returnI (vv rapR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    cases v with
    | bvar i =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv])
    | sort u =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv])
    | const c cus =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rapConst rapHole
      simp only
      refine specR_callNIH (C := ctxH C H) rapX fAppHole ahParams [vv rapBb, vv pH, vv rapNn, vv rapMs, vv rapUs] ahBody
        [BitVec.ofNat 64 bb, Enc.idxW h, BitVec.ofNat 64 nn, cellA C om, Enc.idxW us] (by decide) rfl (by decide) hc.ah.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], trivial⟩
        (PostOEH (ctxH C H)) (fun o w _ _ => w = optWG Enc.idxW o) (fun o w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ahParams _ rfl hlk)
          (ah_spec ra C hok hc.ah ms om hml hM us bb nn hbn h H hp s))
        (fun o wo s0 H0 hp0 hwo => ?_)
      subst hwo
      have hp0' : H <+: H0 := hp0
      rcases o with _ | r
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact rap_ret C hok H0 H hp0' pH rapM h mw memo (memoRep_mono hp0' hm) (fun _ => by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv])
      · have hr1 : Enc.idxW r + 1 ≠ 0#64 := by
          intro e; have := congrArg BitVec.toNat e
          have hlt : (Enc.idxW r).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact r.word.toNat_lt
          simp [BitVec.toNat_add] at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hr1) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI rapX _ (Enc.idxW r) (by decide) (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
        exact rap_ret C hok H0 H hp0' rapX rapM r mw memo (memoRep_mono hp0' hm) (fun _ => by simp +decide [sev, Env.get_cons])
          (fun _ => by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv])
    | lit l =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv])
    | fvar i ty =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv])
    | app a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rapNode
      refine specR_loadI' rapA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rapA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rapAppArm rapHole
      simp only [bind_assoc]
      refine specR_callNIH (C := ctxH C H) rapX fAppHole ahParams [vv rapBb, vv pH, vv rapNn, vv rapMs, vv rapUs] ahBody
        [BitVec.ofNat 64 bb, Enc.idxW h, BitVec.ofNat 64 nn, cellA C om, Enc.idxW us] (by decide) rfl (by decide) hc.ah.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rapParams, ctxEnv], trivial⟩
        (PostOEH (ctxH C H)) (fun o w _ _ => w = optWG Enc.idxW o) (fun o w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ahParams _ rfl hlk)
          (ah_spec ra C hok hc.ah ms om hml hM us bb nn hbn h H hp s))
        (fun o wo s0 H0 hp0 hwo => ?_)
      subst hwo
      have hp0' : H <+: H0 := hp0
      rcases o with _ | r
      swap
      · have hr1 : Enc.idxW r + 1 ≠ 0#64 := by
          intro e; have := congrArg BitVec.toNat e
          have hlt : (Enc.idxW r).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact r.word.toNat_lt
          simp [BitVec.toNat_add] at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hr1) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI rapW _ (Enc.idxW r) (by decide) (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
        try simp only [pure_bind]
        exact rap_set C hok H0 H h r rapM rapM3 mw memo hp0' (memoRep_mono hp0' hm) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
          (by decide) (by decide)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try simp only
      unfold rapBin
      try simp only [bind_assoc]
      refine rap_call C hc ms om us bb nn n ih' H0 (hp.trans hp0') rapQ rapA1 rapM rapY rapM1 (by decide) (by decide) a memo mw (memoRep_mono hp0' hm)
        (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rap_call C hc ms om us bb nn n ih' H1 ((hp.trans hp0').trans hp1) rapQ rapA2 rapM1 rapZ rapM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internAppI ra (ctxOK_H hok H2) hc.app rapW (vv rapY) (vv rapZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rapSet
      exact rap_set C hok H2 H h w rapM2 rapM3 mw2 m2 ((hp0'.trans hp1).trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | lam a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rapNode
      refine specR_loadI' rapA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rapA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rapBin
      simp only [bind_assoc]
      refine rap_call C hc ms om us bb nn n ih' H hp rapQ rapA1 rapM rapY rapM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rap_call C hc ms om us bb nn n ih' H1 (hp.trans hp1) rapQ rapA2 rapM1 rapZ rapM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internLamI ra (ctxOK_H hok H2) hc.lam rapW (vv rapY) (vv rapZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rapSet
      exact rap_set C hok H2 H h w rapM2 rapM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | forallE a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rapNode
      refine specR_loadI' rapA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rapA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rapBin
      simp only [bind_assoc]
      refine rap_call C hc ms om us bb nn n ih' H hp rapQ rapA1 rapM rapY rapM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rap_call C hc ms om us bb nn n ih' H1 (hp.trans hp1) rapQ rapA2 rapM1 rapZ rapM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internForallEI ra (ctxOK_H hok H2) hc.fa rapW (vv rapY) (vv rapZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rapSet
      exact rap_set C hok H2 H h w rapM2 rapM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | letE ty v b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rapNode
      refine specR_loadI' rapA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW v, Enc.idxW b] []) ?_
      refine specR_loadI' rapA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' rapA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v) (Enc.idxW b) [] []) ?_
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => ?_)
      unfold rapLet
      simp only [bind_assoc]
      refine rap_call C hc ms om us bb nn n ih' H hp rapQ rapA1 rapM rapY rapM1 (by decide) (by decide) ty memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨t2, m1⟩ := r1
      simp only
      refine rap_call C hc ms om us bb nn n ih' H1 (hp.trans hp1) rapQ rapA2 rapM1 rapZ rapM2 (by decide)
        (by decide) v m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨v2, m2⟩ := r2
      simp only
      refine rap_call C hc ms om us bb nn n ih' H2 ((hp.trans hp1).trans hp2) rapQ rapA3 rapM2
        rapV rapM3 (by decide) (by decide) b m2 mw2 hm2 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r3 H3 op3 mw3 s3 hp3 hm3 => ?_)
      obtain ⟨b2, m3⟩ := r3
      simp only
      refine specR_internLetI ra (ctxOK_H hok H3) hc.lt rapW (vv rapY) (vv rapZ) (vv rapV) t2 v2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv])
        (fun w s4 => ?_)
      simp only [pure_bind]
      exact rap_set C hok H3 H h w rapM3 rapM2 mw3 m3 ((hp1.trans hp2).trans hp3) hm3 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by decide)
        ⟨by decide, by decide⟩ (by decide) (by decide)
    | proj nm i e =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rapNode
      have hlenp : (encEView (.proj nm i e)).length = 2 + (Enc.limbs i).length := by simp [encEView, Enc.encProj]; omega
      refine specR_loadI' rapA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW nm) (Enc.idxW e :: Enc.limbs i) []) ?_
      refine specR_loadI' rapA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW nm) (Enc.idxW e) (Enc.limbs i) []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_assignI rapB (.const 0) 0 (by decide) rfl ?_
        refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => ?_)
        unfold rapProj
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only [bind_assoc]
        refine rap_call C hc ms om us bb nn n ih' H hp rapQ rapA2 rapM rapY rapM1 (by decide) (by decide) e memo mw hm
          (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
        obtain ⟨u2, m1⟩ := r1
        simp only
        refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rapW (vv rapA1) (vv rapY) (vv rapB) nm _ u2 (by decide) (by decide)
          (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun w s2 => ?_)
        simp only [pure_bind]
        unfold rapSet
        exact rap_set C hok H1 H h w rapM1 rapM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
          (by decide) (by decide)

      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_loadI' rapB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev, Env.get_cons]) rfl
          (by simpa [encEView, Enc.encProj, hl] using wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] []) ?_
        by_cases h63 : i < 2 ^ 63
        · have hi63 : i < 2 ^ 63 := h63
          refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => ?_)
          unfold rapProj
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
            (fun h => absurd rfl h) (fun _ => ?_)
          simp only [bind_assoc]
          refine rap_call C hc ms om us bb nn n ih' H hp rapQ rapA2 rapM rapY rapM1 (by decide) (by decide) e memo mw hm
            (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
          obtain ⟨u2, m1⟩ := r1
          simp only
          refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rapW (vv rapA1) (vv rapY) (vv rapB) nm _ u2 (hi63) (by decide)
            (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun w s2 => ?_)
          simp only [pure_bind]
          unfold rapSet
          exact rap_set C hok H1 H h w rapM1 rapM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
            (by decide) (by decide)

        · refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rapParams, ctxEnv]) (fun _ => ?_)
          unfold rapProj
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



end ConPanqueque.T.Ind
