import ConPanqueque.T.Ind.ReplaceFVars

/-!
# `replaceFVars` at the erasing map (`eraseFVarTys`)

The walk of `ReplaceFVars` (the same memo list), every free variable replaced by itself at `Sort 0`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def rfeM := ofString "rfe_m"
def rfeB := ofString "rfe_b"
def rfeK := ofString "rfe_k"
def rfeX := ofString "rfe_x"
def rfeA1 := ofString "rfe_a1"
def rfeA2 := ofString "rfe_a2"
def rfeA3 := ofString "rfe_a3"
def rfeQ := ofString "rfe_q"
def rfeY := ofString "rfe_y"
def rfeZ := ofString "rfe_z"
def rfeV := ofString "rfe_v"
def rfeM1 := ofString "rfe_m1"
def rfeM2 := ofString "rfe_m2"
def rfeM3 := ofString "rfe_m3"
def rfeW := ofString "rfe_w"
def rfeR := ofString "rfe_r"
def fRfe := ofString "replaceFVarsErase"

def rfeParams : List MlS := [pFu, pH, rfeM]
def rfeLocals : List MlS := gaaLocals ++ [rfeB, rfeK, rfeX, rfeA1, rfeA2, rfeA3, rfeQ, rfeY, rfeZ, rfeV, rfeM1, rfeM2,
  rfeM3, rfeW, rfeR]

/-- Return the pair `[r, memo]`. -/
def rfeRet (C : Ctx) (r m : MlS) : ProgHOL 64 := alloc2 C rfeR (vv r) (vv m) (.return (vv rfeR))

/-- One child walked: `Q := rfv(child, memo)`, then its result in `y` and the memo in `m'`. -/
def rfeCall (x child memo y m' : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, x), none)) fRfe [.op .sub [vv pFu, .const 1], vv child, vv memo])
  (.seq (.assign .local y (.load .one (vv x)))
  (.seq (.assign .local m' (.load .one (.op .add [vv x, .const 8]))) rest))

/-- Memoise `h ↦ w` over the memo in `m`, and return. -/
def rfeSet (C : Ctx) (m : MlS) : ProgHOL 64 :=
  alloc3 C rfeM3 (vv pH) (vv rfeW) (vv m) (rfeRet C rfeW rfeM3)

def rfeBin (C : Ctx) (f : MlS) : ProgHOL 64 :=
  rfeCall rfeQ rfeA1 rfeM rfeY rfeM1 (rfeCall rfeQ rfeA2 rfeM1 rfeZ rfeM2
    (.seq (.call (some (some (.local, rfeW), none)) f [vv rfeY, vv rfeZ]) (rfeSet C rfeM2)))

def rfeLet (C : Ctx) : ProgHOL 64 :=
  rfeCall rfeQ rfeA1 rfeM rfeY rfeM1 (rfeCall rfeQ rfeA2 rfeM1 rfeZ rfeM2 (rfeCall rfeQ rfeA3 rfeM2 rfeV rfeM3
    (.seq (.call (some (some (.local, rfeW), none)) fInternLet [vv rfeY, vv rfeZ, vv rfeV])
      (alloc3 C rfeM2 (vv pH) (vv rfeW) (vv rfeM3) (rfeRet C rfeW rfeM2)))))

def rfeProj (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .notLower (vv rfeB) (.const (BitVec.ofNat 64 (2 ^ 63)))) hang
  (rfeCall rfeQ rfeA2 rfeM rfeY rfeM1
    (.seq (.call (some (some (.local, rfeW), none)) fInternProj [vv rfeA1, vv rfeY, vv rfeB]) (rfeSet C rfeM1)))

/-- The fvar arm: the variable at `Sort 0` (an index past `2^63` halts). -/
def rfeFvarIdx (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .notLower (vv rfeB) (.const (BitVec.ofNat 64 (2 ^ 63)))) hang
  (.seq (.assign .local rfeZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, rfeK), none)) fInternSort [vv rfeZ])
  (.seq (.call (some (some (.local, rfeX), none)) fInternFVar [vv rfeK, vv rfeB])
    (rfeRet C rfeX rfeM))))

def rfeFvar (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local rfeB (.const 0)) (rfeFvarIdx C))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local rfeB (.load .one (.op .add [vv lRp, .const 8]))) (rfeFvarIdx C))
      hang)

/-- A compound node: the view's children loaded, then the memo, then the arm. -/
def rfeNode (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rfeA1 (.load .one (vv lRp)))
  (.seq (.assign .local rfeA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lDg) (.const 7)) (.seq (.assign .local rfeA3 (.load .one (.op .add [vv lRp, .const 16])))
      (rfeMemo C (rfeLet C)))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local rfeB (.const 0)) (rfeMemo C (rfeProj C)))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local rfeB (.load .one (.op .add [vv lRp, .const 16]))) (rfeMemo C (rfeProj C))) hang))
  (rfeMemo C (.ite (.cmp .equal (vv lDg) (.const 4)) (rfeBin C fInternApp)
    (.ite (.cmp .equal (vv lDg) (.const 5)) (rfeBin C fInternLam) (rfeBin C fInternForallE)))))))
where
  rfeMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
    .seq (.call (some (some (.local, rfeX), none)) fMemoFind [vv rfeM, vv pH])
    (.ite (.cmp .equal (vv rfeX) (.const 0)) arm
      (.seq (.assign .local rfeX (.op .sub [vv rfeX, .const 1])) (rfeRet C rfeX rfeM)))

def rfeBody (C : Ctx) : ProgHOL 64 := prologue rfeLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (rfeFvar C)
  (.ite (.cmp .lower (vv lDg) (.const 4)) (rfeRet C pH rfeM)
  (.ite (.cmp .equal (vv lDg) (.const 8)) (rfeRet C pH rfeM) (rfeNode C))))))))

/-- The code `replaceFVarsErase` runs. -/
structure RFECodes (C : Ctx) : Prop where
  self : C.code.lookup fRfe = some (rfeParams.map (fun p => (p, ShapeHOL.one)), rfeBody C, .one)
  mf : C.code.lookup fMemoFind = some (mmfParams.map (fun p => (p, ShapeHOL.one)), mmfBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  lam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  fa : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  lt : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  pj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)

section
variable {σ : Type}

theorem rfe_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rfeLocals → (ctxEnv C ++ rfeParams.zip vals).get x = none :=
  Knot.params_none C rfeLocals rfeParams vals (by decide) (by decide)

/-- The walk at fuel `n`, from any heap holding the openers' block. -/
def RERec (C : Ctx) (n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx EIdx) (mw : BitVec 64) (H : List (BitVec 64)) (s : AState), C.H <+: H →
    MemoRep C.HB H mw memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (rfeParams.zip [BitVec.ofNat 64 n, Enc.idxW h, mw])) (rfeBody C) s
      (replaceFVarsGo .erase memo n h) (PostRF (ctxH C H))

/-- One child walked (`rfeCall`). -/
theorem rfe_call {β : Type} (C : Ctx) (hc : RFECodes C) (n : Nat) (ih : RERec (σ := σ) C n)
    {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx × Std.HashMap EIdx EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (hp : C.H <+: H)
    (x child memo y m' : MlS)
    (hx : x ∈ ctxLocals ++ rfeLocals ∧ y ∈ ctxLocals ++ rfeLocals ∧ m' ∈ ctxLocals ++ rfeLocals)
    (hne : y ≠ x ∧ m' ≠ x ∧ m' ≠ y)
    (c : EIdx) (memo0 : Std.HashMap EIdx EIdx) (mw : BitVec 64) (hm : MemoRep C.HB H mw memo0)
    (gF : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (gC : Γ.get child = some (Enc.idxW c))
    (gM : Γ.get memo = some mw)
    (hk : ∀ (r : EIdx × Std.HashMap EIdx EIdx) (H' : List (BitVec 64)) (op : Nat) (mw' : BitVec 64) (s' : AState),
      H <+: H' → MemoRep C.HB H' mw' r.2 →
      SpecR (Inv (ctxH C H') s' ((m', mw') :: (y, Enc.idxW r.1) :: (x, cellA C op) :: Γ) [] (ctxLocals ++ rfeLocals))
        rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ rfeLocals)) (rfeCall x child memo y m' rest) s
      (replaceFVarsGo .erase memo0 n c >>= k) R := by
  unfold rfeCall
  refine specR_callNIH (C := ctxH C H) x fRfe rfeParams [.op .sub [vv pFu, .const 1], vv child, vv memo]
    (rfeBody C) [BitVec.ofNat 64 n, Enc.idxW c, mw] (by decide) rfl hx.1 hc.self
    ⟨by simp only [sev, sev_vv, gF]; simp; exact ofNat_succ_sub_one n, by simp [sev, gC], by simp [sev, gM], trivial⟩
    (PostRF (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRep C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rfeParams _ rfl hlk) (ih c memo0 mw H s hp hm))
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
theorem rfe_set (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h r : EIdx) (m t : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx EIdx) (hbH : Hb <+: H)
    (hm : MemoRep C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get rfeW = some (Enc.idxW r))
    (gM : Γ.get m = some mw) (ht : t ∈ ctxLocals ++ rfeLocals) (htW : t ≠ rfeW ∧ t ≠ rfeR) (hmt : m ≠ t) (htH : t ≠ pH) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfeLocals))
      (alloc3 C t (vv pH) (vv rfeW) (vv m) (rfeRet C rfeW t)) s (pure (r, memo.insert h r)) (PostRF (ctxH C Hb)) := by
  refine specR_alloc3I (ctxOK_H hok H) t (vv pH) (vv rfeW) (vv m) (Enc.idxW h) (Enc.idxW r) mw ht
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htH e.symm)]; exact gH)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg hmt]; exact gM) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have h3 := img3_prefix H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have hp23 : H <+: _ := (hp2 : H <+: H2).trans h3
  have hm3 := memoRep_insert h r (memoRep_mono hp23 hm) g0 g1 g2
  unfold rfeRet
  refine specR_alloc2I (ctxOK_H hok _) rfeR (vv rfeW) (vv t) (Enc.idxW r) (cellA C H2.length) (by decide)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide), if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.2 e)]; simp; rfl)
    (fun H4 ws4 hp4 hws4 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  have h4 := img2_prefix H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  exact specR_returnI (vv rfeR) (cellA C H4.length) (by simp [sev, Env.get_cons]; rfl) (fun tt htt =>
    ⟨_, H4.length, cellA C H2.length, hbH.trans (hp23.trans ((hp4 : _ <+: H4).trans h4)), rfl, k0, k1,
      memoRep_mono ((hp4 : _ <+: H4).trans h4) hm3, sr_of_eq htt.sr rfl rfl rfl rfl⟩)

end

set_option maxHeartbeats 16000000 in
/-- **`replaceFVarsGo` at the erasing map**. -/
theorem rfe_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RFECodes C)
    : ∀ n, n < 2 ^ 64 → RERec (σ := σ) C n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo mw H s hp hm
    refine specR_prologue (postRF_locals _) (rfe_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rfeParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro hn h memo mw H s hp hm
    have ih' := ih (by omega)
    refine specR_prologue (postRF_locals _) (rfe_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rfeParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [replaceFVarsGo]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, rfeParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s = .ok (v, s) by rw [view_run, hv]) ?_
    -- the leaves
    have hleaf : ∀ (Γ : Env) (M : Mem), Γ.get pH = some (Enc.idxW h) → Γ.get rfeM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfeLocals)) (rfeRet C pH rfeM) s (pure (h, memo))
          (PostRF (ctxH C H)) := by
      intro Γ M gH gM
      unfold rfeRet
      refine specR_alloc2I (ctxOK_H hok H) rfeR (vv pH) (vv rfeM) (Enc.idxW h) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons, gH]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW h) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW h) mw hws
      exact specR_returnI (vv rfeR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hpH : ∀ (Γ0 : Env), Γ0 = ctxEnv (ctxH C H) ++ rfeParams.zip [BitVec.ofNat 64 (n + 1), Enc.idxW h, mw] →
        True := fun _ _ => trivial
    -- the memo step of a compound node
    have hmemo : ∀ (arm : ProgHOL 64) (mnone : AM (EIdx × Std.HashMap EIdx EIdx)) (Γ : Env) (M : Mem),
        Γ.get rfeM = some mw → Γ.get pH = some (Enc.idxW h) →
        (memo[h]? = none → SpecR (σ := σ) (Inv (ctxH C H) s ((rfeX, 0) :: Γ) [] (ctxLocals ++ rfeLocals)) arm s mnone
          (PostRF (ctxH C H))) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfeLocals)) (rfeNode.rfeMemo C arm) s
          (match memo[h]? with
            | some r => pure (r, memo)
            | none => mnone) (PostRF (ctxH C H)) := by
      intro arm mnone Γ M gM gH harm
      obtain ⟨L, hL, hlk⟩ := id hm
      unfold rfeNode.rfeMemo
      rw [hlk h]
      refine specR_pureBind (L.lookup h) ?_
      refine specR_callNIM rfeX fMemoFind mmfParams [vv rfeM, vv pH] mmfBody [mw, Enc.idxW h] (by decide) rfl (by decide)
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
      refine specR_assignI rfeX _ (Enc.idxW r) (by decide)
        (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      unfold rfeRet
      refine specR_alloc2I (ctxOK_H hok H) rfeR (vv rfeX) (vv rfeM) (Enc.idxW r) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW r) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW r) mw hws
      exact specR_returnI (vv rfeR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    cases v with
    | bvar i =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv])
    | sort u =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv])
    | const c us =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv])
    | lit l =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv])
    | fvar i ty =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      rw [fvMapAt]
      simp only [zeroLevel, bind_assoc, pure_bind]
      unfold rfeFvar
      have hlen1 : (encEView (.fvar i ty)).length = 1 + (Enc.limbs i).length := by simp [encEView, Enc.encFVar]; omega
      have hokH := ctxOK_H hok H
      -- the variable at `Sort 0`
      have hidx : ∀ (Γ : Env) (M : Mem), i < 2 ^ 64 → Γ.get rfeB = some (BitVec.ofNat 64 i) → Γ.get rfeM = some mw →
          SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rfeLocals)) (rfeFvarIdx C) s
            (pinZeroLevel >>= fun z => internSortE z >>= fun sz => internFVarE i sz >>= fun v => pure (v, memo))
            (PostRF (ctxH C H)) := by
        intro Γ M hi gB gM
        unfold rfeFvarIdx
        by_cases h63 : i < 2 ^ 63
        swap
        · exact specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [gB, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
            (fun _ => specR_hangI) (fun h => absurd h (by decide))
        refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [gB, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_pinXI hokH pinZeroLevel 1 C.pins.zeroLevel _ (fun s hp => pinZeroLevel_run hokH hp)
          (pin_zeroLevel_cell hokH) rfeZ (by decide) ?_
        refine ILP.callE_spec rfeK fInternSort [lEu] [vv rfeZ] sortBody [Enc.idxW C.pins.zeroLevel] (by decide) rfl
          (by decide) hc.srt ⟨by simp [sev, Env.get_cons]; rfl, trivial⟩
          (sort_body_spec ra (ctxH C H) hokH s C.pins.zeroLevel) (fun s0 s1 => ?_)
        refine ILP.specR_internFVarI ra hokH hc.fv rfeX (vv rfeK) (vv rfeB) s0 i h63 (by decide)
          (by simp [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, gB]) (fun x s2 => ?_)
        unfold rfeRet
        refine specR_alloc2I (ctxOK_H hok H) rfeR (vv rfeX) (vv rfeM) (Enc.idxW x) mw (by decide)
          (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
          (fun H2 ws hp2 hws => ?_)
        obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW x) mw hws
        have h2 := img2_prefix H2 ws (Enc.idxW x) mw hws
        exact specR_returnI (vv rfeR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
          ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
            sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI rfeB (.const 0) 0 (by decide) rfl ?_
        exact hidx _ _ (by decide) (by simp) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv])
      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' rfeB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 i) [] (M := [])
              simpa [encEView, Enc.encFVar, hl] using this) ?_
        exact hidx _ _ ib (by simp) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv])
      have hge : 2 ≤ (Enc.limbs i).length := by
        have := (Big.limbs_length_lt_iff i 1).not.mpr (by simp [Big.B]; omega); omega
      have hsh' : 1 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen1]; exact hlen
      have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 1#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 2#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn1)
        (fun hw => absurd rfl hw) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp +decide [sev, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn2)
        (fun hw => absurd rfl hw) (fun _ => specR_hangI)
    | app a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfeNode
      refine specR_loadI' rfeA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rfeA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rfeBin
      simp only [bind_assoc]
      refine rfe_call C hc n ih' H hp rfeQ rfeA1 rfeM rfeY rfeM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rfe_call C hc n ih' H1 (hp.trans hp1) rfeQ rfeA2 rfeM1 rfeZ rfeM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internAppI ra (ctxOK_H hok H2) hc.app rfeW (vv rfeY) (vv rfeZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rfeSet
      exact rfe_set C hok H2 H h w rfeM2 rfeM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | lam a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfeNode
      refine specR_loadI' rfeA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rfeA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rfeBin
      simp only [bind_assoc]
      refine rfe_call C hc n ih' H hp rfeQ rfeA1 rfeM rfeY rfeM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rfe_call C hc n ih' H1 (hp.trans hp1) rfeQ rfeA2 rfeM1 rfeZ rfeM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internLamI ra (ctxOK_H hok H2) hc.lam rfeW (vv rfeY) (vv rfeZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rfeSet
      exact rfe_set C hok H2 H h w rfeM2 rfeM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | forallE a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfeNode
      refine specR_loadI' rfeA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rfeA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfeBin
      simp only [bind_assoc]
      refine rfe_call C hc n ih' H hp rfeQ rfeA1 rfeM rfeY rfeM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rfe_call C hc n ih' H1 (hp.trans hp1) rfeQ rfeA2 rfeM1 rfeZ rfeM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internForallEI ra (ctxOK_H hok H2) hc.fa rfeW (vv rfeY) (vv rfeZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rfeSet
      exact rfe_set C hok H2 H h w rfeM2 rfeM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | letE ty v b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfeNode
      refine specR_loadI' rfeA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW v, Enc.idxW b] []) ?_
      refine specR_loadI' rfeA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' rfeA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v) (Enc.idxW b) [] []) ?_
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun _ => ?_)
      unfold rfeLet
      simp only [bind_assoc]
      refine rfe_call C hc n ih' H hp rfeQ rfeA1 rfeM rfeY rfeM1 (by decide) (by decide) ty memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨t2, m1⟩ := r1
      simp only
      refine rfe_call C hc n ih' H1 (hp.trans hp1) rfeQ rfeA2 rfeM1 rfeZ rfeM2 (by decide)
        (by decide) v m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨v2, m2⟩ := r2
      simp only
      refine rfe_call C hc n ih' H2 ((hp.trans hp1).trans hp2) rfeQ rfeA3 rfeM2
        rfeV rfeM3 (by decide) (by decide) b m2 mw2 hm2 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r3 H3 op3 mw3 s3 hp3 hm3 => ?_)
      obtain ⟨b2, m3⟩ := r3
      simp only
      refine specR_internLetI ra (ctxOK_H hok H3) hc.lt rfeW (vv rfeY) (vv rfeZ) (vv rfeV) t2 v2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv])
        (fun w s4 => ?_)
      simp only [pure_bind]
      exact rfe_set C hok H3 H h w rfeM3 rfeM2 mw3 m3 ((hp1.trans hp2).trans hp3) hm3 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by decide)
        ⟨by decide, by decide⟩ (by decide) (by decide)
    | proj nm i e =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rfeNode
      have hlenp : (encEView (.proj nm i e)).length = 2 + (Enc.limbs i).length := by simp [encEView, Enc.encProj]; omega
      refine specR_loadI' rfeA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW nm) (Enc.idxW e :: Enc.limbs i) []) ?_
      refine specR_loadI' rfeA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW nm) (Enc.idxW e) (Enc.limbs i) []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_assignI rfeB (.const 0) 0 (by decide) rfl ?_
        refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun _ => ?_)
        unfold rfeProj
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only [bind_assoc]
        refine rfe_call C hc n ih' H hp rfeQ rfeA2 rfeM rfeY rfeM1 (by decide) (by decide) e memo mw hm
          (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
        obtain ⟨u2, m1⟩ := r1
        simp only
        refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rfeW (vv rfeA1) (vv rfeY) (vv rfeB) nm _ u2 (by decide) (by decide)
          (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun w s2 => ?_)
        simp only [pure_bind]
        unfold rfeSet
        exact rfe_set C hok H1 H h w rfeM1 rfeM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
          (by decide) (by decide)

      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_loadI' rfeB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev, Env.get_cons]) rfl
          (by simpa [encEView, Enc.encProj, hl] using wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] []) ?_
        by_cases h63 : i < 2 ^ 63
        · have hi63 : i < 2 ^ 63 := h63
          refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun _ => ?_)
          unfold rfeProj
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
            (fun h => absurd rfl h) (fun _ => ?_)
          simp only [bind_assoc]
          refine rfe_call C hc n ih' H hp rfeQ rfeA2 rfeM rfeY rfeM1 (by decide) (by decide) e memo mw hm
            (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
          obtain ⟨u2, m1⟩ := r1
          simp only
          refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rfeW (vv rfeA1) (vv rfeY) (vv rfeB) nm _ u2 (hi63) (by decide)
            (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun w s2 => ?_)
          simp only [pure_bind]
          unfold rfeSet
          exact rfe_set C hok H1 H h w rfeM1 rfeM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
            (by decide) (by decide)

        · refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rfeParams, ctxEnv]) (fun _ => ?_)
          unfold rfeProj
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

/-! ## `eraseFVarTys` -/

def eftE := ofString "eft_e"
def eftQ := ofString "eft_q"
def eftR := ofString "eft_r"
def fEft := ofString "eraseFVarTys"

def eftParams : List MlS := [eftE]
def eftLocals : List MlS := [eftQ, eftR]

def eftBody : ProgHOL 64 := prologue eftLocals
  (.seq (.call (some (some (.local, eftQ), none)) fRfe [.const (BitVec.ofNat 64 coreWalkFuel), vv eftE, .const 0])
  (.seq (.assign .local eftR (.load .one (vv eftQ))) (.return (vv eftR))))

structure EFTCodes (C : Ctx) : Prop where
  rfe : RFECodes C
  self : C.code.lookup fEft = some (eftParams.map (fun p => (p, ShapeHOL.one)), eftBody, .one)

section
variable {σ : Type}

theorem eft_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ eftLocals → (ctxEnv C ++ eftParams.zip vals).get x = none :=
  Knot.params_none C eftLocals eftParams vals (by decide) (by decide)

/-- **`eraseFVarTys e`**. -/
theorem eft_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : EFTCodes C)
    (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre (ctxH C H) s (eftParams.zip [Enc.idxW e])) eftBody s (eraseFVarTys e)
      (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (eft_none _ _) ?_
  unfold eraseFVarTys replaceFVars
  refine specR_callNIH (C := ctxH C H) eftQ fRfe rfeParams [.const (BitVec.ofNat 64 coreWalkFuel), vv eftE, .const 0]
    (rfeBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0] (by decide) rfl (by decide) hc.rfe.self
    ⟨rfl, by simp +decide [sev, Env.get, eftParams, ctxEnv], rfl, trivial⟩
    (PostRF (ctxH C H)) (fun r w _ H' => ∃ op, w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1))
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, _, _, hsr⟩ => ⟨H', hp', ⟨op, hw, h1⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rfeParams _ rfl hlk)
      (rfe_spec ra C hok hc.rfe coreWalkFuel CV.coreWalkFuel_lt e ∅ 0 H s hp ⟨[], rfl, fun k => by simp⟩))
    (fun r w s1 H1 hp1 ⟨op, hw, h1⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) eftR (vv eftQ) op _ h1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
