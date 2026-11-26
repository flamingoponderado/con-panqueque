import ConPanqueque.T.Ind.Crest

/-!
# `replaceFVars` at the root frame's hole image (`nestCtorNf`'s readback)

Derived from the canonical walk: a hole `nP + m` reads back as `T_m.{lvls} params` (interned on each visit of the
variable, which is not memoised), any other variable as itself.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def rhiM := ofString "rhi_m"
def rhiP := ofString "rhi_p"
def rhiB := ofString "rhi_b"
def rhiK := ofString "rhi_k"
def rhiX := ofString "rhi_x"
def rhiA1 := ofString "rhi_a1"
def rhiA2 := ofString "rhi_a2"
def rhiA3 := ofString "rhi_a3"
def rhiQ := ofString "rhi_q"
def rhiY := ofString "rhi_y"
def rhiZ := ofString "rhi_z"
def rhiV := ofString "rhi_v"
def rhiM1 := ofString "rhi_m1"
def rhiM2 := ofString "rhi_m2"
def rhiM3 := ofString "rhi_m3"
def rhiW := ofString "rhi_w"
def rhiR := ofString "rhi_r"
def fRhi := ofString "replaceFVarsHoleImg"

def rhiMs := ofString "rhi_ms"
def rhiNP := ofString "rhi_np"
def rhiUs := ofString "rhi_us"
def rhiT := ofString "rhi_t"
def rhiL := ofString "rhi_l"
def rhiPm := ofString "rhi_pm"
def rhiQc := ofString "rhi_qc"
def rhiNm := ofString "rhi_nm"
def rhiHd := ofString "rhi_hd"
def rhiL2 := ofString "rhi_l2"
def rhiAp := ofString "rhi_ap"

def rhiParams : List MlS := [pFu, pH, rhiM, rhiMs, rhiNP, rhiUs, rhiP]
def rhiLocals : List MlS := gaaLocals ++ [rhiB, rhiK, rhiX, rhiA1, rhiA2, rhiA3, rhiQ, rhiY, rhiZ, rhiV, rhiM1, rhiM2,
  rhiM3, rhiW, rhiR, rhiT, rhiL, rhiPm, rhiQc, rhiNm, rhiHd, rhiL2, rhiAp]

/-- Return the pair `[r, memo]`. -/
def rhiRet (C : Ctx) (r m : MlS) : ProgHOL 64 := alloc2 C rhiR (vv r) (vv m) (.return (vv rhiR))

/-- One child walked: `Q := rfv(child, memo)`, then its result in `y` and the memo in `m'`. -/
def rhiCall (x child memo y m' : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, x), none)) fRhi [.op .sub [vv pFu, .const 1], vv child, vv memo, vv rhiMs, vv rhiNP, vv rhiUs, vv rhiP])
  (.seq (.assign .local y (.load .one (vv x)))
  (.seq (.assign .local m' (.load .one (.op .add [vv x, .const 8]))) rest))

/-- Memoise `h ↦ w` over the memo in `m`, and return. -/
def rhiSet (C : Ctx) (m : MlS) : ProgHOL 64 :=
  alloc3 C rhiM3 (vv pH) (vv rhiW) (vv m) (rhiRet C rhiW rhiM3)

def rhiBin (C : Ctx) (f : MlS) : ProgHOL 64 :=
  rhiCall rhiQ rhiA1 rhiM rhiY rhiM1 (rhiCall rhiQ rhiA2 rhiM1 rhiZ rhiM2
    (.seq (.call (some (some (.local, rhiW), none)) f [vv rhiY, vv rhiZ]) (rhiSet C rhiM2)))

def rhiLet (C : Ctx) : ProgHOL 64 :=
  rhiCall rhiQ rhiA1 rhiM rhiY rhiM1 (rhiCall rhiQ rhiA2 rhiM1 rhiZ rhiM2 (rhiCall rhiQ rhiA3 rhiM2 rhiV rhiM3
    (.seq (.call (some (some (.local, rhiW), none)) fInternLet [vv rhiY, vv rhiZ, vv rhiV])
      (alloc3 C rhiM2 (vv pH) (vv rhiW) (vv rhiM3) (rhiRet C rhiW rhiM2)))))

def rhiProj (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .notLower (vv rhiB) (.const (BitVec.ofNat 64 (2 ^ 63)))) hang
  (rhiCall rhiQ rhiA2 rhiM rhiY rhiM1
    (.seq (.call (some (some (.local, rhiW), none)) fInternProj [vv rhiA1, vv rhiY, vv rhiB]) (rhiSet C rhiM1)))

/-- The fvar arm: a hole `nP + m` is `T_m.{lvls} params`, any other variable itself. -/
def rhiFvarIdx (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv rhiB) (vv rhiNP)) (rhiRet C pH rhiM)
  (.seq (.assign .local rhiT (.op .sub [vv rhiB, vv rhiNP]))
  (.seq (.assign .local rhiL (.load .one (vv rhiMs)))
  (.ite (.cmp .lower (vv rhiT) (vv rhiL))
    (.seq (.assign .local rhiPm (.load .one (.op .add [.op .add [vv rhiMs, .const 8], .shift .lsl (vv rhiT) (.const 3)])))
    (.seq (.assign .local rhiQc (.load .one (vv rhiPm)))
    (.seq (.assign .local rhiNm (.load .one (vv rhiQc)))
    (.seq (.call (some (some (.local, rhiHd), none)) fInternConst [vv rhiNm, vv rhiUs])
    (.seq (.assign .local rhiL2 (.load .one (vv rhiP)))
    (.seq (.call (some (some (.local, rhiAp), none)) ExK.fMka [vv rhiHd, vv rhiP, .const 0, vv rhiL2])
      (rhiRet C rhiAp rhiM)))))))
    (rhiRet C pH rhiM))))

def rhiFvar (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local rhiB (.const 0)) (rhiFvarIdx C))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local rhiB (.load .one (.op .add [vv lRp, .const 8]))) (rhiFvarIdx C))
      (rhiRet C pH rhiM))

/-- A compound node: the view's children loaded, then the memo, then the arm. -/
def rhiNode (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rhiA1 (.load .one (vv lRp)))
  (.seq (.assign .local rhiA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lDg) (.const 7)) (.seq (.assign .local rhiA3 (.load .one (.op .add [vv lRp, .const 16])))
      (rhiMemo C (rhiLet C)))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local rhiB (.const 0)) (rhiMemo C (rhiProj C)))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local rhiB (.load .one (.op .add [vv lRp, .const 16]))) (rhiMemo C (rhiProj C))) hang))
  (rhiMemo C (.ite (.cmp .equal (vv lDg) (.const 4)) (rhiBin C fInternApp)
    (.ite (.cmp .equal (vv lDg) (.const 5)) (rhiBin C fInternLam) (rhiBin C fInternForallE)))))))
where
  rhiMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
    .seq (.call (some (some (.local, rhiX), none)) fMemoFind [vv rhiM, vv pH])
    (.ite (.cmp .equal (vv rhiX) (.const 0)) arm
      (.seq (.assign .local rhiX (.op .sub [vv rhiX, .const 1])) (rhiRet C rhiX rhiM)))

def rhiBody (C : Ctx) : ProgHOL 64 := prologue rhiLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (rhiFvar C)
  (.ite (.cmp .lower (vv lDg) (.const 4)) (rhiRet C pH rhiM)
  (.ite (.cmp .equal (vv lDg) (.const 8)) (rhiRet C pH rhiM) (rhiNode C))))))))

/-- The code `replaceFVarsCanon` runs. -/
structure RHICodes (C : Ctx) : Prop where
  self : C.code.lookup fRhi = some (rhiParams.map (fun p => (p, ShapeHOL.one)), rhiBody C, .one)
  mf : C.code.lookup fMemoFind = some (mmfParams.map (fun p => (p, ShapeHOL.one)), mmfBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  lam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  fa : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  lt : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  pj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)

section
variable {σ : Type}

theorem rhi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rhiLocals → (ctxEnv C ++ rhiParams.zip vals).get x = none :=
  Knot.params_none C rhiLocals rhiParams vals (by decide) (by decide)

/-- The walk's answer: a pair `[r, memo]`, the memo represented. -/
def PostRHI (C : Ctx) (r : EIdx × Std.HashMap EIdx EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' op mw', C.H <+: H' ∧ w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧ H'[op + 1]? = some mw' ∧
    MemoRep C.HB H' mw' r.2 ∧ SR (ctxH C H') s' st

theorem postRHI_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRHI C a w s' st → PostRHI C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', op, mw', hp, hw, h1, h2, h3, hs⟩ => ⟨H', op, mw', hp, hw, h1, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

/-- The walk at fuel `n`, from any heap holding the openers' block. -/
def RHRec (C : Ctx) (ctx : NestCtx) (om nP pp n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx EIdx) (mw : BitVec 64) (H : List (BitVec 64)) (s : AState), C.H <+: H →
    BlkAt H pp (ctx.params.map Enc.idxW) → MemoRep C.HB H mw memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (rhiParams.zip [BitVec.ofNat 64 n, Enc.idxW h, mw, cellA C om, BitVec.ofNat 64 nP,
      Enc.idxW ctx.lvls, cellA C pp])) (rhiBody C) s
      (replaceFVarsGo (.holeImg ctx [] 0) memo n h) (PostRHI (ctxH C H))

/-- One child walked (`rhiCall`). -/
theorem rhi_call {β : Type} (C : Ctx) (hc : RHICodes C) (ctx : NestCtx) (om nP pp n : Nat) (ih : RHRec (σ := σ) C ctx om nP pp n)
    {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx × Std.HashMap EIdx EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (hp : C.H <+: H)
    (hpf : BlkAt H pp (ctx.params.map Enc.idxW)) (x child memo y m' : MlS)
    (hx : x ∈ ctxLocals ++ rhiLocals ∧ y ∈ ctxLocals ++ rhiLocals ∧ m' ∈ ctxLocals ++ rhiLocals)
    (hne : y ≠ x ∧ m' ≠ x ∧ m' ≠ y)
    (c : EIdx) (memo0 : Std.HashMap EIdx EIdx) (mw : BitVec 64) (hm : MemoRep C.HB H mw memo0)
    (gF : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (gC : Γ.get child = some (Enc.idxW c))
    (gM : Γ.get memo = some mw) (gMs : Γ.get rhiMs = some (cellA C om))
    (gNP : Γ.get rhiNP = some (BitVec.ofNat 64 nP)) (gUs : Γ.get rhiUs = some (Enc.idxW ctx.lvls))
    (gP : Γ.get rhiP = some (cellA C pp))
    (hk : ∀ (r : EIdx × Std.HashMap EIdx EIdx) (H' : List (BitVec 64)) (op : Nat) (mw' : BitVec 64) (s' : AState),
      H <+: H' → MemoRep C.HB H' mw' r.2 →
      SpecR (Inv (ctxH C H') s' ((m', mw') :: (y, Enc.idxW r.1) :: (x, cellA C op) :: Γ) [] (ctxLocals ++ rhiLocals))
        rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ rhiLocals)) (rhiCall x child memo y m' rest) s
      (replaceFVarsGo (.holeImg ctx [] 0) memo0 n c >>= k) R := by
  unfold rhiCall
  refine specR_callNIH (C := ctxH C H) x fRhi rhiParams [.op .sub [vv pFu, .const 1], vv child, vv memo, vv rhiMs, vv rhiNP, vv rhiUs, vv rhiP]
    (rhiBody C) [BitVec.ofNat 64 n, Enc.idxW c, mw, cellA C om, BitVec.ofNat 64 nP, Enc.idxW ctx.lvls, cellA C pp] (by decide) rfl hx.1 hc.self
    ⟨by simp only [sev, sev_vv, gF]; simp; exact ofNat_succ_sub_one n, by simp [sev, gC], by simp [sev, gM],
      by simp [sev, gMs], by simp [sev, gNP], by simp [sev, gUs], by simp [sev, gP], trivial⟩
    (PostRHI (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRep C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rhiParams _ rfl hlk) (ih c memo0 mw H s hp hpf hm))
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
theorem rhi_set (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64))
    (h r : EIdx) (m t : MlS) (mw : BitVec 64) (memo : Std.HashMap EIdx EIdx) (hbH : Hb <+: H)
    (hm : MemoRep C.HB H mw memo) (gH : Γ.get pH = some (Enc.idxW h)) (gW : Γ.get rhiW = some (Enc.idxW r))
    (gM : Γ.get m = some mw) (ht : t ∈ ctxLocals ++ rhiLocals) (htW : t ≠ rhiW ∧ t ≠ rhiR) (hmt : m ≠ t) (htH : t ≠ pH) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rhiLocals))
      (alloc3 C t (vv pH) (vv rhiW) (vv m) (rhiRet C rhiW t)) s (pure (r, memo.insert h r)) (PostRHI (ctxH C Hb)) := by
  refine specR_alloc3I (ctxOK_H hok H) t (vv pH) (vv rhiW) (vv m) (Enc.idxW h) (Enc.idxW r) mw ht
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htH e.symm)]; exact gH)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg hmt]; exact gM) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have h3 := img3_prefix H2 ws (Enc.idxW h) (Enc.idxW r) mw hws
  have hp23 : H <+: _ := (hp2 : H <+: H2).trans h3
  have hm3 := memoRep_insert h r (memoRep_mono hp23 hm) g0 g1 g2
  unfold rhiRet
  refine specR_alloc2I (ctxOK_H hok _) rhiR (vv rhiW) (vv t) (Enc.idxW r) (cellA C H2.length) (by decide)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (by decide), if_neg (fun e => htW.1 e.symm)]; exact gW)
    (fun _ => by simp only [sev, sev_vv, Env.get_cons]; rw [if_neg (fun e => htW.2 e)]; simp; rfl)
    (fun H4 ws4 hp4 hws4 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  have h4 := img2_prefix H4 ws4 (Enc.idxW r) (cellA C H2.length) hws4
  exact specR_returnI (vv rhiR) (cellA C H4.length) (by simp [sev, Env.get_cons]; rfl) (fun tt htt =>
    ⟨_, H4.length, cellA C H2.length, hbH.trans (hp23.trans ((hp4 : _ <+: H4).trans h4)), rfl, k0, k1,
      memoRep_mono ((hp4 : _ <+: H4).trans h4) hm3, sr_of_eq htt.sr rfl rfl rfl rfl⟩)

end

set_option maxHeartbeats 16000000 in
/-- **`replaceFVarsGo` at the root frame's hole image**. -/
theorem rhi_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RHICodes C)
    (ctx : NestCtx) (ms : List MemberShape) (om nP pp : Nat) (hml : ms.length < 2 ^ 59)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (hnP : nP < 2 ^ 62) (hpl : ctx.params.length < 2 ^ 59) :
    ∀ n, n < 2 ^ 64 → RHRec (σ := σ) C ctx om nP pp n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo mw H s hp hpf hm
    refine specR_prologue (postRHI_locals _) (rhi_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rhiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro hn h memo mw H s hp hpf hm
    have ih' := ih (by omega)
    refine specR_prologue (postRHI_locals _) (rhi_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rhiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [replaceFVarsGo]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, rhiParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s = .ok (v, s) by rw [view_run, hv]) ?_
    -- the leaves
    have hleaf : ∀ (Γ : Env) (M : Mem), Γ.get pH = some (Enc.idxW h) → Γ.get rhiM = some mw →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rhiLocals)) (rhiRet C pH rhiM) s (pure (h, memo))
          (PostRHI (ctxH C H)) := by
      intro Γ M gH gM
      unfold rhiRet
      refine specR_alloc2I (ctxOK_H hok H) rhiR (vv pH) (vv rhiM) (Enc.idxW h) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons, gH]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW h) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW h) mw hws
      exact specR_returnI (vv rhiR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hpH : ∀ (Γ0 : Env), Γ0 = ctxEnv (ctxH C H) ++ rhiParams.zip [BitVec.ofNat 64 (n + 1), Enc.idxW h, mw, cellA C pp] →
        True := fun _ _ => trivial
    -- the memo step of a compound node
    have hmemo : ∀ (arm : ProgHOL 64) (mnone : AM (EIdx × Std.HashMap EIdx EIdx)) (Γ : Env) (M : Mem),
        Γ.get rhiM = some mw → Γ.get pH = some (Enc.idxW h) →
        (memo[h]? = none → SpecR (σ := σ) (Inv (ctxH C H) s ((rhiX, 0) :: Γ) [] (ctxLocals ++ rhiLocals)) arm s mnone
          (PostRHI (ctxH C H))) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rhiLocals)) (rhiNode.rhiMemo C arm) s
          (match memo[h]? with
            | some r => pure (r, memo)
            | none => mnone) (PostRHI (ctxH C H)) := by
      intro arm mnone Γ M gM gH harm
      obtain ⟨L, hL, hlk⟩ := id hm
      unfold rhiNode.rhiMemo
      rw [hlk h]
      refine specR_pureBind (L.lookup h) ?_
      refine specR_callNIM rhiX fMemoFind mmfParams [vv rhiM, vv pH] mmfBody [mw, Enc.idxW h] (by decide) rfl (by decide)
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
      refine specR_assignI rhiX _ (Enc.idxW r) (by decide)
        (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      unfold rhiRet
      refine specR_alloc2I (ctxOK_H hok H) rhiR (vv rhiX) (vv rhiM) (Enc.idxW r) mw (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
        (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW r) mw hws
      have h2 := img2_prefix H2 ws (Enc.idxW r) mw hws
      exact specR_returnI (vv rhiR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    cases v with
    | bvar i =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv])
    | sort u =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv])
    | const c us =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv])
    | lit l =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv])
    | fvar i ty =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      rw [fvMapAt]
      try simp only
      unfold rhiFvar
      have hlen1 : (encEView (.fvar i ty)).length = 1 + (Enc.limbs i).length := by simp [encEView, Enc.encFVar]; omega
      have hpl := blkAt_len_le hpf
      simp only [List.length_map] at hpl
      refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
      have hHN' : H.length ≤ C.HN := hHN
      have hlay := hok.heapLay
      have hidx : ∀ (Γ : Env) (M : Mem), i < 2 ^ 64 → Γ.get rhiB = some (BitVec.ofNat 64 i) →
          Γ.get pH = some (Enc.idxW h) → Γ.get rhiM = some mw → Γ.get rhiMs = some (cellA C om) →
          Γ.get rhiNP = some (BitVec.ofNat 64 nP) → Γ.get rhiUs = some (Enc.idxW ctx.lvls) →
          Γ.get rhiP = some (cellA C pp) →
          SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ rhiLocals)) (rhiFvarIdx C) s
            (nestHoleImg ctx [] 0 i >>= fun o => match o with
              | some r => pure (r, memo)
              | none => pure (h, memo)) (PostRHI (ctxH C H)) := by
        intro Γ M hi gB gH gM gMs gNP gUs gP
        unfold rhiFvarIdx
        rw [nestHoleImg]
        have hM' : PtrsRep C H om (MemberRep C H) ms := ptrsRep_mono hp (fun _ _ => memberRep_mono hp) hM
        have hlo := ConPanqueque.T.Decl.nd_lt_iff i nP hi (by omega)
        by_cases hl : i < nP
        · rw [if_neg (by simp [hP]; omega)]
          simp only [pure_bind]
          refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [gB, gNP, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlo.mpr hl])
            (fun _ => ?_) (fun h => absurd h (by decide))
          exact hleaf _ _ gH gM
        refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [gB, gNP, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlo.not.mpr hl])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI rhiT _ (BitVec.ofNat 64 (i - nP)) (by decide)
          (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, gB, gNP]
              apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H) rhiL (vv rhiMs) om _ hM'.1 (by decide)
          (by simp +decide [sev, Env.get_cons, gMs]; rfl) ?_
        have htw := ConPanqueque.T.Decl.nd_lt_iff (i - nP) ms.length (by omega) (by omega)
        by_cases ht : i - nP < ms.length
        swap
        · rw [if_neg (by simp [hP, NestCtx.hiAt, hN]; omega)]
          simp only [pure_bind]
          refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htw.not.mpr ht])
            (fun h => absurd rfl h) (fun _ => ?_)
          exact hleaf _ _ (by simp +decide [Env.get_cons, gH]) (by simp +decide [Env.get_cons, gM])
        rw [if_pos (by simp [hP, NestCtx.hiAt, hN]; omega)]
        refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htw.mpr ht])
          (fun _ => ?_) (fun h => absurd h (by decide))
        obtain ⟨ot, hot1, ⟨oc, hoc1, hoc2⟩, -⟩ := hM'.2 (i - nP) ht
        refine UD.specR_heapLoadI' (C := ctxH C H) rhiPm _ (om + 1 + (i - nP)) _ hot1 (by decide)
          (by simp +decide [sev, Env.get_cons, gMs]; show _ = cellA C (om + 1 + (i - nP))
              rw [← cellA_shl C (om + 1) (i - nP) (by omega), ← cellA_add8]; rfl) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H) rhiQc (vv rhiPm) ot _ hoc1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H) rhiNm (vv rhiQc) oc _ hoc2.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
        have hnm : ctx.names.getD (i - ctx.nP) default = ms[i - nP].cvT.name := by simp [hN, hP, ht]
        rw [hnm]
        simp only [bind_assoc]
        refine ILP.callE_spec (C := ctxH C H) rhiHd fInternConst [lEn, lEus] [vv rhiNm, vv rhiUs] constBody
          [Enc.idxW ms[i - nP].cvT.name, Enc.idxW ctx.lvls] (by decide) rfl (by decide) hc.ic
          ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, gUs], trivial⟩
          (by exact const_body_spec ra (ctxH C H) (ctxOK_H hok H) s _ _) (fun hd s2 => ?_)
        refine UD.specR_heapLoadI' (C := ctxH C H) rhiL2 (vv rhiP) pp _ hpf.1 (by decide)
          (by simp +decide [sev, Env.get_cons, gP]; rfl) ?_
        refine ILP.callE_spec (C := ctxH C H) rhiAp ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
          [vv rhiHd, vv rhiP, .const 0, vv rhiL2] ExK.mkaBody
          [Enc.idxW hd, cellA C pp, BitVec.ofNat 64 0, BitVec.ofNat 64 ctx.params.length] (by decide) rfl (by decide) hc.mka
          ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, gP], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
          (ExK.mkAppN_spec ra (ctxH C H) (ctxOK_H hok H) hc.mka hc.app pp ctx.params hpf (by omega) 0 (by omega) hd s2)
          (fun r s3 => ?_)
        simp only [pure_bind]
        unfold rhiRet
        refine specR_alloc2I (ctxOK_H hok H) rhiR (vv rhiAp) (vv rhiM) (Enc.idxW r) mw (by decide)
          (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons, gM])
          (fun H2 ws hp2 hws => ?_)
        obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW r) mw hws
        have h2 := img2_prefix H2 ws (Enc.idxW r) mw hws
        exact specR_returnI (vv rhiR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
          ⟨_, H2.length, mw, (hp2 : H <+: H2).trans h2, rfl, g0, g1, memoRep_mono ((hp2 : H <+: H2).trans h2) hm,
            sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI rhiB (.const 0) 0 (by decide) rfl ?_
        refine hidx _ _ (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]
      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' rhiB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 i) [] (M := [])
              simpa [encEView, Enc.encFVar, hl] using this) ?_
        refine hidx _ _ ib ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]
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
      rw [nestHoleImg, if_neg (by simp [hP, NestCtx.hiAt, hN]; omega)]
      simp only [pure_bind]
      exact hleaf _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv])
    | app a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rhiNode
      refine specR_loadI' rhiA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rhiA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rhiBin
      simp only [bind_assoc]
      refine rhi_call C hc ctx om nP pp n ih' H hp hpf rhiQ rhiA1 rhiM rhiY rhiM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rhi_call C hc ctx om nP pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rhiQ rhiA2 rhiM1 rhiZ rhiM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internAppI ra (ctxOK_H hok H2) hc.app rhiW (vv rhiY) (vv rhiZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rhiSet
      exact rhi_set C hok H2 H h w rhiM2 rhiM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | lam a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rhiNode
      refine specR_loadI' rhiA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rhiA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold rhiBin
      simp only [bind_assoc]
      refine rhi_call C hc ctx om nP pp n ih' H hp hpf rhiQ rhiA1 rhiM rhiY rhiM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rhi_call C hc ctx om nP pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rhiQ rhiA2 rhiM1 rhiZ rhiM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internLamI ra (ctxOK_H hok H2) hc.lam rhiW (vv rhiY) (vv rhiZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rhiSet
      exact rhi_set C hok H2 H h w rhiM2 rhiM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | forallE a b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rhiNode
      refine specR_loadI' rhiA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' rhiA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rhiBin
      simp only [bind_assoc]
      refine rhi_call C hc ctx om nP pp n ih' H hp hpf rhiQ rhiA1 rhiM rhiY rhiM1 (by decide) (by decide) a memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨a2, m1⟩ := r1
      simp only
      refine rhi_call C hc ctx om nP pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rhiQ rhiA2 rhiM1 rhiZ rhiM2 (by decide)
        (by decide) b m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨b2, m2⟩ := r2
      simp only
      refine specR_internForallEI ra (ctxOK_H hok H2) hc.fa rhiW (vv rhiY) (vv rhiZ) a2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun w s3 => ?_)
      simp only [pure_bind]
      unfold rhiSet
      exact rhi_set C hok H2 H h w rhiM2 rhiM3 mw2 m2 (hp1.trans hp2) hm2 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
        (by decide) (by decide)
    | letE ty v b =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rhiNode
      refine specR_loadI' rhiA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW v, Enc.idxW b] []) ?_
      refine specR_loadI' rhiA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' rhiA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v) (Enc.idxW b) [] []) ?_
      refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun _ => ?_)
      unfold rhiLet
      simp only [bind_assoc]
      refine rhi_call C hc ctx om nP pp n ih' H hp hpf rhiQ rhiA1 rhiM rhiY rhiM1 (by decide) (by decide) ty memo mw hm
        (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
      obtain ⟨t2, m1⟩ := r1
      simp only
      refine rhi_call C hc ctx om nP pp n ih' H1 (hp.trans hp1) (blkAt_mono hpf hp1) rhiQ rhiA2 rhiM1 rhiZ rhiM2 (by decide)
        (by decide) v m1 mw1 hm1 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r2 H2 op2 mw2 s2 hp2 hm2 => ?_)
      obtain ⟨v2, m2⟩ := r2
      simp only
      refine rhi_call C hc ctx om nP pp n ih' H2 ((hp.trans hp1).trans hp2) (blkAt_mono hpf (hp1.trans hp2)) rhiQ rhiA3 rhiM2
        rhiV rhiM3 (by decide) (by decide) b m2 mw2 hm2 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r3 H3 op3 mw3 s3 hp3 hm3 => ?_)
      obtain ⟨b2, m3⟩ := r3
      simp only
      refine specR_internLetI ra (ctxOK_H hok H3) hc.lt rhiW (vv rhiY) (vv rhiZ) (vv rhiV) t2 v2 b2 (by decide) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv])
        (fun w s4 => ?_)
      simp only [pure_bind]
      exact rhi_set C hok H3 H h w rhiM3 rhiM2 mw3 m3 ((hp1.trans hp2).trans hp3) hm3 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by decide)
        ⟨by decide, by decide⟩ (by decide) (by decide)
    | proj nm i e =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold rhiNode
      have hlenp : (encEView (.proj nm i e)).length = 2 + (Enc.limbs i).length := by simp [encEView, Enc.encProj]; omega
      refine specR_loadI' rhiA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev, Env.get_cons])
        (by simp) (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW nm) (Enc.idxW e :: Enc.limbs i) []) ?_
      refine specR_loadI' rhiA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW nm) (Enc.idxW e) (Enc.limbs i) []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_assignI rhiB (.const 0) 0 (by decide) rfl ?_
        refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun _ => ?_)
        unfold rhiProj
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only [bind_assoc]
        refine rhi_call C hc ctx om nP pp n ih' H hp hpf rhiQ rhiA2 rhiM rhiY rhiM1 (by decide) (by decide) e memo mw hm
          (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
        obtain ⟨u2, m1⟩ := r1
        simp only
        refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rhiW (vv rhiA1) (vv rhiY) (vv rhiB) nm _ u2 (by decide) (by decide)
          (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun w s2 => ?_)
        simp only [pure_bind]
        unfold rhiSet
        exact rhi_set C hok H1 H h w rhiM1 rhiM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
          (by decide) (by decide)

      by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenp, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_loadI' rhiB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev, Env.get_cons]) rfl
          (by simpa [encEView, Enc.encProj, hl] using wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] []) ?_
        by_cases h63 : i < 2 ^ 63
        · have hi63 : i < 2 ^ 63 := h63
          refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun _ => ?_)
          unfold rhiProj
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> omega)
            (fun h => absurd rfl h) (fun _ => ?_)
          simp only [bind_assoc]
          refine rhi_call C hc ctx om nP pp n ih' H hp hpf rhiQ rhiA2 rhiM rhiY rhiM1 (by decide) (by decide) e memo mw hm
            (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun r1 H1 op1 mw1 s1 hp1 hm1 => ?_)
          obtain ⟨u2, m1⟩ := r1
          simp only
          refine specR_internProjI ra (ctxOK_H hok H1) hc.pj rhiW (vv rhiA1) (vv rhiY) (vv rhiB) nm _ u2 (hi63) (by decide)
            (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun w s2 => ?_)
          simp only [pure_bind]
          unfold rhiSet
          exact rhi_set C hok H1 H h w rhiM1 rhiM3 mw1 m1 hp1 hm1 (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by decide) ⟨by decide, by decide⟩
            (by decide) (by decide)

        · refine hmemo _ _ _ _ (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, rhiParams, ctxEnv]) (fun _ => ?_)
          unfold rhiProj
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
