import ConPanqueque.T.Ex.FvarRange
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `abstract1Go`

Close a binder body: `fvar d` leaves become `bvar k`, `k` bumped under binders. The fvar-range
cutoff comes first (a call to `fvarB`), then a tag dispatch; each recursive arm probes the `abs1C`
memo (key `(h, k)`), views the node, recurses, and rebuilds only when a child changed (Pancake
compares the handle words). As a Pancake function `abs1(ad, fu, h, k)`.
-/

namespace ConPanqueque.T.ExA
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExL ConPanqueque.T.ExF

def fAbs1 := ofString "abstract1Go"
def pAd := ofString "ad"

def callA (x arg : MlS) (kE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fAbs1 [vv pAd, .op .sub [vv pFu, .const 1], vv arg, kE]

def callFvb (x : MlS) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fFvarB [.op .sub [vv pFu, .const 1], vv pH]

def eqE (x y : MlS) : ExpHOL 64 := .cmp .equal (vv x) (vv y)

/-- `w := h` (nothing changed) or the rebuild, then `rest`. -/
def rebuild (same : ExpHOL 64) (call rest : ProgHOL 64) : ProgHOL 64 :=
  .ite same (.seq (.assign .local lW (vv pH)) rest) (.seq call rest)

def setRet (G : BitVec 64) : ProgHOL 64 := memoSetP G (.return (vv lW))

def appA (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (callA lY lA1 (vv pD)) (.seq (callA lZ lA2 (vv pD))
    (rebuild (.op .and [eqE lY lA1, eqE lZ lA2])
      (.call (some (some (.local, lW), none)) fInternApp [vv lY, vv lZ]) (setRet G)))))))))

def bindA (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callA lY lA1 (vv pD)) (.seq (callA lZ lA2 (vv lD1))
    (.ite (.op .and [eqE lY lA1, eqE lZ lA2]) (.seq (.assign .local lW (vv pH)) (setRet G))
      (.ite (tagIsE pH 5) (bindTail G fInternLam) (bindTail G fInternForallE))))))))))))

def letA (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callA lY lA1 (vv pD)) (.seq (callA lZ lA2 (vv pD)) (.seq (callA lB lA3 (vv lD1))
    (rebuild (.op .and [.op .and [eqE lY lA1, eqE lZ lA2], eqE lB lA3])
      (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB]) (setRet G)))))))))))))

def projRestA (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.seq (callA lY lA2 (vv pD))
      (rebuild (eqE lY lA2) (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (setRet G)))

def projA (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRestA G))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRestA G)) hang)))))))

/-- `fvar idx`: `idx = d` interns `bvar k`, else `h`. -/
def fvarRestA : ProgHOL 64 :=
  .ite (eqE lB pAd) (.seq (.call (some (some (.local, lW), none)) fInternBVar [vv pD]) (.return (vv lW)))
    (.return (vv pH))

def fvarA : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.const 0)) fvarRestA)
      (.ite (.cmp .equal (vv lRn) (.const 2))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 8]))) fvarRestA) hang))))

def coreA (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.seq (callFvb lB)
   (.ite (.cmp .notLower (vv pAd) (vv lB)) (.return (vv pH))
    (.ite (isAppE (vv pH)) (appA G)
     (.ite (.op .or [tagIsE pH 5, tagIsE pH 6]) (bindA G)
      (.ite (tagIsE pH 1) fvarA
       (.ite (tagIsE pH 7) (letA G)
        (.ite (tagIsE pH 9) (projA G) (.return (vv pH)))))))))

def bodyA (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreA (C.mG (.e .abs1)))

theorem abs1Get_run (k : EIdx × Nat) (s : AState) : abs1Get k s = .ok ((memoSel .abs1 s.memos)[k]?, s) := rfl
theorem abs1Set_run (k : EIdx × Nat) (r : EIdx) (s : AState) :
    abs1Set k r s = .ok ((), { s with memos := memoUpd .abs1 s.memos ((memoSel .abs1 s.memos).insert k r) }) := rfl
theorem abs1Clear_run (s : AState) : abs1Clear s = .ok ((), { s with memos := memoUpd .abs1 s.memos ∅ }) := rfl

structure CodesA (C : Ctx) (B : ProgHOL 64) : Prop where
  abs1 : C.code.lookup fAbs1 = some ([(pAd, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one)
  fvarB : C.code.lookup fFvarB = some ([(pFu, .one), (pH, .one)], fvbBody C, .one)
  fvr : CodesF C (bodyF C)
  internApp : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  internLam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  internForallE : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  internLet : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  internBVar : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  internProj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)

section
variable {σ : Type}

def RecA (C : Ctx) (B : ProgHOL 64) (n : Nat) : Prop :=
  ∀ (d : Nat) (h : EIdx) (k : Nat) (s : AState), d < 2 ^ 63 → k < 2 ^ 63 →
    SpecR (Pre (σ := σ) C s [(pAd, BitVec.ofNat 64 d), (pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h),
      (pD, BitVec.ofNat 64 k)]) B s (abstract1Go d n h k) (PostE C)

theorem callA_spec {β : Type} (C : Ctx) (B : ProgHOL 64)
    (hcode : C.code.lookup fAbs1 = some ([(pAd, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one))
    (n : Nat) (ih : RecA (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (kE : ExpHOL 64) (d : Nat) (h : EIdx) (c : Nat)
    (hd : d < 2 ^ 63) (hc : c < 2 ^ 63) (hx : x ∈ DI)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (harg : Γ.get arg = some (Enc.idxW h)) (hkE : sev Γ kE = some (BitVec.ofNat 64 c))
    (hk : ∀ a s', SpecR (Inv C s' ((x, Enc.idxW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callA x arg kE) rest) s (abstract1Go d n h c >>= k) R := by
  refine specR_call4IM x fAbs1 pAd pFu pH pD (by decide) _ _ _ _ B (BitVec.ofNat 64 d) (BitVec.ofNat 64 (n + 1) - 1)
    (Enc.idxW h) (BitVec.ofNat 64 c) hx hcode (by simp [hA]) (by simp [sev, hfu]) (by simp [harg]) hkE
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 w hw => by
      subst hw
      exact ih d h c s hd hc _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; rw [h2, ofNat_succ_sub_one]
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · split at hy
              · rename_i e; subst e; simp at hy; subst hy; exact h4
              · simp at hy⟩)
    (fun a w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk a s')

theorem callFvb_spec {β : Type} (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesA C B) (n : Nat)
    (hn : n + 1 < 2 ^ 64) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (h : EIdx) (hx : x ∈ DI)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hk : ∀ a s', a < 2 ^ 63 → SpecR (Inv C s' ((x, natW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callFvb x) rest) s (fvarB n h >>= k) R := by
  refine specR_call2IM x fFvarB pFu pH (by decide) _ _ (fvbBody C) (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW h) hx
    hc.fvarB (by simp [sev, hfu]) (by simp [hh]) (PostN C) (fun _ _ _ _ hp => hp.2.2)
    (fun u hu _ h1 h2 w hw => by
      subst hw
      exact fvarB_spec C hok hc.fvr s n h (by omega) _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; rw [h1, ofNat_succ_sub_one]
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun a w s' st hp => by obtain ⟨rfl, ha, _⟩ := hp; exact hk a s' ha)

/-- The handle-equality test's word. -/
def eqW (a b : EIdx) : BitVec 64 :=
  if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (Enc.idxW a) (Enc.idxW b) then 1 else 0

theorem sev_eqE (Γ : Env) (x y : MlS) (a b : EIdx) (hx : Γ.get x = some (Enc.idxW a))
    (hy : Γ.get y = some (Enc.idxW b)) : sev Γ (eqE x y) = some (eqW a b) := by
  simp [eqE, sev, hx, hy, eqW]

theorem eqW_cases (a b : EIdx) : (eqW a b = 1 ∧ (a == b) = true) ∨ (eqW a b = 0 ∧ (a == b) = false) := by
  by_cases e : a = b
  · subst e; left; simp [eqW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · right
    have hne : Enc.idxW a ≠ Enc.idxW b := fun x => e (Enc.idxW_inj x)
    simp [eqW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne, e]

theorem eqW_iff (a b : EIdx) : eqW a b ≠ 0 ↔ (a == b) = true := by
  rcases eqW_cases a b with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem eqW2_iff (a b c d : EIdx) : (eqW a b &&& eqW c d) ≠ 0 ↔ ((a == b) && (c == d)) = true := by
  rcases eqW_cases a b with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases eqW_cases c d with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp [h1, h2, h3, h4]

theorem eqW3_iff (a b c d e f : EIdx) :
    (eqW a b &&& eqW c d &&& eqW e f) ≠ 0 ↔ ((a == b) && (c == d) && (e == f)) = true := by
  rcases eqW_cases a b with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases eqW_cases c d with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases eqW_cases e f with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> simp [h1, h2, h3, h4, h5, h6]

/-- The rebuild: `h` when nothing changed, else the interning call. -/
theorem rebuild_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (same : ExpHOL 64) (w : BitVec 64) (b : Bool) (h : EIdx)
    (els rest : ProgHOL 64) (op : AM EIdx) (hs : sev Γ same = some w) (hb : w ≠ 0 ↔ b = true)
    (hh : Γ.get pH = some (Enc.idxW h))
    (hsame : SpecR (Inv C s ((lW, Enc.idxW h) :: Γ) M DI) rest s (k h) R)
    (hop : SpecR (Inv C s Γ M DI) els s (op >>= k) R) :
    SpecR (Inv (σ := σ) C s Γ M DI) (.ite same (.seq (.assign .local lW (vv pH)) rest) els) s
      ((if b then pure h else op) >>= k) R := by
  refine specR_congr (m' := if b then k h else op >>= k) (by cases b <;> rfl) ?_
  refine specR_iteI same w hs hb (fun _ => ?_) (fun _ => hop)
  exact specR_assignI lW (vv pH) (Enc.idxW h) (by decide) (by simp [hh]) hsame

theorem probedA_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env}
    {M : Mem} (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (h : EIdx) (c : Nat) (hc63 : c < 2 ^ 63) (miss : ProgHOL 64) (m : AM EIdx)
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hkb : Γ.get lKb = some C.KB)
    (hmiss : SpecR (Inv (σ := σ) C s ((lX, 0) :: Γ) [] DI) miss s m (PostE C)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (probed (C.mG (.e .abs1)) miss) s
      (do match ← abs1Get (h, c) with | some r => pure r | none => m) (PostE C) := by
  unfold probed memoGetP
  refine specR_memoGetI hok .abs1 abs1Get abs1Get_run hcG hcP lX (vv pH) (vv pD) h c hc63 (by decide)
    (by simp [hh]) (by simp [hcc]) hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW, optWG]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, optWG, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    exact specR_ifI (vv lX) 0 (by simp [optW, optWG]) (fun hw => absurd rfl hw) (fun _ => hmiss)

theorem setRetA_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env}
    {M : Mem} (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (h : EIdx) (c : Nat) (hc63 : c < 2 ^ 63) (r : EIdx)
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hkb : Γ.get lKb = some C.KB)
    (hw : Γ.get lW = some (Enc.idxW r)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (setRet (C.mG (.e .abs1))) s (do abs1Set (h, c) r; pure r) (PostE C) := by
  unfold setRet memoSetP
  refine specR_memoSetI hok .abs1 abs1Set abs1Set_run hcS hcI lX (vv pH) (vv pD) (vv lW) h c r hc63
    (by decide) (by simp [hh]) (by simp [hcc]) (by simp [hw]) hkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [hw]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem appA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesA C B) (n : Nat) (ih : RecA (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hc63 : c < 2 ^ 63) (h4 : h.tag = 4)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (appA (C.mG (.e .abs1))) s (abstract1ArmApp d n h c) (PostE C) := by
  refine specR_congr (by rw [abstract1ArmApp]) ?_
  unfold appA
  refine probedA_spec hok hc.fvr.memoGet hc.fvr.memoProbe h c hc63 _ _ hh hcc hkb ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewAppI h h4 (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun f a P => ?_)
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine callA_spec C B hc.abs1 n ih lY lA1 (vv pD) d f c hd hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun f' s1 => ?_)
  refine callA_spec C B hc.abs1 n ih lZ lA2 (vv pD) d a c hd hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun a' s2 => ?_)
  refine rebuild_spec _ (eqW f' f &&& eqW a' a) (f' == f && a' == a) h _ _ (internAppE f' a') ?_ (eqW2_iff _ _ _ _)
    (by simp +decide [hh]) ?_ ?_
  · simp +decide [sev, eqE, eqW]
  · exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 h (by simp +decide [hh]) (by simp +decide [hcc])
      (by simp +decide [hkb]) (by simp +decide)
  · refine specR_internAppI ra hok hc.internApp lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide)
      (by simp +decide) (fun r s3 => ?_)
    exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc])
      (by simp +decide [hkb]) (by simp +decide)

end

section
variable {σ : Type}

theorem bindA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesA C B) (n : Nat) (ih : RecA (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hc63 : c < 2 ^ 63) (hb : h.tag = 5 ∨ h.tag = 6)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (bindA (C.mG (.e .abs1))) s (abstract1ArmBind d n h c) (PostE C) := by
  refine specR_congr (by rw [abstract1ArmBind]) ?_
  unfold bindA
  refine probedA_spec hok hc.fvr.memoGet hc.fvr.memoProbe h c hc63 _ _ hh hcc hkb ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h hb s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  cases vw with
    | lam ty bd =>
      have htag : h.tag = 5 := by
        simp [ENodeView.tagN] at htg
        apply UInt32.toNat_inj.mp; simp; omega
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
        (wordsAt_mem0 _ _ _ _) ?_
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp +decide [sev]) rfl
        (wordsAt_mem1 _ _ _ _ _) ?_
      refine specR_assignI lD1 _ (BitVec.ofNat 64 (c + 1)) (by decide)
        (by simp +decide [sev, hcc]; rw [word_add1_eq]) ?_
      refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (c + 1) >>> (63 : BitVec 64).toNat)
        (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
      have hlt := (shr63_eq_zero (c + 1) (by omega)).mp hw
      refine callA_spec C B hc.abs1 n ih lY lA1 (vv pD) d ty c hd hc63 (by decide) (by simp +decide [hA])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
      refine callA_spec C B hc.abs1 n ih lZ lA2 (vv lD1) d bd (c + 1) hd hlt (by decide) (by simp +decide [hA])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s2 => ?_)
      refine specR_congr (m' := internRebuiltBind h (t' == ty && b' == bd) h.tag t' b' >>=
        fun r => do abs1Set (h, c) r; pure r) rfl ?_
      unfold internRebuiltBind
      refine rebuild_spec _ (eqW t' ty &&& eqW b' bd) (t' == ty && b' == bd) h _ _ (internBindE h.tag t' b') ?_
        (eqW2_iff _ _ _ _) (by simp +decide [hh]) ?_ ?_
      · simp +decide [sev, eqE, eqW]
      · exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 h (by simp +decide [hh]) (by simp +decide [hcc])
          (by simp +decide [hkb]) (by simp +decide)
      obtain ⟨w5, hw5, hw5i⟩ := sev_tagIs ((lZ, Enc.idxW b') :: (lY, Enc.idxW t') :: (lD1, BitVec.ofNat 64 (c + 1)) ::
        (lA2, Enc.idxW bd) :: (lA1, Enc.idxW ty) :: (lRp, P) ::
        (lRn, BitVec.ofNat 64 (encEView (.lam ty bd)).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
        (lDg, BitVec.ofNat 64 (ENodeView.lam ty bd).tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
        (lDh, Enc.idxW h) :: (lFl, C.FLe) :: (lX, 0) :: Γ) pH h (by simp +decide [hh]) 5 (by decide) (by decide)
      refine specR_ifI (tagIsE pH 5) w5 hw5 (fun hw => ?_) (fun hw => absurd (hw5i.mpr htag) (by simp [hw]))
      have hib : internBindE h.tag t' b' = internLamE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (by rw [hib]) ?_
      unfold bindTail
      refine specR_internLamI ra hok hc.internLam lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc])
        (by simp +decide [hkb]) (by simp +decide)
    | forallE ty bd =>
      have htag : h.tag = 6 := by
        simp [ENodeView.tagN] at htg
        apply UInt32.toNat_inj.mp; simp; omega
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
        (wordsAt_mem0 _ _ _ _) ?_
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp +decide [sev]) rfl
        (wordsAt_mem1 _ _ _ _ _) ?_
      refine specR_assignI lD1 _ (BitVec.ofNat 64 (c + 1)) (by decide)
        (by simp +decide [sev, hcc]; rw [word_add1_eq]) ?_
      refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (c + 1) >>> (63 : BitVec 64).toNat)
        (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
      have hlt := (shr63_eq_zero (c + 1) (by omega)).mp hw
      refine callA_spec C B hc.abs1 n ih lY lA1 (vv pD) d ty c hd hc63 (by decide) (by simp +decide [hA])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
      refine callA_spec C B hc.abs1 n ih lZ lA2 (vv lD1) d bd (c + 1) hd hlt (by decide) (by simp +decide [hA])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s2 => ?_)
      refine specR_congr (m' := internRebuiltBind h (t' == ty && b' == bd) h.tag t' b' >>=
        fun r => do abs1Set (h, c) r; pure r) rfl ?_
      unfold internRebuiltBind
      refine rebuild_spec _ (eqW t' ty &&& eqW b' bd) (t' == ty && b' == bd) h _ _ (internBindE h.tag t' b') ?_
        (eqW2_iff _ _ _ _) (by simp +decide [hh]) ?_ ?_
      · simp +decide [sev, eqE, eqW]
      · exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 h (by simp +decide [hh]) (by simp +decide [hcc])
          (by simp +decide [hkb]) (by simp +decide)
      obtain ⟨w5, hw5, hw5i⟩ := sev_tagIs ((lZ, Enc.idxW b') :: (lY, Enc.idxW t') :: (lD1, BitVec.ofNat 64 (c + 1)) ::
        (lA2, Enc.idxW bd) :: (lA1, Enc.idxW ty) :: (lRp, P) ::
        (lRn, BitVec.ofNat 64 (encEView (.forallE ty bd)).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
        (lDg, BitVec.ofNat 64 (ENodeView.forallE ty bd).tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
        (lDh, Enc.idxW h) :: (lFl, C.FLe) :: (lX, 0) :: Γ) pH h (by simp +decide [hh]) 5 (by decide) (by decide)
      refine specR_ifI (tagIsE pH 5) w5 hw5 (fun hw => absurd (hw5i.mp hw) (by rw [htag]; decide)) (fun hw => ?_)
      have hib : internBindE h.tag t' b' = internForallEE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (by rw [hib]) ?_
      unfold bindTail
      refine specR_internForallEI ra hok hc.internForallE lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc])
        (by simp +decide [hkb]) (by simp +decide)
    | _ => simp [ENodeView.tagN] at htg; rcases hb with hb | hb <;> rw [hb] at htg <;> simp at htg

theorem letA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesA C B) (n : Nat) (ih : RecA (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hc63 : c < 2 ^ 63) (h7 : h.tag = 7)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (letA (C.mG (.e .abs1))) s (abstract1ArmLet d n h c) (PostE C) := by
  refine specR_congr (by rw [abstract1ArmLet]) ?_
  unfold letA
  refine probedA_spec hok hc.fvr.memoGet hc.fvr.memoProbe h c hc63 _ _ hh hcc hkb ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewLet projLet h (fun vw hvw => viewLet_run h h7 s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  cases vw with
  | letE ty vl bd =>
    refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
      (wordsAt_mem0 _ _ _ _) ?_
    refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW vl) (by decide) (by simp +decide [sev]) rfl
      (wordsAt_mem1 _ _ _ _ _) ?_
    refine specR_loadI' lA3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW bd) (by decide) (by simp +decide [sev])
      rfl (wordsAt_mem2 _ _ _ _ _ _) ?_
    refine specR_assignI lD1 _ (BitVec.ofNat 64 (c + 1)) (by decide)
      (by simp +decide [sev, hcc]; rw [word_add1_eq]) ?_
    refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (c + 1) >>> (63 : BitVec 64).toNat)
      (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
    have hlt := (shr63_eq_zero (c + 1) (by omega)).mp hw
    refine callA_spec C B hc.abs1 n ih lY lA1 (vv pD) d ty c hd hc63 (by decide) (by simp +decide [hA])
      (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
    refine callA_spec C B hc.abs1 n ih lZ lA2 (vv pD) d vl c hd hc63 (by decide) (by simp +decide [hA])
      (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun w' s2 => ?_)
    refine callA_spec C B hc.abs1 n ih lB lA3 (vv lD1) d bd (c + 1) hd hlt (by decide) (by simp +decide [hA])
      (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s3 => ?_)
    refine rebuild_spec _ (eqW t' ty &&& eqW w' vl &&& eqW b' bd) (t' == ty && w' == vl && b' == bd) h _ _
      (internLetEE t' w' b') ?_ (eqW3_iff _ _ _ _ _ _) (by simp +decide [hh]) ?_ ?_
    · simp +decide [sev, eqE, eqW]
    · exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 h (by simp +decide [hh]) (by simp +decide [hcc])
        (by simp +decide [hkb]) (by simp +decide)
    · refine specR_internLetI ra hok hc.internLet lW (vv lY) (vv lZ) (vv lB) t' w' b' (by decide) (by simp +decide)
        (by simp +decide) (by simp +decide) (fun r s4 => ?_)
      exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc])
        (by simp +decide [hkb]) (by simp +decide)
  | _ => simp [ENodeView.tagN, h7] at htg

theorem projRestA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesA C B) (n : Nat) (ih : RecA (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hc63 : c < 2 ^ 63) (nm : NIdx) (i : Nat) (e : EIdx)
    (hi : i < 2 ^ 64)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (ha1 : Γ.get lA1 = some (Enc.idxW nm)) (ha2 : Γ.get lA2 = some (Enc.idxW e))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projRestA (C.mG (.e .abs1))) s
      (do let u ← abstract1Go d n e c; let r ← internRebuiltProj h (u == e) nm i u; abs1Set (h, c) r; pure r)
      (PostE C) := by
  unfold projRestA
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine callA_spec C B hc.abs1 n ih lY lA2 (vv pD) d e c hd hc63 (by decide) hA hfu ha2 (by simp [hcc])
    (fun u s1 => ?_)
  unfold internRebuiltProj
  refine rebuild_spec _ (eqW u e) (u == e) h _ _ (internProjE nm i u) (sev_eqE _ _ _ _ _ (by simp +decide)
    (by simp +decide [ha2])) (eqW_iff _ _) (by simp +decide [hh]) ?_ ?_
  · exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 h (by simp +decide [hh]) (by simp +decide [hcc])
      (by simp +decide [hkb]) (by simp +decide)
  · refine specR_internProjI ra hok hc.internProj lW (vv lA1) (vv lY) (vv lB) nm i u hi63 (by decide)
      (by simp +decide [ha1]) (by simp +decide) (by simp +decide [hb]) (fun r s2 => ?_)
    exact setRetA_spec hok hc.fvr.memoSet hc.fvr.memoIns h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc])
      (by simp +decide [hkb]) (by simp +decide)

theorem projA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesA C B) (n : Nat) (ih : RecA (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hc63 : c < 2 ^ 63) (h9 : h.tag = 9)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projA (C.mG (.e .abs1))) s (abstract1ArmProj d n h c) (PostE C) := by
  refine specR_congr (by rw [abstract1ArmProj]) ?_
  unfold projA
  refine probedA_spec hok hc.fvr.memoGet hc.fvr.memoProbe h c hc63 _ _ hh hcc hkb ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewProj projProj h (fun vw hvw => viewProj_run h h9 s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  cases vw with
  | proj nm i e =>
    refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev]) rfl
      (wordsAt_mem0 _ _ _ _) ?_
    refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev]) rfl
      (wordsAt_mem1 _ _ _ _ _) ?_
    have hlen : (encEView (.proj nm i e)).length = 2 + (Enc.limbs i).length := by
      simp [encEView, Enc.encProj]; omega
    by_cases i0 : i = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
      exact projRestA_spec ra C hok B hc n ih d h c hd hc63 nm 0 e (by decide) (by simp +decide [hA])
        (by simp +decide [hfu]) (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb])
        (by simp +decide) (by simp +decide) (by simp)
    · by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' lB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] (M := [])
              simpa [encEView, Enc.encProj, hl] using this) ?_
        exact projRestA_spec ra C hok B hc n ih d h c hd hc63 nm i e ib (by simp +decide [hA])
          (by simp +decide [hfu]) (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb])
          (by simp +decide) (by simp +decide) (by simp)
      · have hl := limbs_len_ge2 i (by omega)
        have hlt : 2 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen]; exact hsh
        have hn2 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 2#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn3 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 3#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn3, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  | _ => simp [ENodeView.tagN, h9] at htg

theorem viewFVarIdx_run (h : EIdx) (h1 : h.tag = 1) (s : AState) (v : ENodeView)
    (hv : s.store.view h = some v) : ConRon.Arena.viewFVarIdx h s = .ok (projFVarIdx v, s) :=
  viewX_run ConRon.Arena.viewFVarIdx (fun st h => st.viewFVarIdx h) (fun _ _ => rfl) projFVarIdx h
    (fun st => viewFVarIdx_bind st h h1) s v hv

theorem fvarRestA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesA C B) {s : AState} {Γ : Env} {M : Mem} (d : Nat) (h : EIdx) (c i : Nat) (hd : d < 2 ^ 63)
    (hc63 : c < 2 ^ 63) (hi : i < 2 ^ 64)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hh : Γ.get pH = some (Enc.idxW h))
    (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) fvarRestA s (if i = d then internBVarE c else pure h) (PostE C) := by
  unfold fvarRestA
  by_cases e : i = d
  · subst e
    refine specR_ifI _ 1 (by simp [eqE, sev, hb, hA, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    refine specR_congr (m' := internBVarE c >>= fun a => pure a) (by simp) ?_
    refine specR_internBVarI ra hok hc.internBVar lW (vv pD) c hc63 (by decide) (by simp [hcc]) (fun r s' => ?_)
    exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 d := fun x => e ((word_eq_iff i d hi (by omega)).mp x)
    refine specR_ifI _ 0 (by simp [eqE, sev, hb, hA, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_congr (m' := pure h) (by simp [e]) ?_
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp [hh]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem fvarA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesA C B) {s : AState} {Γ : Env} {M : Mem} (d : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63)
    (hc63 : c < 2 ^ 63) (h1 : h.tag = 1)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hh : Γ.get pH = some (Enc.idxW h))
    (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hfle : Γ.get lFle = some C.FLe)
    (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) fvarA s (abstract1ArmFVar d h c) (PostE C) := by
  unfold abstract1ArmFVar fvarA
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewFVarIdx projFVarIdx h (fun vw hvw => viewFVarIdx_run h h1 s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  cases vw with
  | fvar idx ty =>
    have hlen : (encEView (.fvar idx ty)).length = 1 + (Enc.limbs idx).length := by
      simp [encEView, Enc.encFVar]; omega
    by_cases i0 : idx = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
      exact fvarRestA_spec ra C hok B hc d h c 0 hd hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hh])
        (by simp +decide [hcc]) (by simp)
    · by_cases ib : idx < 2 ^ 64
      · have hl : Enc.limbs idx = [BitVec.ofNat 64 idx] := by rw [limbs_small idx ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' lB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 idx) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 idx) [] (M := M)
              simpa [encEView, Enc.encFVar, hl] using this) ?_
        exact fvarRestA_spec ra C hok B hc d h c idx hd hc63 ib (by simp +decide [hA]) (by simp +decide [hh])
          (by simp +decide [hcc]) (by simp)
      · have hl := limbs_len_ge2 idx (by omega)
        have hlt : 1 + (Enc.limbs idx).length < 2 ^ 61 := by rw [← hlen]; exact hsh
        have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 2#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  | _ => simp [ENodeView.tagN, h1] at htg

end

section
variable {σ : Type}

theorem params_noneA (d : Nat) (h : EIdx) (n c : Nat) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pAd, BitVec.ofNat 64 d), (pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h),
      (pD, BitVec.ofNat 64 c)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem abs1_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesA C (bodyA C)) :
    ∀ n, n < 2 ^ 64 → RecA (σ := σ) C (bodyA C) n := by
  intro n
  induction n with
  | zero =>
    intro _ d h c s _ _
    refine specR_prologue (postE_locals C) (params_noneA d h 0 c C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf d h c s hd hc63
    have ih' := ih (by omega)
    refine specR_prologue (postE_locals C) (params_noneA d h (n + 1) c C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [abstract1Go_succ]) ?_
    refine callFvb_spec C hok (bodyA C) hc n hf lB h (by decide) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (fun fb s1 hfb => ?_)
    by_cases g : fb ≤ d
    · have hnlt : ¬ BitVec.ofNat 64 d < BitVec.ofNat 64 fb :=
        fun x => absurd ((word_lt_iff d fb (by omega) (by omega)).mp x) (by omega)
      have hle : BitVec.ofNat 64 fb ≤ BitVec.ofNat 64 d := BitVec.not_lt.mp hnlt
      refine specR_ifI _ 1 (by simp +decide [sev, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hle, ctxEnv])
        (fun _ => ?_)
        (fun hw => absurd hw (by decide))
      refine specR_congr (by rw [if_pos g]) ?_
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hlt : BitVec.ofNat 64 d < BitVec.ofNat 64 fb := (word_lt_iff d fb (by omega) (by omega)).mpr (by omega)
    have hnle : ¬ BitVec.ofNat 64 fb ≤ BitVec.ofNat 64 d := BitVec.not_le.mpr hlt
    refine specR_ifI _ 0 (by simp +decide [sev, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle, ctxEnv])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_congr (by rw [if_neg g]) ?_
    refine specR_iteI (isAppE (vv pH)) (isAppW (Enc.idxW h)) ?_
      (by rw [isApp_iff]; simp [ETag.app]) (fun hb => ?_) (fun _ => ?_)
    · exact Ex2.sev_isApp _ pH _ (by simp +decide [ctxEnv])
    · have h4 : h.tag = 4 := by simpa [ETag.app] using hb
      exact appA_spec ra C hok (bodyA C) hc n ih' d h c hd hc63 h4 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (.op .or [tagIsE pH 5, tagIsE pH 6]) (tagW h 5 ||| tagW h 6) ?_
      (isBind_iff h _ _ (tagW_iff h 5 (by decide) (by decide)) (tagW_iff h 6 (by decide) (by decide)))
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have hb' : h.tag = 5 ∨ h.tag = 6 := by
        simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq, ETag.lam, ETag.forallE] at hb; exact hb
      exact bindA_spec ra C hok (bodyA C) hc n ih' d h c hd hc63 hb' (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (tagIsE pH 1) (tagW h 1) ?_ (by rw [tagW_iff h 1 (by decide) (by decide)]; simp [ETag.fvar])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h1 : h.tag = 1 := by simpa [ETag.fvar] using hb
      exact fvarA_spec ra C hok (bodyA C) hc d h c hd hc63 h1 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (tagIsE pH 7) (tagW h 7) ?_ (by rw [tagW_iff h 7 (by decide) (by decide)]; simp [ETag.letE])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h7 : h.tag = 7 := by simpa [ETag.letE] using hb
      exact letA_spec ra C hok (bodyA C) hc n ih' d h c hd hc63 h7 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (tagIsE pH 9) (tagW h 9) ?_ (by rw [tagW_iff h 9 (by decide) (by decide)]; simp [ETag.proj])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h9 : h.tag = 9 := by simpa [ETag.proj] using hb
      exact projA_spec ra C hok (bodyA C) hc n ih' d h c hd hc63 h9 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

def fAbs1F := ofString "abstract1"

/-- `abstract1(fu, d, k, h)`: clear the memo, walk, clear again. -/
def fastBodyA (C : Ctx) : ProgHOL 64 :=
  prologue fastLocals (clearCode (C.mg (.e .abs1))
    (.seq (.call (some (some (.local, lW), none)) fAbs1 [vv pAd, vv pFu, vv pH, vv pD])
      (clearCode (C.mg (.e .abs1)) (.return (vv lW)))))

theorem fastA_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesA C (bodyA C))
    (s : AState) (fuel d k : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) (hd : d < 2 ^ 63) (hk : k < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pAd, BitVec.ofNat 64 d), (pD, BitVec.ofNat 64 k),
      (pH, Enc.idxW e)]) (fastBodyA C) s (abstract1Fast fuel e d k) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [fastLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  refine specR_memoClearI hok .abs1 abs1Clear abs1Clear_run (by decide) ?_
  refine specR_call4IM lW fAbs1 pAd pFu pH pD (by decide) _ _ _ _ (bodyA C) (BitVec.ofNat 64 d)
    (BitVec.ofNat 64 fuel) (Enc.idxW e) (BitVec.ofNat 64 k) (by decide) hc.abs1 (by simp +decide [Env.kill, ctxEnv])
    (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 w hw => by
      subst hw
      exact abs1_spec ra C hok hc fuel hf d e k _ hd hk _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · split at hy
              · rename_i e; subst e; simp at hy; subst hy; exact h4
              · simp at hy⟩)
    (fun r w s' st hp => ?_)
  obtain ⟨rfl, _⟩ := hp
  refine specR_memoClearI hok .abs1 abs1Clear abs1Clear_run (by decide) ?_
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [Env.kill])
    (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExA
