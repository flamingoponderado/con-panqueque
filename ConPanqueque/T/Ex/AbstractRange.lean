import ConPanqueque.T.Ex.Abstract1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `abstractRangeGo`

Close the `k` free variables `d … d + k - 1` into `bvar`s at cursor `c` (innermost binder to the lowest
index): `abstract1`'s walk (same `abs1C` memo, same cutoff and rebuilds) with a range test in the
`fvar` arm. As a Pancake function `absR(ad, ak, fu, h, c)`.
-/

namespace ConPanqueque.T.ExR
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExL ConPanqueque.T.ExF
open ConPanqueque.T.ExA

def fAbsR := ofString "abstractRangeGo"
def pAk := ofString "ak"

def callR (x arg : MlS) (cE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fAbsR [vv pAd, vv pAk, .op .sub [vv pFu, .const 1], vv arg, cE]

def appR (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (callR lY lA1 (vv pD)) (.seq (callR lZ lA2 (vv pD))
    (rebuild (.op .and [eqE lY lA1, eqE lZ lA2])
      (.call (some (some (.local, lW), none)) fInternApp [vv lY, vv lZ]) (setRet G)))))))))

def bindR (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callR lY lA1 (vv pD)) (.seq (callR lZ lA2 (vv lD1))
    (.ite (.op .and [eqE lY lA1, eqE lZ lA2]) (.seq (.assign .local lW (vv pH)) (setRet G))
      (.ite (tagIsE pH 5) (bindTail G fInternLam) (bindTail G fInternForallE))))))))))))

def letR (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callR lY lA1 (vv pD)) (.seq (callR lZ lA2 (vv pD)) (.seq (callR lB lA3 (vv lD1))
    (rebuild (.op .and [.op .and [eqE lY lA1, eqE lZ lA2], eqE lB lA3])
      (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB]) (setRet G)))))))))))))

def projRestR (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.seq (callR lY lA2 (vv pD))
      (rebuild (eqE lY lA2) (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (setRet G)))

def projR (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRestR G))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRestR G)) hang)))))))


/-- `fvar idx` (`idx` in `bb`): inside `[d, d + k)` interns `bvar (c + (d + k - 1 - idx))` (guarded), else `h`. -/
def fvarRestR : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
   (.seq (.assign .local lD1 (.op .add [vv pAd, vv pAk]))
    (.ite (.op .and [.cmp .notLower (vv lB) (vv pAd), .cmp .lower (vv lB) (vv lD1)])
      (.seq (.assign .local lW (.op .add [vv pD, .op .sub [.op .sub [vv lD1, .const 1], vv lB]]))
        (.ite (.shift .lsr (vv lW) (.const 63)) hang
          (.seq (.call (some (some (.local, lW), none)) fInternBVar [vv lW]) (.return (vv lW)))))
      (.return (vv pH))))

def fvarR : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.const 0)) fvarRestR)
      (.ite (.cmp .equal (vv lRn) (.const 2))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 8]))) fvarRestR) hang))))

def coreR (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.seq (callFvb lB)
   (.ite (.cmp .notLower (vv pAd) (vv lB)) (.return (vv pH))
    (.ite (isAppE (vv pH)) (appR G)
     (.ite (.op .or [tagIsE pH 5, tagIsE pH 6]) (bindR G)
      (.ite (tagIsE pH 1) fvarR
       (.ite (tagIsE pH 7) (letR G)
        (.ite (tagIsE pH 9) (projR G) (.return (vv pH)))))))))

def bodyR (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreR (C.mG (.e .abs1)))

structure CodesR (C : Ctx) (B : ProgHOL 64) : Prop where
  absR : C.code.lookup fAbsR = some ([(pAd, .one), (pAk, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one)
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

def RecR (C : Ctx) (B : ProgHOL 64) (n : Nat) : Prop :=
  ∀ (d kk : Nat) (h : EIdx) (c : Nat) (s : AState), d < 2 ^ 63 → kk < 2 ^ 63 → c < 2 ^ 63 →
    SpecR (Pre (σ := σ) C s [(pAd, BitVec.ofNat 64 d), (pAk, BitVec.ofNat 64 kk), (pFu, BitVec.ofNat 64 n),
      (pH, Enc.idxW h), (pD, BitVec.ofNat 64 c)]) B s (abstractRangeGo d kk n h c) (PostE C)

theorem callR_spec {β : Type} (C : Ctx) (B : ProgHOL 64)
    (hcode : C.code.lookup fAbsR = some ([(pAd, .one), (pAk, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one))
    (n : Nat) (ih : RecR (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (cE : ExpHOL 64) (d kk : Nat) (h : EIdx) (c : Nat)
    (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63) (hc : c < 2 ^ 63) (hx : x ∈ DI)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (harg : Γ.get arg = some (Enc.idxW h)) (hcE : sev Γ cE = some (BitVec.ofNat 64 c))
    (hk : ∀ a s', SpecR (Inv C s' ((x, Enc.idxW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callR x arg cE) rest) s (abstractRangeGo d kk n h c >>= k) R := by
  refine specR_call5IM x fAbsR pAd pAk pFu pH pD (by decide) _ _ _ _ _ B (BitVec.ofNat 64 d) (BitVec.ofNat 64 kk)
    (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW h) (BitVec.ofNat 64 c) hx hcode (by simp [hA]) (by simp [hK])
    (by simp [sev, hfu]) (by simp [harg]) hcE
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 h5 w hw => by
      subst hw
      exact ih d kk h c s hd hkk hc _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; rw [h3, ofNat_succ_sub_one]
            · split at hy
              · rename_i e; subst e; simp at hy; subst hy; exact h4
              · split at hy
                · rename_i e; subst e; simp at hy; subst hy; exact h5
                · simp at hy⟩)
    (fun a w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk a s')

theorem callFvbR_spec {β : Type} (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesR C B) (n : Nat)
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

end

section
variable {σ : Type}

theorem appR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesR C B) (n : Nat) (ih : RecR (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d kk : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63) (hc63 : c < 2 ^ 63) (h4 : h.tag = 4)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (appR (C.mG (.e .abs1))) s (absRangeGoArmApp d kk n h c) (PostE C) := by
  refine specR_congr (by rw [absRangeGoArmApp]) ?_
  unfold appR
  refine probedA_spec hok hc.fvr.memoGet hc.fvr.memoProbe h c hc63 _ _ hh hcc hkb ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewAppI h h4 (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun f a P => ?_)
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine callR_spec C B hc.absR n ih lY lA1 (vv pD) d kk f c hd hkk hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hK])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun f' s1 => ?_)
  refine callR_spec C B hc.absR n ih lZ lA2 (vv pD) d kk a c hd hkk hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hK])
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


theorem bindR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesR C B) (n : Nat) (ih : RecR (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d kk : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63) (hc63 : c < 2 ^ 63) (hb : h.tag = 5 ∨ h.tag = 6)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (bindR (C.mG (.e .abs1))) s (absRangeGoArmBind d kk n h c) (PostE C) := by
  refine specR_congr (by rw [absRangeGoArmBind]) ?_
  unfold bindR
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
      refine callR_spec C B hc.absR n ih lY lA1 (vv pD) d kk ty c hd hkk hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hK])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
      refine callR_spec C B hc.absR n ih lZ lA2 (vv lD1) d kk bd (c + 1) hd hkk hlt (by decide) (by simp +decide [hA]) (by simp +decide [hK])
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
      refine callR_spec C B hc.absR n ih lY lA1 (vv pD) d kk ty c hd hkk hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hK])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
      refine callR_spec C B hc.absR n ih lZ lA2 (vv lD1) d kk bd (c + 1) hd hkk hlt (by decide) (by simp +decide [hA]) (by simp +decide [hK])
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

theorem letR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesR C B) (n : Nat) (ih : RecR (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d kk : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63) (hc63 : c < 2 ^ 63) (h7 : h.tag = 7)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (letR (C.mG (.e .abs1))) s (absRangeGoArmLet d kk n h c) (PostE C) := by
  refine specR_congr (by rw [absRangeGoArmLet]) ?_
  unfold letR
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
    refine callR_spec C B hc.absR n ih lY lA1 (vv pD) d kk ty c hd hkk hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hK])
      (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
    refine callR_spec C B hc.absR n ih lZ lA2 (vv pD) d kk vl c hd hkk hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hK])
      (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun w' s2 => ?_)
    refine callR_spec C B hc.absR n ih lB lA3 (vv lD1) d kk bd (c + 1) hd hkk hlt (by decide) (by simp +decide [hA]) (by simp +decide [hK])
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

theorem projRestR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesR C B) (n : Nat) (ih : RecR (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d kk : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63) (hc63 : c < 2 ^ 63) (nm : NIdx) (i : Nat) (e : EIdx)
    (hi : i < 2 ^ 64)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (ha1 : Γ.get lA1 = some (Enc.idxW nm)) (ha2 : Γ.get lA2 = some (Enc.idxW e))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projRestR (C.mG (.e .abs1))) s
      (do let u ← abstractRangeGo d kk n e c; let r ← internRebuiltProj h (u == e) nm i u; abs1Set (h, c) r; pure r)
      (PostE C) := by
  unfold projRestR
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine callR_spec C B hc.absR n ih lY lA2 (vv pD) d kk e c hd hkk hc63 (by decide) hA hK hfu ha2 (by simp [hcc])
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

theorem projR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesR C B) (n : Nat) (ih : RecR (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (d kk : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63) (hc63 : c < 2 ^ 63) (h9 : h.tag = 9)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projR (C.mG (.e .abs1))) s (absRangeGoArmProj d kk n h c) (PostE C) := by
  refine specR_congr (by rw [absRangeGoArmProj]) ?_
  unfold projR
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
      exact projRestR_spec ra C hok B hc n ih d kk h c hd hkk hc63 nm 0 e (by decide) (by simp +decide [hA]) (by simp +decide [hK])
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
        exact projRestR_spec ra C hok B hc n ih d kk h c hd hkk hc63 nm i e ib (by simp +decide [hA]) (by simp +decide [hK])
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


end

section
variable {σ : Type}

theorem word_range_eq (c d kk i : Nat) (hc : c < 2 ^ 63) (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63) (h1 : d ≤ i)
    (h2 : i < d + kk) :
    BitVec.ofNat 64 c + (BitVec.ofNat 64 (d + kk) - 1#64 - BitVec.ofNat 64 i) =
      BitVec.ofNat 64 (c + (d + kk - 1 - i)) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_sub]
  omega

theorem fvarRestR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesR C B) {s : AState} {Γ : Env} {M : Mem} (d kk : Nat) (h : EIdx) (c i : Nat) (hd : d < 2 ^ 63)
    (hkk : kk < 2 ^ 63) (hc63 : c < 2 ^ 63) (hi : i < 2 ^ 64)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk))
    (hh : Γ.get pH = some (Enc.idxW h))
    (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) fvarRestR s
      (if (d ≤ i && i < d + kk) then internBVarE (c + (d + kk - 1 - i)) else pure h) (PostE C) := by
  unfold fvarRestR
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + kk)) (by decide)
    (by simp [sev, hA, hK]; rw [BitVec.ofNat_add_ofNat]) ?_
  by_cases g : d ≤ i ∧ i < d + kk
  · have h1 : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 d := fun x => absurd ((word_lt_iff i d hi (by omega)).mp x) (by omega)
    have h2 : BitVec.ofNat 64 i < BitVec.ofNat 64 (d + kk) := (word_lt_iff i (d + kk) hi (by omega)).mpr g.2
    refine specR_ifI _ 1 (by
        simp +decide [sev, hb, hA, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h1, h2]
        simp [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega),
          Nat.mod_eq_of_lt (show i < 18446744073709551616 by omega), g.1])
      (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_assignI lW _ (BitVec.ofNat 64 (c + (d + kk - 1 - i))) (by decide)
      (by simp +decide [sev, hb, hcc]; exact word_range_eq c d kk i hc63 hd hkk g.1 g.2) ?_
    refine specR_ifI (.shift .lsr (vv lW) (.const 63)) (BitVec.ofNat 64 (c + (d + kk - 1 - i)) >>> (63 : BitVec 64).toNat)
      (by simp [sev]) (fun _ => specR_hangI) (fun hw2 => ?_)
    have hs63 := (shr63_eq_zero _ (by omega)).mp hw2
    refine specR_congr (m' := internBVarE (c + (d + kk - 1 - i)) >>= fun a => pure a) (by simp [g.1, g.2]) ?_
    refine specR_internBVarI ra hok hc.internBVar lW (vv lW) _ hs63 (by decide) (by simp) (fun r s' => ?_)
    exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have g' : (decide (d ≤ i) && decide (i < d + kk)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have hw0 : ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 i) (BitVec.ofNat 64 d)
        then (1 : BitVec 64) else 0) &&& (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i)
        (BitVec.ofNat 64 (d + kk)) then 1 else 0)) = 0 := by
      by_cases a : i < d
      · have := (word_lt_iff i d hi (by omega)).mpr a
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
      · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 (d + kk) :=
          fun x => absurd ((word_lt_iff i (d + kk) hi (by omega)).mp x) (by omega)
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
    refine specR_ifI _ _ (by simp +decide [sev, hb, hA]) (fun hw => absurd hw0 hw) (fun _ => ?_)
    refine specR_congr (m' := pure h) (by rw [g']; rfl) ?_
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [hh]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem fvarR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesR C B) {s : AState} {Γ : Env} {M : Mem} (d kk : Nat) (h : EIdx) (c : Nat) (hd : d < 2 ^ 63)
    (hkk : kk < 2 ^ 63) (hc63 : c < 2 ^ 63) (h1 : h.tag = 1)
    (hA : Γ.get pAd = some (BitVec.ofNat 64 d)) (hK : Γ.get pAk = some (BitVec.ofNat 64 kk)) (hh : Γ.get pH = some (Enc.idxW h))
    (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hfle : Γ.get lFle = some C.FLe)
    (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) fvarR s (absRangeArmFVar d kk h c) (PostE C) := by
  unfold absRangeArmFVar fvarR
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
      exact fvarRestR_spec ra C hok B hc d kk h c 0 hd hkk hc63 (by decide) (by simp +decide [hA]) (by simp +decide [hK]) (by simp +decide [hh])
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
        exact fvarRestR_spec ra C hok B hc d kk h c idx hd hkk hc63 ib (by simp +decide [hA]) (by simp +decide [hK]) (by simp +decide [hh])
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

theorem params_noneR (d kk : Nat) (h : EIdx) (n c : Nat) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pAd, BitVec.ofNat 64 d), (pAk, BitVec.ofNat 64 kk), (pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h),
      (pD, BitVec.ofNat 64 c)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem absR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesR C (bodyR C)) :
    ∀ n, n < 2 ^ 64 → RecR (σ := σ) C (bodyR C) n := by
  intro n
  induction n with
  | zero =>
    intro _ d kk h c s _ _ _
    refine specR_prologue (postE_locals C) (params_noneR d kk h 0 c C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf d kk h c s hd hkk hc63
    have ih' := ih (by omega)
    refine specR_prologue (postE_locals C) (params_noneR d kk h (n + 1) c C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [abstractRangeGo_succ]) ?_
    refine callFvbR_spec C hok (bodyR C) hc n hf lB h (by decide) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (fun fb s1 hfb => ?_)
    by_cases g : fb ≤ d
    · have hnlt : ¬ BitVec.ofNat 64 d < BitVec.ofNat 64 fb :=
        fun x => absurd ((word_lt_iff d fb (by omega) (by omega)).mp x) (by omega)
      have hle : BitVec.ofNat 64 fb ≤ BitVec.ofNat 64 d := BitVec.not_lt.mp hnlt
      refine specR_ifI _ 1 (by simp +decide [sev, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hle, ctxEnv])
        (fun _ => ?_)
        (fun hw => absurd hw (by decide))
      refine specR_congr (by rw [ite_eq_left g]) ?_
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hlt : BitVec.ofNat 64 d < BitVec.ofNat 64 fb := (word_lt_iff d fb (by omega) (by omega)).mpr (by omega)
    have hnle : ¬ BitVec.ofNat 64 fb ≤ BitVec.ofNat 64 d := BitVec.not_le.mpr hlt
    refine specR_ifI _ 0 (by simp +decide [sev, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle, ctxEnv])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_congr (by rw [ite_eq_right g]) ?_
    refine specR_iteI (isAppE (vv pH)) (isAppW (Enc.idxW h)) ?_
      (by rw [isApp_iff]; simp [ETag.app]) (fun hb => ?_) (fun _ => ?_)
    · exact Ex2.sev_isApp _ pH _ (by simp +decide [ctxEnv])
    · have h4 : h.tag = 4 := by simpa [ETag.app] using hb
      exact appR_spec ra C hok (bodyR C) hc n ih' d kk h c hd hkk hc63 h4 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (.op .or [tagIsE pH 5, tagIsE pH 6]) (tagW h 5 ||| tagW h 6) ?_
      (isBind_iff h _ _ (tagW_iff h 5 (by decide) (by decide)) (tagW_iff h 6 (by decide) (by decide)))
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have hb' : h.tag = 5 ∨ h.tag = 6 := by
        simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq, ETag.lam, ETag.forallE] at hb; exact hb
      exact bindR_spec ra C hok (bodyR C) hc n ih' d kk h c hd hkk hc63 hb' (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (tagIsE pH 1) (tagW h 1) ?_ (by rw [tagW_iff h 1 (by decide) (by decide)]; simp [ETag.fvar])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h1 : h.tag = 1 := by simpa [ETag.fvar] using hb
      exact fvarR_spec ra C hok (bodyR C) hc d kk h c hd hkk hc63 h1 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (tagIsE pH 7) (tagW h 7) ?_ (by rw [tagW_iff h 7 (by decide) (by decide)]; simp [ETag.letE])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h7 : h.tag = 7 := by simpa [ETag.letE] using hb
      exact letR_spec ra C hok (bodyR C) hc n ih' d kk h c hd hkk hc63 h7 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    refine specR_iteI (tagIsE pH 9) (tagW h 9) ?_ (by rw [tagW_iff h 9 (by decide) (by decide)]; simp [ETag.proj])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h9 : h.tag = 9 := by simpa [ETag.proj] using hb
      exact projR_spec ra C hok (bodyR C) hc n ih' d kk h c hd hkk hc63 h9 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

def fastBodyR (C : Ctx) : ProgHOL 64 :=
  prologue fastLocals (.ite (.cmp .equal (vv pAk) (.const 0)) (.return (vv pH))
    (clearCode (C.mg (.e .abs1))
      (.seq (.call (some (some (.local, lW), none)) fAbsR [vv pAd, vv pAk, vv pFu, vv pH, vv pD])
        (clearCode (C.mg (.e .abs1)) (.return (vv lW))))))

theorem fastR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesR C (bodyR C))
    (s : AState) (fuel d kk c : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) (hd : d < 2 ^ 63) (hkk : kk < 2 ^ 63)
    (hc63 : c < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pAd, BitVec.ofNat 64 d), (pAk, BitVec.ofNat 64 kk),
      (pD, BitVec.ofNat 64 c), (pH, Enc.idxW e)]) (fastBodyR C) s (abstractRangeFast fuel e d kk c) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [fastLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  unfold abstractRangeFast
  by_cases k0 : kk = 0
  · subst k0
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure e) (by simp) ?_
    exact specR_returnI (vv pH) (Enc.idxW e) (by simp +decide [ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hne : BitVec.ofNat 64 kk ≠ 0#64 := ofNat_ne_zero kk k0 (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_congr (by rw [ite_eq_right k0]) ?_
  refine specR_memoClearI hok .abs1 abs1Clear abs1Clear_run (by decide) ?_
  refine specR_call5IM lW fAbsR pAd pAk pFu pH pD (by decide) _ _ _ _ _ (bodyR C) (BitVec.ofNat 64 d)
    (BitVec.ofNat 64 kk) (BitVec.ofNat 64 fuel) (Enc.idxW e) (BitVec.ofNat 64 c) (by decide) hc.absR
    (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 h5 w hw => by
      subst hw
      exact absR_spec ra C hok hc fuel hf d kk e c _ hd hkk hc63 _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · split at hy
              · rename_i e; subst e; simp at hy; subst hy; exact h4
              · split at hy
                · rename_i e; subst e; simp at hy; subst hy; exact h5
                · simp at hy⟩)
    (fun r w s' st hp => ?_)
  obtain ⟨rfl, _⟩ := hp
  refine specR_memoClearI hok .abs1 abs1Clear abs1Clear_run (by decide) ?_
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [Env.kill])
    (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExR
