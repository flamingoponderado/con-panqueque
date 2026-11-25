import ConPanqueque.T.Ex.InstList
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `instantiateListGo`, the memoized bulk walk

The `instL` memo (key `(h, d)`) in front of each recursive arm; the `bvar` case is the pure walk.
As a Pancake function `ilg(vs, n, k, fu, h, d)`.
-/

namespace ConPanqueque.T.ExQ
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.ExL
open ConPanqueque.T.ExP

def fIlg := ofString "instantiateListGo"

def callQ (x arg : MlS) (kE dE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fIlg [vv pVs, vv pVn, kE, .op .sub [vv pFu, .const 1], vv arg, dE]

def appQ (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (callQ lY lA1 (vv pVk) (vv pD)) (.seq (callQ lZ lA2 (vv pVk) (vv pD))
    (.seq (.call (some (some (.local, lW), none)) fInternApp [vv lY, vv lZ]) (memoSetP G (.return (vv lW)))))))))))

def bindQ (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callQ lY lA1 (vv pVk) (vv pD)) (.seq (callQ lZ lA2 (vv pVk) (vv lD1))
    (.ite (tagIsE pH 5) (bindTail G fInternLam) (bindTail G fInternForallE)))))))))))

def letQ (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callQ lY lA1 (vv pVk) (vv pD)) (.seq (callQ lZ lA2 (vv pVk) (vv pD)) (.seq (callQ lB lA3 (vv pVk) (vv lD1))
    (.seq (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB]) (memoSetP G (.return (vv lW)))))))))))))))

def projRestQ (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.seq (callQ lY lA2 (vv pVk) (vv pD))
      (.seq (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (memoSetP G (.return (vv lW)))))

def projQ (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRestQ G))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRestQ G)) hang)))))))


def coreQ (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
   (.seq (.assign .local lB (bvarFieldE (vv lDo1)))
   (.ite (.op .and [.cmp .lower (vv lB) (.const 32767), .cmp .notLower (vv pD) (vv lB)]) (.return (vv pH))
    (.ite (isAppE (vv pH)) (appQ G)
     (.ite (.op .or [tagIsE pH 5, tagIsE pH 6]) (bindQ G)
      (.ite (tagIsE pH 7) (letQ G)
       (.ite (tagIsE pH 9) (projQ G)
        (.ite (tagIsE pH 0)
          (.seq (.call (some (some (.local, lW), none)) fIlp
            [vv pVs, vv pVn, vv pVk, .op .sub [vv pFu, .const 1], vv pH, vv pD]) (.return (vv lW)))
          (.return (vv pH))))))))))))

def ilgBody (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreQ (C.mG (.e .instL)))

theorem instLGet_run (k : EIdx × Nat) (s : AState) : instLGet k s = .ok ((memoSel .instL s.memos)[k]?, s) := rfl
theorem instLSet_run (k : EIdx × Nat) (r : EIdx) (s : AState) :
    instLSet k r s = .ok ((), { s with memos := memoUpd .instL s.memos ((memoSel .instL s.memos).insert k r) }) := rfl
theorem instLClear_run (s : AState) : instLClear s = .ok ((), { s with memos := memoUpd .instL s.memos ∅ }) := rfl

structure CodesQ (C : Ctx) extends CodesP C : Prop where
  ilg : C.code.lookup fIlg = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilgBody C, .one)
  memoGet : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  memoProbe : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  memoSet : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  memoIns : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)

section
variable {σ : Type}

def RecQ (C : Ctx) (vs : Array EIdx) (o n n' : Nat) : Prop :=
  ∀ (k : Nat) (h : EIdx) (d : Nat) (s : AState), k < 2 ^ 63 → d < 2 ^ 63 →
    SpecR (Pre (σ := σ) C s (ilpParams.zip [cellA C o, BitVec.ofNat 64 n, BitVec.ofNat 64 k, BitVec.ofNat 64 n',
      Enc.idxW h, BitVec.ofNat 64 d])) (ilgBody C) s (instantiateListGo vs n k n' h d) (PostE C)

theorem callQ_spec {β : Type} (C : Ctx)
    (hcode : C.code.lookup fIlg = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilgBody C, .one))
    (vs : Array EIdx) (o n n' : Nat) (ih : RecQ (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x arg : MlS) (kE dE : ExpHOL 64) (kk : Nat) (h : EIdx) (d : Nat) (hkk : kk < 2 ^ 63) (hd : d < 2 ^ 63)
    (hx : x ∈ DI) (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkE : sev Γ kE = some (BitVec.ofNat 64 kk)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (harg : Γ.get arg = some (Enc.idxW h)) (hdE : sev Γ dE = some (BitVec.ofNat 64 d))
    (hk : ∀ a s', SpecR (Inv C s' ((x, Enc.idxW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (.call (some (some (.local, x), none)) fIlg
      [vv pVs, vv pVn, kE, .op .sub [vv pFu, .const 1], vv arg, dE]) rest) s
      (instantiateListGo vs n kk n' h d >>= k) R := by
  refine specR_callNIM x fIlg ilpParams _ (ilgBody C)
    [cellA C o, BitVec.ofNat 64 n, BitVec.ofNat 64 kk, BitVec.ofNat 64 n', Enc.idxW h, BitVec.ofNat 64 d]
    (by decide) rfl hx hcode
    ⟨by simp [hvs], by simp [hn], hkE, by simp [sev, hfu]; exact ofNat_succ_sub_one n', by simp [harg], hdE, trivial⟩
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hl w hw => by subst hw; exact ih kk h d s hkk hd _ (pre_of_lookups hu _ _ rfl hl))
    (fun a w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk a s')

theorem probedQ_spec {C : Ctx} (hok : CtxOK C) (hc : CodesQ C) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (miss : ProgHOL 64) (m : AM EIdx)
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d)) (hkb : Γ.get lKb = some C.KB)
    (hmiss : SpecR (Inv (σ := σ) C s ((lX, 0) :: Γ) [] DI) miss s m (PostE C)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (probed (C.mG (.e .instL)) miss) s
      (do match ← instLGet (h, d) with | some r => pure r | none => m) (PostE C) := by
  unfold probed memoGetP
  refine specR_memoGetI hok .instL instLGet instLGet_run hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide)
    (by simp [hh]) (by simp [hdd]) hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW, optWG]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, optWG, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    exact specR_ifI (vv lX) 0 (by simp [optW, optWG]) (fun hw => absurd rfl hw) (fun _ => hmiss)

theorem setRetQ_spec {C : Ctx} (hok : CtxOK C) (hc : CodesQ C) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (r : EIdx)
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d)) (hkb : Γ.get lKb = some C.KB)
    (hw : Γ.get lW = some (Enc.idxW r)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (memoSetP (C.mG (.e .instL)) (.return (vv lW))) s
      (do instLSet (h, d) r; pure r) (PostE C) := by
  unfold memoSetP
  refine specR_memoSetI hok .instL instLSet instLSet_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd
    (by decide) (by simp [hh]) (by simp [hdd]) (by simp [hw]) hkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [hw]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem appQ_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecQ (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (h4 : h.tag = 4)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) (hkb : Γ.get lKb = some C.KB) :
    SpecR (Inv (σ := σ) C s Γ M DI) (appQ (C.mG (.e .instL))) s (instListGoArmApp vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListGoArmApp]) ?_
  unfold appQ
  refine probedQ_spec hok hc h d hd _ _ hh hdd hkb ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewAppI h h4 (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun f a P => ?_)
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine callQ_spec C hc.ilg vs o n n' ih lY lA1 (vv pVk) (vv pD) k f d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun f' s1 => ?_)
  refine callQ_spec C hc.ilg vs o n n' ih lZ lA2 (vv pVk) (vv pD) k a d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun a' s2 => ?_)
  refine specR_internAppI ra hok hc.internApp lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide)
    (by simp +decide) (fun r s3 => ?_)
  exact setRetQ_spec hok hc h d hd r (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hkb]) (by simp +decide)

theorem bindQ_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecQ (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (hb : h.tag = 5 ∨ h.tag = 6)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) (hkb : Γ.get lKb = some C.KB) :
    SpecR (Inv (σ := σ) C s Γ M DI) (bindQ (C.mG (.e .instL))) s (instListGoArmBind vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListGoArmBind]) ?_
  unfold bindQ
  refine probedQ_spec hok hc h d hd _ _ hh hdd hkb ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h hb s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  have common : ∀ (ty bd : EIdx) (tg : Nat) (htag : h.tag = UInt32.ofNat tg) (htg5 : tg = 5 ∨ tg = 6),
      SpecR (Inv (σ := σ) C s ((lRp, P) :: (lRn, BitVec.ofNat 64 2) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
        (lDg, BitVec.ofNat 64 tg) :: (lDi, BitVec.ofNat 64 h.idxNat) :: (lDh, Enc.idxW h) :: (lFl, C.FLe) :: (lX, 0) :: Γ)
        (wordsAt P [Enc.idxW ty, Enc.idxW bd] ++ []) DI)
      (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
      (.ite (.shift .lsr (vv lD1) (.const 63)) hang
      (.seq (callQ lY lA1 (vv pVk) (vv pD)) (.seq (callQ lZ lA2 (vv pVk) (vv lD1))
      (.ite (tagIsE pH 5) (bindTail (C.mG (.e .instL)) fInternLam) (bindTail (C.mG (.e .instL)) fInternForallE))))))))
      s (instantiateListGo vs n k n' ty d >>= fun t => instantiateListGo vs n k n' bd (d + 1) >>= fun b =>
        internBindE h.tag t b >>= fun r => do instLSet (h, d) r; pure r) (PostE C) := by
    intro ty bd tg htag htg5
    refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
      (wordsAt_mem0 _ _ _ _) ?_
    refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp +decide [sev]) rfl
      (wordsAt_mem1 _ _ _ _ _) ?_
    refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
      (by simp +decide [sev, hdd]; rw [word_add1_eq]) ?_
    refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (d + 1) >>> (63 : BitVec 64).toNat)
      (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
    have hlt := (shr63_eq_zero (d + 1) (by omega)).mp hw
    refine callQ_spec C hc.ilg vs o n n' ih lY lA1 (vv pVk) (vv pD) k ty d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
    refine callQ_spec C hc.ilg vs o n n' ih lZ lA2 (vv pVk) (vv lD1) k bd (d + 1) hk63 hlt (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s2 => ?_)
    obtain ⟨w5, hw5, hw5i⟩ := sev_tagIs ((lZ, Enc.idxW b') :: (lY, Enc.idxW t') :: (lD1, BitVec.ofNat 64 (d + 1)) ::
      (lA2, Enc.idxW bd) :: (lA1, Enc.idxW ty) :: (lRp, P) ::
      (lRn, BitVec.ofNat 64 2) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 tg) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
      (lDh, Enc.idxW h) :: (lFl, C.FLe) :: (lX, 0) :: Γ) pH h (by simp +decide [hh]) 5 (by decide) (by decide)
    rcases htg5 with rfl | rfl
    · refine specR_ifI (tagIsE pH 5) w5 hw5 (fun _ => ?_) (fun hw => absurd (hw5i.mpr htag) (by simp [hw]))
      have hib : internBindE h.tag t' b' = internLamE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (m' := internLamE t' b' >>= fun r => do instLSet (h, d) r; pure r) (by rw [hib]) ?_
      refine specR_internLamI ra hok hc.internLam lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      exact setRetQ_spec hok hc h d hd r (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hkb]) (by simp +decide)
    · refine specR_ifI (tagIsE pH 5) w5 hw5 (fun hw => absurd (hw5i.mp hw) (by rw [htag]; decide)) (fun _ => ?_)
      have hib : internBindE h.tag t' b' = internForallEE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (m' := internForallEE t' b' >>= fun r => do instLSet (h, d) r; pure r) (by rw [hib]) ?_
      refine specR_internForallEI ra hok hc.internForallE lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      exact setRetQ_spec hok hc h d hd r (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hkb]) (by simp +decide)
  cases vw with
  | lam ty bd =>
    have htag : h.tag = UInt32.ofNat 5 := by
      simp [ENodeView.tagN] at htg; apply UInt32.toNat_inj.mp; simp; omega
    exact common ty bd 5 htag (Or.inl rfl)
  | forallE ty bd =>
    have htag : h.tag = UInt32.ofNat 6 := by
      simp [ENodeView.tagN] at htg; apply UInt32.toNat_inj.mp; simp; omega
    exact common ty bd 6 htag (Or.inr rfl)
  | _ => simp [ENodeView.tagN] at htg; rcases hb with hb | hb <;> rw [hb] at htg <;> simp at htg

theorem letQ_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecQ (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (h7 : h.tag = 7)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) (hkb : Γ.get lKb = some C.KB) :
    SpecR (Inv (σ := σ) C s Γ M DI) (letQ (C.mG (.e .instL))) s (instListGoArmLet vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListGoArmLet]) ?_
  unfold letQ
  refine probedQ_spec hok hc h d hd _ _ hh hdd hkb ?_
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
    refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
      (by simp +decide [sev, hdd]; rw [word_add1_eq]) ?_
    refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (d + 1) >>> (63 : BitVec 64).toNat)
      (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
    have hlt := (shr63_eq_zero (d + 1) (by omega)).mp hw
    refine callQ_spec C hc.ilg vs o n n' ih lY lA1 (vv pVk) (vv pD) k ty d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
    refine callQ_spec C hc.ilg vs o n n' ih lZ lA2 (vv pVk) (vv pD) k vl d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun w' s2 => ?_)
    refine callQ_spec C hc.ilg vs o n n' ih lB lA3 (vv pVk) (vv lD1) k bd (d + 1) hk63 hlt (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide ) (fun b' s3 => ?_)
    refine specR_internLetI ra hok hc.internLet lW (vv lY) (vv lZ) (vv lB) t' w' b' (by decide) (by simp +decide)
      (by simp +decide) (by simp +decide) (fun r s4 => ?_)
    exact setRetQ_spec hok hc h d hd r (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hkb]) (by simp +decide)
  | _ => simp [ENodeView.tagN, h7] at htg

theorem projRestQ_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecQ (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (nm : NIdx) (i : Nat) (e : EIdx) (hi : i < 2 ^ 64)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (ha1 : Γ.get lA1 = some (Enc.idxW nm)) (ha2 : Γ.get lA2 = some (Enc.idxW e))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) (hkb : Γ.get lKb = some C.KB) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projRestQ (C.mG (.e .instL))) s
      (do let u ← instantiateListGo vs n k n' e d; let r ← internProjE nm i u; instLSet (h, d) r; pure r) (PostE C) := by
  unfold projRestQ
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine callQ_spec C hc.ilg vs o n n' ih lY lA2 (vv pVk) (vv pD) k e d hk63 hd (by decide) hvs hn
    (by simp [hkk]) hfu ha2 (by simp [hdd]) (fun u s1 => ?_)
  refine specR_internProjI ra hok hc.internProj lW (vv lA1) (vv lY) (vv lB) nm i u hi63 (by decide)
    (by simp +decide [ha1]) (by simp +decide) (by simp +decide [hb]) (fun r s2 => ?_)
  exact setRetQ_spec hok hc h d hd r (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hkb]) (by simp +decide)

theorem projQ_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecQ (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (h9 : h.tag = 9)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) (hkb : Γ.get lKb = some C.KB) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projQ (C.mG (.e .instL))) s (instListGoArmProj vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListGoArmProj]) ?_
  unfold projQ
  refine probedQ_spec hok hc h d hd _ _ hh hdd hkb ?_
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
      exact projRestQ_spec ra C hok hc vs o n n' ih h k d hk63 hd nm 0 e (by decide) (by simp +decide [hvs])
        (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide [hh])
        (by simp +decide [hdd]) (by simp +decide) (by simp +decide) (by simp) (by simp +decide [hkb])
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
        exact projRestQ_spec ra C hok hc vs o n n' ih h k d hk63 hd nm i e ib (by simp +decide [hvs])
          (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide [hh])
          (by simp +decide [hdd]) (by simp +decide) (by simp +decide) (by simp) (by simp +decide [hkb])
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

theorem instantiateListGo_succ' (vs : Array EIdx) (n k n' : Nat) (h : EIdx) (d : Nat) :
    instantiateListGo vs n k (n' + 1) h d = (derivedE h >>= fun der =>
      if (decide ((ConLeche.bvarOfData der).toNat < ConLeche.satRange) &&
        decide ((ConLeche.bvarOfData der).toNat ≤ d)) = true then pure h
      else if h.tag == ETag.app then instListGoArmApp vs n k n' h d
      else if ETag.isBind h.tag then instListGoArmBind vs n k n' h d
      else if h.tag == ETag.letE then instListGoArmLet vs n k n' h d
      else if h.tag == ETag.proj then instListGoArmProj vs n k n' h d
      else if h.tag == ETag.bvar then instantiateList vs n k n' h d
      else pure h) := by
  rw [instantiateListGo_succ]; simp only [instListCutoff, bind_assoc, pure_bind]

section
variable {σ : Type}

theorem ilg_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o n : Nat) (hblk : BlkAt C.H o (vs.toList.map Enc.idxW)) (hsz : vs.size < 2 ^ 59)
    (hn63 : n < 2 ^ 59) :
    ∀ n', n' < 2 ^ 64 → RecQ (σ := σ) C vs o n n' := by
  intro n'
  induction n' with
  | zero =>
    intro _ k h d s _ _
    refine specR_prologue (postE_locals C) (params_noneP _ C) ?_
    refine specR_ifI _ _ (by simp +decide [sev, ctxEnv, ilpParams]; rfl) (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n' ih =>
    intro hf k h d s hk63 hd
    have ih' := ih (by omega)
    have ihp := ilp_spec (σ := σ) ra C hok hc.toCodesP vs o n hblk hsz hn63 n' (by omega)
    refine specR_prologue (postE_locals C) (params_noneP _ C) ?_
    refine specR_ifI _ _ (by simp +decide [sev, ctxEnv, ilpParams]; rfl) (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n' + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [instantiateListGo_succ']) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv, ilpParams]) ?_
    refine specR_derivedEI h rfl rfl rfl (by decide) ?_
    have hbt : (ConLeche.bvarOfData (s.store.derived h)).toBitVec =
        BitVec.ofNat 64 (ConLeche.bvarOfData (s.store.derived h)).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    have hb15 : (ConLeche.bvarOfData (s.store.derived h)).toNat < 2 ^ 15 := by
      simp only [ConLeche.bvarOfData, UInt64.toNat_mod]; simp; omega
    refine specR_assignI lB (bvarFieldE (vv lDo1)) (ConLeche.bvarOfData (s.store.derived h)).toBitVec (by decide)
      (by simp [sev, bvarFieldE]; exact bvarOfData_word _) ?_
    generalize hbdef : (ConLeche.bvarOfData (s.store.derived h)).toNat = b at hb15 hbt
    refine specR_iteI (.op .and [.cmp .lower (vv lB) (.const 32767), .cmp .notLower (vv pD) (vv lB)])
      ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 b) 32767 then (1 : BitVec 64) else 0) &&&
        (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 d) (BitVec.ofNat 64 b) then 1 else 0))
      ?_ (cutoff_iff b d hb15 hd) (fun _ => ?_) (fun _ => ?_)
    · simp +decide [sev, Env.kill, ctxEnv, hbt, ilpParams]
    · exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv, ilpParams])
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_iteI (isAppE (vv pH)) (isAppW (Enc.idxW h)) ?_
      (by rw [isApp_iff]; simp [ETag.app]) (fun hb => ?_) (fun _ => ?_)
    · exact Ex2.sev_isApp _ pH _ (by simp +decide [Env.kill, ctxEnv, ilpParams])
    · have h4 : h.tag = 4 := by simpa [ETag.app] using hb
      exact appQ_spec ra C hok hc vs o n n' ih' h k d hk63 hd h4 (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (.op .or [tagIsE pH 5, tagIsE pH 6]) (tagW h 5 ||| tagW h 6) ?_
      (isBind_iff h _ _ (tagW_iff h 5 (by decide) (by decide)) (tagW_iff h 6 (by decide) (by decide)))
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · have hb' : h.tag = 5 ∨ h.tag = 6 := by
        simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq, ETag.lam, ETag.forallE] at hb; exact hb
      exact bindQ_spec ra C hok hc vs o n n' ih' h k d hk63 hd hb' (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (tagIsE pH 7) (tagW h 7) ?_ (by rw [tagW_iff h 7 (by decide) (by decide)]; simp [ETag.letE])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · have h7 : h.tag = 7 := by simpa [ETag.letE] using hb
      exact letQ_spec ra C hok hc vs o n n' ih' h k d hk63 hd h7 (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (tagIsE pH 9) (tagW h 9) ?_ (by rw [tagW_iff h 9 (by decide) (by decide)]; simp [ETag.proj])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · have h9 : h.tag = 9 := by simpa [ETag.proj] using hb
      exact projQ_spec ra C hok hc vs o n n' ih' h k d hk63 hd h9 (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (tagIsE pH 0) (tagW h 0) ?_ (by rw [tagW_iff h 0 (by decide) (by decide)]; simp [ETag.bvar])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · refine specR_congr (m' := instantiateList vs n k n' h d >>= fun r => pure r) (by simp) ?_
      refine callP_spec C hc.ilp vs o n n' ihp lW pH (vv pVk) (vv pD) k h d hk63 hd (by decide) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
        (fun r s1 => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `instantiateRevRange`, `instantiateListFast` -/

def fIrr := ofString "instantiateRevRange"
def pS := ofString "irs"
def irrParams : List MlS := [pVs, pS, pVn, pFu, pH, pD]
def irrLocals : List MlS := [lJ0, lW, lB, lY, lA3]

/-- With the clamped end in `bb` and the range length in `ww`: clear, walk, clear. -/
def irrTail (C : Ctx) : ProgHOL 64 :=
  clearCode (C.mg (.e .instL))
    (.seq (.call (some (some (.local, lY), none)) fIlg [vv pVs, vv lB, vv lW, vv pFu, vv pH, vv pD])
      (clearCode (C.mg (.e .instL)) (.return (vv lY))))

def irrK (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lW (.const 0))
    (.ite (.cmp .lower (vv pS) (vv lB)) (.seq (.assign .local lW (.op .sub [vv lB, vv pS])) (irrTail C)) (irrTail C))

def irrCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lA3 (.load .one (vv pVs)))
    (.seq (.assign .local lB (vv pVn))
      (.ite (.cmp .lower (vv lA3) (vv lB)) (.seq (.assign .local lB (vv lA3)) (irrK C)) (irrK C)))

def irrBody (C : Ctx) : ProgHOL 64 := prologue irrLocals (irrCore C)

abbrev DR : List MlS := ctxLocals ++ irrLocals

section
variable {σ : Type}

theorem irrTail_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o : Nat) (hblk : BlkAt C.H o (vs.toList.map Enc.idxW)) (hsz : vs.size < 2 ^ 59)
    {s : AState} {Γ : Env} {M : Mem} (fuel n2 k d : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) (hn2 : n2 < 2 ^ 59)
    (hk : k < 2 ^ 63) (hd : d < 2 ^ 63)
    (hvs : Γ.get pVs = some (cellA C o)) (hb : Γ.get lB = some (BitVec.ofNat 64 n2))
    (hw : Γ.get lW = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 fuel))
    (hh : Γ.get pH = some (Enc.idxW e)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d)) :
    SpecR (Inv (σ := σ) C s Γ M DR) (irrTail C) s
      (do instLClear; let r ← instantiateListGo vs n2 k fuel e d; instLClear; pure r) (PostE C) := by
  unfold irrTail
  refine specR_memoClearI hok .instL instLClear instLClear_run (by decide) ?_
  refine specR_callNIM lY fIlg ilpParams _ (ilgBody C)
    [cellA C o, BitVec.ofNat 64 n2, BitVec.ofNat 64 k, BitVec.ofNat 64 fuel, Enc.idxW e, BitVec.ofNat 64 d]
    (by decide) rfl (by decide) hc.ilg
    ⟨by simp +decide [Env.get_kill_of_not_mem, hvs], by simp +decide [Env.get_kill_of_not_mem, hb],
      by simp +decide [Env.get_kill_of_not_mem, hw], by simp +decide [Env.get_kill_of_not_mem, hfu],
      by simp +decide [Env.get_kill_of_not_mem, hh], by simp +decide [Env.get_kill_of_not_mem, hdd], trivial⟩
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hl w hw' => by
      subst hw'
      exact ilg_spec ra C hok hc vs o n2 hblk hsz hn2 fuel hf k e d _ hk hd _ (pre_of_lookups hu _ _ rfl hl))
    (fun r w s' st hp => ?_)
  obtain ⟨rfl, _⟩ := hp
  refine specR_memoClearI hok .instL instLClear instLClear_run (by decide) ?_
  exact specR_returnI (vv lY) (Enc.idxW r) (by simp +decide [Env.get_kill_of_not_mem])
    (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem irr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o : Nat) (hblk : BlkAt C.H o (vs.toList.map Enc.idxW)) (hsz : vs.size < 2 ^ 59)
    (s : AState) (fuel st n d : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) (hst : st < 2 ^ 63) (hn : n < 2 ^ 63)
    (hd : d < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s (irrParams.zip [cellA C o, BitVec.ofNat 64 st, BitVec.ofNat 64 n, BitVec.ofNat 64 fuel,
      Enc.idxW e, BitVec.ofNat 64 d])) (irrBody C) s (instantiateRevRange fuel e vs st n d) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [irrLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> rfl
  unfold irrCore instantiateRevRange
  obtain ⟨hol, hv0⟩ := blkAt_get0 hblk
  refine specR_heapLoadI lA3 (vv pVs) o hol (by decide) (by simp +decide [ctxEnv, irrParams]) ?_
  rw [show C.H[o]'hol = BitVec.ofNat 64 vs.size by rw [hv0]; simp]
  refine specR_assignI lB (vv pVn) (BitVec.ofNat 64 n) (by decide) (by simp +decide [ctxEnv, irrParams]) ?_
  have hK : ∀ (n2 : Nat), n2 = (if n < vs.size then n else vs.size) → ∀ (Γ : Env) (M : Mem),
      Γ.get lB = some (BitVec.ofNat 64 n2) → Γ.get pS = some (BitVec.ofNat 64 st) →
      Γ.get pVs = some (cellA C o) → Γ.get pFu = some (BitVec.ofNat 64 fuel) → Γ.get pH = some (Enc.idxW e) →
      Γ.get pD = some (BitVec.ofNat 64 d) →
      SpecR (Inv (σ := σ) C s Γ M DR) (irrK C) s
        (do instLClear
            let r ← instantiateListGo vs n2 (if st < n2 then n2 - st else 0) fuel e d
            instLClear; pure r) (PostE C) := by
    intro n2 hn2 Γ M hb hs hvs hfu hh hdd
    have hn2' : n2 < 2 ^ 59 := by split at hn2 <;> omega
    unfold irrK
    refine specR_assignI lW (.const 0) 0 (by decide) rfl ?_
    by_cases g : st < n2
    · have hlt : BitVec.ofNat 64 st < BitVec.ofNat 64 n2 := (word_lt_iff st n2 (by omega) (by omega)).mpr g
      refine specR_ifI _ 1 (by simp +decide [sev, hs, hb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_assignI lW _ (BitVec.ofNat 64 (n2 - st)) (by decide)
        (by simp +decide [sev, hs, hb]; exact word_sub_eq n2 st (by omega) (by omega)) ?_
      rw [ite_eq_left g]
      exact irrTail_spec ra C hok hc vs o hblk hsz fuel n2 (n2 - st) d e hf hn2' (by omega) hd
        (by simp +decide [hvs]) (by simp +decide [hb]) (by simp +decide) (by simp +decide [hfu])
        (by simp +decide [hh]) (by simp +decide [hdd])
    · have hnlt : ¬ BitVec.ofNat 64 st < BitVec.ofNat 64 n2 := fun x => g ((word_lt_iff st n2 (by omega) (by omega)).mp x)
      refine specR_ifI _ 0 (by simp +decide [sev, hs, hb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt])
        (fun hw => absurd rfl hw) (fun _ => ?_)
      rw [ite_eq_right g]
      exact irrTail_spec ra C hok hc vs o hblk hsz fuel n2 0 d e hf hn2' (by decide) hd
        (by simp +decide [hvs]) (by simp +decide [hb]) (by simp +decide) (by simp +decide [hfu])
        (by simp +decide [hh]) (by simp +decide [hdd])
  by_cases g : vs.size < n
  · have hl : BitVec.ofNat 64 vs.size < BitVec.ofNat 64 n := (word_lt_iff _ n (by omega) (by omega)).mpr g
    refine specR_ifI _ 1 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl])
      (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_assignI lB (vv lA3) (BitVec.ofNat 64 vs.size) (by decide) (by simp +decide) ?_
    have e2 : (if n < vs.size then n else vs.size) = vs.size := by split <;> omega
    refine specR_congr (m' := instLClear >>= fun _ =>
        instantiateListGo vs vs.size (if st < vs.size then vs.size - st else 0) fuel e d >>= fun r =>
        instLClear >>= fun _ => pure r) (by simp only [e2]) ?_
    refine hK vs.size e2.symm _ _ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [ctxEnv, irrParams]
  · have hnl : ¬ BitVec.ofNat 64 vs.size < BitVec.ofNat 64 n :=
      fun x => g ((word_lt_iff _ n (by omega) (by omega)).mp x)
    refine specR_ifI _ 0 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnl])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    have e2 : (if n < vs.size then n else vs.size) = n := by split <;> omega
    refine specR_congr (m' := instLClear >>= fun _ =>
        instantiateListGo vs n (if st < n then n - st else 0) fuel e d >>= fun r =>
        instLClear >>= fun _ => pure r) (by simp only [e2]) ?_
    refine hK n e2.symm _ _ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [ctxEnv, irrParams]

/-- `instantiateListFast` is the whole range. -/
theorem ilFast_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesQ C)
    (vs : Array EIdx) (o : Nat) (hblk : BlkAt C.H o (vs.toList.map Enc.idxW)) (hsz : vs.size < 2 ^ 59)
    (s : AState) (fuel d : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) (hd : d < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s (irrParams.zip [cellA C o, BitVec.ofNat 64 0, BitVec.ofNat 64 vs.size,
      BitVec.ofNat 64 fuel, Enc.idxW e, BitVec.ofNat 64 d])) (irrBody C) s (instantiateListFast fuel e vs d)
      (PostE C) :=
  irr_spec ra C hok hc vs o hblk hsz s fuel 0 vs.size d e hf (by decide) (by omega) hd

end

end ConPanqueque.T.ExQ
