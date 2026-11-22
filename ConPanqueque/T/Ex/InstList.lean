import ConPanqueque.T.CallN
import ConPanqueque.T.Ex.MkApp
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `instantiateList`, the pure bulk walk

Bound variable `j ≥ d` with `j - d < k` becomes `vs[n - 1 - (j - d)]` (instantiated again at the
shorter range unless closed), variables past the range drop by `k`. The values sit in a block of the
image. As a Pancake function `ilp(vs, n, k, fu, h, d)`.
-/

namespace ConPanqueque.T.ExP
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.ExL

def fIlp := ofString "instantiateList"
def pVs := ofString "vsp"
def pVn := ofString "vsn"
def pVk := ofString "vsk"

def ilpParams : List MlS := [pVs, pVn, pVk, pFu, pH, pD]

def callP (x arg : MlS) (kE dE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fIlp [vv pVs, vv pVn, kE, .op .sub [vv pFu, .const 1], vv arg, dE]

def appP : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (callP lY lA1 (vv pVk) (vv pD)) (.seq (callP lZ lA2 (vv pVk) (vv pD))
    (.seq (.call (some (some (.local, lW), none)) fInternApp [vv lY, vv lZ]) (.return (vv lW)))))))))

def bindRetP (fn : MlS) : ProgHOL 64 :=
  .seq (.call (some (some (.local, lW), none)) fn [vv lY, vv lZ]) (.return (vv lW))

def bindP : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callP lY lA1 (vv pVk) (vv pD)) (.seq (callP lZ lA2 (vv pVk) (vv lD1))
    (.ite (tagIsE pH 5) (bindRetP fInternLam) (bindRetP fInternForallE))))))))))

def letP : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callP lY lA1 (vv pVk) (vv pD)) (.seq (callP lZ lA2 (vv pVk) (vv pD)) (.seq (callP lB lA3 (vv pVk) (vv lD1))
    (.seq (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB]) (.return (vv lW)))))))))))))

def projRestP : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.seq (callP lY lA2 (vv pVk) (vv pD))
      (.seq (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (.return (vv lW))))

def projP : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) projRestP)
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) projRestP) hang))))))

/-- `j` in `bb`: below `d` answers `h`; in range reads the value (closed: as is, else instantiated at
`k := j - d`); past the range interns `bvar (j - k)`. -/
def bvarRestP : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
  (.ite (.cmp .lower (vv lB) (vv pD)) (.return (vv pH))
  (.seq (.assign .local lW (.op .sub [vv lB, vv pD]))
  (.ite (.cmp .lower (vv lW) (vv pVk))
    (.seq (.assign .local lA3 (.load .one (vv pVs)))
    (.ite (.op .and [.cmp .lower (vv lW) (vv pVn), .cmp .notLower (vv lA3) (vv pVn)])
      (.seq (.assign .local lY (.load .one (.op .add [vv pVs, .shift .lsl (.op .sub [vv pVn, vv lW]) (.const 3)])))
      (.seq (.assign .local lDh (vv lY)) (.seq (.assign .local lFl (vv lFle)) (.seq (storeDerived 9 10)
      (.seq (.assign .local lX (bvarFieldE (vv lDo1)))
      (.ite (.op .and [.cmp .lower (vv lX) (.const 32767), .cmp .notLower (vv pD) (vv lX)]) (.return (vv lY))
        (.seq (.call (some (some (.local, lZ), none)) fIlp
            [vv pVs, vv pVn, vv lW, .op .sub [vv pFu, .const 1], vv lY, vv pD])
          (.return (vv lZ)))))))))
      (.return (vv pH))))
    (.seq (.call (some (some (.local, lW), none)) fInternBVar [.op .sub [vv lB, vv pVk]]) (.return (vv lW))))))

def bvarP : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local lB (.const 0)) bvarRestP)
      (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 0])))
        bvarRestP) hang))))

def coreP : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
   (.seq (.assign .local lB (bvarFieldE (vv lDo1)))
   (.ite (.op .and [.cmp .lower (vv lB) (.const 32767), .cmp .notLower (vv pD) (vv lB)]) (.return (vv pH))
    (.ite (isAppE (vv pH)) appP
     (.ite (.op .or [tagIsE pH 5, tagIsE pH 6]) bindP
      (.ite (tagIsE pH 7) letP
       (.ite (tagIsE pH 9) projP
        (.ite (tagIsE pH 0) bvarP (.return (vv pH))))))))))))

def ilpBody : ProgHOL 64 := prologue inst1Locals coreP

structure CodesP (C : Ctx) : Prop where
  ilp : C.code.lookup fIlp = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpBody, .one)
  internApp : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  internLam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  internForallE : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  internLet : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  internBVar : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  internProj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)

section
variable {σ : Type}

/-- The walk at fuel `n'`, for the fixed value block (`vs` at `o`, range end `n`). -/
def RecP (C : Ctx) (vs : Array EIdx) (o n n' : Nat) : Prop :=
  ∀ (k : Nat) (h : EIdx) (d : Nat) (s : AState), k < 2 ^ 63 → d < 2 ^ 63 →
    SpecR (Pre (σ := σ) C s (ilpParams.zip [cellA C o, BitVec.ofNat 64 n, BitVec.ofNat 64 k, BitVec.ofNat 64 n',
      Enc.idxW h, BitVec.ofNat 64 d])) ilpBody s (instantiateList vs n k n' h d) (PostE C)

theorem callP_spec {β : Type} (C : Ctx) (hcode : C.code.lookup fIlp = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpBody, .one))
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x arg : MlS) (kE dE : ExpHOL 64) (kk : Nat) (h : EIdx) (d : Nat) (hkk : kk < 2 ^ 63) (hd : d < 2 ^ 63)
    (hx : x ∈ DI) (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkE : sev Γ kE = some (BitVec.ofNat 64 kk)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (harg : Γ.get arg = some (Enc.idxW h)) (hdE : sev Γ dE = some (BitVec.ofNat 64 d))
    (hk : ∀ a s', SpecR (Inv C s' ((x, Enc.idxW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (.call (some (some (.local, x), none)) fIlp
      [vv pVs, vv pVn, kE, .op .sub [vv pFu, .const 1], vv arg, dE]) rest) s
      (instantiateList vs n kk n' h d >>= k) R := by
  refine specR_callNIM x fIlp ilpParams _ ilpBody
    [cellA C o, BitVec.ofNat 64 n, BitVec.ofNat 64 kk, BitVec.ofNat 64 n', Enc.idxW h, BitVec.ofNat 64 d]
    (by decide) rfl hx hcode
    ⟨by simp [hvs], by simp [hn], hkE, by simp [sev, hfu]; exact ofNat_succ_sub_one n', by simp [harg], hdE, trivial⟩
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hl w hw => by subst hw; exact ih kk h d s hkk hd _ (pre_of_lookups hu _ _ rfl hl))
    (fun a w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk a s')

end

section
variable {σ : Type}

theorem appP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (h4 : h.tag = 4)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) appP s (instListArmApp vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListArmApp]) ?_
  unfold appP
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewAppI h h4 (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun f a P => ?_)
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine callP_spec C hc.ilp vs o n n' ih lY lA1 (vv pVk) (vv pD) k f d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun f' s1 => ?_)
  refine callP_spec C hc.ilp vs o n n' ih lZ lA2 (vv pVk) (vv pD) k a d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun a' s2 => ?_)
  refine specR_congr (m' := internAppE f' a' >>= fun r => pure r) (by simp) ?_
  refine specR_internAppI ra hok hc.internApp lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide)
    (by simp +decide) (fun r s3 => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem bindP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (hb : h.tag = 5 ∨ h.tag = 6)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) bindP s (instListArmBind vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListArmBind]) ?_
  unfold bindP
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h hb s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  have common : ∀ (ty bd : EIdx) (tg : Nat) (htag : h.tag = UInt32.ofNat tg) (htg5 : tg = 5 ∨ tg = 6),
      SpecR (Inv (σ := σ) C s ((lRp, P) :: (lRn, BitVec.ofNat 64 2) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
        (lDg, BitVec.ofNat 64 tg) :: (lDi, BitVec.ofNat 64 h.idxNat) :: (lDh, Enc.idxW h) :: (lFl, C.FLe) :: Γ)
        (wordsAt P [Enc.idxW ty, Enc.idxW bd] ++ M) DI)
      (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
      (.ite (.shift .lsr (vv lD1) (.const 63)) hang
      (.seq (callP lY lA1 (vv pVk) (vv pD)) (.seq (callP lZ lA2 (vv pVk) (vv lD1))
      (.ite (tagIsE pH 5) (bindRetP fInternLam) (bindRetP fInternForallE))))))))
      s (instantiateList vs n k n' ty d >>= fun t => instantiateList vs n k n' bd (d + 1) >>= fun b =>
        internBindE h.tag t b) (PostE C) := by
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
    refine callP_spec C hc.ilp vs o n n' ih lY lA1 (vv pVk) (vv pD) k ty d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
    refine callP_spec C hc.ilp vs o n n' ih lZ lA2 (vv pVk) (vv lD1) k bd (d + 1) hk63 hlt (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s2 => ?_)
    obtain ⟨w5, hw5, hw5i⟩ := sev_tagIs ((lZ, Enc.idxW b') :: (lY, Enc.idxW t') :: (lD1, BitVec.ofNat 64 (d + 1)) ::
      (lA2, Enc.idxW bd) :: (lA1, Enc.idxW ty) :: (lRp, P) ::
      (lRn, BitVec.ofNat 64 2) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 tg) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
      (lDh, Enc.idxW h) :: (lFl, C.FLe) :: Γ) pH h (by simp +decide [hh]) 5 (by decide) (by decide)
    rcases htg5 with rfl | rfl
    · refine specR_ifI (tagIsE pH 5) w5 hw5 (fun _ => ?_) (fun hw => absurd (hw5i.mpr htag) (by simp [hw]))
      have hib : internBindE h.tag t' b' = internLamE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (m' := internLamE t' b' >>= fun r => pure r) (by rw [hib]; simp) ?_
      refine specR_internLamI ra hok hc.internLam lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI (tagIsE pH 5) w5 hw5 (fun hw => absurd (hw5i.mp hw) (by rw [htag]; decide)) (fun _ => ?_)
      have hib : internBindE h.tag t' b' = internForallEE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (m' := internForallEE t' b' >>= fun r => pure r) (by rw [hib]; simp) ?_
      refine specR_internForallEI ra hok hc.internForallE lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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

end

section
variable {σ : Type}

theorem letP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (h7 : h.tag = 7)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) letP s (instListArmLet vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListArmLet]) ?_
  unfold letP
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
    refine callP_spec C hc.ilp vs o n n' ih lY lA1 (vv pVk) (vv pD) k ty d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
    refine callP_spec C hc.ilp vs o n n' ih lZ lA2 (vv pVk) (vv pD) k vl d hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun w' s2 => ?_)
    refine callP_spec C hc.ilp vs o n n' ih lB lA3 (vv pVk) (vv lD1) k bd (d + 1) hk63 hlt (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide) (by simp +decide ) (fun b' s3 => ?_)
    refine specR_congr (m' := internLetEE t' w' b' >>= fun r => pure r) (by simp) ?_
    refine specR_internLetI ra hok hc.internLet lW (vv lY) (vv lZ) (vv lB) t' w' b' (by decide) (by simp +decide)
      (by simp +decide) (by simp +decide) (fun r s4 => ?_)
    exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | _ => simp [ENodeView.tagN, h7] at htg

theorem projRestP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (nm : NIdx) (i : Nat) (e : EIdx) (hi : i < 2 ^ 64)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (ha1 : Γ.get lA1 = some (Enc.idxW nm)) (ha2 : Γ.get lA2 = some (Enc.idxW e))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) projRestP s
      (do let u ← instantiateList vs n k n' e d; internProjE nm i u) (PostE C) := by
  unfold projRestP
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine callP_spec C hc.ilp vs o n n' ih lY lA2 (vv pVk) (vv pD) k e d hk63 hd (by decide) hvs hn
    (by simp [hkk]) hfu ha2 (by simp [hdd]) (fun u s1 => ?_)
  refine specR_congr (m' := internProjE nm i u >>= fun r => pure r) (by simp) ?_
  refine specR_internProjI ra hok hc.internProj lW (vv lA1) (vv lY) (vv lB) nm i u hi63 (by decide)
    (by simp +decide [ha1]) (by simp +decide) (by simp +decide [hb]) (fun r s2 => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem projP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n') {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (h9 : h.tag = 9)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) projP s (instListArmProj vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListArmProj]) ?_
  unfold projP
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
      exact projRestP_spec ra C hok hc vs o n n' ih h k d hk63 hd nm 0 e (by decide) (by simp +decide [hvs])
        (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide [hh])
        (by simp +decide [hdd]) (by simp +decide) (by simp +decide) (by simp)
    · by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' lB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] (M := M)
              simpa [encEView, Enc.encProj, hl] using this) ?_
        exact projRestP_spec ra C hok hc vs o n n' ih h k d hk63 hd nm i e ib (by simp +decide [hvs])
          (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide [hh])
          (by simp +decide [hdd]) (by simp +decide) (by simp +decide) (by simp)
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

end ConPanqueque.T.ExP
