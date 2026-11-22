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

/-- The twin's `bvar` arm after the index `j` is read. -/
def bvarTw (vs : Array EIdx) (n k n' : Nat) (h : EIdx) (d j : Nat) : AM EIdx :=
  if j < d then pure h
  else if j - d < k then
    if hlt : j - d < n ∧ n ≤ vs.size then
      instListCutoff (vs[n - 1 - (j - d)]'(by omega)) d >>= fun b =>
        if b = true then pure (vs[n - 1 - (j - d)]'(by omega))
        else instantiateList vs n (j - d) n' (vs[n - 1 - (j - d)]'(by omega)) d
    else pure h
  else internBVarE (j - k)

theorem word_sub_eq (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem Env.get_kill_of_not_mem (Γ : Env) (xs : List MlS) (y : MlS) (hy : y ∉ xs) :
    (Γ.kill xs).get y = Γ.get y := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨x, v⟩ := p
    unfold Env.kill at ih ⊢
    by_cases hx : x ∈ xs
    · have hne : y ≠ x := fun e => hy (e ▸ hx)
      rw [List.filter_cons_of_neg (by simp [hx])]
      simp only [Env.get, hne, ite_false]; exact ih
    · rw [List.filter_cons_of_pos (by simp [hx])]
      simp only [Env.get]
      split
      · rfl
      · exact ih

theorem addr_rev (C : Ctx) (o n j d : Nat) (h1 : j - d < n) (hn : n < 2 ^ 59) :
    cellA C o + (BitVec.ofNat 64 n - BitVec.ofNat 64 (j - d)) <<< 3 = cellA C (o + 1 + (n - 1 - (j - d))) := by
  apply BitVec.eq_of_toNat_eq
  simp [cellA, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

section
variable {σ : Type}

theorem bvarRestP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n')
    (hblk : BlkAt C.H o (vs.toList.map Enc.idxW)) (hsz : vs.size < 2 ^ 59) (hn63 : n < 2 ^ 59)
    {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d j : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (hj : j < 2 ^ 64)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) (hb : Γ.get lB = some (BitVec.ofNat 64 j)) :
    SpecR (Inv (σ := σ) C s Γ M DI) bvarRestP s (bvarTw vs n k n' h d j) (PostE C) := by
  unfold bvarRestP
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 j >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hj63 := (shr63_eq_zero j hj).mp hw
  by_cases g1 : j < d
  · have hlt : BitVec.ofNat 64 j < BitVec.ofNat 64 d := (word_lt_iff j d hj (by omega)).mpr g1
    refine specR_ifI _ 1 (by simp [sev, hb, hdd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure h) (by simp [bvarTw, g1]) ?_
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp [hh]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hnlt : ¬ BitVec.ofNat 64 j < BitVec.ofNat 64 d := fun x => g1 ((word_lt_iff j d hj (by omega)).mp x)
  refine specR_ifI _ 0 (by simp [sev, hb, hdd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_assignI lW _ (BitVec.ofNat 64 (j - d)) (by decide)
    (by simp [sev, hb, hdd]; exact word_sub_eq j d (by omega) hj) ?_
  by_cases g2 : j - d < k
  · have hlt : BitVec.ofNat 64 (j - d) < BitVec.ofNat 64 k := (word_lt_iff _ k (by omega) (by omega)).mpr g2
    refine specR_ifI _ 1 (by simp +decide [sev, hkk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    obtain ⟨hol, hv0⟩ := blkAt_get0 hblk
    refine specR_heapLoadI lA3 (vv pVs) o hol (by decide) (by simp +decide [hvs]) ?_
    rw [show C.H[o]'hol = BitVec.ofNat 64 vs.size by rw [hv0]; simp]
    by_cases g3 : j - d < n ∧ n ≤ vs.size
    · have h1 : BitVec.ofNat 64 (j - d) < BitVec.ofNat 64 n := (word_lt_iff _ n (by omega) (by omega)).mpr g3.1
      have h2 : ¬ BitVec.ofNat 64 vs.size < BitVec.ofNat 64 n :=
        fun x => absurd ((word_lt_iff _ n (by omega) (by omega)).mp x) (by omega)
      refine specR_ifI _ 1 (by
          simp +decide [sev, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h1, h2,
            Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega),
            Nat.mod_eq_of_lt (show vs.size < 18446744073709551616 by omega), g3.2])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      have hidx : n - 1 - (j - d) < (vs.toList.map Enc.idxW).length := by simp; omega
      obtain ⟨hl2, hv2⟩ := blkAt_get hblk (n - 1 - (j - d)) hidx
      refine specR_heapLoadI lY _ (o + 1 + (n - 1 - (j - d))) hl2 (by decide) ?_ ?_
      · simp +decide [sev, hvs, hn]; exact addr_rev C o n j d g3.1 hn63
      rw [show C.H[o + 1 + (n - 1 - (j - d))]'hl2 = Enc.idxW (vs[n - 1 - (j - d)]'(by omega)) by rw [hv2]; simp]
      generalize hvi : vs[n - 1 - (j - d)]'(by omega) = vi
      refine specR_congr (m' := derivedE vi >>= fun der =>
        if (decide ((ConLeche.bvarOfData der).toNat < ConLeche.satRange) &&
          decide ((ConLeche.bvarOfData der).toNat ≤ d)) = true then pure vi
        else instantiateList vs n (j - d) n' vi d) (by simp [bvarTw, g1, g2, g3, instListCutoff, hvi]) ?_
      refine specR_assignI lDh (vv lY) (Enc.idxW vi) (by decide) (by simp +decide) ?_
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
      refine specR_derivedEI vi (by simp +decide) (by simp +decide) (by simp +decide [hdir]) (by decide) ?_
      have hbt : (ConLeche.bvarOfData (s.store.derived vi)).toBitVec =
          BitVec.ofNat 64 (ConLeche.bvarOfData (s.store.derived vi)).toNat := by
        apply BitVec.eq_of_toNat_eq; simp
      have hb15 : (ConLeche.bvarOfData (s.store.derived vi)).toNat < 2 ^ 15 := by
        simp only [ConLeche.bvarOfData, UInt64.toNat_mod]; simp; omega
      refine specR_assignI lX (bvarFieldE (vv lDo1)) (ConLeche.bvarOfData (s.store.derived vi)).toBitVec (by decide)
        (by simp [sev, bvarFieldE]; exact bvarOfData_word _) ?_
      generalize hbdef : (ConLeche.bvarOfData (s.store.derived vi)).toNat = bb at hb15 hbt
      refine specR_iteI (.op .and [.cmp .lower (vv lX) (.const 32767), .cmp .notLower (vv pD) (vv lX)])
        ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 bb) 32767 then (1 : BitVec 64) else 0) &&&
          (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 d) (BitVec.ofNat 64 bb) then 1 else 0))
        ?_ (cutoff_iff bb d hb15 hd) (fun _ => ?_) (fun _ => ?_)
      · simp +decide [sev, Env.get_kill_of_not_mem, hbt, hdd]
      · exact specR_returnI (vv lY) (Enc.idxW vi) (by simp +decide [Env.get_kill_of_not_mem])
          (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_congr (m' := instantiateList vs n (j - d) n' vi d >>= fun r => pure r) (by simp) ?_
        refine callP_spec C hc.ilp vs o n n' ih lZ lY (vv lW) (vv pD) (j - d) vi d (by omega) hd (by decide)
          (by simp +decide [Env.get_kill_of_not_mem, hvs]) (by simp +decide [Env.get_kill_of_not_mem, hn]) (by simp +decide [Env.get_kill_of_not_mem])
          (by simp +decide [Env.get_kill_of_not_mem, hfu]) (by simp +decide [Env.get_kill_of_not_mem]) (by simp +decide [Env.get_kill_of_not_mem, hdd])
          (fun r s1 => ?_)
        exact specR_returnI (vv lZ) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hw0 : ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 (j - d)) (BitVec.ofNat 64 n)
          then (1 : BitVec 64) else 0) &&& (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower
          (BitVec.ofNat 64 vs.size) (BitVec.ofNat 64 n) then 1 else 0)) = 0 := by
        by_cases a : j - d < n
        · have hsn : vs.size < n := by omega
          have : BitVec.ofNat 64 vs.size < BitVec.ofNat 64 n := (word_lt_iff _ n (by omega) (by omega)).mpr hsn
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
        · have : ¬ BitVec.ofNat 64 (j - d) < BitVec.ofNat 64 n :=
            fun x => a ((word_lt_iff _ n (by omega) (by omega)).mp x)
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
      refine specR_ifI _ _ (by simp +decide [sev, hn]) (fun hw => absurd hw0 hw) (fun _ => ?_)
      refine specR_congr (m' := pure h) (by simp [bvarTw, g1, g2, g3]) ?_
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [hh]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hnl : ¬ BitVec.ofNat 64 (j - d) < BitVec.ofNat 64 k := fun x => g2 ((word_lt_iff _ k (by omega) (by omega)).mp x)
    refine specR_ifI _ 0 (by simp +decide [sev, hkk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnl])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_congr (m' := internBVarE (j - k) >>= fun r => pure r) (by simp [bvarTw, g1, g2]) ?_
    refine specR_internBVarI ra hok hc.internBVar lW _ (j - k) (by omega) (by decide)
      (by simp +decide [sev, hb, hkk]; exact word_sub_eq j k (by omega) hj) (fun r s' => ?_)
    exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem bvarP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n n' : Nat) (ih : RecP (σ := σ) C vs o n n')
    (hblk : BlkAt C.H o (vs.toList.map Enc.idxW)) (hsz : vs.size < 2 ^ 59) (hn63 : n < 2 ^ 59)
    {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (k d : Nat) (hk63 : k < 2 ^ 63) (hd : d < 2 ^ 63) (h0 : h.tag = 0)
    (hvs : Γ.get pVs = some (cellA C o)) (hn : Γ.get pVn = some (BitVec.ofNat 64 n))
    (hkk : Γ.get pVk = some (BitVec.ofNat 64 k)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n' + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) bvarP s (instListArmBVar vs n k n' h d) (PostE C) := by
  refine specR_congr (by rw [instListArmBVar]) ?_
  unfold bvarP
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewBVar projBVar h (fun vw hvw => viewBVar_run h h0 s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  cases vw with
  | bvar j =>
    refine specR_congr (m' := bvarTw vs n k n' h d j) rfl ?_
    by_cases i0 : j = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
      exact bvarRestP_spec ra C hok hc vs o n n' ih hblk hsz hn63 h k d 0 hk63 hd (by decide) (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hfle]) (by simp +decide [hdir]) (by simp)
    · by_cases ib : j < 2 ^ 64
      · have hl : Enc.limbs j = [BitVec.ofNat 64 j] := by rw [limbs_small j ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' lB _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 j) (by decide) (by simp +decide [sev])
          rfl (by have := wordsAt_mem0 P (BitVec.ofNat 64 j) [] (M := M); simpa [encEView, Enc.encBVar, hl] using this)
          ?_
        exact bvarRestP_spec ra C hok hc vs o n n' ih hblk hsz hn63 h k d j hk63 hd ib (by simp +decide [hvs]) (by simp +decide [hn]) (by simp +decide [hkk]) (by simp +decide [hfu]) (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hfle]) (by simp +decide [hdir]) (by simp)
      · have hl := limbs_len_ge2 j (by omega)
        have hlt : (Enc.limbs j).length < 2 ^ 61 := hsh
        have hn0 : BitVec.ofNat 64 (Enc.limbs j).length ≠ 0#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn1 : BitVec.ofNat 64 (Enc.limbs j).length ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hn0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  | _ => simp [ENodeView.tagN, h0] at htg

end

theorem instantiateList_succ' (vs : Array EIdx) (n k n' : Nat) (h : EIdx) (d : Nat) :
    instantiateList vs n k (n' + 1) h d = (derivedE h >>= fun der =>
      if (decide ((ConLeche.bvarOfData der).toNat < ConLeche.satRange) &&
        decide ((ConLeche.bvarOfData der).toNat ≤ d)) = true then pure h
      else if h.tag == ETag.app then instListArmApp vs n k n' h d
      else if ETag.isBind h.tag then instListArmBind vs n k n' h d
      else if h.tag == ETag.letE then instListArmLet vs n k n' h d
      else if h.tag == ETag.proj then instListArmProj vs n k n' h d
      else if h.tag == ETag.bvar then instListArmBVar vs n k n' h d
      else pure h) := by
  rw [instantiateList_succ]; simp only [instListCutoff, bind_assoc, pure_bind]

section
variable {σ : Type}

theorem params_noneP (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ ilpParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ ilpParams := by
    simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have hz : ∀ (ps : List MlS) (vs : List (BitVec 64)), x ∉ ps → Env.get (ps.zip vs) x = none := by
    intro ps vs hp
    induction ps generalizing vs with
    | nil => rfl
    | cons p ps ih =>
      cases vs with
      | nil => rfl
      | cons v vs =>
        simp only [List.mem_cons, not_or] at hp
        simp only [List.zip_cons_cons, Env.get, hp.1, ite_false]; exact ih vs hp.2
  have happ : ∀ (A B : Env), A.get x = none → B.get x = none → (A ++ B).get x = none := by
    intro A B hA hB
    induction A with
    | nil => exact hB
    | cons p A ih =>
      obtain ⟨y, v⟩ := p
      simp only [List.cons_append, Env.get] at hA ⊢
      split at hA
      · simp at hA
      · rename_i e; simp only [e, ite_false]; exact ih hA
  exact happ _ _ hc (hz _ _ hnot)

theorem ilp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesP C)
    (vs : Array EIdx) (o n : Nat) (hblk : BlkAt C.H o (vs.toList.map Enc.idxW)) (hsz : vs.size < 2 ^ 59)
    (hn63 : n < 2 ^ 59) :
    ∀ n', n' < 2 ^ 64 → RecP (σ := σ) C vs o n n' := by
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
    refine specR_prologue (postE_locals C) (params_noneP _ C) ?_
    refine specR_ifI _ _ (by simp +decide [sev, ctxEnv, ilpParams]; rfl) (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n' + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [instantiateList_succ']) ?_
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
      exact appP_spec ra C hok hc vs o n n' ih' h k d hk63 hd h4 (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (.op .or [tagIsE pH 5, tagIsE pH 6]) (tagW h 5 ||| tagW h 6) ?_
      (isBind_iff h _ _ (tagW_iff h 5 (by decide) (by decide)) (tagW_iff h 6 (by decide) (by decide)))
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · have hb' : h.tag = 5 ∨ h.tag = 6 := by
        simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq, ETag.lam, ETag.forallE] at hb; exact hb
      exact bindP_spec ra C hok hc vs o n n' ih' h k d hk63 hd hb' (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (tagIsE pH 7) (tagW h 7) ?_ (by rw [tagW_iff h 7 (by decide) (by decide)]; simp [ETag.letE])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · have h7 : h.tag = 7 := by simpa [ETag.letE] using hb
      exact letP_spec ra C hok hc vs o n n' ih' h k d hk63 hd h7 (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (tagIsE pH 9) (tagW h 9) ?_ (by rw [tagW_iff h 9 (by decide) (by decide)]; simp [ETag.proj])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · have h9 : h.tag = 9 := by simpa [ETag.proj] using hb
      exact projP_spec ra C hok hc vs o n n' ih' h k d hk63 hd h9 (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    refine specR_iteI (tagIsE pH 0) (tagW h 0) ?_ (by rw [tagW_iff h 0 (by decide) (by decide)]; simp [ETag.bvar])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv, ilpParams]
    · have h0 : h.tag = 0 := by simpa [ETag.bvar] using hb
      exact bvarP_spec ra C hok hc vs o n n' ih' hblk hsz hn63 h k d hk63 hd h0 (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (by simp +decide [Env.kill, ctxEnv, ilpParams])
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv, ilpParams]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExP
