import ConPanqueque.T.Ex.SizeB
import ConPanqueque.T.Memo
import ConPanqueque.T.Proj
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `instantiate1Go`: a memoized rebuilding walk

The twin's `instantiate1Go v fuel h d` (replace `bvar d` by `v`, lowering loose `bvar`s above `d`): the
derived-word cutoff, the tag dispatch, and five arms that probe the memo, rebuild through the interns
and record the answer. As a Pancake function `inst1Go(v, fu, h, d)`.
-/

namespace ConPanqueque.T.ExI
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS

def fInst1 := ofString "inst1Go"
def pV := ofString "iv"
def pD := ofString "idd"
def lB := ofString "bb"
def lW := ofString "ww"
def lD1 := ofString "dd1"

def callG (x arg : MlS) (dE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fInst1 [vv pV, .op .sub [vv pFu, .const 1], vv arg, dE]

/-- `KB[0] := h; KB[1] := d; x := memoGet(G, len)`. -/
def memoGetP (G : BitVec 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (vv pD))
      (.seq (.call (some (some (.local, lX), none)) fMemoGet [.const G, lenE (vv pD)]) rest))

/-- `KB[0] := h; KB[1] := d; x := memoSet(G, len, w)`. -/
def memoSetP (G : BitVec 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (vv pD))
      (.seq (.call (some (some (.local, lX), none)) fMemoSet [.const G, lenE (vv pD), vv lW]) rest))

/-- The memo probe, and on a hit its answer. -/
def probed (G : BitVec 64) (miss : ProgHOL 64) : ProgHOL 64 :=
  memoGetP G (.ite (vv lX) (.return (.op .sub [vv lX, .const 1])) miss)

def appArm (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (callG lY lA1 (vv pD)) (.seq (callG lZ lA2 (vv pD))
    (.seq (.call (some (some (.local, lW), none)) fInternApp [vv lY, vv lZ])
    (memoSetP G (.return (vv lW)))))))))))

def bindTail (G : BitVec 64) (fn : MlS) : ProgHOL 64 :=
  .seq (.call (some (some (.local, lW), none)) fn [vv lY, vv lZ]) (memoSetP G (.return (vv lW)))

def bindArm (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callG lY lA1 (vv pD)) (.seq (callG lZ lA2 (vv lD1))
    (.ite (tagIsE pH 5) (bindTail G fInternLam) (bindTail G fInternForallE)))))))))))

def letArm (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
    (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callG lY lA1 (vv pD)) (.seq (callG lZ lA2 (vv pD)) (.seq (callG lB lA3 (vv lD1))
    (.seq (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB])
    (memoSetP G (.return (vv lW)))))))))))))))

def inst1Locals : List MlS := [lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, lRp, lRn, lB, lX, lA1, lA2, lA3, lY, lZ, lW, lD1]

abbrev DI : List MlS := ctxLocals ++ inst1Locals

section
variable {σ : Type}

/-- The spec of the walk at fuel `n`, for every body `B` (the function's code). -/
def Rec1 (C : Ctx) (B : ProgHOL 64) (n : Nat) : Prop :=
  ∀ (v h : EIdx) (d : Nat) (s : AState), d < 2 ^ 63 →
    SpecR (Pre (σ := σ) C s [(pV, Enc.idxW v), (pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h), (pD, BitVec.ofNat 64 d)])
      B s (instantiate1Go v n h d) (PostE C)

theorem callG_spec {β : Type} (C : Ctx) (B : ProgHOL 64)
    (hcode : C.code.lookup fInst1 = some ([(pV, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one))
    (n : Nat) (ih : Rec1 (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (dE : ExpHOL 64) (v c : EIdx) (d : Nat)
    (hd : d < 2 ^ 63) (hx : x ∈ DI)
    (hv : Γ.get pV = some (Enc.idxW v)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (harg : Γ.get arg = some (Enc.idxW c)) (hdE : sev Γ dE = some (BitVec.ofNat 64 d))
    (hk : ∀ a s', SpecR (Inv C s' ((x, Enc.idxW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callG x arg dE) rest) s (instantiate1Go v n c d >>= k) R := by
  refine specR_call4IM x fInst1 pV pFu pH pD (by decide) _ _ _ _ B (Enc.idxW v) (BitVec.ofNat 64 (n + 1) - 1)
    (Enc.idxW c) (BitVec.ofNat 64 d) hx hcode (by simp [hv]) (by simp [sev, hfu]) (by simp [harg]) hdE
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 w hw => by
      subst hw
      exact ih v c d s hd _ ⟨hu, fun y z hy => by
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

end

/-- The code map holds the walk's body `B` and every function it calls. -/
structure Codes (C : Ctx) (B : ProgHOL 64) : Prop where
  inst1 : C.code.lookup fInst1 = some ([(pV, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one)
  memoGet : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  memoProbe : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  memoSet : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  memoIns : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)
  internApp : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  internLam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  internForallE : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  internLet : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  internBVar : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  internProj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)

section
variable {σ : Type}

theorem appArm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : Codes C B) (n : Nat) (ih : Rec1 (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (v h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (h4 : h.tag = 4)
    (hv : Γ.get pV = some (Enc.idxW v)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (appArm C.mG) s (instantiate1ArmApp v n h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmApp]) ?_
  unfold appArm probed memoGetP
  refine specR_inst1GetI hok hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide) (by simp [hh])
    (by simp [hdd]) hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    refine specR_ifI (vv lX) 0 (by simp [optW]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
    refine specR_viewAppI h h4 (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun f a P => ?_)
    refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
    refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
    refine callG_spec C B hc.inst1 n ih lY lA1 (vv pD) v f d hd (by decide) (by simp +decide [hv])
      (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun f' s1 => ?_)
    refine callG_spec C B hc.inst1 n ih lZ lA2 (vv pD) v a d hd (by decide) (by simp +decide [hv])
      (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun a' s2 => ?_)
    refine specR_internAppI ra hok hc.internApp lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide)
      (by simp +decide) (fun r s3 => ?_)
    unfold memoSetP
    refine specR_inst1SetI hok hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
      (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide) (by simp +decide [hkb]) (fun w => ?_)
    exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem viewBind_run (h : EIdx) (hb : h.tag = 5 ∨ h.tag = 6) (s : AState) (v : ENodeView)
    (hv : s.store.view h = some v) : ConRon.Arena.viewBind h s = .ok (projBind v, s) :=
  viewX_run ConRon.Arena.viewBind (fun st h => st.viewBind h) (fun _ _ => rfl) projBind h
    (fun st => viewBind_bind st h hb) s v hv

theorem bindArm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : Codes C B) (n : Nat) (ih : Rec1 (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (v h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (hb : h.tag = 5 ∨ h.tag = 6)
    (hv : Γ.get pV = some (Enc.idxW v)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (bindArm C.mG) s (instantiate1ArmBind v n h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmBind]) ?_
  unfold bindArm probed memoGetP
  refine specR_inst1GetI hok hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide) (by simp [hh])
    (by simp [hdd]) hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    refine specR_ifI (vv lX) 0 (by simp [optW]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
    refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h hb s vw hvw)
      (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg => ?_)
    cases vw with
    | lam ty bd =>
      have htag : h.tag = 5 := by
        simp [ENodeView.tagN] at htg
        apply UInt32.toNat_inj.mp; simp; omega
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
        (wordsAt_mem0 _ _ _ _) ?_
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp +decide [sev]) rfl
        (wordsAt_mem1 _ _ _ _ _) ?_
      refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
        (by simp +decide [sev, hdd]; rw [word_add1_eq]) ?_
      refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (d + 1) >>> (63 : BitVec 64).toNat)
        (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
      have hlt := (shr63_eq_zero (d + 1) (by omega)).mp hw
      refine callG_spec C B hc.inst1 n ih lY lA1 (vv pD) v ty d hd (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
      refine callG_spec C B hc.inst1 n ih lZ lA2 (vv lD1) v bd (d + 1) hlt (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s2 => ?_)
      obtain ⟨w5, hw5, hw5i⟩ := sev_tagIs ((lZ, Enc.idxW b') :: (lY, Enc.idxW t') :: (lD1, BitVec.ofNat 64 (d + 1)) ::
        (lA2, Enc.idxW bd) :: (lA1, Enc.idxW ty) :: (lRp, P) ::
        (lRn, BitVec.ofNat 64 (encEView (.lam ty bd)).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
        (lDg, BitVec.ofNat 64 (ENodeView.lam ty bd).tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
        (lDh, Enc.idxW h) :: (lFl, C.FLe) :: Γ) pH h (by simp +decide [hh]) 5 (by decide) (by decide)
      refine specR_ifI (tagIsE pH 5) w5 hw5 (fun hw => ?_) (fun hw => absurd (hw5i.mpr htag) (by simp [hw]))
      have hib : internBindE h.tag t' b' = internLamE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (by rw [hib]) ?_
      unfold bindTail
      refine specR_internLamI ra hok hc.internLam lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      unfold memoSetP
      refine specR_inst1SetI hok hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
        (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide) (by simp +decide [hkb]) (fun w => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | forallE ty bd =>
      have htag : h.tag = 6 := by
        simp [ENodeView.tagN] at htg
        apply UInt32.toNat_inj.mp; simp; omega
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
        (wordsAt_mem0 _ _ _ _) ?_
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp +decide [sev]) rfl
        (wordsAt_mem1 _ _ _ _ _) ?_
      refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
        (by simp +decide [sev, hdd]; rw [word_add1_eq]) ?_
      refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (d + 1) >>> (63 : BitVec 64).toNat)
        (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
      have hlt := (shr63_eq_zero (d + 1) (by omega)).mp hw
      refine callG_spec C B hc.inst1 n ih lY lA1 (vv pD) v ty d hd (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
      refine callG_spec C B hc.inst1 n ih lZ lA2 (vv lD1) v bd (d + 1) hlt (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s2 => ?_)
      obtain ⟨w5, hw5, hw5i⟩ := sev_tagIs ((lZ, Enc.idxW b') :: (lY, Enc.idxW t') :: (lD1, BitVec.ofNat 64 (d + 1)) ::
        (lA2, Enc.idxW bd) :: (lA1, Enc.idxW ty) :: (lRp, P) ::
        (lRn, BitVec.ofNat 64 (encEView (.forallE ty bd)).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
        (lDg, BitVec.ofNat 64 (ENodeView.forallE ty bd).tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
        (lDh, Enc.idxW h) :: (lFl, C.FLe) :: Γ) pH h (by simp +decide [hh]) 5 (by decide) (by decide)
      refine specR_ifI (tagIsE pH 5) w5 hw5 (fun hw => absurd (hw5i.mp hw) (by rw [htag]; decide)) (fun hw => ?_)
      have hib : internBindE h.tag t' b' = internForallEE t' b' := by simp [internBindE, htag, ETag.lam]
      refine specR_congr (by rw [hib]) ?_
      unfold bindTail
      refine specR_internForallEI ra hok hc.internForallE lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide)
        (by simp +decide) (fun r s3 => ?_)
      unfold memoSetP
      refine specR_inst1SetI hok hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
        (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide) (by simp +decide [hkb]) (fun w => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ => simp [ENodeView.tagN] at htg; rcases hb with hb | hb <;> rw [hb] at htg <;> simp at htg

end

section
variable {σ : Type}

theorem viewLet_run (h : EIdx) (h7 : h.tag = 7) (s : AState) (v : ENodeView)
    (hv : s.store.view h = some v) : ConRon.Arena.viewLet h s = .ok (projLet v, s) :=
  viewX_run ConRon.Arena.viewLet (fun st h => st.viewLet h) (fun _ _ => rfl) projLet h
    (fun st => viewLet_bind st h h7) s v hv

theorem letArm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : Codes C B) (n : Nat) (ih : Rec1 (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (v h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (h7 : h.tag = 7)
    (hv : Γ.get pV = some (Enc.idxW v)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (letArm C.mG) s (instantiate1ArmLet v n h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmLet]) ?_
  unfold letArm probed memoGetP
  refine specR_inst1GetI hok hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide) (by simp [hh])
    (by simp [hdd]) hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    refine specR_ifI (vv lX) 0 (by simp [optW]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
    refine specR_viewXI ConRon.Arena.viewLet projLet h (fun vw hvw => viewLet_run h h7 s vw hvw)
      (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg => ?_)
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
      refine callG_spec C B hc.inst1 n ih lY lA1 (vv pD) v ty d hd (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
      refine callG_spec C B hc.inst1 n ih lZ lA2 (vv pD) v vl d hd (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun w' s2 => ?_)
      refine callG_spec C B hc.inst1 n ih lB lA3 (vv lD1) v bd (d + 1) hlt (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s3 => ?_)
      refine specR_internLetI ra hok hc.internLet lW (vv lY) (vv lZ) (vv lB) t' w' b' (by decide) (by simp +decide)
        (by simp +decide) (by simp +decide) (fun r s4 => ?_)
      unfold memoSetP
      refine specR_inst1SetI hok hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
        (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide) (by simp +decide [hkb]) (fun w => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ => simp [ENodeView.tagN, h7] at htg

end

end ConPanqueque.T.ExI
