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

/-- The `bvar` arm after `bb` holds the index: `i = d` answers `v`, `i > d` interns `bvar (i - 1)`, else `h`. -/
def bvarRest : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.ite (.cmp .equal (vv lB) (vv pD)) (.return (vv pV))
      (.ite (.cmp .lower (vv pD) (vv lB))
        (.seq (.call (some (some (.local, lW), none)) fInternBVar [.op .sub [vv lB, .const 1]]) (.return (vv lW)))
        (.return (vv pH))))

def bvarArm : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local lB (.const 0)) bvarRest)
      (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 0])))
        bvarRest) hang))))

def projRest (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.seq (callG lY lA2 (vv pD))
      (.seq (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (memoSetP G (.return (vv lW)))))

def projArm (G : BitVec 64) : ProgHOL 64 :=
  probed G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRest G))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRest G)) hang)))))))

/-- The cutoff word `(der >>> 16) & 32767` (the packed word's bvar-range field). -/
def bvarFieldE (e : ExpHOL 64) : ExpHOL 64 := .op .and [.shift .lsr e (.const 16), .const 32767]

def core (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
   (.seq (.assign .local lB (bvarFieldE (vv lDo1)))
   (.ite (.op .and [.cmp .lower (vv lB) (.const 32767), .cmp .notLower (vv pD) (vv lB)]) (.return (vv pH))
    (.ite (isAppE (vv pH)) (appArm G)
     (.ite (.op .or [tagIsE pH 5, tagIsE pH 6]) (bindArm G)
      (.ite (tagIsE pH 0) bvarArm
       (.ite (tagIsE pH 7) (letArm G)
        (.ite (tagIsE pH 9) (projArm G) (.return (vv pH))))))))))))

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
    SpecR (Inv (σ := σ) C s Γ M DI) (appArm (C.mG .inst1)) s (instantiate1ArmApp v n h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmApp]) ?_
  unfold appArm probed memoGetP
  refine specR_memoGetI hok .inst1 inst1Get inst1Get_run hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide) (by simp [hh])
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
    refine specR_memoSetI hok .inst1 inst1Set inst1Set_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
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
    SpecR (Inv (σ := σ) C s Γ M DI) (bindArm (C.mG .inst1)) s (instantiate1ArmBind v n h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmBind]) ?_
  unfold bindArm probed memoGetP
  refine specR_memoGetI hok .inst1 inst1Get inst1Get_run hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide) (by simp [hh])
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
      refine specR_memoSetI hok .inst1 inst1Set inst1Set_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
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
      refine specR_memoSetI hok .inst1 inst1Set inst1Set_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
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
    SpecR (Inv (σ := σ) C s Γ M DI) (letArm (C.mG .inst1)) s (instantiate1ArmLet v n h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmLet]) ?_
  unfold letArm probed memoGetP
  refine specR_memoGetI hok .inst1 inst1Get inst1Get_run hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide) (by simp [hh])
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
      refine callG_spec C B hc.inst1 n ih lY lA1 (vv pD) v ty d hd (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun t' s1 => ?_)
      refine callG_spec C B hc.inst1 n ih lZ lA2 (vv pD) v vl d hd (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hdd]) (fun w' s2 => ?_)
      refine callG_spec C B hc.inst1 n ih lB lA3 (vv lD1) v bd (d + 1) hlt (by decide) (by simp +decide [hv])
        (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s3 => ?_)
      refine specR_internLetI ra hok hc.internLet lW (vv lY) (vv lZ) (vv lB) t' w' b' (by decide) (by simp +decide)
        (by simp +decide) (by simp +decide) (fun r s4 => ?_)
      unfold memoSetP
      refine specR_memoSetI hok .inst1 inst1Set inst1Set_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
        (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide) (by simp +decide [hkb]) (fun w => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ => simp [ENodeView.tagN, h7] at htg

end

section
variable {σ : Type}

theorem limbs_len_ge2 (i : Nat) (hi : 2 ^ 64 ≤ i) : 2 ≤ (Enc.limbs i).length := by
  unfold Enc.limbs
  have h0 : i ≠ 0 := by omega
  simp only [h0, ↓reduceDIte, List.length_cons]
  unfold Enc.limbs
  have h1 : i / 2 ^ 64 ≠ 0 := by omega
  simp [h1]

theorem viewBVar_run (h : EIdx) (h0 : h.tag = 0) (s : AState) (v : ENodeView)
    (hv : s.store.view h = some v) : ConRon.Arena.viewBVar h s = .ok (projBVar v, s) :=
  viewX_run ConRon.Arena.viewBVar (fun st h => st.viewBVar h) (fun _ _ => rfl) projBVar h
    (fun st => viewBVar_bind st h h0) s v hv

theorem word_eq_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp at this; omega
  · intro e; rw [e]

theorem word_lt_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a < BitVec.ofNat 64 b ↔ a < b := by
  rw [BitVec.lt_def]; simp; omega

theorem bvarRest_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : Codes C B) {s : AState} {Γ : Env} {M : Mem} (v h : EIdx) (d i : Nat) (hd : d < 2 ^ 63) (hi : i < 2 ^ 64)
    (hv : Γ.get pV = some (Enc.idxW v)) (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) bvarRest s
      (if i = d then pure v else if i > d then internBVarE (i - 1) else pure h) (PostE C) := by
  unfold bvarRest
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  by_cases e : i = d
  · subst e
    refine specR_ifI _ 1 (by simp [sev, hb, hdd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure v) (by simp) ?_
    exact specR_returnI (vv pV) (Enc.idxW v) (by simp [hv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 d := fun x => e ((word_eq_iff i d hi (by omega)).mp x)
    refine specR_ifI _ 0 (by simp [sev, hb, hdd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    by_cases g : i > d
    · have hlt : BitVec.ofNat 64 d < BitVec.ofNat 64 i := (word_lt_iff d i (by omega) hi).mpr g
      refine specR_ifI _ 1 (by simp [sev, hb, hdd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]) (fun _ => ?_)
        (fun hw => absurd hw (by decide))
      refine specR_congr (m' := internBVarE (i - 1) >>= fun a => pure a) (by simp [e, g]) ?_
      refine specR_internBVarI ra hok hc.internBVar lW _ (i - 1) (by omega) (by decide)
        (by simp [sev, hb]; rw [show BitVec.ofNat 64 i - 1#64 = BitVec.ofNat 64 (i - 1) by
          rw [show (1#64) = BitVec.ofNat 64 1 from rfl]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega])
        (fun r s' => ?_)
      exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hnlt : ¬ BitVec.ofNat 64 d < BitVec.ofNat 64 i := fun x => g ((word_lt_iff d i (by omega) hi).mp x)
      refine specR_ifI _ 0 (by simp [sev, hb, hdd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt])
        (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_congr (m' := pure h) (by simp [e, g]) ?_
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp [hh]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem bvarArm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : Codes C B) {s : AState} {Γ : Env} {M : Mem}
    (v h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (h0 : h.tag = 0)
    (hv : Γ.get pV = some (Enc.idxW v)) (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) bvarArm s (instantiate1ArmBVar v h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmBVar]) ?_
  unfold bvarArm
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewXI ConRon.Arena.viewBVar projBVar h (fun vw hvw => viewBVar_run h h0 s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
  cases vw with
  | bvar i =>
    by_cases i0 : i = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
      exact bvarRest_spec ra C hok B hc v h d 0 hd (by decide) (by simp +decide [hv]) (by simp +decide [hh])
        (by simp +decide [hdd]) (by simp)
    · by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' lB _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by decide) (by simp +decide [sev])
          rfl (by have := wordsAt_mem0 P (BitVec.ofNat 64 i) [] (M := M); simpa [encEView, Enc.encBVar, hl] using this)
          ?_
        exact bvarRest_spec ra C hok B hc v h d i hd ib (by simp +decide [hv]) (by simp +decide [hh])
          (by simp +decide [hdd]) (by simp)
      · have hl := limbs_len_ge2 i (by omega)
        have hlt : (Enc.limbs i).length < 2 ^ 61 := hsh
        have hn0 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 0#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn1 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hn0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  | _ => simp [ENodeView.tagN, h0] at htg

end

section
variable {σ : Type}

theorem viewProj_run (h : EIdx) (h9 : h.tag = 9) (s : AState) (v : ENodeView)
    (hv : s.store.view h = some v) : ConRon.Arena.viewProj h s = .ok (projProj v, s) :=
  viewX_run ConRon.Arena.viewProj (fun st h => st.viewProj h) (fun _ _ => rfl) projProj h
    (fun st => viewProj_bind st h h9) s v hv

theorem projRest_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : Codes C B) (n : Nat) (ih : Rec1 (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (v h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (c : NIdx) (i : Nat) (e : EIdx) (hi : i < 2 ^ 64)
    (hv : Γ.get pV = some (Enc.idxW v)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hkb : Γ.get lKb = some C.KB) (ha1 : Γ.get lA1 = some (Enc.idxW c)) (ha2 : Γ.get lA2 = some (Enc.idxW e))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projRest (C.mG .inst1)) s
      (do let u ← instantiate1Go v n e d; let r ← internProjE c i u; inst1Set (h, d) r; pure r) (PostE C) := by
  unfold projRest
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine callG_spec C B hc.inst1 n ih lY lA2 (vv pD) v e d hd (by decide) hv hfu ha2 (by simp [hdd]) (fun u s1 => ?_)
  refine specR_internProjI ra hok hc.internProj lW (vv lA1) (vv lY) (vv lB) c i u hi63 (by decide)
    (by simp +decide [ha1]) (by simp +decide) (by simp +decide [hb]) (fun r s2 => ?_)
  unfold memoSetP
  refine specR_memoSetI hok .inst1 inst1Set inst1Set_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd (by decide)
    (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide) (by simp +decide [hkb]) (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem projArm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : Codes C B) (n : Nat) (ih : Rec1 (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (v h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (h9 : h.tag = 9)
    (hv : Γ.get pV = some (Enc.idxW v)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projArm (C.mG .inst1)) s (instantiate1ArmProj v n h d) (PostE C) := by
  refine specR_congr (by rw [instantiate1ArmProj]) ?_
  unfold projArm probed memoGetP
  refine specR_memoGetI hok .inst1 inst1Get inst1Get_run hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd (by decide) (by simp [hh])
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
    refine specR_viewXI ConRon.Arena.viewProj projProj h (fun vw hvw => viewProj_run h h9 s vw hvw)
      (by simp) (by simp +decide) (by simp +decide [hdir]) (by decide) (fun vw P htg hsh => ?_)
    cases vw with
    | proj c i e =>
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp [sev]) rfl
        (wordsAt_mem0 _ _ _ _) ?_
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev]) rfl
        (wordsAt_mem1 _ _ _ _ _) ?_
      have hlen : (encEView (.proj c i e)).length = 2 + (Enc.limbs i).length := by
        simp [encEView, Enc.encProj]; omega
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
        exact projRest_spec ra C hok B hc n ih v h d hd c 0 e (by decide) (by simp +decide [hv]) (by simp +decide [hfu])
          (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hkb]) (by simp +decide) (by simp +decide)
          (by simp)
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' lB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
            (by simp +decide [sev]) rfl
            (by have := wordsAt_mem2 P (Enc.idxW c) (Enc.idxW e) (BitVec.ofNat 64 i) [] (M := [])
                simpa [encEView, Enc.encProj, hl] using this) ?_
          exact projRest_spec ra C hok B hc n ih v h d hd c i e ib (by simp +decide [hv]) (by simp +decide [hfu])
            (by simp +decide [hh]) (by simp +decide [hdd]) (by simp +decide [hkb]) (by simp +decide) (by simp +decide)
            (by simp)
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

def body (C : Ctx) : ProgHOL 64 := prologue inst1Locals (core (C.mG .inst1))

theorem bvarOfData_word (der : UInt64) :
    der.toBitVec >>> (16 : Nat) &&& 32767#64 = (ConLeche.bvarOfData der).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ConLeche.bvarOfData]
  have e : (32767#64).toNat = 2 ^ 15 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  simp [UInt64.toNat_div, UInt64.toNat_mod]

theorem cutoff_iff (b d : Nat) (hb : b < 2 ^ 15) (hd : d < 2 ^ 63) :
    ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 b) 32767 then (1 : BitVec 64) else 0) &&&
      (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 d) (BitVec.ofNat 64 b) then 1 else 0))
      ≠ 0 ↔ (decide (b < ConLeche.satRange) && decide (b ≤ d)) = true := by
  have h1 : (BitVec.ofNat 64 b < (32767 : BitVec 64)) ↔ b < 32767 := by
    rw [BitVec.lt_def]; simp; omega
  have h2 : (BitVec.ofNat 64 d < BitVec.ofNat 64 b) ↔ d < b := by
    rw [BitVec.lt_def]; simp; omega
  have e1 : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 b) 32767 = decide (b < 32767) := by
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact decide_eq_decide.mpr h1
  have e2 : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 d) (BitVec.ofNat 64 b) =
      decide (b ≤ d) := by
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases c : d < b
    · have := h2.mpr c; simp [this]; omega
    · have : ¬ BitVec.ofNat 64 d < BitVec.ofNat 64 b := fun x => c (h2.mp x)
      simp [this]; omega
  rw [e1, e2]
  simp only [ConLeche.satRange]
  by_cases c1 : b < 32767 <;> by_cases c2 : b ≤ d <;> simp [c1, c2]

section
variable {σ : Type}

/-- The tag test's value at a handle word. -/
def tagW (h : EIdx) (k : Nat) : BitVec 64 :=
  if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal ((Enc.idxW h >>> (26 : Nat)) &&& 31) (BitVec.ofNat 64 k)
  then 1 else 0

theorem tagW_iff (h : EIdx) (k : Nat) (hk : k < 16) (hk4 : k ≠ 4) : tagW h k ≠ 0 ↔ h.tag = UInt32.ofNat k := by
  rw [← tag_bits_iff h k hk hk4]
  unfold tagW
  by_cases e : (Enc.idxW h >>> (26 : Nat)) &&& 31 = BitVec.ofNat 64 k
  · simp [e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem params_none1 (v h : EIdx) (n d : Nat) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pV, Enc.idxW v), (pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h),
      (pD, BitVec.ofNat 64 d)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem isBind_iff (h : EIdx) (w5 w6 : BitVec 64) (h5 : w5 ≠ 0 ↔ h.tag = UInt32.ofNat 5)
    (h6 : w6 ≠ 0 ↔ h.tag = UInt32.ofNat 6) : (w5 ||| w6) ≠ 0 ↔ ETag.isBind h.tag = true := by
  rw [Ne, show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl]
  simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq, ETag.lam, ETag.forallE]
  constructor
  · intro hn
    by_cases a : w5 = 0
    · have b : w6 ≠ 0 := fun b => hn ⟨a, b⟩
      exact Or.inr (h6.mp b)
    · exact Or.inl (h5.mp a)
  · rintro (e | e) ⟨a, b⟩
    · exact h5.mpr e a
    · exact h6.mpr e b

theorem inst1_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : Codes C (body C)) :
    ∀ n, n < 2 ^ 64 → Rec1 (σ := σ) C (body C) n := by
  intro n
  induction n with
  | zero =>
    intro _ v h d s hd
    refine specR_prologue (postE_locals C) (params_none1 v h 0 d C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf v h d s hd
    have ih' := ih (by omega)
    refine specR_prologue (postE_locals C) (params_none1 v h (n + 1) d C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [instantiate1Go_succ]) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) rfl ?_
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
    · simp +decide [sev, Env.kill, ctxEnv, hbt]
    · exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv])
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_iteI (isAppE (vv pH)) (isAppW (Enc.idxW h)) ?_
      (by rw [isApp_iff]; simp [ETag.app]) (fun hb => ?_) (fun _ => ?_)
    · exact Ex2.sev_isApp _ pH _ (by simp +decide [Env.kill, ctxEnv])
    · have h4 : h.tag = 4 := by simpa [ETag.app] using hb
      exact appArm_spec ra C hok (body C) hc n ih' v h d hd h4 (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    refine specR_iteI (.op .or [tagIsE pH 5, tagIsE pH 6]) (tagW h 5 ||| tagW h 6) ?_
      (isBind_iff h _ _ (tagW_iff h 5 (by decide) (by decide)) (tagW_iff h 6 (by decide) (by decide)))
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv]
    · have hb' : h.tag = 5 ∨ h.tag = 6 := by
        simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq, ETag.lam, ETag.forallE] at hb; exact hb
      exact bindArm_spec ra C hok (body C) hc n ih' v h d hd hb' (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    refine specR_iteI (tagIsE pH 0) (tagW h 0) ?_ (by rw [tagW_iff h 0 (by decide) (by decide)]; simp [ETag.bvar])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv]
    · have h0 : h.tag = 0 := by simpa [ETag.bvar] using hb
      exact bvarArm_spec ra C hok (body C) hc v h d hd h0 (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    refine specR_iteI (tagIsE pH 7) (tagW h 7) ?_ (by rw [tagW_iff h 7 (by decide) (by decide)]; simp [ETag.letE])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv]
    · have h7 : h.tag = 7 := by simpa [ETag.letE] using hb
      exact letArm_spec ra C hok (body C) hc n ih' v h d hd h7 (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    refine specR_iteI (tagIsE pH 9) (tagW h 9) ?_ (by rw [tagW_iff h 9 (by decide) (by decide)]; simp [ETag.proj])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, Env.kill, ctxEnv]
    · have h9 : h.tag = 9 := by simpa [ETag.proj] using hb
      exact projArm_spec ra C hok (body C) hc n ih' v h d hd h9 (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
end

end ConPanqueque.T.ExI
