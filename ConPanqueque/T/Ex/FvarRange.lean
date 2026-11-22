import ConPanqueque.T.Ex.Lift
import ConPanqueque.T.MemoN
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `fvarRangeGo`

The exact fvar range of a term (one more than its largest `fvar` index, `0` if none), memoized in
the `EIdx → Nat` memo `fvarBC`. As a Pancake function `fvr(fu, h)` returning the range as a word;
indices whose range does not fit below `2^63` decline (hang).
-/

namespace ConPanqueque.T.ExF
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExL

def fFvr := ofString "fvarRangeGo"

def callF (x arg : MlS) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fFvr [.op .sub [vv pFu, .const 1], vv arg]

/-- `KB[0] := h; x := memoGet(G, 1)`; a hit answers. -/
def probedF (G : BitVec 64) (miss : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
    (.seq (.call (some (some (.local, lX), none)) fMemoGet [.const G, .const 1])
      (.ite (vv lX) (.return (.op .sub [vv lX, .const 1])) miss))

/-- `KB[0] := h; memoSet(G, 1, w); return w`. -/
def setRetF (G : BitVec 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
    (.seq (.call (some (some (.local, lX), none)) fMemoSet [.const G, .const 1, vv lW]) (.return (vv lW)))

/-- `w := max w z; rest`. -/
def maxW (z : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower (vv lW) (vv z)) (.seq (.assign .local lW (vv z)) rest) rest

/-- Two children at `rp`, `rp + 8` (`app`, `lam`, `forallE`). -/
def twoF (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (callF lY lA1) (.seq (callF lZ lA2) (.seq (.assign .local lW (vv lY)) (maxW lZ (setRetF G))))))

def letF (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
  (.seq (callF lY lA1) (.seq (callF lZ lA2) (.seq (callF lB lA3)
    (.seq (.assign .local lW (vv lY)) (maxW lZ (maxW lB (setRetF G)))))))))

def projF (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (callF lY lA2) (.seq (.assign .local lW (vv lY)) (setRetF G)))

/-- `fvar idx ty`: `idx` in `bb` (from the limbs), range `idx + 1` (guarded below `2^63`). -/
def fvarRestF (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.seq (.assign .local lW (.op .add [vv lB, .const 1]))
      (.ite (.shift .lsr (vv lW) (.const 63)) hang (setRetF G)))

def fvarF (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.const 0)) (fvarRestF G))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 8]))) (fvarRestF G)) hang)

def leafF (G : BitVec 64) : ProgHOL 64 := .seq (.assign .local lW (.const 0)) (setRetF G)

def coreF (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (probedF G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
     (.ite (tagEq 4) (twoF G)
      (.ite (tagEq 5) (twoF G)
       (.ite (tagEq 6) (twoF G)
        (.ite (tagEq 7) (letF G)
         (.ite (tagEq 9) (projF G)
          (.ite (tagEq 1) (fvarF G) (leafF G)))))))))))

def bodyF (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreF (C.mG (.n .fvarB)))

theorem fvarBGet_run (k : EIdx) (s : AState) : fvarBGet k s = .ok ((memoSelN .fvarB s.memos)[k]?, s) := rfl
theorem fvarBSet_run (k : EIdx) (r : Nat) (s : AState) :
    fvarBSet k r s = .ok ((), { s with memos := memoUpdN .fvarB s.memos ((memoSelN .fvarB s.memos).insert k r) }) := rfl

structure CodesF (C : Ctx) (B : ProgHOL 64) : Prop where
  fvr : C.code.lookup fFvr = some ([(pFu, .one), (pH, .one)], B, .one)
  memoGet : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  memoProbe : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  memoSet : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  memoIns : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)

section
variable {σ : Type}

/-- A Nat-returning function's post: the word is the answer, which is below `2^63`. -/
def PostN (C : Ctx) (a : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = natW a ∧ a < 2 ^ 63 ∧ SR C s' st

theorem postN_locals (C : Ctx) : ∀ (a : Nat) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostN C a w s' st → PostN C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

def RecF (C : Ctx) (B : ProgHOL 64) (n : Nat) : Prop :=
  ∀ (h : EIdx) (s : AState),
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)]) B s (fvarRangeGo n h) (PostN C)

theorem callF_spec {β : Type} (C : Ctx) (B : ProgHOL 64)
    (hcode : C.code.lookup fFvr = some ([(pFu, .one), (pH, .one)], B, .one))
    (n : Nat) (ih : RecF (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (h : EIdx) (hx : x ∈ DI)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (harg : Γ.get arg = some (Enc.idxW h))
    (hk : ∀ a s', a < 2 ^ 63 → SpecR (Inv C s' ((x, natW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callF x arg) rest) s (fvarRangeGo n h >>= k) R := by
  refine specR_call2IM x fFvr pFu pH (by decide) _ _ B (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW h) hx hcode
    (by simp [sev, hfu]) (by simp [harg]) (PostN C) (fun _ _ _ _ hp => hp.2.2)
    (fun u hu _ h1 h2 w hw => by
      subst hw
      exact ih h s _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; rw [h1, ofNat_succ_sub_one]
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun a w s' st hp => by obtain ⟨rfl, ha, _⟩ := hp; exact hk a s' ha)

/-- The memo probe: a hit answers, a miss runs `miss`. -/
theorem probedF_spec {C : Ctx} (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesF C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (miss : ProgHOL 64) (m : AM Nat)
    (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB)
    (hmiss : SpecR (Inv (σ := σ) C s ((lX, 0) :: Γ) [] DI) miss s m (PostN C)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (probedF (C.mG (.n .fvarB)) miss) s
      (do match ← fvarBGet h with | some r => pure r | none => m) (PostN C) := by
  unfold probedF
  refine specR_memoGetNI .fvarB fvarBGet fvarBGet_run hc.memoGet hc.memoProbe hok lX (vv pH) h (by decide)
    (by simp [hh]) hkb (fun r hr => ?_)
  cases r with
  | some w =>
    have hw := hr w rfl
    refine specR_ifI (vv lX) (natW w + 1) (by simp [optWG]) (fun _ => ?_)
      (fun e => absurd e (natW_add_one_ne w hw))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (natW w) (by simp [sev, optWG, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    exact specR_ifI (vv lX) 0 (by simp [optWG]) (fun hw => absurd rfl hw) (fun _ => hmiss)

/-- `KB[0] := h; memoSet(fvarBC, w); return w`. -/
theorem setRetF_spec {C : Ctx} (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesF C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (r : Nat) (hr : r < 2 ^ 63)
    (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB) (hw : Γ.get lW = some (natW r)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (setRetF (C.mG (.n .fvarB))) s (do fvarBSet h r; pure r) (PostN C) := by
  unfold setRetF
  refine specR_memoSetNI hok .fvarB fvarBSet fvarBSet_run hc.memoSet hc.memoIns lX (vv pH) (vv lW) h r hr
    (by decide) (by simp [hh]) (by simp [hw]) hkb (fun w => ?_)
  exact specR_returnI (vv lW) (natW r) (by simp +decide [hw]) (fun t ht => ⟨rfl, hr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- `w := max w z`. -/
theorem maxW_spec {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (z : MlS) (a b : Nat) (ha : a < 2 ^ 63)
    (hb : b < 2 ^ 63) (hwa : Γ.get lW = some (natW a)) (hzb : Γ.get z = some (natW b))
    (hk : ∀ Γ' : Env, Γ'.get lW = some (natW (max a b)) → (∀ y, y ≠ lW → Γ'.get y = Γ.get y) →
      SpecR (Inv C s Γ' M DI) rest s m R) :
    SpecR (Inv (σ := σ) C s Γ M DI) (maxW z rest) s m R := by
  unfold maxW
  by_cases g : a < b
  · have hlt : BitVec.ofNat 64 a < BitVec.ofNat 64 b := (word_lt_iff a b (by omega) (by omega)).mpr g
    refine specR_ifI _ 1 (by simp [sev, hwa, hzb, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt])
      (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_assignI lW (vv z) (natW b) (by decide) (by simp [hzb]) ?_
    exact hk _ (by simp [Nat.max_eq_right (Nat.le_of_lt g)]) (fun y hy => by simp [hy])
  · have hnlt : ¬ BitVec.ofNat 64 a < BitVec.ofNat 64 b := fun x => g ((word_lt_iff a b (by omega) (by omega)).mp x)
    refine specR_ifI _ 0 (by simp [sev, hwa, hzb, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    exact hk _ (by rw [hwa, Nat.max_eq_left (by omega)]) (fun _ _ => rfl)

end

section
variable {σ : Type}

theorem twoF_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesF C B) (n : Nat) (ih : RecF (σ := σ) C B n)
    {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (P : BitVec 64)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (a b : EIdx)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW a) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (twoF (C.mG (.n .fvarB))) s
      ((do let x ← fvarRangeGo n a; let y ← fvarRangeGo n b; pure (max x y)) >>= fun r => do fvarBSet h r; pure r)
      (PostN C) := by
  unfold twoF
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW a) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine specR_congr (m' := fvarRangeGo n a >>= fun x => fvarRangeGo n b >>= fun y => (do fvarBSet h (max x y); pure (max x y)))
    (by simp only [bind_assoc, pure_bind]) ?_
  refine callF_spec C B hc.fvr n ih lY lA1 a (by decide) (by simp +decide [hfu]) (by simp +decide) (fun x s1 hx => ?_)
  refine callF_spec C B hc.fvr n ih lZ lA2 b (by decide) (by simp +decide [hfu]) (by simp +decide) (fun y s2 hy => ?_)
  refine specR_assignI lW (vv lY) (natW x) (by decide) (by simp +decide) ?_
  refine maxW_spec lZ x y hx hy (by simp +decide) (by simp +decide) (fun Γ' hw hfr => ?_)
  exact setRetF_spec hok B hc h (max x y) (by omega) (by rw [hfr _ (by decide)]; simp +decide [hh])
    (by rw [hfr _ (by decide)]; simp +decide [hkb]) hw

theorem letF_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesF C B) (n : Nat) (ih : RecF (σ := σ) C B n)
    {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (P : BitVec 64)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (ty v b : EIdx)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW ty) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW v) ∈ M)
    (hm2 : (P + BitVec.ofNat 64 16, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (letF (C.mG (.n .fvarB))) s
      ((do let x ← fvarRangeGo n ty; let y ← fvarRangeGo n v; let z ← fvarRangeGo n b; pure (max (max x y) z)) >>=
        fun r => do fvarBSet h r; pure r) (PostN C) := by
  unfold letF
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW ty) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW v) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine specR_loadI' lA3 _ (P + 16) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm2 ?_
  refine specR_congr (m' := fvarRangeGo n ty >>= fun x => fvarRangeGo n v >>= fun y => fvarRangeGo n b >>= fun z =>
      (do fvarBSet h (max (max x y) z); pure (max (max x y) z))) (by simp only [bind_assoc, pure_bind]) ?_
  refine callF_spec C B hc.fvr n ih lY lA1 ty (by decide) (by simp +decide [hfu]) (by simp +decide) (fun x s1 hx => ?_)
  refine callF_spec C B hc.fvr n ih lZ lA2 v (by decide) (by simp +decide [hfu]) (by simp +decide) (fun y s2 hy => ?_)
  refine callF_spec C B hc.fvr n ih lB lA3 b (by decide) (by simp +decide [hfu]) (by simp +decide) (fun z s3 hz => ?_)
  refine specR_assignI lW (vv lY) (natW x) (by decide) (by simp +decide) ?_
  refine maxW_spec lZ x y hx hy (by simp +decide) (by simp +decide) (fun Γ' hw hfr => ?_)
  refine maxW_spec lB (max x y) z (by omega) hz hw (by rw [hfr _ (by decide)]; simp +decide) (fun Γ'' hw' hfr' => ?_)
  exact setRetF_spec hok B hc h (max (max x y) z) (by omega)
    (by rw [hfr' _ (by decide), hfr _ (by decide)]; simp +decide [hh])
    (by rw [hfr' _ (by decide), hfr _ (by decide)]; simp +decide [hkb]) hw'

theorem projF_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesF C B) (n : Nat) (ih : RecF (σ := σ) C B n)
    {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (P : BitVec 64)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (sub : EIdx)
    (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW sub) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projF (C.mG (.n .fvarB))) s
      (fvarRangeGo n sub >>= fun r => do fvarBSet h r; pure r) (PostN C) := by
  unfold projF
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW sub) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine callF_spec C B hc.fvr n ih lY lA2 sub (by decide) (by simp +decide [hfu]) (by simp +decide) (fun x s1 hx => ?_)
  refine specR_assignI lW (vv lY) (natW x) (by decide) (by simp +decide) ?_
  exact setRetF_spec hok B hc h x hx (by simp +decide [hh]) (by simp +decide [hkb]) (by simp +decide)

theorem fvarRestF_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesF C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (i : Nat) (hi : i < 2 ^ 64)
    (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB) (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (fvarRestF (C.mG (.n .fvarB))) s
      (pure (i + 1) >>= fun r => do fvarBSet h r; pure r) (PostN C) := by
  unfold fvarRestF
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine specR_assignI lW _ (BitVec.ofNat 64 (i + 1)) (by decide) (by simp +decide [sev, hb]; rw [word_add1_eq]) ?_
  refine specR_ifI (.shift .lsr (vv lW) (.const 63)) (BitVec.ofNat 64 (i + 1) >>> (63 : BitVec 64).toNat)
    (by simp [sev]) (fun _ => specR_hangI) (fun hw2 => ?_)
  have hs63 := (shr63_eq_zero (i + 1) (by omega)).mp hw2
  refine specR_congr (by rw [pure_bind]) ?_
  exact setRetF_spec hok B hc h (i + 1) hs63 (by simp +decide [hh]) (by simp +decide [hkb]) (by simp +decide [natW])

theorem leafF_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesF C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB) :
    SpecR (Inv (σ := σ) C s Γ M DI) (leafF (C.mG (.n .fvarB))) s
      (pure 0 >>= fun r => do fvarBSet h r; pure r) (PostN C) := by
  unfold leafF
  refine specR_assignI lW (.const 0) (natW 0) (by decide) rfl ?_
  refine specR_congr (by rw [pure_bind]) ?_
  exact setRetF_spec hok B hc h 0 (by decide) (by simp +decide [hh]) (by simp +decide [hkb]) (by simp +decide)

end

section
variable {σ : Type}

macro "tagF" : term => `(fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)

theorem params_noneF (h : EIdx) (n : Nat) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem fvrGo_spec (C : Ctx) (hok : CtxOK C) (hc : CodesF C (bodyF C)) :
    ∀ n, n < 2 ^ 64 → RecF (σ := σ) C (bodyF C) n := by
  intro n
  induction n with
  | zero =>
    intro _ h s
    refine specR_prologue (postN_locals C) (params_noneF h 0 C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf h s
    have ih' := ih (by omega)
    refine specR_prologue (postN_locals C) (params_noneF h (n + 1) C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [fvarRangeGo_succ]) ?_
    refine probedF_spec hok (bodyF C) hc h _ _ (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) rfl ?_
    refine specR_congr (by rw [bind_assoc]) ?_
    refine specR_viewI h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by decide)
      (fun v P htg hsh => ?_)
    cases v with
    | app a b =>
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := fvarRangeArmApp n a b >>= fun r => do fvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [fvarRangeArmApp]) ?_
      refine twoF_spec C hok (bodyF C) hc n ih' h P ?_ ?_ ?_ ?_ a b
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | lam ty bd =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := fvarRangeArmBind n ty bd >>= fun r => do fvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [fvarRangeArmBind]) ?_
      refine twoF_spec C hok (bodyF C) hc n ih' h P ?_ ?_ ?_ ?_ ty bd
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | forallE ty bd =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := fvarRangeArmBind n ty bd >>= fun r => do fvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [fvarRangeArmBind]) ?_
      refine twoF_spec C hok (bodyF C) hc n ih' h P ?_ ?_ ?_ ?_ ty bd
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | letE ty vl bd =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := fvarRangeArmLet n ty vl bd >>= fun r => do fvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [fvarRangeArmLet]) ?_
      refine letF_spec C hok (bodyF C) hc n ih' h P ?_ ?_ ?_ ?_ ty vl bd
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) (wordsAt_mem2 _ _ _ _ _ _) <;> simp +decide [ctxEnv]
    | proj nm i sub =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine projF_spec C hok (bodyF C) hc n ih' h P ?_ ?_ ?_ ?_ sub (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | fvar idx ty =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      unfold fvarF
      have hlen : (encEView (.fvar idx ty)).length = 1 + (Enc.limbs idx).length := by
        simp [encEView, Enc.encFVar]; omega
      by_cases i0 : idx = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
        exact fvarRestF_spec C hok (bodyF C) hc h 0 (by decide) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
          (by simp)
      · by_cases ib : idx < 2 ^ 64
        · have hl : Enc.limbs idx = [BitVec.ofNat 64 idx] := by rw [limbs_small idx ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' lB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 idx) (by decide)
            (by simp +decide [sev]) rfl
            (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 idx) [] (M := [])
                simpa [encEView, Enc.encFVar, hl] using this) ?_
          exact fvarRestF_spec C hok (bodyF C) hc h idx ib (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
            (by simp)
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
    | bvar i =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafF_spec C hok (bodyF C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    | sort u =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafF_spec C hok (bodyF C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    | const nm us =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafF_spec C hok (bodyF C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    | lit l =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafF_spec C hok (bodyF C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])

end

/-! ## `fvarRangeMemo` and `fvarB` -/

theorem fvarBClear_run (s : AState) : fvarBClear s = .ok ((), { s with memos := memoUpdN .fvarB s.memos ∅ }) := rfl

theorem fvarOfData_word (der : UInt64) :
    der.toBitVec >>> (1 : Nat) &&& 32767#64 = (ConLeche.fvarOfData der).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ConLeche.fvarOfData]
  have e : (32767#64).toNat = 2 ^ 15 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  simp [UInt64.toNat_div, UInt64.toNat_mod]

def fFvarB := ofString "fvarB"

def fvbLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, lB, lJ0, lW]

/-- `fvarB(fu, h)`: the packed fvar-range field, or on saturation the memoized walk between clears. -/
def fvbBody (C : Ctx) : ProgHOL 64 :=
  prologue fvbLocals
   (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
   (.seq (.assign .local lB (.op .and [.shift .lsr (vv lDo1) (.const 1), .const 32767]))
   (.ite (.cmp .equal (vv lB) (.const 32767))
     (clearCode (C.mg (.n .fvarB))
       (.seq (.call (some (some (.local, lW), none)) fFvr [vv pFu, vv pH])
         (clearCode (C.mg (.n .fvarB)) (.return (vv lW)))))
     (.return (vv lB)))))))

section
variable {σ : Type}

theorem fvarB_spec (C : Ctx) (hok : CtxOK C) (hc : CodesF C (bodyF C)) (s : AState) (fuel : Nat) (e : EIdx)
    (hf : fuel < 2 ^ 64) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pH, Enc.idxW e)]) (fvbBody C) s (fvarB fuel e)
      (PostN C) := by
  refine specR_prologue (postN_locals C) (fun x hx => ?_) ?_
  · simp only [fvbLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW e) (by decide) rfl ?_
  unfold fvarB
  refine specR_derivedEI e rfl rfl rfl (by decide) ?_
  have hb15 : (ConLeche.fvarOfData (s.store.derived e)).toNat < 2 ^ 15 := by
    simp only [ConLeche.fvarOfData, UInt64.toNat_mod]; simp; omega
  have hbt : (ConLeche.fvarOfData (s.store.derived e)).toBitVec =
      BitVec.ofNat 64 (ConLeche.fvarOfData (s.store.derived e)).toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  refine specR_assignI lB _ (ConLeche.fvarOfData (s.store.derived e)).toBitVec (by decide)
    (by simp [sev]; exact fvarOfData_word _) ?_
  generalize hbdef : (ConLeche.fvarOfData (s.store.derived e)).toNat = b at hb15 hbt
  rw [hbt]
  refine specR_iteI (.cmp .equal (vv lB) (.const 32767))
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 b) 32767 then 1 else 0)
    (by simp [sev]) ?_ (fun _ => ?_) (fun hne => ?_)
  · have : (BitVec.ofNat 64 b = (32767 : BitVec 64)) ↔ b = 32767 :=
      word_eq_iff b 32767 (by omega) (by decide)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ConLeche.satRange]; exact this
  · unfold fvarRangeMemo
    refine specR_memoClearNI hok .fvarB fvarBClear fvarBClear_run (by decide) ?_
    refine specR_call2IM lW fFvr pFu pH (by decide) _ _ (bodyF C) (BitVec.ofNat 64 fuel) (Enc.idxW e) (by decide)
      hc.fvr (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
      (PostN C) (fun _ _ _ _ hp => hp.2.2)
      (fun u hu _ h1 h2 w hw => by
        subst hw
        exact fvrGo_spec C hok hc fuel hf e _ _ ⟨hu, fun y z hy => by
          simp only [Env.get] at hy
          split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h1
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h2
            · simp at hy⟩)
      (fun r w s' st hp => ?_)
    obtain ⟨rfl, hr, _⟩ := hp
    refine specR_memoClearNI hok .fvarB fvarBClear fvarBClear_run (by decide) ?_
    exact specR_returnI (vv lW) (natW r) (by simp +decide [Env.kill])
      (fun t ht => ⟨rfl, hr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · exact specR_returnI (vv lB) (natW b) (by simp +decide [natW])
      (fun t ht => ⟨rfl, by omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExF
