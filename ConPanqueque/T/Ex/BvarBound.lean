import ConPanqueque.T.Ex.FvarRange
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `bvarBoundGo`

The exact loose-bvar bound of a term (one more than its largest loose `bvar` index, binders
subtracting one, `0` if none), memoized in the `EIdx → Nat` memo `bvarBC`. As a Pancake function
`bvr(fu, h)` returning the bound as a word;
indices whose range does not fit below `2^63` decline (hang).
-/

namespace ConPanqueque.T.ExB
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExL ConPanqueque.T.ExF

def fBvr := ofString "bvarBoundGo"

def callB (x arg : MlS) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fBvr [.op .sub [vv pFu, .const 1], vv arg]

/-- `KB[0] := h; x := memoGet(G, 1)`; a hit answers. -/
def probedB (G : BitVec 64) (miss : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
    (.seq (.call (some (some (.local, lX), none)) fMemoGet [.const G, .const 1])
      (.ite (vv lX) (.return (.op .sub [vv lX, .const 1])) miss))

/-- `KB[0] := h; memoSet(G, 1, w); return w`. -/
def setRetB (G : BitVec 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
    (.seq (.call (some (some (.local, lX), none)) fMemoSet [.const G, .const 1, vv lW]) (.return (vv lW)))

/-- Two children at `rp`, `rp + 8` (`app`, `lam`, `forallE`). -/
def twoB (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (callB lY lA1) (.seq (callB lZ lA2) (.seq (.assign .local lW (vv lY)) (maxW lZ (setRetB G))))))

/-- `z - 1` on naturals (`0 - 1 = 0`). -/
def predE (z : MlS) : ExpHOL 64 := .op .sub [vv z, .cmp .notEqual (vv z) (.const 0)]

/-- A binder: type at `rp`, body at `rp + 8`; the body's bound loses one. -/
def bindB (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (callB lY lA1) (.seq (callB lZ lA2) (.seq (.assign .local lZ (predE lZ))
    (.seq (.assign .local lW (vv lY)) (maxW lZ (setRetB G)))))))

def letB (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
  (.seq (callB lY lA1) (.seq (callB lZ lA2) (.seq (callB lB lA3) (.seq (.assign .local lB (predE lB))
    (.seq (.assign .local lW (vv lY)) (maxW lZ (maxW lB (setRetB G))))))))))

def projB (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (callB lY lA2) (.seq (.assign .local lW (vv lY)) (setRetB G)))

/-- `bvar i`: `i` in `bb` (from the limbs), bound `i + 1` (guarded below `2^63`). -/
def bvarRestB (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.seq (.assign .local lW (.op .add [vv lB, .const 1]))
      (.ite (.shift .lsr (vv lW) (.const 63)) hang (setRetB G)))

def bvarArmB (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local lB (.const 0)) (bvarRestB G))
    (.ite (.cmp .equal (vv lRn) (.const 1))
      (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 0]))) (bvarRestB G)) hang)

def leafB (G : BitVec 64) : ProgHOL 64 := .seq (.assign .local lW (.const 0)) (setRetB G)

def coreB (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (probedB G (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
     (.ite (tagEq 4) (twoB G)
      (.ite (tagEq 5) (bindB G)
       (.ite (tagEq 6) (bindB G)
        (.ite (tagEq 7) (letB G)
         (.ite (tagEq 9) (projB G)
          (.ite (tagEq 0) (bvarArmB G) (leafB G)))))))))))

def bodyB (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreB (C.mG (.n .bvarB)))

theorem bvarBGet_run (k : EIdx) (s : AState) : bvarBGet k s = .ok ((memoSelN .bvarB s.memos)[k]?, s) := rfl
theorem bvarBSet_run (k : EIdx) (r : Nat) (s : AState) :
    bvarBSet k r s = .ok ((), { s with memos := memoUpdN .bvarB s.memos ((memoSelN .bvarB s.memos).insert k r) }) := rfl

structure CodesB (C : Ctx) (B : ProgHOL 64) : Prop where
  bvr : C.code.lookup fBvr = some ([(pFu, .one), (pH, .one)], B, .one)
  memoGet : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  memoProbe : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  memoSet : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  memoIns : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)

section
variable {σ : Type}

def RecB (C : Ctx) (B : ProgHOL 64) (n : Nat) : Prop :=
  ∀ (h : EIdx) (s : AState),
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)]) B s (bvarBoundGo n h) (PostN C)

theorem callB_spec {β : Type} (C : Ctx) (B : ProgHOL 64)
    (hcode : C.code.lookup fBvr = some ([(pFu, .one), (pH, .one)], B, .one))
    (n : Nat) (ih : RecB (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (h : EIdx) (hx : x ∈ DI)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (harg : Γ.get arg = some (Enc.idxW h))
    (hk : ∀ a s', a < 2 ^ 63 → SpecR (Inv C s' ((x, natW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callB x arg) rest) s (bvarBoundGo n h >>= k) R := by
  refine specR_call2IM x fBvr pFu pH (by decide) _ _ B (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW h) hx hcode
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
theorem probedB_spec {C : Ctx} (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (miss : ProgHOL 64) (m : AM Nat)
    (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB)
    (hmiss : SpecR (Inv (σ := σ) C s ((lX, 0) :: Γ) [] DI) miss s m (PostN C)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (probedB (C.mG (.n .bvarB)) miss) s
      (do match ← bvarBGet h with | some r => pure r | none => m) (PostN C) := by
  unfold probedB
  refine specR_memoGetNI .bvarB bvarBGet bvarBGet_run hc.memoGet hc.memoProbe hok lX (vv pH) h (by decide)
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

/-- `KB[0] := h; memoSet(bvarBC, w); return w`. -/
theorem setRetB_spec {C : Ctx} (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (r : Nat) (hr : r < 2 ^ 63)
    (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB) (hw : Γ.get lW = some (natW r)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (setRetB (C.mG (.n .bvarB))) s (do bvarBSet h r; pure r) (PostN C) := by
  unfold setRetB
  refine specR_memoSetNI hok .bvarB bvarBSet bvarBSet_run hc.memoSet hc.memoIns lX (vv pH) (vv lW) h r hr
    (by decide) (by simp [hh]) (by simp [hw]) hkb (fun w => ?_)
  exact specR_returnI (vv lW) (natW r) (by simp +decide [hw]) (fun t ht => ⟨rfl, hr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem sev_predE (Γ : Env) (z : MlS) (y : Nat) (hy : y < 2 ^ 63) (hz : Γ.get z = some (natW y)) :
    sev Γ (predE z) = some (natW (y - 1)) := by
  by_cases y0 : y = 0
  · subst y0; simp [predE, sev, hz, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have hne : BitVec.ofNat 64 y ≠ 0#64 := ofNat_ne_zero y y0 (by omega)
    simp [predE, sev, hz, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub]; omega

theorem twoB_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) (n : Nat) (ih : RecB (σ := σ) C B n)
    {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (P : BitVec 64)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (a b : EIdx)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW a) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (twoB (C.mG (.n .bvarB))) s
      ((do let x ← bvarBoundGo n a; let y ← bvarBoundGo n b; pure (max x y)) >>= fun r => do bvarBSet h r; pure r)
      (PostN C) := by
  unfold twoB
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW a) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine specR_congr (m' := bvarBoundGo n a >>= fun x => bvarBoundGo n b >>= fun y => (do bvarBSet h (max x y); pure (max x y)))
    (by simp only [bind_assoc, pure_bind]) ?_
  refine callB_spec C B hc.bvr n ih lY lA1 a (by decide) (by simp +decide [hfu]) (by simp +decide) (fun x s1 hx => ?_)
  refine callB_spec C B hc.bvr n ih lZ lA2 b (by decide) (by simp +decide [hfu]) (by simp +decide) (fun y s2 hy => ?_)
  refine specR_assignI lW (vv lY) (natW x) (by decide) (by simp +decide) ?_
  refine maxW_spec lZ x y hx hy (by simp +decide) (by simp +decide) (fun Γ' hw hfr => ?_)
  exact setRetB_spec hok B hc h (max x y) (by omega) (by rw [hfr _ (by decide)]; simp +decide [hh])
    (by rw [hfr _ (by decide)]; simp +decide [hkb]) hw

theorem bindB_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) (n : Nat) (ih : RecB (σ := σ) C B n)
    {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (P : BitVec 64)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (a b : EIdx)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW a) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (bindB (C.mG (.n .bvarB))) s
      ((do let x ← bvarBoundGo n a; let y ← bvarBoundGo n b; pure (max x (y - 1))) >>= fun r => do bvarBSet h r; pure r)
      (PostN C) := by
  unfold bindB
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW a) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine specR_congr (m' := bvarBoundGo n a >>= fun x => bvarBoundGo n b >>= fun y =>
      (do bvarBSet h (max x (y - 1)); pure (max x (y - 1)))) (by simp only [bind_assoc, pure_bind]) ?_
  refine callB_spec C B hc.bvr n ih lY lA1 a (by decide) (by simp +decide [hfu]) (by simp +decide) (fun x s1 hx => ?_)
  refine callB_spec C B hc.bvr n ih lZ lA2 b (by decide) (by simp +decide [hfu]) (by simp +decide) (fun y s2 hy => ?_)
  refine specR_assignI lZ (predE lZ) (natW (y - 1)) (by decide) (sev_predE _ lZ y hy (by simp +decide)) ?_
  refine specR_assignI lW (vv lY) (natW x) (by decide) (by simp +decide) ?_
  refine maxW_spec lZ x (y - 1) hx (by omega) (by simp +decide) (by simp +decide) (fun Γ' hw hfr => ?_)
  exact setRetB_spec hok B hc h (max x (y - 1)) (by omega) (by rw [hfr _ (by decide)]; simp +decide [hh])
    (by rw [hfr _ (by decide)]; simp +decide [hkb]) hw

theorem letB_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) (n : Nat) (ih : RecB (σ := σ) C B n)
    {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (P : BitVec 64)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (ty v b : EIdx)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW ty) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW v) ∈ M)
    (hm2 : (P + BitVec.ofNat 64 16, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (letB (C.mG (.n .bvarB))) s
      ((do let x ← bvarBoundGo n ty; let y ← bvarBoundGo n v; let z ← bvarBoundGo n b; pure (max (max x y) (z - 1))) >>=
        fun r => do bvarBSet h r; pure r) (PostN C) := by
  unfold letB
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW ty) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW v) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine specR_loadI' lA3 _ (P + 16) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm2 ?_
  refine specR_congr (m' := bvarBoundGo n ty >>= fun x => bvarBoundGo n v >>= fun y => bvarBoundGo n b >>= fun z =>
      (do bvarBSet h (max (max x y) (z - 1)); pure (max (max x y) (z - 1)))) (by simp only [bind_assoc, pure_bind]) ?_
  refine callB_spec C B hc.bvr n ih lY lA1 ty (by decide) (by simp +decide [hfu]) (by simp +decide) (fun x s1 hx => ?_)
  refine callB_spec C B hc.bvr n ih lZ lA2 v (by decide) (by simp +decide [hfu]) (by simp +decide) (fun y s2 hy => ?_)
  refine callB_spec C B hc.bvr n ih lB lA3 b (by decide) (by simp +decide [hfu]) (by simp +decide) (fun z s3 hz => ?_)
  refine specR_assignI lB (predE lB) (natW (z - 1)) (by decide) (sev_predE _ lB z hz (by simp +decide)) ?_
  refine specR_assignI lW (vv lY) (natW x) (by decide) (by simp +decide) ?_
  refine maxW_spec lZ x y hx hy (by simp +decide) (by simp +decide) (fun Γ' hw hfr => ?_)
  refine maxW_spec lB (max x y) (z - 1) (by omega) (by omega) hw (by rw [hfr _ (by decide)]; simp +decide)
    (fun Γ'' hw' hfr' => ?_)
  exact setRetB_spec hok B hc h (max (max x y) (z - 1)) (by omega)
    (by rw [hfr' _ (by decide), hfr _ (by decide)]; simp +decide [hh])
    (by rw [hfr' _ (by decide), hfr _ (by decide)]; simp +decide [hkb]) hw'

theorem projB_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) (n : Nat) (ih : RecB (σ := σ) C B n)
    {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (P : BitVec 64)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (sub : EIdx)
    (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW sub) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projB (C.mG (.n .bvarB))) s
      (bvarBoundGo n sub >>= fun r => do bvarBSet h r; pure r) (PostN C) := by
  unfold projB
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW sub) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine callB_spec C B hc.bvr n ih lY lA2 sub (by decide) (by simp +decide [hfu]) (by simp +decide) (fun x s1 hx => ?_)
  refine specR_assignI lW (vv lY) (natW x) (by decide) (by simp +decide) ?_
  exact setRetB_spec hok B hc h x hx (by simp +decide [hh]) (by simp +decide [hkb]) (by simp +decide)

theorem bvarRestB_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (i : Nat) (hi : i < 2 ^ 64)
    (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB) (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (bvarRestB (C.mG (.n .bvarB))) s
      (pure (i + 1) >>= fun r => do bvarBSet h r; pure r) (PostN C) := by
  unfold bvarRestB
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine specR_assignI lW _ (BitVec.ofNat 64 (i + 1)) (by decide) (by simp +decide [sev, hb]; rw [word_add1_eq]) ?_
  refine specR_ifI (.shift .lsr (vv lW) (.const 63)) (BitVec.ofNat 64 (i + 1) >>> (63 : BitVec 64).toNat)
    (by simp [sev]) (fun _ => specR_hangI) (fun hw2 => ?_)
  have hs63 := (shr63_eq_zero (i + 1) (by omega)).mp hw2
  refine specR_congr (by rw [pure_bind]) ?_
  exact setRetB_spec hok B hc h (i + 1) hs63 (by simp +decide [hh]) (by simp +decide [hkb]) (by simp +decide [natW])

theorem leafB_spec (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesB C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB) :
    SpecR (Inv (σ := σ) C s Γ M DI) (leafB (C.mG (.n .bvarB))) s
      (pure 0 >>= fun r => do bvarBSet h r; pure r) (PostN C) := by
  unfold leafB
  refine specR_assignI lW (.const 0) (natW 0) (by decide) rfl ?_
  refine specR_congr (by rw [pure_bind]) ?_
  exact setRetB_spec hok B hc h 0 (by decide) (by simp +decide [hh]) (by simp +decide [hkb]) (by simp +decide)

end

section
variable {σ : Type}

theorem params_noneB (h : EIdx) (n : Nat) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem bvrGo_spec (C : Ctx) (hok : CtxOK C) (hc : CodesB C (bodyB C)) :
    ∀ n, n < 2 ^ 64 → RecB (σ := σ) C (bodyB C) n := by
  intro n
  induction n with
  | zero =>
    intro _ h s
    refine specR_prologue (postN_locals C) (params_noneB h 0 C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf h s
    have ih' := ih (by omega)
    refine specR_prologue (postN_locals C) (params_noneB h (n + 1) C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [bvarBoundGo_succ]) ?_
    refine probedB_spec hok (bodyB C) hc h _ _ (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) rfl ?_
    refine specR_congr (by rw [bind_assoc]) ?_
    refine specR_viewI h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (by decide)
      (fun v P htg hsh => ?_)
    cases v with
    | app a b =>
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := bvarBoundArmApp n a b >>= fun r => do bvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [bvarBoundArmApp]) ?_
      refine twoB_spec C hok (bodyB C) hc n ih' h P ?_ ?_ ?_ ?_ a b
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | lam ty bd =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := bvarBoundArmBind n ty bd >>= fun r => do bvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [bvarBoundArmBind]) ?_
      refine bindB_spec C hok (bodyB C) hc n ih' h P ?_ ?_ ?_ ?_ ty bd
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | forallE ty bd =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := bvarBoundArmBind n ty bd >>= fun r => do bvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [bvarBoundArmBind]) ?_
      refine bindB_spec C hok (bodyB C) hc n ih' h P ?_ ?_ ?_ ?_ ty bd
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | letE ty vl bd =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine specR_congr (m' := bvarBoundArmLet n ty vl bd >>= fun r => do bvarBSet h r; pure r) rfl ?_
      refine specR_congr (by rw [bvarBoundArmLet]) ?_
      refine letB_spec C hok (bodyB C) hc n ih' h P ?_ ?_ ?_ ?_ ty vl bd
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) (wordsAt_mem2 _ _ _ _ _ _) <;> simp +decide [ctxEnv]
    | proj nm i sub =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      refine projB_spec C hok (bodyB C) hc n ih' h P ?_ ?_ ?_ ?_ sub (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [ctxEnv]
    | fvar idx ty =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafB_spec C hok (bodyB C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    | bvar i =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) tagF
      unfold bvarArmB
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
        exact bvarRestB_spec C hok (bodyB C) hc h 0 (by decide) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
          (by simp)
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' lB _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by decide) (by simp +decide [sev])
            rfl (by have := wordsAt_mem0 P (BitVec.ofNat 64 i) [] (M := []); simpa [encEView, Enc.encBVar, hl] using this)
            ?_
          exact bvarRestB_spec C hok (bodyB C) hc h i ib (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
            (by simp)
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
    | sort u =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafB_spec C hok (bodyB C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    | const nm us =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafB_spec C hok (bodyB C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
    | lit l =>
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      refine specR_ifI _ _ rfl tagF (fun _ => ?_)
      exact leafB_spec C hok (bodyB C) hc h (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])

end

/-! ## `bvarBoundMemo` and `bvarB` -/

theorem bvarBClear_run (s : AState) : bvarBClear s = .ok ((), { s with memos := memoUpdN .bvarB s.memos ∅ }) := rfl

def fBvarB := ofString "bvarB"

def bvbLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, lB, lJ0, lW]

/-- `bvarB(fu, h)`: the packed loose-bvar field, or on saturation the memoized walk between clears. -/
def bvbBody (C : Ctx) : ProgHOL 64 :=
  prologue bvbLocals
   (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
   (.seq (.assign .local lB (bvarFieldE (vv lDo1)))
   (.ite (.cmp .equal (vv lB) (.const 32767))
     (clearCode (C.mg (.n .bvarB))
       (.seq (.call (some (some (.local, lW), none)) fBvr [vv pFu, vv pH])
         (clearCode (C.mg (.n .bvarB)) (.return (vv lW)))))
     (.return (vv lB)))))))

section
variable {σ : Type}

theorem bvarB_spec (C : Ctx) (hok : CtxOK C) (hc : CodesB C (bodyB C)) (s : AState) (fuel : Nat) (e : EIdx)
    (hf : fuel < 2 ^ 64) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pH, Enc.idxW e)]) (bvbBody C) s (bvarB fuel e)
      (PostN C) := by
  refine specR_prologue (postN_locals C) (fun x hx => ?_) ?_
  · simp only [bvbLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW e) (by decide) rfl ?_
  unfold bvarB
  refine specR_derivedEI e rfl rfl rfl (by decide) ?_
  have hb15 : (ConLeche.bvarOfData (s.store.derived e)).toNat < 2 ^ 15 := by
    simp only [ConLeche.bvarOfData, UInt64.toNat_mod]; simp; omega
  have hbt : (ConLeche.bvarOfData (s.store.derived e)).toBitVec =
      BitVec.ofNat 64 (ConLeche.bvarOfData (s.store.derived e)).toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  refine specR_assignI lB _ (ConLeche.bvarOfData (s.store.derived e)).toBitVec (by decide)
    (by simp [sev, bvarFieldE]; exact bvarOfData_word _) ?_
  generalize hbdef : (ConLeche.bvarOfData (s.store.derived e)).toNat = b at hb15 hbt
  rw [hbt]
  refine specR_iteI (.cmp .equal (vv lB) (.const 32767))
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 b) 32767 then 1 else 0)
    (by simp [sev]) ?_ (fun _ => ?_) (fun hne => ?_)
  · have : (BitVec.ofNat 64 b = (32767 : BitVec 64)) ↔ b = 32767 :=
      word_eq_iff b 32767 (by omega) (by decide)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ConLeche.satRange]; exact this
  · unfold bvarBoundMemo
    refine specR_memoClearNI hok .bvarB bvarBClear bvarBClear_run (by decide) ?_
    refine specR_call2IM lW fBvr pFu pH (by decide) _ _ (bodyB C) (BitVec.ofNat 64 fuel) (Enc.idxW e) (by decide)
      hc.bvr (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
      (PostN C) (fun _ _ _ _ hp => hp.2.2)
      (fun u hu _ h1 h2 w hw => by
        subst hw
        exact bvrGo_spec C hok hc fuel hf e _ _ ⟨hu, fun y z hy => by
          simp only [Env.get] at hy
          split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h1
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h2
            · simp at hy⟩)
      (fun r w s' st hp => ?_)
    obtain ⟨rfl, hr, _⟩ := hp
    refine specR_memoClearNI hok .bvarB bvarBClear bvarBClear_run (by decide) ?_
    exact specR_returnI (vv lW) (natW r) (by simp +decide [Env.kill])
      (fun t ht => ⟨rfl, hr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · exact specR_returnI (vv lB) (natW b) (by simp +decide [natW])
      (fun t ht => ⟨rfl, by omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExB
