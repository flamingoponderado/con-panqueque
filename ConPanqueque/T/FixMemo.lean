import ConPanqueque.T.DefeqMemo
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The instantiated-constant caches `constTyC`/`constValC`

Key `[idxW n, idxW us]` in the key buffer, value the handle.
-/

namespace ConPanqueque.T

inductive FixK | ty | val
  deriving DecidableEq

def FixK.toK : FixK → CacheK | .ty => .constTy | .val => .constVal

def FixK.sel : FixK → Caches → Std.HashMap (NIdx × LsIdx) EIdx
  | .ty, c => c.constTyC | .val, c => c.constValC

def FixK.upd : FixK → Caches → Std.HashMap (NIdx × LsIdx) EIdx → Caches
  | .ty, c, x => { c with constTyC := x } | .val, c, x => { c with constValC := x }

/-- The twin's detach-then-insert write of a fixed cache. -/
def FixK.setOp (k : FixK) (key : NIdx × LsIdx) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := k.sel s.caches
  let s := { s with caches := k.upd s.caches ∅ }
  set { s with caches := k.upd s.caches (mp.insert key r) }

def fixSetS (k : FixK) (s : AState) (key : NIdx × LsIdx) (r : EIdx) : AState :=
  { s with caches := k.upd s.caches ((k.sel s.caches).insert key r) }

theorem FixK.setOp_run (k : FixK) (key : NIdx × LsIdx) (r : EIdx) (s : AState) :
    k.setOp key r s = .ok ((), fixSetS k s key r) := by cases k <;> rfl

theorem encNL_inj : ∀ x y, encNL x = encNL y → x = y := by
  intro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [encNL, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [Enc.idxW_inj h1, Enc.idxW_inj h2]

section
variable {σ : Type}

theorem FixK.cacheAt_sel (k : FixK) (t : PState σ) (C : Ctx) (c : Caches) :
    CacheAt t C c k.toK = MemoAtG encNL Enc.idxW t (C.mG (.c k.toK)) (C.mg (.c k.toK)) (k.sel c) := by
  cases k <;> rfl

theorem FixK.cacheAt_upd_ne (k : FixK) (k' : CacheK) (h : k' ≠ k.toK) (t : PState σ) (C : Ctx) (c : Caches)
    (x : Std.HashMap (NIdx × LsIdx) EIdx) : CacheAt t C (k.upd c x) k' = CacheAt t C c k' := by
  cases k <;> cases k' <;> first | rfl | exact absurd rfl h

theorem FixK.sel_upd (k : FixK) (c : Caches) (x : Std.HashMap (NIdx × LsIdx) EIdx) : k.sel (k.upd c x) = x := by
  cases k <;> rfl

theorem words_kbNL {C : Ctx} {u : PState σ} {a : NIdx} {b : LsIdx}
    (hM : ∀ x v, (x, v) ∈ [(C.KB + BitVec.ofNat 64 (8 * 0), Enc.idxW a), (C.KB + BitVec.ofNat 64 (8 * 1), Enc.idxW b)] →
      u.memaddrs x ∧ u.memory x = .word v) : Words u C.KB (encNL (a, b)) := by
  intro j hj
  have : j < 2 := by simpa [encNL] using hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact hM _ (Enc.idxW a) (by simp)
  · exact hM _ (Enc.idxW b) (by simp)

/-- `KB[0] := en; KB[1] := eu; x := memoGet(cache k, 2); rest`. -/
def fixGetP (C : Ctx) (k : CacheK) (x : MlS) (en eu : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) en)
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) eu)
      (.seq (.call (some (some (.local, x), none)) fMemoGet [.const (C.mG (.c k)), .const 2]) rest))

def fixSetP (C : Ctx) (k : CacheK) (x : MlS) (en eu ev : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) en)
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) eu)
      (.seq (.call (some (some (.local, x), none)) fMemoSet [.const (C.mG (.c k)), .const 2, ev]) rest))

theorem specR_fixGetI {β : Type} {C : Ctx} (hok : CtxOK C) (k : FixK)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k' : Option EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (en eu : ExpHOL 64) (n : NIdx) (us : LsIdx) (hx : x ∈ D)
    (hen : sev Γ en = some (Enc.idxW n)) (heu : sev Γ eu = some (Enc.idxW us)) (hkb : Γ.get lKb = some C.KB)
    (hk : SpecR (Inv C s ((x, optW (k.sel s.caches)[(n, us)]?) :: Γ) [] D) rest s (k' (k.sel s.caches)[(n, us)]?) R) :
    SpecR (Inv C s Γ M D) (fixGetP C k.toK x en eu rest) s
      ((fun s => .ok ((k.sel s.caches)[(n, us)]?, s) : AM (Option EIdx)) >>= k') R := by
  refine specR_storeKB2I hok en eu (Enc.idxW n) (Enc.idxW us) hen heu hkb ?_
  exact specR_memoGetGI encNL_inj (C.mG (.c k.toK)) (C.mg (.c k.toK)) (k.sel s.caches) (n, us) _ rfl
    (fun u hu => by have := hu.cache k.toK; rw [k.cacheAt_sel] at this; exact this) hcodeG hcodeP x
    (.const (C.mG (.c k.toK))) (.const 2) hx rfl rfl (by simp [encNL]) (fun u hM => words_kbNL hM) hk

theorem specR_fixSetI {β : Type} {C : Ctx} (hok : CtxOK C) (k : FixK)
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k' : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (en eu ev : ExpHOL 64) (n : NIdx) (us : LsIdx) (r : EIdx) (hx : x ∈ D)
    (hen : sev Γ en = some (Enc.idxW n)) (heu : sev Γ eu = some (Enc.idxW us))
    (hev : sev Γ ev = some (Enc.idxW r)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv C (fixSetS k s (n, us) r) ((x, w) :: Γ) [] D) rest (fixSetS k s (n, us) r) (k' ()) R) :
    SpecR (Inv C s Γ M D) (fixSetP C k.toK x en eu ev rest) s (k.setOp (n, us) r >>= k') R := by
  refine specR_storeKB2I hok en eu (Enc.idxW n) (Enc.idxW us) hen heu hkb ?_
  refine specR_memoSetGI encNL_inj (C.mG (.c k.toK)) (C.mg (.c k.toK)) (k.sel s.caches) (n, us) r _
    (k.setOp_run (n, us) r s) (fun u hu => by have := hu.cache k.toK; rw [k.cacheAt_sel] at this; exact this)
    (fun i hi => hok.kbMemo _ i (by simp [encNL] at hi; omega)) (fun j hj => hok.mdescMemo _ _ j hj)
    (fun u u' hsr hmem hfr hd hg hc => ?_) hcodeS hcodeI x (.const (C.mG (.c k.toK))) (.const 2) ev hx rfl rfl hev
    (by simp [encNL]) (fun u hM => words_kbNL hM) hk
  refine sr_upd_fix hok k.toK hsr hfr hd hg hc rfl rfl rfl ?_ (fun k'' hk'' => k.cacheAt_upd_ne k'' hk'' _ _ _ _)
    (by cases k <;> exact ⟨rfl, rfl⟩)
    (cachesOK_congr hsr.cok rfl (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> cases k <;> rfl))
  show CacheAt u' C (k.upd s.caches _) k.toK
  rw [k.cacheAt_sel, k.sel_upd]; exact hmem

end

end ConPanqueque.T
