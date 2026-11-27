import ConPanqueque.Front.QuotRec
import ConPanqueque.T.Ind.IndTele
import ConPanqueque.Scan.IndFields

/-! # The inductive line: generic pieces

* robust facts: a fact about cells at or above `X` survives any image keeping those cells
  (`KeepsAbove`); the inductive block's records are written as robust facts, so the stores into the
  block's own pointer cells (below `X`) keep them;
* `allocWr`: allocate a block and store a list of words into it;
* `cvP`: one constant's common part (name and type through the tables, the type's telescope
  length, the level-parameter block), with its bounds. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec scanNatList)

set_option autoImplicit false

variable {σ : Type}

/-! ## Robust facts -/

theorem keepsAbove_refl (X : Nat) (H : List (BitVec 64)) : KeepsAbove X H H := fun _ _ _ h => h

theorem keepsAbove_of_agree {X : Nat} {H H' : List (BitVec 64)} (h : ∀ c, c < H.length → H'[c]? = H[c]?) :
    KeepsAbove X H H' := fun c _ v hv => by
  have hl : c < H.length := by
    by_cases hl : c < H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hv; cases hv
  rw [h c hl]; exact hv

theorem keepsAbove_set_lt {X : Nat} {H : List (BitVec 64)} {c : Nat} (hc : c < X) (w : BitVec 64) :
    KeepsAbove X H (H.set c w) := fun c' hc' v hv => by
  rw [List.getElem?_set, ite_eq_right (by omega)]; exact hv

theorem keepsAbove_mono {X Y : Nat} {H H' : List (BitVec 64)} (h : KeepsAbove X H H') (hXY : X ≤ Y) :
    KeepsAbove Y H H' := fun c hc v hv => h c (by omega) v hv

/-- A cell fact at or above `X`, robust. -/
theorem keep_get {X : Nat} {H H' : List (BitVec 64)} (h : KeepsAbove X H H') {c : Nat} {v : BitVec 64}
    (hc : X ≤ c) (hv : H[c]? = some v) : H'[c]? = some v := h c hc v hv

theorem blkAt_keep {X : Nat} {H H' : List (BitVec 64)} (h : KeepsAbove X H H') {o : Nat} {xs : List (BitVec 64)}
    (hb : BlkAt H o xs) (ho : X ≤ o) : BlkAt H' o xs :=
  ⟨h o ho _ hb.1, fun i hi => h _ (by omega) _ (hb.2 i hi)⟩

/-- A robust stored constant. -/
def RCIE (X : Nat) (C : Ctx) (H : List (BitVec 64)) (o : Nat) (ci : IConstantInfo) : Prop :=
  ∀ H', KeepsAbove X H H' → CIE C.HB H' o ci

theorem rcie_keep {X : Nat} {C : Ctx} {H H' : List (BitVec 64)} {o : Nat} {ci : IConstantInfo}
    (h : RCIE X C H o ci) (hk : KeepsAbove X H H') : RCIE X C H' o ci :=
  fun H'' hk' => h H'' (keepsAbove_trans hk hk')

theorem rcie_mono {X Y : Nat} {C : Ctx} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo}
    (h : RCIE Y C H o ci) (hXY : X ≤ Y) : RCIE X C H o ci :=
  fun H' hk => h H' (keepsAbove_mono hk hXY)

/-! ## Words -/

def B55 : Nat := 2 ^ 55

theorem natW_small {x : Nat} (h : (Scan.natW x).toNat < B55) : x < B55 ∧ Scan.natW x = BitVec.ofNat 64 x := by
  unfold Scan.natW at *
  have h1 : min x natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1] at h
  unfold B55 natCap at *
  have : min x (2 ^ 62) = x := by
    by_cases hx : x ≤ 2 ^ 62
    · exact Nat.min_eq_left hx
    · have := Nat.min_eq_right (show 2 ^ 62 ≤ x by omega); omega
  rw [this] at h ⊢; exact ⟨h, rfl⟩

theorem natW_eq_small {x n : Nat} (hn : n < B55) (h : Scan.natW x = BitVec.ofNat 64 n) : x = n := by
  unfold Scan.natW at h
  have h1 : min x natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by unfold B55 at hn; omega)] at this
  unfold natCap B55 at *
  by_cases hx : x ≤ 2 ^ 62
  · rw [Nat.min_eq_left hx] at this; exact this
  · rw [Nat.min_eq_right (by omega)] at this; omega

theorem sev_lt_c (Γ : Env) (x : MlS) (w c : BitVec 64) (hx : Γ.get x = some w) :
    sev Γ (.cmp .lower (vv x) (.const c)) = some (bw (w.toNat < c.toNat)) := by
  simp only [sev, vv, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw]
  by_cases h : w.toNat < c.toNat <;> simp [h, BitVec.lt_def, BitVec.le_def] <;> omega

theorem sev_ne_v (Γ : Env) (x y : MlS) (w v : BitVec 64) (hx : Γ.get x = some w) (hy : Γ.get y = some v) :
    sev Γ (.cmp .notEqual (vv x) (vv y)) = some (bw (w ≠ v)) := by
  simp only [sev, vv, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw]
  by_cases h : w = v <;> simp [h]

theorem sev_ne_c (Γ : Env) (x : MlS) (w c : BitVec 64) (hx : Γ.get x = some w) :
    sev Γ (.cmp .notEqual (vv x) (.const c)) = some (bw (w ≠ c)) := by
  simp only [sev, vv, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw]
  by_cases h : w = c <;> simp [h]

/-- `if x < c then rest else hang`. -/
theorem specR_ltGuardI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (w c : BitVec 64) (hx : Γ.get x = some w)
    (hk : w.toNat < c.toNat → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .lower (vv x) (.const c)) rest hang) s m R :=
  specR_ifI _ _ (sev_lt_c Γ x w c hx) (fun h => hk (by by_cases e : w.toNat < c.toNat; exact e; simp [bw, e] at h))
    (fun _ => specR_hangI)

/-- `if x ≠ y then hang else rest`. -/
theorem specR_eqGuardI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : MlS) (w v : BitVec 64) (hx : Γ.get x = some w)
    (hy : Γ.get y = some v) (hk : w = v → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .notEqual (vv x) (vv y)) hang rest) s m R :=
  specR_ifI _ _ (sev_ne_v Γ x y w v hx hy) (fun _ => specR_hangI)
    (fun h => hk (by by_cases e : w = v; exact e; simp [bw, e] at h))

/-- `if x ≠ c then hang else rest`. -/
theorem specR_eqcGuardI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (w c : BitVec 64) (hx : Γ.get x = some w)
    (hk : w = c → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .notEqual (vv x) (.const c)) hang rest) s m R :=
  specR_ifI _ _ (sev_ne_c Γ x w c hx) (fun _ => specR_hangI)
    (fun h => hk (by by_cases e : w = c; exact e; simp [bw, e] at h))

/-! ## Four-argument calls specified by `RetP` -/

theorem call4_retP (s : PanSemStateFiniteExact 64 σ) (x f x1 x2 x3 x4 : MlS) (body : ProgHOL 64)
    (a1 a2 a3 a4 : ExpHOL 64) (v1 v2 v3 v4 w0 : BitVec 64) (P : BitVec 64 → Prop) (hnd : [x1, x2, x3, x4].Nodup)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one), (x4, .one)], body, .one))
    (ha1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a1 =
      some (.val (.word v1)))
    (ha2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 =
      some (.val (.word v2)))
    (ha3 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 =
      some (.val (.word v3)))
    (ha4 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a4 =
      some (.val (.word v4)))
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → callee.lookup x4 = some (.val (.word v4)) →
      RetP (callEntryStateHOLFinite s callee) body P) :
    Stop (evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3, a4])).1 ∨
      ∃ w u, P w ∧ evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3, a4]) = (none, u) ∧
        SetsLocal s x w u := by
  obtain ⟨callee, hlk, hx1, hx2, hx3, hx4⟩ := Scan.lookupCode4 s f x1 x2 x3 x4 body v1 v2 v3 v4 hnd hcode
  rcases hbody callee hx1 hx2 hx3 hx4 with hs | ⟨w, r1, hp, r2⟩
  · have := call_ret s x f [a1, a2, a3, a4] _ body callee 0 w0
      (by simp [evalListHOLFinite, evalListHOLExact, ha1, ha2, ha3, ha4]) hlk (Or.inl hs) hx
    rcases this with h | ⟨u, hu, -⟩
    · exact Or.inl h
    · exfalso
      rw [evaluateHOLFiniteState_call] at hu
      simp only [evalListHOLFinite] at hu
      have hcl : s.clock ≠ 0 := by
        intro h0; simp [evalListHOLExact, ha1, ha2, ha3, ha4, hlk, h0] at hu
      generalize he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = r at hs
      obtain ⟨r1', r2'⟩ := r
      simp only at hs
      rcases hs with e | ⟨ev, e⟩ <;> subst e <;> simp [evalListHOLExact, ha1, ha2, ha3, ha4, hlk, hcl, he] at hu
  · rcases call_ret s x f [a1, a2, a3, a4] _ body callee w w0
      (by simp [evalListHOLFinite, evalListHOLExact, ha1, ha2, ha3, ha4]) hlk (Or.inr ⟨r1, r2⟩) hx with h | ⟨u, hu, hs⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, u, hp, hu, hs⟩

/-- `x := f(a₁, …, a₄); rest` at a pure callee specified by `RetP`. -/
theorem specR_retP4 {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x f x1 x2 x3 x4 : MlS) (body : ProgHOL 64) (a1 a2 a3 a4 : ExpHOL 64) (v1 v2 v3 v4 : BitVec 64)
    (P : BitVec 64 → Prop) (hnd : [x1, x2, x3, x4].Nodup) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one), (x4, .one)], body, .one))
    (he1 : sev Γ a1 = some v1) (he2 : sev Γ a2 = some v2) (he3 : sev Γ a3 = some v3) (he4 : sev Γ a4 = some v4)
    (hbody : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)), Inv C s Γ M D t →
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → callee.lookup x4 = some (.val (.word v4)) →
      RetP (callEntryStateHOLFinite t callee) body P)
    (hk : ∀ w, P w → SpecR (Inv C s ((x, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (callTo x f [a1, a2, a3, a4]) rest) s m R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  rcases call4_retP t x f x1 x2 x3 x4 body a1 a2 a3 a4 v1 v2 v3 v4 w0 P hnd (by rw [ht.sr.code]; exact hcode)
      (inv_ev ht he1) (inv_ev ht he2) (inv_ev ht he3) (inv_ev ht he4) hw0
      (fun callee h1 h2 h3 h4 => hbody t callee ht h1 h2 h3 h4) with
    hs | ⟨w, u, hp, hu, m1, d1, g1, c1, b1, lx, lo⟩
  · exact Or.inl (seq_stop t _ _ hs)
  have hinv : Inv C s ((x, w) :: Γ) M D u := by
    refine ⟨sr_of_eq ht.sr m1 d1 g1 c1, fun y v hy => ?_, fun a v ha => by rw [m1, d1]; exact ht.mem a v ha,
      fun y hy => ?_⟩
    · simp only [Env.get] at hy
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact lx
      · rename_i e; rw [lo y e]; exact ht.env y v hy
    · by_cases e : y = x
      · subst e; exact ⟨w, lx⟩
      · rw [lo y e]; exact ht.decl y hy
  simp only [callTo]
  rw [seq_normal _ hu]
  exact hk w hp u hinv

/-! ## Scanner calls from the `Inv` world -/

/-- The buffer's bytes in any state the invariant holds of. -/
theorem inv_bytes {C : Ctx} (hok : CtxOK C) {bufJ : Nat} {b : ByteArray} (hbuf : BufOK C bufJ b)
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ} (ht : Inv C s Γ M D t) :
    BytesAt t (cellA C bufJ) b.data.toList :=
  bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)

/-- `x := f(kBA, kBN, y)` at a buffer reader. -/
theorem specR_scan3 {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b)
    (x f y : MlS) (body : ProgHOL 64) (i : Nat) (P : BitVec 64 → Prop) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(sB, .one), (sN, .one), (sI, .one)], body, .one))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hy : Γ.get y = some (BitVec.ofNat 64 i))
    (hsound : ∀ (u : PState σ), BytesAt u (cellA C bufJ) b.data.toList → u.code = C.code →
      u.locals.lookup sB = some (.val (.word (cellA C bufJ))) →
      u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i))) → RetP u body P)
    (hk : ∀ w, P w → SpecR (Inv C s ((x, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (callTo x f [vv kBA, vv kBN, vv y]) rest) s m R :=
  specR_retP3 x f sB sN sI body (vv kBA) (vv kBN) (vv y) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 i) P (by decide) (by decide) (by decide) hx hcode
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hy)
    (fun t callee ht h1 h2 h3 => hsound _ (bytesAt_congr (t := t) (inv_bytes hok hbuf ht) rfl rfl rfl)
      (by show t.code = C.code; exact ht.sr.code) h1 h2 h3) hk

/-- `x := f(kBA, kBN, y, e)` at a buffer reader. -/
theorem specR_scan4 {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b)
    (x f y : MlS) (e : ExpHOL 64) (body : ProgHOL 64) (i J : Nat) (P : BitVec 64 → Prop) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], body, .one))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hy : Γ.get y = some (BitVec.ofNat 64 i)) (he : sev Γ e = some (BitVec.ofNat 64 J))
    (hsound : ∀ (u : PState σ), BytesAt u (cellA C bufJ) b.data.toList → u.code = C.code →
      u.locals.lookup sB = some (.val (.word (cellA C bufJ))) →
      u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i))) →
      u.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J))) → RetP u body P)
    (hk : ∀ w, P w → SpecR (Inv C s ((x, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (callTo x f [vv kBA, vv kBN, vv y, e]) rest) s m R :=
  specR_retP4 x f sB sN sI sL body (vv kBA) (vv kBN) (vv y) e (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 i) (BitVec.ofNat 64 J) P (by decide) hx hcode
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hy) he
    (fun t callee ht h1 h2 h3 h4 => hsound _ (bytesAt_congr (t := t) (inv_bytes hok hbuf ht) rfl rfl rfl)
      (by show t.code = C.code; exact ht.sr.code) h1 h2 h3 h4) hk

theorem specR_heapLoadV {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (j : Nat) (w : BitVec 64)
    (hw : C.H[j]? = some w) (hx : x ∈ D) (he : sev Γ e = some (cellA C j))
    (h : SpecR (Inv C s ((x, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one e)) rest) s m R := by
  obtain ⟨hj, hjw⟩ := List.getElem?_eq_some_iff.mp hw
  exact specR_heapLoadI x e j hj hx he (hjw ▸ h)

/-! ## Allocate and write -/

/-- Allocate a block for `es` and store them in order; its address in `x`. -/
def allocWr (C : Ctx) (x : MlS) (es : List (ExpHOL 64)) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const (BitVec.ofNat 64 (8 * es.length))) (storesP x 0 es rest)

theorem specR_allocWrI {α : Type} (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (hx : x ∈ D) (es : List (ExpHOL 64)) (ws : List (BitVec 64)) (hl : es.length = ws.length)
    (h8 : 8 * ws.length < 2 ^ 60)
    (hes : ∀ v i (hi : i < es.length), sev ((x, v) :: Γ) es[i] = some (ws.getD i 0))
    (hk : ∀ (H' : List (BitVec 64)) (r : Nat), C.H <+: H' → C.H.length ≤ r → r + ws.length ≤ H'.length →
      (∀ i (hi : i < ws.length), H'[r + i]? = some ws[i]) →
      SpecR (Inv (ctxH C H') s ((x, cellA C r) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (allocWr C x es rest) s m R := by
  have hlay := hok.heapLay
  unfold allocWr
  refine specR_allocI (C := C) x _ ws.length (by omega) hx (fun v => by rw [hl]; rfl)
    (fun H2 wsR hp2 hwl2 hcap2 => ?_)
  refine specR_dropMem ?_
  let r := H2.length
  have hkx : Env.get ((x, cellA C r) :: Γ) x = some (cellA C r) := by simp [Env.get_cons]
  refine storesP_spec C hok s _ D x r hkx ws rest es 0 (H2 ++ wsR) (by omega) (by simp [hwl2, r])
    (by have : H2.length + ws.length ≤ C.HN := hcap2; omega)
    (fun i hi => by simpa using hes (cellA C r) i hi) ?_
  have hp0 : C.H <+: H2 ++ wsR := hp2.trans (List.prefix_append _ _)
  refine hk _ r (prefix_kcH hp0 r (by have := hp2.length_le; omega) ws _) (hp2.length_le)
    (by simp [kcH_length, hwl2, r]) (fun i hi => ?_)
  rw [show (0 : Nat) + es.length = ws.length by omega, kcH_get, ite_eq_left ⟨by omega, by omega, by simp [hwl2]; omega⟩,
    show r + i - r = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem bufOK_prefix {C : Ctx} {bufJ : Nat} {b : ByteArray} (h : BufOK C bufJ b) {H' : List (BitVec 64)}
    (hp : C.H <+: H') : BufOK (ctxH C H') bufJ b :=
  ⟨packed_prefix h.pk hp, h.al, Nat.lt_of_lt_of_le h.len hp.length_le, h.plat, h.small⟩

/-! ## One constant's common part -/

def ilT := ofString "il_tl"
def ilL := ofString "il_l"

def cvMods : List MlS := [fy, fz, ilT, ilL] ++ lbMods

/-- Name and type through the tables, the type's telescope length (below `2⁵⁵`), the level-parameter
block (fewer than `2⁵⁵` names); then `rest`. -/
def cvP (C : Ctx) (rest : ProgHOL 64) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblGetP fz (vv fTE) (vv fCap) (vv fW3)
      (.seq (.call (some (some (.local, ilT), none)) T.Ind.fIndTele [.const (BitVec.ofNat 64 B55), vv fz])
        (lstBlkP C fTN
          (.seq (.assign .local ilL (.load .one (vv kKA0)))
            (.ite (.cmp .lower (vv ilL) (.const (BitVec.ofNat 64 B55))) rest hang)))))

theorem cvP_spec {α : Type} (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcI : C.code.lookup T.Ind.fIndTele = some ([(T.Ex.pFu, .one), (T.Ex.pH, .one)], T.Ind.iptBody T.Ind.fIndTele, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ cvMods, x ∈ D)
    (st : StateD) (jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b)
    (cv : CVRec) (wpos : BitVec 64) (hslot : ListAt b wpos cv.levelParams)
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hU : Γ.get fU = some (Scan.natW cv.name)) (hW : Γ.get fW3 = some (Scan.natW cv.type))
    (hV : Γ.get fV2 = some wpos)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64)
    (hk : ∀ (H' : List (BitVec 64)) (o : Nat) (Γ' : Env) (nmh : NIdx) (tyh : EIdx) (n : Nat),
      C.H <+: H' → C.H.length ≤ o → BlkAt H' o (tWords st.names cv.levelParams) →
      st.names.get? cv.name = some nmh → st.exprs.get? cv.type = some tyh →
      (∀ j (hj : j < cv.levelParams.length), (st.names.get? cv.levelParams[j]).isSome) →
      cv.levelParams.length < B55 → n < B55 →
      indPiTeleLen (s.store.nodeCount + 1) tyh s = .ok (n, s) →
      (∀ e, denoteE s.store tyh = some e → n = ConLeche.Frontend.indPiTeleLen e) →
      Γ'.get fy = some (Enc.idxW nmh) → Γ'.get fz = some (Enc.idxW tyh) → Γ'.get ilT = some (BitVec.ofNat 64 n) →
      Γ'.get kKA0 = some (cellA C o) → (∀ y, y ∉ cvMods → Γ'.get y = Γ.get y) →
      SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (cvP C rest) s m R := by
  have hNC : min cv.name natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hTC : min cv.type natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hus : cv.levelParams.length < 2 ^ 60 := by
    have := hbuf.small
    rcases hslot with ⟨p, e', -, hsc⟩ | ⟨h0, -⟩
    · have := scanNatList_len hsc; omega
    · rw [h0]; simp
  unfold cvP
  refine specR_tblGetI fy (hD fy (by simp [cvMods])) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv fU)
    (by simpa [sev, vv] using hTN) (by simpa [sev, vv] using hC) _ hNC (by simpa [sev, vv, Scan.natW] using hU)
    (fun nmh hnm => ?_)
  have hnm' := get_capped hreln hcapN _ nmh hnm
  let Γ1 : Env := (fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ
  have g1 : ∀ y, y ≠ fy → Env.get Γ1 y = Env.get Γ y := fun y h => by simp only [Γ1, Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fz (hD fz (by simp [cvMods])) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv fW3)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTE) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC)
    _ hTC (by simp only [sev, vv]; rw [g1 _ (by decide)]; simpa [Scan.natW] using hW) (fun tyh hty => ?_)
  have hty' := get_capped hrele hcapN _ tyh hty
  let Γ2 : Env := (fz, Enc.idxW tyh) :: (fz, Enc.idxW tyh + 1) :: Γ1
  have g2 : ∀ y, y ≠ fz → y ≠ fy → Env.get Γ2 y = Env.get Γ y := fun y h1 h2 => by
    simp only [Γ2, Env.get_cons, ite_eq_right h1]; exact g1 y h2
  refine T.Ind.specR_iptI C hcI ilT fz tyh B55 (by unfold B55; decide) (hD ilT (by simp [cvMods]))
    (by simp [Γ2, Env.get_cons]) (fun n H1 hp1 hn hrun hden => ?_)
  let Γ3 : Env := (ilT, BitVec.ofNat 64 n) :: Γ2
  have g3 : ∀ y, y ≠ ilT → y ≠ fz → y ≠ fy → Env.get Γ3 y = Env.get Γ y := fun y h0 h1 h2 => by
    simp only [Γ3, Env.get_cons, ite_eq_right h0]; exact g2 y h1 h2
  have hok1 := ctxOK_H hok H1
  change SpecR _ (lstBlkP (ctxH C H1) fTN _) _ _ _
  refine lstBlk_spec (ctxH C H1) hok1 hnc hcN s Γ3 [] D (fun x hx => hD x (by simp [cvMods, hx])) fTN (by decide)
    st.names jN cap (tblRel_prefix hreln hp1) hcap hcapN bufJ b (bufOK_prefix hbuf hp1) cv.levelParams hus wpos
    hslot (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hC)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hV) _
    (fun H' o Γ' hp' ho hblk hall hka0 hkeep => ?_)
  have hp2 : C.H <+: H' := hp1.trans hp'
  have hoH : o < H'.length := by
    have := hblk.1
    by_cases hl : o < H'.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at this; cases this
  have hlen : (tWords st.names cv.levelParams).length = cv.levelParams.length := by simp [tWords]
  have hblk1 := hblk.1
  rw [hlen] at hblk1
  refine specR_heapLoadV (C := ctxH (ctxH C H1) H') ilL (vv kKA0) o _ hblk1
    (hD ilL (by simp [cvMods])) (by simp only [sev, vv]; rw [hka0]; rfl) ?_
  refine specR_ltGuardI ilL (BitVec.ofNat 64 cv.levelParams.length) _ (by simp [Env.get_cons]) (fun hl => ?_)
  have hl' : cv.levelParams.length < B55 := by
    have : (BitVec.ofNat 64 cv.levelParams.length).toNat = cv.levelParams.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [this] at hl; unfold B55 at *; simpa using hl
  have gk : ∀ y, y ∉ lbMods → y ≠ ilT → y ≠ fz → y ≠ fy → Γ'.get y = Γ.get y := fun y h h0 h1 h2 => by
    rw [hkeep y h]; exact g3 y h0 h1 h2
  refine hk H' o _ nmh tyh n hp2 (Nat.le_trans hp1.length_le ho) hblk hnm' hty' hall hl' hn hrun hden
    ?_ ?_ ?_ ?_ ?_
  · rw [Env.get_cons, ite_eq_right (by decide), hkeep fy (by decide)]
    simp [Γ3, Γ2, Γ1, Env.get_cons, show fy ≠ ilT by decide, show fy ≠ fz by decide]
  · rw [Env.get_cons, ite_eq_right (by decide), hkeep fz (by decide)]
    simp [Γ3, Γ2, Env.get_cons, show fz ≠ ilT by decide]
  · rw [Env.get_cons, ite_eq_right (by decide), hkeep ilT (by decide)]
    simp [Γ3, Env.get_cons]
  · rw [Env.get_cons, ite_eq_right (by decide)]; exact hka0
  · intro y hy
    simp only [cvMods, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [Env.get_cons, ite_eq_right hy.1.2.2.2]
    exact gk y hy.2 hy.1.2.2.1 hy.1.2.1 hy.1.1

end ConPanqueque.Front
