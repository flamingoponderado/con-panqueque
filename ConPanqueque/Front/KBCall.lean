import ConPanqueque.Front.RetCall
import ConPanqueque.T.Intern

/-! # Scanner calls that leave three words in the key buffer

A `RetP` callee returns one word.  A scanner that finds several results (the line's payload tag, its value,
its index and the next position) had to be called once per result, scanning the same bytes each time.

`RetK`: the callee returns one word and leaves three more in the key buffer `KB`, the scratch cells `SR`
does not describe (`sr_storeKB`); memory is otherwise unchanged.  `specR_callK3`: a call to such a callee
followed by the three loads binds all four words from one scan. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

/-- `t` with the key buffer's three words set. -/
def kbSt (KB : BitVec 64) (t : PanSemStateFiniteExact 64 σ) (w0 w1 w2 : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  { t with memory := fun c =>
      if c = KB + BitVec.ofNat 64 (8 * 2) then .word w2 else
      if c = KB + BitVec.ofNat 64 (8 * 1) then .word w1 else
      if c = KB + BitVec.ofNat 64 (8 * 0) then .word w0 else t.memory c }

/-- The callee stops, or returns `w` with the key buffer holding `w0 w1 w2` (`P w w0 w1 w2`) and nothing else
of memory, its domain, the globals, the code or the endianness changed. -/
def RetK (KB : BitVec 64) (t : PanSemStateFiniteExact 64 σ) (c : ProgHOL 64)
    (P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop) : Prop :=
  Stop (evaluateHOLFiniteState t c).1 ∨
    ∃ w w0 w1 w2, (evaluateHOLFiniteState t c).1 = some (.returned (.val (.word w))) ∧ P w w0 w1 w2 ∧
      (evaluateHOLFiniteState t c).2.memory = (kbSt KB t w0 w1 w2).memory ∧
      (evaluateHOLFiniteState t c).2.memaddrs = t.memaddrs ∧
      (evaluateHOLFiniteState t c).2.globals = t.globals ∧
      (evaluateHOLFiniteState t c).2.code = t.code ∧
      (evaluateHOLFiniteState t c).2.be = t.be

theorem retK_dec {KB : BitVec 64} {u : PanSemStateFiniteExact 64 σ} {x : MlS} {e : ExpHOL 64} {body : ProgHOL 64}
    {w : BitVec 64} {P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop}
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e =
      some (.val (.word w)))
    (h : RetK KB (setVarHOLFinite x (.val (.word w)) u) body P) : RetK KB u (.dec x .one e body) P := by
  unfold RetK at h ⊢
  rw [dec_word_eq u x e w body he]
  exact h

theorem retK_decsOf {KB : BitVec 64} (P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop) :
    ∀ (ds : List (MlS × BitVec 64)) (body : ProgHOL 64) (u : PanSemStateFiniteExact 64 σ),
      RetK KB (ds.foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) u) body P →
      RetK KB u (decsOf ds body) P := by
  intro ds
  induction ds with
  | nil => intro body u h; exact h
  | cons d r ih =>
    intro body u h
    obtain ⟨x, w⟩ := d
    exact retK_dec (by simp [evalHOLExact]) (ih body _ h)

theorem retK_seq {KB : BitVec 64} {u u1 : PanSemStateFiniteExact 64 σ} {p q : ProgHOL 64}
    {P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop}
    (h : evaluateHOLFiniteState u p = (none, u1)) (hq : RetK KB u1 q P)
    (m : u1.memory = u.memory) (d : u1.memaddrs = u.memaddrs) (g : u1.globals = u.globals)
    (c : u1.code = u.code) (b : u1.be = u.be) : RetK KB u (.seq p q) P := by
  unfold RetK at hq ⊢
  rw [seq_normal _ h]
  rcases hq with hs | ⟨w, w0, w1, w2, r1, hp, r2, r3, r4, r5, r6⟩
  · exact Or.inl hs
  · refine Or.inr ⟨w, w0, w1, w2, r1, hp, ?_, r3.trans d, r4.trans g, r5.trans c, r6.trans b⟩
    rw [r2]; simp only [kbSt, m]

/-- A call at a `RetK` callee: the caller continues with the result bound, the key buffer set, and nothing
else changed. -/
theorem call3_retK (KB : BitVec 64) (s : PanSemStateFiniteExact 64 σ) (x f x1 x2 x3 : MlS) (body : ProgHOL 64)
    (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 w0 : BitVec 64) (P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (ha1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a1 =
      some (.val (.word v1)))
    (ha2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 =
      some (.val (.word v2)))
    (ha3 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 =
      some (.val (.word v3)))
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetK KB (callEntryStateHOLFinite s callee) body P) :
    Stop (evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3])).1 ∨
      ∃ w k0 k1 k2 u, P w k0 k1 k2 ∧
        evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3]) = (none, u) ∧
        u.memory = (kbSt KB s k0 k1 k2).memory ∧ u.memaddrs = s.memaddrs ∧ u.globals = s.globals ∧
        u.code = s.code ∧ u.be = s.be ∧ u.locals.lookup x = some (.val (.word w)) ∧
        ∀ y, y ≠ x → u.locals.lookup y = s.locals.lookup y := by
  obtain ⟨callee, hlk, hx1, hx2, hx3⟩ := Scan.lookupCode3 s f x1 x2 x3 body v1 v2 v3 h12 h13 h23 hcode
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2, a3] =
      some [.val (.word v1), .val (.word v2), .val (.word v3)] := by
    simp [evalListHOLFinite, evalListHOLExact, ha1, ha2, ha3]
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite] at hargs
  by_cases hck : s.clock = 0
  · left; simp [hargs, hlk, hck, Stop]
  rcases hbody callee hx1 hx2 hx3 with hst | ⟨w, k0, k1, k2, hr, hp, hm, hd, hg, hc, hb⟩
  · left
    generalize he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = r at hst
    obtain ⟨r1, r2⟩ := r
    simp only at hst
    rcases hst with e | ⟨ev, e⟩ <;> subst e <;> simp [hargs, hlk, hck, he, Stop]
  · right
    generalize he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = r at hr hm hd hg hc hb
    obtain ⟨r1, r2⟩ := r
    simp only at hr hm hd hg hc hb
    subst hr
    have hv : isValidValueHOLExact s.toExact .local x (.val (.word w)) = true := by
      simp [isValidValueHOLExact, lookupKvarHOLExact, hx, shapeOfHOLExact, shapeEqHOL]
    refine ⟨w, k0, k1, k2, setKvarHOLFinite .local x (.val (.word w)) { r2 with locals := s.locals }, hp, ?_,
      ?_, hd, hg, hc, hb, lookup_setVar_same _ _ _, fun y hy => ?_⟩
    · simp [hargs, hlk, hck, he, shapeOfHOLExact, shapeEqHOL, hv]
    · show r2.memory = _; rw [hm]; rfl
    · show (setVarHOLFinite x _ _).locals.lookup y = _
      rw [lookup_setVar_other _ _ hy]

theorem kb_ne {KB : BitVec 64} {i j : Nat} (hi : i < 3) (hj : j < 3) (h : i ≠ j) :
    KB + BitVec.ofNat 64 (8 * i) ≠ KB + BitVec.ofNat 64 (8 * j) := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-- The key buffer's words of `kbSt`. -/
theorem kbSt_get (KB : BitVec 64) (t : PanSemStateFiniteExact 64 σ) (w0 w1 w2 : BitVec 64) :
    (kbSt KB t w0 w1 w2).memory (KB + BitVec.ofNat 64 (8 * 0)) = .word w0 ∧
    (kbSt KB t w0 w1 w2).memory (KB + BitVec.ofNat 64 (8 * 1)) = .word w1 ∧
    (kbSt KB t w0 w1 w2).memory (KB + BitVec.ofNat 64 (8 * 2)) = .word w2 := by
  have n01 : KB + BitVec.ofNat 64 (8 * 0) ≠ KB + BitVec.ofNat 64 (8 * 1) := kb_ne (by decide) (by decide) (by decide)
  have n02 : KB + BitVec.ofNat 64 (8 * 0) ≠ KB + BitVec.ofNat 64 (8 * 2) := kb_ne (by decide) (by decide) (by decide)
  have n12 : KB + BitVec.ofNat 64 (8 * 1) ≠ KB + BitVec.ofNat 64 (8 * 2) := kb_ne (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [kbSt, ite_eq_right n01, ite_eq_right n02, ite_eq_right n12, ↓reduceIte]

/-- Setting the key buffer keeps the representation. -/
theorem sr_kbSt {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (h : SR C s t) (w0 w1 w2 : BitVec 64) :
    SR C s (kbSt C.KB t w0 w1 w2) := by
  have h0 := sr_storeKB hok h 0 (by decide) w0
  have h1 := sr_storeKB hok h0 1 (by decide) w1
  have h2 := sr_storeKB hok h1 2 (by decide) w2
  exact h2

/-- `x := f(a₁, a₂, a₃); y₀ := KB[0]; y₁ := KB[1]; y₂ := KB[2]; rest` at a `RetK` callee: all four words
from one call. -/
def kbLoad (k : Nat) : ExpHOL 64 := .load .one (.op .add [.var .global gKb, .const (BitVec.ofNat 64 (8 * k))])

theorem specR_callK3 {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x y0 y1 y2 f x1 x2 x3 : MlS) (body : ProgHOL 64) (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 : BitVec 64)
    (P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hx : x ∈ D) (hy0 : y0 ∈ D) (hy1 : y1 ∈ D) (hy2 : y2 ∈ D)
    (hcode : C.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (he1 : sev Γ a1 = some v1) (he2 : sev Γ a2 = some v2) (he3 : sev Γ a3 = some v3)
    (hbody : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)), Inv C s Γ M D t →
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetK C.KB (callEntryStateHOLFinite t callee) body P)
    (hk : ∀ w w0 w1 w2, P w w0 w1 w2 →
      SpecR (Inv C s ((y2, w2) :: (y1, w1) :: (y0, w0) :: (x, w) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D)
      (.seq (callTo x f [a1, a2, a3]) (.seq (.assign .local y0 (kbLoad 0))
        (.seq (.assign .local y1 (kbLoad 1)) (.seq (.assign .local y2 (kbLoad 2)) rest)))) s m R := by
  intro t ht
  obtain ⟨wx, hwx⟩ := ht.decl x hx
  rcases call3_retK C.KB t x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 wx P h12 h13 h23 (by rw [ht.sr.code]; exact hcode)
      (inv_ev ht he1) (inv_ev ht he2) (inv_ev ht he3) hwx (fun callee c1 c2 c3 => hbody t callee ht c1 c2 c3) with
    hs | ⟨w, k0, k1, k2, u, hp, hu, hm, hd, hg, hc, hb, lx, lo⟩
  · exact Or.inl (seq_stop t _ _ hs)
  simp only [callTo]
  rw [seq_normal _ hu]
  have hsr : SR C s u := sr_of_eq (sr_kbSt hok ht.sr k0 k1 k2) hm hd hg hc
  -- the three loads
  have hKB : u.globals.lookup gKb = some (.val (.word C.KB)) := by rw [hg]; exact ht.sr.gkb
  have hget := kbSt_get C.KB t k0 k1 k2
  have ld : ∀ (v : PState σ) (j : Nat) (kw : BitVec 64), j < 3 → v.globals = u.globals → v.memaddrs = u.memaddrs →
      v.memory = u.memory → u.memory (C.KB + BitVec.ofNat 64 (8 * j)) = .word kw →
      T.EV v (kbLoad j) = some (.val (.word kw)) := by
    intro v j kw hj hgv hdv hmv hval
    have ha : T.EV v (.op .add [.var .global gKb, .const (BitVec.ofNat 64 (8 * j))]) =
        some (.val (.word (C.KB + BitVec.ofNat 64 (8 * j)))) := by
      simp only [T.EV]; rw [evalHOLExact]
      simp [evalListHOLExact, evalHOLExact, hgv, hKB, wordOpHOL, wordOp, valueIsWord, valueWord]
    have := eval_load_word v _ _ ha (by rw [hdv, hd]; exact ht.sr.kbuf j hj)
    rw [hmv, hval] at this; exact this
  obtain ⟨w0', hw0'⟩ := ht.decl y0 hy0
  have hy0u : ∃ z, u.locals.lookup y0 = some (.val (.word z)) := by
    by_cases e : y0 = x
    · subst e; exact ⟨w, lx⟩
    · exact ⟨w0', by rw [lo y0 e]; exact hw0'⟩
  obtain ⟨z0, hz0⟩ := hy0u
  rw [seq_normal _ (ConsLoop.assign_local u y0 _ k0 z0 (ld u 0 k0 (by decide) rfl rfl rfl (by rw [hm]; exact hget.1)) hz0)]
  let u1 := setVarHOLFinite y0 (.val (.word k0)) u
  have hy1u : ∃ z, u1.locals.lookup y1 = some (.val (.word z)) := by
    by_cases e1 : y1 = y0
    · subst e1; exact ⟨k0, lookup_setVar_same _ _ _⟩
    rw [lookup_setVar_other _ _ e1]
    by_cases e : y1 = x
    · subst e; exact ⟨w, lx⟩
    · obtain ⟨z, hz⟩ := ht.decl y1 hy1; exact ⟨z, by rw [lo y1 e]; exact hz⟩
  obtain ⟨z1, hz1⟩ := hy1u
  rw [seq_normal _ (ConsLoop.assign_local u1 y1 _ k1 z1 (ld u1 1 k1 (by decide) rfl rfl rfl (by rw [hm]; exact hget.2.1)) hz1)]
  let u2 := setVarHOLFinite y1 (.val (.word k1)) u1
  have hy2u : ∃ z, u2.locals.lookup y2 = some (.val (.word z)) := by
    by_cases e2 : y2 = y1
    · subst e2; exact ⟨k1, lookup_setVar_same _ _ _⟩
    rw [lookup_setVar_other _ _ e2]
    by_cases e1 : y2 = y0
    · subst e1; exact ⟨k0, lookup_setVar_same _ _ _⟩
    rw [lookup_setVar_other _ _ e1]
    by_cases e : y2 = x
    · subst e; exact ⟨w, lx⟩
    · obtain ⟨z, hz⟩ := ht.decl y2 hy2; exact ⟨z, by rw [lo y2 e]; exact hz⟩
  obtain ⟨z2, hz2⟩ := hy2u
  rw [seq_normal _ (ConsLoop.assign_local u2 y2 _ k2 z2 (ld u2 2 k2 (by decide) rfl rfl rfl (by rw [hm]; exact hget.2.2)) hz2)]
  let u3 := setVarHOLFinite y2 (.val (.word k2)) u2
  have hinv : Inv C s ((y2, k2) :: (y1, k1) :: (y0, k0) :: (x, w) :: Γ) [] D u3 := by
    refine ⟨sr_of_eq hsr rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp), fun y hy => ?_⟩
    · simp only [Env.get] at hy
      by_cases e2 : y = y2
      · rw [ite_eq_left e2] at hy; cases hy; subst e2; exact lookup_setVar_same _ _ _
      rw [ite_eq_right e2] at hy
      rw [lookup_setVar_other _ _ e2]
      by_cases e1 : y = y1
      · rw [ite_eq_left e1] at hy; cases hy; subst e1; exact lookup_setVar_same _ _ _
      rw [ite_eq_right e1] at hy
      rw [lookup_setVar_other _ _ e1]
      by_cases e0 : y = y0
      · rw [ite_eq_left e0] at hy; cases hy; subst e0; exact lookup_setVar_same _ _ _
      rw [ite_eq_right e0] at hy
      rw [lookup_setVar_other _ _ e0]
      by_cases ex : y = x
      · rw [ite_eq_left ex] at hy; cases hy; subst ex; exact lx
      rw [ite_eq_right ex] at hy
      rw [lo y ex]; exact ht.env y v hy
    · by_cases e2 : y = y2
      · subst e2; exact ⟨k2, lookup_setVar_same _ _ _⟩
      rw [lookup_setVar_other _ _ e2]
      by_cases e1 : y = y1
      · subst e1; exact ⟨k1, lookup_setVar_same _ _ _⟩
      rw [lookup_setVar_other _ _ e1]
      by_cases e0 : y = y0
      · subst e0; exact ⟨k0, lookup_setVar_same _ _ _⟩
      rw [lookup_setVar_other _ _ e0]
      by_cases ex : y = x
      · subst ex; exact ⟨w, lx⟩
      rw [lo y ex]; exact ht.decl y hy
  exact hk w k0 k1 k2 hp u3 hinv

end ConPanqueque.Front
