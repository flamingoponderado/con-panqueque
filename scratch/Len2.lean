import ConPanqueque.Examples.ListLength
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.Sep ConPanqueque.Examples.ListLength

/-- The value of local `len` as a natural number (0 if absent). -/
def lenOf {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Nat :=
  match t.locals.lookup (ofString "len") with
  | some (.val (.word w)) => w.toNat
  | _ => 0

theorem listRep_nil_iff {p : BitVec 64} {xs : List (BitVec 64)} {h : Heap} (hr : ListRep p xs h) :
    p = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp [ListRep] at hr; simp [hr.1]
  | cons y ys => simp [ListRep] at hr; simp [hr.1]

theorem lenLoop_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (xs : List (BitVec 64)) (l : BitVec 64)
    (hsmall : xs.length < 2 ^ 64)
    (hl0 : s.locals.lookup (ofString "len") = some (.val (.word 0)))
    (hp0 : s.locals.lookup (ofString "p") = some (.val (.word l)))
    (hrep : Sat s (ListRep l xs)) (hclk : xs.length ≤ s.clock) :
    ∃ s', evaluateHOLFiniteState s lenLoop = (none, s') ∧
      s'.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 xs.length))) ∧
      s'.memory = s.memory := by
  let I : PanSemStateFiniteExact 64 σ → Prop := fun t => ∃ k q, k ≤ xs.length ∧
    t.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 k))) ∧
    t.locals.lookup (ofString "p") = some (.val (.word q)) ∧
    Sat t (ListRep q (xs.drop k)) ∧ xs.length - k ≤ t.clock ∧
    t.memory = s.memory ∧ t.memaddrs = s.memaddrs
  let Q : PanSemStateFiniteExact 64 σ → Prop := fun t =>
    t.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 xs.length))) ∧ t.memory = s.memory
  have hI0 : I s := ⟨0, l, Nat.zero_le _, by simpa using hl0, hp0, by simpa using hrep, by omega, rfl, rfl⟩
  refine while_rule (.cmp .notEqual (.var .local (ofString "p")) (.const 0))
    (.seq (.assign .local (ofString "len") (.op .add [.var .local (ofString "len"), .const 1]))
      (.assign .local (ofString "p") (.load .one (.op .add [.var .local (ofString "p"), .const 8]))))
    I (fun t => xs.length - lenOf t) Q ?_ s hI0
  rintro t ⟨k, q, hk, hlen, hp, hsat, hck, hmem, hdom⟩
  have hkn : lenOf t = k := by
    simp [lenOf, hlen]; omega
  refine ⟨if q ≠ 0 then 1 else 0, ?_, ?_, ?_⟩
  · simp [evalHOLFinite, evalHOLExact, hp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · intro hw
    have hq : q = 0 := by simpa using hw
    obtain ⟨h, hr, _⟩ := hsat
    have hnil := (listRep_nil_iff hr).mp hq
    have : k = xs.length := by simp at hnil; omega
    subst this
    exact ⟨hlen, hmem⟩
  · intro hw
    have hq : q ≠ 0 := by simpa using hw
    obtain ⟨y, ys, hys⟩ : ∃ y ys, xs.drop k = y :: ys := by
      obtain ⟨h, hr, _⟩ := hsat
      cases e : xs.drop k with
      | nil => exact absurd ((listRep_nil_iff hr).mpr e) hq
      | cons y ys => exact ⟨y, ys, rfl⟩
    have hlt : k < xs.length := by
      have : (xs.drop k).length = xs.length - k := List.length_drop ..
      rw [hys] at this; simp at this; omega
    rw [hys] at hsat
    obtain ⟨_, q', hd8, hv8, hrest⟩ := listRep_cons_next t q y ys hsat
    let t0 := decClockHOLFinite t
    obtain ⟨t', hev, hlen', hp', hmem', hdom', hclk'⟩ :=
      lenBody_step t0 (BitVec.ofNat 64 k) q q' (by simpa [t0, decClockHOLFinite] using hlen)
        (by simpa [t0, decClockHOLFinite] using hp) (by simpa [t0, decClockHOLFinite] using hd8)
        (by simpa [t0, decClockHOLFinite] using hv8)
    refine ⟨by omega, by omega, t', hev, ⟨k + 1, q', by omega, ?_, hp', ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hlen']; simp [BitVec.ofNat_add]
    · have : xs.drop (k + 1) = ys := by
        rw [← List.drop_drop, hys]; rfl
      rw [this]
      exact sat_of_mem (by simp [hmem', t0, decClockHOLFinite]) (by simp [hdom', t0, decClockHOLFinite]) hrest
    · simp [hclk', t0, decClockHOLFinite]; omega
    · simp [hmem', t0, decClockHOLFinite, hmem]
    · simp [hdom', t0, decClockHOLFinite, hdom]
    · have : lenOf t' = k + 1 := by
        simp [lenOf, hlen']; omega
      omega
