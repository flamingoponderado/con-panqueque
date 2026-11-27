import ConPanqueque.Front.Feed

/-! # The twin's parse does not read its declarations

`withPre P st`: the parse state `st` with the records `P` in front of its own.  The line functions
read the three id tables only and push records, so `feedAll (withPre P st) b i n` runs as
`feedAll st b i n` does, with `P` in front of the records it ends with (`feedAll_withPre`).  The
program parses the built-in prelude and then the stream into one registry: the stream's parse
starts from the prelude's records. -/

open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Prelude

open ConPanqueque.Front

/-- The parse state with `P` in front of its records. -/
@[reducible] def withPre (P : Array IDeclaration) (st : StateD) : StateD :=
  { st with decls := P ++ st.decls }

theorem withPre_nil (st : StateD) : withPre #[] st = st := by
  cases st; simp [withPre]

theorem parseCVD_withPre (P : Array IDeclaration) (st : StateD) (cv : ConLeche.Frontend.CVRec) :
    parseCVD (withPre P st) cv = parseCVD st cv := rfl

theorem validateIndD_withPre (P : Array IDeclaration) (st : StateD) tys cts rcs :
    validateIndD (withPre P st) tys cts rcs = validateIndD st tys cts rcs := rfl

theorem pushDecl_withPre (P : Array IDeclaration) (st : StateD) (d : IDeclaration) :
    pushDecl (withPre P st) d = withPre P <$> pushDecl st d := by
  simp only [pushDecl, map_pure, withPre, Array.append_push]

theorem parseRuleD_withPre (P : Array IDeclaration) (st : StateD) :
    parseRuleD (withPre P st) = parseRuleD st := rfl

theorem installIndD_withPre (P : Array IDeclaration) (st : StateD) tys cts rcs nPd :
    installIndD (withPre P st) tys cts rcs nPd = withPre P <$> installIndD st tys cts rcs nPd := by
  simp only [installIndD, parseCVD_withPre, parseRuleD_withPre, pushDecl_withPre, map_bind]

theorem parseNameEntryD_withPre (P : Array IDeclaration) (st : StateD) (i : Nat) (r : ConLeche.Frontend.NameRec) :
    parseNameEntryD (withPre P st) i r = withPre P <$> parseNameEntryD st i r := by
  cases r <;> simp only [parseNameEntryD, map_bind, map_pure] <;> rfl

theorem parseLevelEntryD_withPre (P : Array IDeclaration) (st : StateD) (i : Nat) (r : ConLeche.Frontend.LevelRec) :
    parseLevelEntryD (withPre P st) i r = withPre P <$> parseLevelEntryD st i r := by
  cases r <;> simp only [parseLevelEntryD, map_bind, map_pure] <;> rfl

theorem parseExprEntryD_withPre (P : Array IDeclaration) (st : StateD) (i : Nat) (r : ConLeche.Frontend.ExprRec) :
    parseExprEntryD (withPre P st) i r = withPre P <$> parseExprEntryD st i r := by
  cases r <;> simp only [parseExprEntryD, map_bind, map_pure] <;> rfl

/-- The state component of a line's outcome, with `P` in front. -/
def preOut (P : Array IDeclaration) : StateD ⊕ RecordVerdict → StateD ⊕ RecordVerdict
  | .inl st => .inl (withPre P st)
  | .inr v => .inr v

theorem processLineCoreD_withPre (P : Array IDeclaration) (st : StateD) (d : ConLeche.Frontend.DeclRec) :
    processLineCoreD (withPre P st) d = preOut P <$> processLineCoreD st d := by
  cases d with
  | ax cvr u =>
    simp only [processLineCoreD, parseCVD_withPre, map_bind]
    congr 1; funext cvp
    cases u <;> simp [-Array.push_append, Array.append_push, pushDecl, withPre, preOut]
  | defn cvr v h sf =>
    simp only [processLineCoreD, parseCVD_withPre, map_bind]
    congr 1; funext cvp
    split
    · simp only [map_bind]; congr 1; funext vl
      simp [-Array.push_append, Array.append_push, pushDecl, withPre, preOut]
    · simp [preOut]
  | thm cvr v =>
    simp only [processLineCoreD, parseCVD_withPre, map_bind]
    congr 1; funext cvp
    try simp only [map_bind]
    congr 1; funext vl
    simp [-Array.push_append, Array.append_push, pushDecl, withPre, preOut]
  | opaq cvr v u =>
    simp only [processLineCoreD, parseCVD_withPre, map_bind]
    congr 1; funext cvp
    cases u
    · try simp only [map_bind]
      congr 1; funext vl
      simp [-Array.push_append, Array.append_push, pushDecl, withPre, preOut]
      try rfl
    · simp [preOut]
  | quot cvr k =>
    simp only [processLineCoreD, parseCVD_withPre, map_bind]
    congr 1; funext cv
    split <;> simp [-Array.push_append, Array.append_push, pushDecl, withPre, preOut]
  | ind tys cts rcs =>
    simp only [processLineCoreD, validateIndD_withPre, map_bind]
    congr 1; funext v
    cases v with
    | inl v => simp [preOut]
    | inr p =>
      obtain ⟨cts', nPd⟩ := p
      simp only [installIndD_withPre, map_bind]
      simp [preOut]

theorem applyLine_withPre (P : Array IDeclaration) (st : StateD) (r : ConLeche.Frontend.LineRec) (n : Nat) :
    applyLine (withPre P st) r n = preOut P <$> applyLine st r n := by
  unfold applyLine
  split
  · cases r with
    | expr i e => simp [applyRecord, parseExprEntryD_withPre, preOut]
    | name i e => simp [applyRecord, parseNameEntryD_withPre, preOut]
    | level i e => simp [applyRecord, parseLevelEntryD_withPre, preOut]
    | decl d => simp [applyRecord, applyDeclD, processLineCoreD_withPre]
    | header => simp [applyRecord, preOut]
    | blank => simp [applyRecord, preOut]
  · simp only [fail, throwThe, MonadExceptOf.throw]
    funext s; rfl

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front

theorem am_map_ok {α β : Type} (f : α → β) (x : AM α) (s s' : AState) (b : β)
    (h : (f <$> x) s = .ok (b, s')) : ∃ a, x s = .ok (a, s') ∧ b = f a := by
  have e : (f <$> x) s = (x s).map (fun p => (f p.1, p.2)) := by
    show (x >>= fun a => pure (f a)) s = _
    rw [ConRon.Bridge.AM.bind_apply]
    cases x s <;> rfl
  rw [e] at h
  cases hx : x s with
  | error er => rw [hx] at h; cases h
  | ok p =>
    rw [hx] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨p.1, by rw [← h.2], h.1.symm⟩

/-- **The parse with records in front** runs as the parse without them. -/
theorem feedAll_withPre (P : Array IDeclaration) (b : ByteArray) :
    ∀ msr (i : USize) (st : StateD) (n : Nat) (s s' : AState) (st' : StateD), b.size - i.toNat = msr →
      feedAll (withPre P st) b i n s = .ok (st', s') →
      ∃ st0, feedAll st b i n s = .ok (st0, s') ∧ st' = withPre P st0 := by
  intro msr
  induction msr using Nat.strongRecOn with
  | ind msr ih =>
    intro i st n s s' st' hm h
    rw [feedAll] at h
    rw [feedAll]
    by_cases hi : i < b.usize
    · rw [dite_eq_left hi] at h ⊢
      revert h
      cases hsc : ConLeche.Frontend.scanLineFwd b i with
      | err e => intro h; exact (ConRon.Bridge.AM.fail_ok h).elim
      | ok r j =>
        intro h
        simp only at h ⊢
        obtain ⟨x, s1, hx, hrest⟩ := ConRon.Bridge.AM.bind_ok h
        rw [applyLine_withPre] at hx
        obtain ⟨y, hy, rfl⟩ := am_map_ok _ _ _ _ _ hx
        rw [bind_ok_apply hy]
        cases y with
        | inr v => exact (ConRon.Bridge.AM.fail_ok hrest).elim
        | inl st1 =>
          simp only [preOut] at hrest ⊢
          by_cases hj0 : (j == 0) = true
          · rw [ite_eq_left hj0] at hrest ⊢
            obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.pure_ok hrest
            exact ⟨st1, rfl, rfl⟩
          · rw [ite_eq_right hj0] at hrest ⊢
            by_cases hij : i < j
            · rw [dite_eq_left hij] at hrest ⊢
              have hlt := USize.lt_iff_toNat_lt.mp hij
              have hb := ConLeche.Frontend.usizeInBounds b i hi
              exact ih _ (by omega) j st1 (n + 1) s1 s' st' rfl hrest
            · rw [dite_eq_right hij] at hrest; exact (ConRon.Bridge.AM.fail_ok hrest).elim
    · rw [dite_eq_right hi] at h ⊢
      obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.pure_ok h
      exact ⟨st, rfl, rfl⟩

end ConPanqueque.Prelude
