import ConLeche.Verify.Frontend.Prepare

/-! # `frontOf` on a stream whose prelude copies are the prelude's records

`OverOK ps ds`: for every prelude record `p`, at most one stream record declares `p`'s key, and the
one that does is `p` itself.  Then con-leche's `frontSpec` (and so `frontOf`) puts exactly the
prelude in front and leaves the stream without the records declaring a prelude key
(`frontSpec_over`): the program drops those copies and hangs on any other overlap. -/

namespace ConPanqueque.Prelude

open ConLeche ConLeche.Frontend

/-- A stream record no prelude record's key names. -/
def keep (ps : List Declaration) (d : Declaration) : Bool := !(ps.any fun p => declares (preludeKey p) d)

/-- The overlap the program accepts: per prelude key, at most one stream record declares it, and
that record is the prelude's. -/
def OverOK (ps ds : List Declaration) : Prop :=
  ∀ p ∈ ps, (∀ d ∈ ds, declares (preludeKey p) d = true → d = p) ∧
    (ds.filter (declares (preludeKey p))).length ≤ 1

theorem pickSpec_over (n : Name) (p : Declaration) : ∀ ds : List Declaration,
    (∀ d ∈ ds, declares n d = true → d = p) → (ds.filter (declares n)).length ≤ 1 →
    (pickSpec n ds).1.getD p = p ∧ (pickSpec n ds).2 = ds.filter (fun d => !declares n d)
  | [], _, _ => by simp [pickSpec]
  | d :: ds, h1, h2 => by
    by_cases hd : declares n d = true
    · have h0 : (ds.filter (declares n)).length = 0 := by
        simp only [List.filter_cons, hd, ite_true, List.length_cons] at h2; omega
      have hnone : ∀ x ∈ ds, declares n x = false := by
        intro x hx
        cases hx' : declares n x
        · rfl
        · exfalso
          have : x ∈ ds.filter (declares n) := List.mem_filter.mpr ⟨hx, hx'⟩
          rw [List.length_eq_zero_iff.mp h0] at this; cases this
      simp only [pickSpec, hd, ite_true, Option.getD_some, List.filter_cons, Bool.not_true,
        Bool.false_eq_true, ite_false]
      refine ⟨h1 d (List.mem_cons_self ..) hd, ?_⟩
      symm; rw [List.filter_eq_self]; intro x hx; simp [hnone x hx]
    · have hd' : declares n d = false := by simpa using hd
      have ih := pickSpec_over n p ds (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (by simpa [List.filter_cons, hd'] using h2)
      simp only [pickSpec, hd', Bool.false_eq_true, ite_false, List.filter_cons, Bool.not_false,
        ite_true]
      exact ⟨ih.1, by rw [ih.2]⟩

theorem overOK_filter {ps ds : List Declaration} (h : OverOK ps ds) (f : Declaration → Bool) :
    OverOK ps (ds.filter f) := by
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  refine ⟨fun d hd => h1 d (List.mem_filter.mp hd).1, ?_⟩
  rw [List.filter_filter]
  refine Nat.le_trans ?_ h2
  apply List.Sublist.length_le
  rw [show (fun a => declares (preludeKey p) a && f a) = (fun a => f a && declares (preludeKey p) a) from
    funext fun a => Bool.and_comm _ _, ← List.filter_filter]
  exact List.filter_sublist

/-- **The front is the prelude; the rest is the stream without its prelude copies.** -/
theorem frontSpec_over : ∀ (ps ds : List Declaration), OverOK ps ds →
    (frontSpec ps ds).1 = ps ∧ (frontSpec ps ds).2 = ds.filter (keep ps)
  | [], ds, _ => by
    have : keep [] = fun _ => true := by funext d; simp [keep]
    simp only [frontSpec, this, true_and]; exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
  | p :: ps, ds, h => by
    obtain ⟨h1, h2⟩ := h p (List.mem_cons_self ..)
    obtain ⟨e1, e2⟩ := pickSpec_over (preludeKey p) p ds h1 h2
    have hrest : OverOK ps (ds.filter (fun d => !declares (preludeKey p) d)) :=
      overOK_filter (fun q hq => h q (List.mem_cons_of_mem _ hq)) _
    obtain ⟨f1, f2⟩ := frontSpec_over ps _ hrest
    simp only [frontSpec]
    rw [e2, e1, f1, f2, List.filter_filter]
    refine ⟨rfl, ?_⟩
    congr 1; funext d
    simp [keep, Bool.and_comm]

/-- `frontOf` from an empty accumulator, at an accepted overlap. -/
theorem frontOf_over (ps : List Declaration) (ds : Array Declaration) (h : OverOK ps ds.toList) :
    (frontOf #[] ps ds).1.toList = ps ∧ (frontOf #[] ps ds).2.toList = ds.toList.filter (keep ps) := by
  obtain ⟨h1, h2⟩ := frontOf_toList ps #[] ds
  obtain ⟨f1, f2⟩ := frontSpec_over ps ds.toList h
  rw [h1, h2, f1, f2]; simp

end ConPanqueque.Prelude
