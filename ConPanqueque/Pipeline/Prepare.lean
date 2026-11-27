import ConPanqueque.Pipeline.Ext2
import ConLeche.Frontend.Prepare

/-! # `preparePrelude` on a stream that declares no prelude name

`preparePrelude pre ds` moves the stream's own copy of each prelude record to the front and hoists
the ground of pinned `Nat` operations.  On a stream none of whose records declares a prelude record's
key, with no pinned `Nat` operation record anywhere, it is the prelude followed by the stream
(`preparePrelude_eq`).  `pipeline_of_stream`: then an accepting run of the stream alone and one of
the prelude give an accepting run of the prepared stream, con-leche's fold input. -/

namespace ConPanqueque.Pipeline

open ConLeche ConLeche.Frontend

set_option pp.funBinderTypes true

theorem hoistTargets_empty (used : Declaration → Array Name) (ds : Array Declaration)
    (h : ∀ i : Nat, isNatOpRecord ds[i]! = none) : hoistTargets used ds = {} := by
  unfold hoistTargets
  simp only [h]
  have hf : ∀ (l : List Nat) (b : Std.HashMap Nat Nat), List.foldl (fun (b : Std.HashMap Nat Nat) (_ : Nat) => b) b l = b := by
    intro l; induction l <;> simp_all
  simp [Id.run, hf]
  rfl

theorem pick_none (n : Name) (ds : Array Declaration) (h : ∀ d ∈ ds.toList, declares n d = false) :
    pick n ds = (none, ds) := by
  have hi : ds.findIdx (declares n) = ds.size := by
    rw [Array.findIdx_eq_size]; intro x hx; exact h x (by simpa using hx)
  simp only [pick, hi, Array.getElem?_eq_none (Nat.le_refl _)]
  congr 1
  simp [Array.eraseIdxIfInBounds]

theorem frontOf_none (ds : Array Declaration) : ∀ (ps : List Declaration) (acc : Array Declaration),
    (∀ p ∈ ps, ∀ d ∈ ds.toList, declares (preludeKey p) d = false) →
    frontOf acc ps ds = (acc ++ ps.toArray, ds)
  | [], acc, _ => by simp [frontOf]
  | p :: ps, acc, h => by
    simp only [frontOf, pick_none _ ds (h p (List.mem_cons_self ..)), Option.getD_none]
    rw [frontOf_none ds ps _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))]
    simp

theorem getElem!_none (a : Array Declaration) (h : ∀ d ∈ a.toList, isNatOpRecord d = none) (i : Nat) :
    isNatOpRecord a[i]! = none := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]; exact h _ (by simp)
  · rw [getElem!_neg a i hi]; decide

theorem preparePrelude_eq (pre : PreludeIx) (ds : Array Declaration)
    (hN : ∀ p ∈ pre.decls.toList, ∀ d ∈ ds.toList, declares (preludeKey p) d = false)
    (hOp : ∀ d ∈ pre.decls.toList ++ ds.toList, isNatOpRecord d = none) :
    (preparePrelude pre ds).toList = pre.decls.toList ++ ds.toList := by
  unfold preparePrelude prepareD
  rw [frontOf_none ds pre.decls.toList #[] hN]
  simp only [hoistNatOpGround]
  rw [hoistTargets_empty _ _ (getElem!_none _ (fun d hd => hOp d (by simpa using hd)))]
  simp


/-- A stream record the bridge accepts: a value, quotient or `sorryAx` record, or an inductive block,
at names the guards do not read, which the prelude's environment does not declare and no prelude
record is keyed by (and, in a block, not `Quot.mk`). -/
def RecOK (pre : PreludeIx) (envP : Env) (d : Declaration) : Prop :=
  ∃ ns, recNames d = some ns ∧ ∀ n ∈ ns, NameOK n ∧ envP.find? n = none ∧
    (∀ p ∈ pre.decls.toList, preludeKey p ≠ n) ∧ ((∃ b k, d = .indDecl b k) → n ≠ quotMkName)

theorem recOK_of_recName {pre : PreludeIx} {envP : Env} {d : Declaration} {n : Name} (hn : recName d = some n)
    (h1 : NameOK n) (h2 : envP.find? n = none) (h3 : ∀ p ∈ pre.decls.toList, preludeKey p ≠ n) :
    RecOK pre envP d :=
  ⟨[n], recNames_of_recName hn, fun m hm => by
    rw [List.mem_singleton] at hm; subst hm
    exact ⟨h1, h2, h3, fun ⟨b, k, he⟩ => by subst he; simp [recName, valName] at hn⟩⟩

theorem valName_names {d : Declaration} {n : Name} (h : valName d = some n) : d.names = [n] := by
  cases d <;> simp_all [valName, Declaration.names]

theorem recName_names {d : Declaration} {n : Name} (h : recName d = some n) : d.names = [n] := by
  rcases recName_cases h with h | ⟨c, rfl, -, rfl⟩ | ⟨k, c, rfl, rfl⟩ | ⟨c, rfl, -, rfl⟩
  · exact valName_names h
  · simp [Declaration.names]
  · simp [Declaration.names]
  · simp [Declaration.names]

theorem valName_natOp {d : Declaration} {n : Name} (h : valName d = some n) (hn : NameOK n) :
    isNatOpRecord d = none := by
  obtain ⟨hop, -⟩ := hn
  simp only [natOpName, Bool.or_eq_false_iff] at hop
  cases d <;> simp_all [valName, isNatOpRecord]

theorem recName_natOp {d : Declaration} {n : Name} (h : recName d = some n) (hn : NameOK n) :
    isNatOpRecord d = none := by
  rcases recName_cases h with h | ⟨c, rfl, -, rfl⟩ | ⟨k, c, rfl, rfl⟩ | ⟨c, rfl, -, rfl⟩
  · exact valName_natOp h hn
  · simp [isNatOpRecord]
  · simp [isNatOpRecord]
  · simp [isNatOpRecord]

theorem recNames_names {d : Declaration} {ns : List Name} (h : recNames d = some ns) : ∀ n ∈ d.names, n ∈ ns := by
  rcases recNames_cases h with ⟨b, k, rfl, rfl⟩ | ⟨n, hn, rfl, -⟩
  · exact fun n hn => List.mem_append_left _ hn
  · rw [recName_names hn]; exact fun m hm => hm

theorem recNames_natOp {d : Declaration} {ns : List Name} (h : recNames d = some ns) (hok : ∀ n ∈ ns, NameOK n) :
    isNatOpRecord d = none := by
  rcases recNames_cases h with ⟨b, k, rfl, rfl⟩ | ⟨n, hn, rfl, -⟩
  · rfl
  · exact recName_natOp hn (hok n (List.mem_singleton_self _))

/-- **The prepared stream accepts**: con-leche's prelude accepted, and the stream accepted alone. -/
theorem pipeline_of_stream (pins pins₀ : List NatOpPinSet) (pre : PreludeIx) (ds : Array Declaration)
    {envP E₁ : Env} (hP : PureRun pins pre.decls.toList Env.empty envP)
    (hpOp : ∀ p ∈ pre.decls.toList, isNatOpRecord p = none)
    (hS : PureRun pins₀ ds.toList Env.empty E₁) (hok : ∀ d ∈ ds.toList, RecOK pre envP d) :
    ∃ E, PureRun pins (preparePrelude pre ds).toList Env.empty E := by
  rw [preparePrelude_eq pre ds (fun p hp d hd => by
      obtain ⟨ns, hns, hall⟩ := hok d hd
      simp only [declares]
      rw [Bool.eq_false_iff]
      intro hc
      have hm := recNames_names hns _ (List.contains_iff_mem.mp hc)
      exact (hall _ hm).2.2.1 p hp rfl)
    (fun d hd => by
      rcases List.mem_append.mp hd with h | h
      · exact hpOp d h
      · obtain ⟨ns, hns, hall⟩ := hok d h; exact recNames_natOp hns (fun n hn => (hall n hn).1))]
  exact prelude_then_streamI pins pins₀ _ _ hP hS (fun d hd => by
    obtain ⟨ns, hns, hall⟩ := hok d hd
    exact ⟨ns, hns, fun n hn => ⟨(hall n hn).1, (hall n hn).2.1, (hall n hn).2.2.2⟩⟩)

end ConPanqueque.Pipeline
