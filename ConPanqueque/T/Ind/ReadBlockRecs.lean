import ConLeche.Verify.Inductives.BlockShapeInv
import ConLeche.Frontend.ExportC
import ConRon.Arena.Frontend.Readback
import ConLeche.Kernel.Install

/-! # The pure reader's records are the block's

`readBlock_records`: every member, constructor and recursor con-leche's `readBlock` reads is a record
of the block (with the record's own counts), every index count is bounded by a record's telescope or
a recursor's major index, and the constructors of all members number at most the block's records.
`denoteCIList_mem`, `denoteCI_*`: a denoted block's records are the denotations of the stored ones. -/

open ConRon.Arena

namespace ConPanqueque.T.Ind

set_option autoImplicit false


theorem piBinders_len (e : ConLeche.Expr) : e.piBinders.1.length = ConLeche.Frontend.indPiTeleLen e := by
  induction e with
  | forallE ty b _ ihb => simp [ConLeche.Expr.piBinders, ConLeche.Frontend.indPiTeleLen, ihb]
  | _ => simp [ConLeche.Expr.piBinders, ConLeche.Frontend.indPiTeleLen]

/-- A member's index count is read off its own telescope or off a recursor's major index. -/
theorem blockCounts_bound {nPd k nC nR : Nat} {cvT : ConLeche.ConstantVal} {r : Option (ConLeche.Name × Nat × Nat)}
    {c : Nat × Nat} (h : ConLeche.blockCounts nPd k nC nR cvT r = .ok c) :
    c.2 ≤ ConLeche.Frontend.indPiTeleLen cvT.type ∨ ∃ rn mI rP, r = some (rn, mI, rP) ∧ c.2 ≤ mI := by
  unfold ConLeche.blockCounts at h
  split at h
  · rename_i bs s heq
    split at h
    · cases h
      left
      have := congrArg (fun q => q.1.length) heq
      simp only [piBinders_len] at this
      simp only; omega
    · cases h
  · split at h
    · cases h
    · rename_i rn mI rP
      split at h
      · cases h
      split at h
      · cases h; exact Or.inr ⟨rn, mI, rP, rfl, by simp⟩
      split at h
      · cases h; exact Or.inr ⟨rn, mI, rP, rfl, by simp⟩
      · cases h

theorem blockMemberCounts_bound {nPd k nC : Nat} {names : List ConLeche.Name}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)} :
    ∀ (cvTs : List ConLeche.ConstantVal) (m : Nat) (nIdxs : List Nat),
      ConLeche.blockMemberCounts nPd k nC names rs m cvTs = .ok nIdxs →
      ∀ n ∈ nIdxs, (∃ cvT ∈ cvTs, n ≤ ConLeche.Frontend.indPiTeleLen cvT.type) ∨ ∃ q ∈ rs, n ≤ q.2.1
  | [], m, nIdxs, h => by
    simp only [ConLeche.blockMemberCounts, Except.ok.injEq] at h
    subst h; intro n hn; exact absurd hn (List.not_mem_nil)
  | cvT :: ts, m, nIdxs, h => by
    rw [ConLeche.blockMemberCounts] at h
    cases hc : ConLeche.blockCounts nPd k nC rs.length cvT
        ((rs.find? fun q => ConLeche.recTargetOf names q.2.1 q.1.type == m).map
          fun q => (q.1.name, q.2.1, q.2.2.1)) with
    | error e => rw [hc] at h; exact nomatch h
    | ok c =>
    rw [hc] at h
    cases hm : ConLeche.blockMemberCounts nPd k nC names rs (m + 1) ts with
    | error e => rw [hm] at h; exact nomatch h
    | ok ns =>
      rw [hm] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · rcases blockCounts_bound hc with h1 | ⟨rn, mI, rP, hr, h2⟩
        · exact Or.inl ⟨cvT, List.mem_cons_self, h1⟩
        · obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hr
          refine Or.inr ⟨q, List.mem_of_find?_eq_some hq, ?_⟩
          simp only [Prod.mk.injEq] at hqe
          rw [hqe.2.1]; exact h2
      · rcases blockMemberCounts_bound ts (m + 1) ns hm n hn with ⟨cv, hcv, h1⟩ | h2
        · exact Or.inl ⟨cv, List.mem_cons_of_mem _ hcv, h1⟩
        · exact Or.inr h2

theorem blockSplitRecs_mem :
    ∀ {block : List ConLeche.ConstantInfo} {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
      ConLeche.blockSplitRecs block = some rs → ∀ r ∈ rs, .recInfo r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∈ block
  | [], rs, h, r, hr => by
    simp only [ConLeche.blockSplitRecs, Option.some.injEq] at h
    subst h; exact nomatch hr
  | .recInfo cvR mI rP isK rules :: rest, rs, h, r, hr => by
    simp only [ConLeche.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (blockSplitRecs_mem h' r hr)
  | .axiomInfo .. :: _, _, h, _, _ | .defnInfo .. :: _, _, h, _, _ | .thmInfo .. :: _, _, h, _, _
  | .indInfo .. :: _, _, h, _, _ | .ctorInfo .. :: _, _, h, _, _ => nomatch h

theorem blockSplitCtors_mem :
    ∀ {block : List ConLeche.ConstantInfo} {cs : List (ConLeche.ConstantVal × Nat × Nat)}
      {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
      ConLeche.blockSplitCtors block = some (cs, rs) →
      (∀ c ∈ cs, ∃ T, .ctorInfo c.1 c.2.1 c.2.2 T ∈ block) ∧
        (∀ r ∈ rs, .recInfo r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∈ block)
  | .ctorInfo cvC nP nF T :: rest, cs, rs, h => by
    simp only [ConLeche.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hc, hr⟩ := blockSplitCtors_mem h'
    refine ⟨fun c hc' => ?_, fun r hr' => List.mem_cons_of_mem _ (hr r hr')⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ⟨T, List.mem_cons_self⟩
    · obtain ⟨T', hT'⟩ := hc c hc'
      exact ⟨T', List.mem_cons_of_mem _ hT'⟩
  | [], cs, rs, h => by
    simp only [ConLeche.blockSplitCtors, ConLeche.blockSplitRecs, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun c hc => (nomatch hc), fun r hr => nomatch hr⟩
  | .recInfo cvR mI rP isK rules :: rest, cs, rs, h => by
    simp only [ConLeche.blockSplitCtors, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨rs', h', rfl, rfl⟩ := h
    exact ⟨fun c hc => (nomatch hc), blockSplitRecs_mem h'⟩
  | .axiomInfo .. :: _, _, _, h | .defnInfo .. :: _, _, _, h | .thmInfo .. :: _, _, _, h
  | .indInfo .. :: _, _, _, h => by
    simp [ConLeche.blockSplitCtors, ConLeche.blockSplitRecs] at h

theorem blockSplit_mem :
    ∀ {block : List ConLeche.ConstantInfo} {cvTs : List ConLeche.ConstantVal}
      {cs : List (ConLeche.ConstantVal × Nat × Nat)}
      {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
      ConLeche.blockSplit block = some (cvTs, cs, rs) →
      (∀ cv ∈ cvTs, ∃ caps, .indInfo cv caps ∈ block) ∧ (∀ c ∈ cs, ∃ T, .ctorInfo c.1 c.2.1 c.2.2 T ∈ block) ∧
        (∀ r ∈ rs, .recInfo r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∈ block)
  | .indInfo cvT caps :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hT, hc, hr⟩ := blockSplit_mem h'
    refine ⟨fun cv hcv => ?_, fun c hc' => ?_, fun r hr' => List.mem_cons_of_mem _ (hr r hr')⟩
    · rcases List.mem_cons.mp hcv with rfl | hcv
      · exact ⟨caps, List.mem_cons_self⟩
      · obtain ⟨c', hc''⟩ := hT cv hcv
        exact ⟨c', List.mem_cons_of_mem _ hc''⟩
    · obtain ⟨T, hT'⟩ := hc c hc'
      exact ⟨T, List.mem_cons_of_mem _ hT'⟩
  | [], cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, ConLeche.blockSplitCtors, ConLeche.blockSplitRecs, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨fun c hc => (nomatch hc), fun c hc => (nomatch hc), fun r hr => nomatch hr⟩
  | .ctorInfo cvC nP nF T :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨cs', rs'⟩, h', rfl, rfl, rfl⟩ := h
    obtain ⟨hc, hr⟩ := blockSplitCtors_mem h'
    exact ⟨fun c hc => (nomatch hc), hc, hr⟩
  | .recInfo cvR mI rP isK rules :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨cs', rs'⟩, h', rfl, rfl, rfl⟩ := h
    obtain ⟨hc, hr⟩ := blockSplitCtors_mem h'
    exact ⟨fun c hc => (nomatch hc), hc, hr⟩
  | .axiomInfo .. :: _, _, _, _, h | .defnInfo .. :: _, _, _, _, h | .thmInfo .. :: _, _, _, _, h => by
    simp [ConLeche.blockSplit, ConLeche.blockSplitCtors, ConLeche.blockSplitRecs] at h

theorem sum_map_eq_zero {α : Type} (f : α → Nat) : ∀ (l : List α), (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      sum_map_eq_zero f l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem sum_map_add' {α : Type} (f g : α → Nat) : ∀ (l : List α),
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_add' f g l]; omega

theorem sum_ind_le (v : Option Nat) : ∀ k : Nat,
    ((List.range k).map fun m => if (v == some m) = true then 1 else 0).sum ≤ 1
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append]
    have ih := sum_ind_le v k
    by_cases hv : v = some k
    · subst hv
      have h0 : ((List.range k).map fun m => if (some k == some m) = true then 1 else 0).sum = 0 :=
        sum_map_eq_zero _ _ (fun m hm => by
          have : m < k := List.mem_range.mp hm
          have hne : ¬ (some k == some m) = true := by simp; omega
          simp only [hne]; rfl)
      rw [h0]; simp
    · have hne : ¬ (v == some k) = true := by simpa using hv
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

/-- The constructors of all groups, counted, are at most the constructors. -/
theorem sum_filter_some_le {α : Type} (g : α → Option Nat) :
    ∀ (cs : List α) (k : Nat), ((List.range k).map fun m => (cs.filter fun c => g c == some m).length).sum ≤ cs.length
  | [], k => by
    rw [sum_map_eq_zero _ _ (fun m _ => by simp)]; simp
  | c :: cs, k => by
    have ih := sum_filter_some_le g cs k
    have hind := sum_ind_le (g c) k
    have e : ((List.range k).map fun m => ((c :: cs).filter fun c => g c == some m).length) =
        (List.range k).map fun m => (if (g c == some m) = true then 1 else 0) +
          (cs.filter fun c => g c == some m).length := by
      refine List.map_congr_left fun m _ => ?_
      rw [List.filter_cons]
      split <;> simp [Nat.add_comm]
    rw [e, sum_map_add']
    simp only [List.length_cons]
    omega

theorem sum_zip_le {α β : Type} (f : β → Nat) :
    ∀ (l : List α) (g : List β), ((l.zip g).map (fun a => f a.2)).sum ≤ (g.map f).sum
  | [], g => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: g => by
    have := sum_zip_le f l g
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    omega

theorem blockSplitRecs_len : ∀ {block : List ConLeche.ConstantInfo} {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplitRecs block = some rs → rs.length ≤ block.length
  | [], rs, h => by simp only [ConLeche.blockSplitRecs, Option.some.injEq] at h; subst h; simp
  | .recInfo cvR mI rP isK rules :: rest, rs, h => by
    simp only [ConLeche.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    have := blockSplitRecs_len h'
    simp only [List.length_cons]; omega
  | .axiomInfo .. :: _, _, h | .defnInfo .. :: _, _, h | .thmInfo .. :: _, _, h
  | .indInfo .. :: _, _, h | .ctorInfo .. :: _, _, h => nomatch h

theorem blockSplitCtors_len : ∀ {block : List ConLeche.ConstantInfo} {cs : List (ConLeche.ConstantVal × Nat × Nat)}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplitCtors block = some (cs, rs) → cs.length ≤ block.length
  | .ctorInfo cvC nP nF T :: rest, cs, rs, h => by
    simp only [ConLeche.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := blockSplitCtors_len h'
    simp only [List.length_cons]; omega
  | [], cs, rs, h => by
    simp only [ConLeche.blockSplitCtors, ConLeche.blockSplitRecs, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | .recInfo cvR mI rP isK rules :: rest, cs, rs, h => by
    simp only [ConLeche.blockSplitCtors, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨rs', h', rfl, rfl⟩ := h; simp
  | .axiomInfo .. :: _, _, _, h | .defnInfo .. :: _, _, _, h | .thmInfo .. :: _, _, _, h
  | .indInfo .. :: _, _, _, h => by
    simp [ConLeche.blockSplitCtors, ConLeche.blockSplitRecs] at h

theorem blockSplit_ctors_len : ∀ {block : List ConLeche.ConstantInfo} {cvTs : List ConLeche.ConstantVal}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplit block = some (cvTs, cs, rs) → cs.length ≤ block.length
  | .indInfo cvT caps :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have := blockSplit_ctors_len h'
    simp only [List.length_cons]; omega
  | [], cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, ConLeche.blockSplitCtors, ConLeche.blockSplitRecs, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; simp
  | .ctorInfo cvC nP nF T :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨cs', rs'⟩, h', rfl, rfl, rfl⟩ := h
    exact blockSplitCtors_len (block := .ctorInfo cvC nP nF T :: rest) h'
  | .recInfo cvR mI rP isK rules :: rest, cvTs, cs, rs, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨cs', rs'⟩, h', rfl, rfl, rfl⟩ := h
    exact blockSplitCtors_len (block := .recInfo cvR mI rP isK rules :: rest) h'
  | .axiomInfo .. :: _, _, _, _, h | .defnInfo .. :: _, _, _, _, h | .thmInfo .. :: _, _, _, _, h => by
    simp [ConLeche.blockSplit, ConLeche.blockSplitCtors, ConLeche.blockSplitRecs] at h

/-- **The pure reader's answer, by the block's records**: every member is an inductive record of
the block (at its own declared former), its index count read off a record's telescope or a recursor's
major index, its constructors constructor records, every recursor a recursor record. -/
theorem readBlock_records {nPd : Nat} {b : List ConLeche.ConstantInfo} {pP : ConLeche.BlockShape}
    (h : ConLeche.readBlock nPd b = .ok pP) :
    pP.nP = nPd ∧
    (∀ ms ∈ pP.members, (∃ caps, .indInfo ms.cvT caps ∈ b) ∧ ms.declared = ms.cvT ∧
      ((∃ caps, ∃ cv, .indInfo cv caps ∈ b ∧ ms.nIdx ≤ ConLeche.Frontend.indPiTeleLen cv.type) ∨
        ∃ cv mI rP isK rules, .recInfo cv mI rP isK rules ∈ b ∧ ms.nIdx ≤ mI) ∧
      ∀ c ∈ ms.ctors, ∃ nP T, .ctorInfo c.1 nP c.2 T ∈ b) ∧
    (∀ rc ∈ pP.recs, .recInfo rc.cvR rc.mI rc.rP rc.isK rc.rules ∈ b) ∧
    (pP.members.map (·.ctors.length)).sum ≤ b.length := by
  obtain ⟨hnP, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, hk, -, hnl, hbmc, -, hmem, hrecs⟩ :=
    ConLeche.readBlock_inv h
  obtain ⟨hT, hC, hR⟩ := blockSplit_mem hsp
  have hbnd := blockMemberCounts_bound cvTs 0 nIdxs hbmc
  refine ⟨hnP, fun ms hms => ?_, fun rc hrc => ?_, ?_⟩
  · rw [hmem] at hms
    obtain ⟨⟨⟨cvT, nIdx⟩, g⟩, ha, rfl⟩ := List.mem_map.mp hms
    obtain ⟨h1, h2⟩ := List.of_mem_zip ha
    obtain ⟨h3, h4⟩ := List.of_mem_zip h1
    refine ⟨hT cvT h3, rfl, ?_, fun c hc => ?_⟩
    · rcases hbnd nIdx h4 with ⟨cv, hcv, hle⟩ | ⟨q, hq, hle⟩
      · obtain ⟨caps, hcaps⟩ := hT cv hcv
        exact Or.inl ⟨caps, cv, hcaps, hle⟩
      · exact Or.inr ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, hR q hq, hle⟩
    · have := ConLeche.mem_blockGroups h2 hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp this
      obtain ⟨T, hT'⟩ := hC c' hc'
      exact ⟨c'.2.1, T, hT'⟩
  · rw [hrecs] at hrc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrc
    exact hR r hr
  · have hlen : cs.length ≤ b.length := blockSplit_ctors_len hsp
    rw [hmem, List.map_map]
    refine Nat.le_trans (sum_zip_le (fun g : List (ConLeche.ConstantVal × Nat) => g.length) _ _) ?_
    refine Nat.le_trans ?_ hlen
    unfold ConLeche.blockGroups
    split
    · simp
    · rw [List.map_map]
      exact Nat.le_trans (sum_filter_some_le _ _ _) (by simp)


/-! ## A denoted block's records -/

theorem denoteCIList_mem {st : EStore} : ∀ {block : List IConstantInfo} {b : List ConLeche.ConstantInfo},
    Frontend.denoteCIList st block = some b → ∀ c ∈ b, ∃ ci ∈ block, Frontend.denoteCI st ci = some c
  | [], b, h, c, hc => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at h; subst h; exact absurd hc List.not_mem_nil
  | ci :: cis, b, h, c, hc => by
    simp only [Frontend.denoteCIList] at h
    cases h1 : Frontend.denoteCI st ci with
    | none => rw [h1] at h; exact nomatch h
    | some x =>
    cases h2 : Frontend.denoteCIList st cis with
    | none => rw [h1, h2] at h; exact nomatch h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨ci, List.mem_cons_self, h1⟩
    · obtain ⟨ci', hci', hd⟩ := denoteCIList_mem h2 c hc
      exact ⟨ci', List.mem_cons_of_mem _ hci', hd⟩

theorem denoteCIList_length {st : EStore} : ∀ {block : List IConstantInfo} {b : List ConLeche.ConstantInfo},
    Frontend.denoteCIList st block = some b → block.length = b.length
  | [], b, h => by simp only [Frontend.denoteCIList, Option.some.injEq] at h; subst h; rfl
  | ci :: cis, b, h => by
    simp only [Frontend.denoteCIList] at h
    cases h1 : Frontend.denoteCI st ci with
    | none => rw [h1] at h; exact nomatch h
    | some x =>
    cases h2 : Frontend.denoteCIList st cis with
    | none => rw [h1, h2] at h; exact nomatch h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    simp [denoteCIList_length h2]

theorem denoteCI_toCV {st : EStore} {ci : IConstantInfo} {c : ConLeche.ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) : Frontend.denoteCV st ci.toConstantVal = some c.toConstantVal := by
  cases ci with
  | axiomInfo v =>
    cases h1 : Frontend.denoteCV st v <;> simp only [Frontend.denoteCI, h1, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at h
    subst h; exact h1
  | thmInfo v =>
    cases h1 : Frontend.denoteCV st v <;> simp only [Frontend.denoteCI, h1, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at h
    subst h; exact h1
  | defnInfo v e hh =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : denoteE st e <;>
      simp only [Frontend.denoteCI, h1, h2, reduceCtorEq, Option.some.injEq] at h
    subst h; exact h1
  | indInfo v cp =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : Frontend.denoteCaps st cp <;>
      simp only [Frontend.denoteCI, h1, h2, reduceCtorEq, Option.some.injEq] at h
    subst h; exact h1
  | ctorInfo v nP nF T =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : denoteN st.ns T <;>
      simp only [Frontend.denoteCI, h1, h2, reduceCtorEq, Option.some.injEq] at h
    subst h; exact h1
  | recInfo v mI rP k rs =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : Frontend.denoteRules st rs <;>
      simp only [Frontend.denoteCI, h1, h2, reduceCtorEq, Option.some.injEq] at h
    subst h; exact h1

theorem denoteCI_ctor {st : EStore} {ci : IConstantInfo} {cv : ConLeche.ConstantVal} {nP nF : Nat}
    {T : ConLeche.Name} (h : Frontend.denoteCI st ci = some (.ctorInfo cv nP nF T)) :
    ∃ v iT, ci = .ctorInfo v nP nF iT := by
  cases ci with
  | axiomInfo v =>
    cases h1 : Frontend.denoteCV st v <;> simp [Frontend.denoteCI, h1] at h
  | thmInfo v =>
    cases h1 : Frontend.denoteCV st v <;> simp [Frontend.denoteCI, h1] at h
  | defnInfo v e hh =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : denoteE st e <;> simp [Frontend.denoteCI, h1, h2] at h
  | indInfo v cp =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : Frontend.denoteCaps st cp <;> simp [Frontend.denoteCI, h1, h2] at h
  | ctorInfo v nP' nF' T' =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : denoteN st.ns T' <;>
      simp only [Frontend.denoteCI, h1, h2, reduceCtorEq, Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at h
    obtain ⟨-, rfl, rfl, -⟩ := h
    exact ⟨v, T', rfl⟩
  | recInfo v mI rP k rs =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : Frontend.denoteRules st rs <;> simp [Frontend.denoteCI, h1, h2] at h

theorem denoteRules_length {st : EStore} : ∀ {rs : List IRecRule} {rsP : List ConLeche.RecRule},
    Frontend.denoteRules st rs = some rsP → rs.length = rsP.length
  | [], rsP, h => by simp only [Frontend.denoteRules, Option.some.injEq] at h; subst h; rfl
  | r :: rs, rsP, h => by
    simp only [Frontend.denoteRules] at h
    cases h1 : Frontend.denoteRule st r with
    | none => rw [h1] at h; exact nomatch h
    | some x =>
    cases h2 : Frontend.denoteRules st rs with
    | none => rw [h1, h2] at h; exact nomatch h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    simp [denoteRules_length h2]

theorem denoteCI_rec {st : EStore} {ci : IConstantInfo} {cv : ConLeche.ConstantVal} {mI rP : Nat} {k : Bool}
    {rules : List ConLeche.RecRule} (h : Frontend.denoteCI st ci = some (.recInfo cv mI rP k rules)) :
    ∃ v rs, ci = .recInfo v mI rP k rs ∧ rs.length = rules.length := by
  cases ci with
  | axiomInfo v =>
    cases h1 : Frontend.denoteCV st v <;> simp [Frontend.denoteCI, h1] at h
  | thmInfo v =>
    cases h1 : Frontend.denoteCV st v <;> simp [Frontend.denoteCI, h1] at h
  | defnInfo v e hh =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : denoteE st e <;> simp [Frontend.denoteCI, h1, h2] at h
  | indInfo v cp =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : Frontend.denoteCaps st cp <;> simp [Frontend.denoteCI, h1, h2] at h
  | ctorInfo v nP' nF' T' =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : denoteN st.ns T' <;> simp [Frontend.denoteCI, h1, h2] at h
  | recInfo v mI' rP' k' rs =>
    cases h1 : Frontend.denoteCV st v <;> cases h2 : Frontend.denoteRules st rs <;>
      simp only [Frontend.denoteCI, h1, h2, reduceCtorEq, Option.some.injEq, ConLeche.ConstantInfo.recInfo.injEq] at h
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨v, rs, rfl, denoteRules_length h2⟩

theorem denoteNList_length {ns : NStore} : ∀ {xs : List NIdx} {ys : List ConLeche.Name},
    Frontend.denoteNList ns xs = some ys → xs.length = ys.length
  | [], ys, h => by simp only [Frontend.denoteNList, Option.some.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN ns x with
    | none => rw [h1] at h; exact nomatch h
    | some y =>
    cases h2 : Frontend.denoteNList ns xs with
    | none => rw [h1, h2] at h; exact nomatch h
    | some ys' =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    simp [denoteNList_length h2]

theorem denoteNList_get {ns : NStore} : ∀ {xs : List NIdx} {ys : List ConLeche.Name},
    Frontend.denoteNList ns xs = some ys → ∀ j (hj : j < xs.length) (hj' : j < ys.length), denoteN ns xs[j] = some ys[j]
  | [], ys, h, j, hj, _ => absurd hj (by simp)
  | x :: xs, ys, h, j, hj, hj' => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN ns x with
    | none => rw [h1] at h; exact nomatch h
    | some y =>
    cases h2 : Frontend.denoteNList ns xs with
    | none => rw [h1, h2] at h; exact nomatch h
    | some ys' =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    cases j with
    | zero => simpa using h1
    | succ j => simpa using denoteNList_get h2 j (by simpa using hj) (by simpa using hj')

/-! ## The projection tables con-leche reads off a block -/

theorem structCtor_mem {ms : ConLeche.MemberShape} {c : ConLeche.ConstantVal × Nat}
    (h : ms.structCtor? = some c) : c ∈ ms.ctors := by
  unfold ConLeche.MemberShape.structCtor? at h
  split at h
  · rename_i c' hc
    split at h
    · cases h; rw [hc]; exact List.mem_singleton_self _
    · cases h
  · cases h

theorem blockTables_mem {pP : ConLeche.BlockShape} :
    ∀ (ms : List ConLeche.MemberShape) (q : List ConLeche.ProjTable), ConLeche.blockTables pP ms = some q →
      ∀ t ∈ q, t.levelParams = pP.lps ∧ t.numParams = pP.nP ∧ ∃ m ∈ ms, ∃ c ∈ m.ctors, t.numFields = c.2
  | [], q, h, t, ht => by
    simp only [ConLeche.blockTables, Option.some.injEq] at h; subst h; exact absurd ht List.not_mem_nil
  | m :: ms, q, h, t, ht => by
    simp only [ConLeche.blockTables] at h
    cases hc : m.structCtor? with
    | none =>
      rw [hc] at h
      obtain ⟨h1, h2, m', hm', h3⟩ := blockTables_mem ms q h t ht
      exact ⟨h1, h2, m', List.mem_cons_of_mem _ hm', h3⟩
    | some c =>
      rw [hc] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨bodies, -, q', hq', rfl⟩ := h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨rfl, rfl, m, List.mem_cons_self, c, structCtor_mem hc, rfl⟩
      · obtain ⟨h1, h2, m', hm', h3⟩ := blockTables_mem ms q' hq' t ht
        exact ⟨h1, h2, m', List.mem_cons_of_mem _ hm', h3⟩

theorem denoteProjTableList_mem {st : EStore} : ∀ {Q : List IProjTable} {q : List ConLeche.ProjTable},
    Frontend.denoteProjTableList st Q = some q → ∀ t ∈ Q, ∃ pt ∈ q, Frontend.denoteProjTable st t = some pt
  | [], q, h, t, ht => absurd ht List.not_mem_nil
  | t0 :: ts, q, h, t, ht => by
    simp only [Frontend.denoteProjTableList] at h
    cases h1 : Frontend.denoteProjTable st t0 with
    | none => rw [h1] at h; exact nomatch h
    | some x =>
    cases h2 : Frontend.denoteProjTableList st ts with
    | none => rw [h1, h2] at h; exact nomatch h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨x, List.mem_cons_self, h1⟩
    · obtain ⟨pt, hpt, hd⟩ := denoteProjTableList_mem h2 t ht
      exact ⟨pt, List.mem_cons_of_mem _ hpt, hd⟩

theorem denoteProjTable_parts {st : EStore} {t : IProjTable} {pt : ConLeche.ProjTable}
    (h : Frontend.denoteProjTable st t = some pt) :
    Frontend.denoteNList st.ns t.levelParams = some pt.levelParams ∧ t.numParams = pt.numParams ∧
      t.numFields = pt.numFields ∧ (Frontend.denoteEList st t.bodies.toList).isSome := by
  simp only [Frontend.denoteProjTable] at h
  cases h1 : denoteN st.ns t.structName <;> cases h2 : Frontend.denoteNList st.ns t.levelParams <;>
    cases h3 : denoteN st.ns t.ctor <;> simp only [h1, h2, h3, reduceCtorEq] at h
  simp only [Frontend.denoteEArray] at h
  cases h4 : Frontend.denoteEList st t.bodies.toList <;> simp only [h4, reduceCtorEq, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem denoteEList_get {st : EStore} : ∀ {xs : List EIdx} {ys : List ConLeche.Expr},
    Frontend.denoteEList st xs = some ys → ∀ x ∈ xs, (denoteE st x).isSome = true
  | [], ys, h, x, hx => absurd hx List.not_mem_nil
  | a :: xs, ys, h, x, hx => by
    simp only [Frontend.denoteEList] at h
    cases h1 : denoteE st a with
    | none => rw [h1] at h; exact nomatch h
    | some y =>
    cases h2 : Frontend.denoteEList st xs with
    | none => rw [h1, h2] at h; exact nomatch h
    | some ys' =>
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [h1]; rfl
    · exact denoteEList_get h2 x hx

end ConPanqueque.T.Ind
