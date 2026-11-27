import ConRon.Arena.Frontend.ExportC

/-! # The twin's inductive record, on the success path

A pure twin-level lemma (no Pancake): `processLineCoreD st (.ind [t] cts [r])` pushes the block
`indBlockD st t cts r T` when the record's indices are bound and its redundant fields agree.  The two
`for` loops of `validateIndD` are split into named `forIn`s (`IndTwin.validateIndD_unfold`, by `rfl`),
transcribed from `ConRon.Refine2.Frontend.SpecInd` (not imported). -/

open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConLeche.Frontend (IdTable CVRec RuleRec DeclRec IndTypeRec IndCtorRec IndRecRec)

set_option autoImplicit false
set_option backward.do.legacy true

/-- A declaration's common data, read through the tables. -/
def cvOfD (st : StateD) (cv : CVRec) : IConstantVal :=
  ⟨(st.names.get? cv.name).getD default, cv.levelParams.map (fun x => (st.names.get? x).getD default),
    (st.exprs.get? cv.type).getD default⟩

/-- A recursor rule, read through the tables. -/
def ruleOfD (st : StateD) (ru : RuleRec) : IRecRule :=
  ⟨(st.names.get? ru.ctor).getD default, ru.nfields, .plain, (st.exprs.get? ru.rhs).getD default⟩

/-- The block a one-type inductive record installs. -/
def indBlockD (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (T : NIdx) :
    List IConstantInfo :=
  [.indInfo (cvOfD st t.cv) {}] ++ cts.map (fun c => .ctorInfo (cvOfD st c.cv) c.numParams c.numFields T) ++
  [.recInfo (cvOfD st r.cv) (r.numParams + r.numMotives + r.numMinors + r.numIndices)
    (r.numParams + r.numMotives + r.numMinors) r.k (r.rules.map (ruleOfD st))]

namespace IndTwin

/-! ## `validateIndD`'s loops, transcribed (from `ConRon.Refine2.Frontend.SpecInd`) -/

abbrev VRes := RecordVerdict ⊕ (List (IndCtorRec × NIdx) × Nat)

def orderCtorStepD (st : StateD) (fuel : Nat) (T : NIdx)
    (ctorIx : Std.HashMap NIdx Nat) (ctsA : Array IndCtorRec) (nPd : Nat)
    (n : NIdx) (j : Nat) (ordered : Array (IndCtorRec × NIdx)) :
    AM (ForInStep (MProd (Option VRes) (MProd Nat (Array (IndCtorRec × NIdx))))) := do
  let some k := ctorIx[n]? | return .done ⟨some (.inl (.invalid
    s!"No such constructor {← readName n}")), j, ordered⟩
  let some c := ctsA[k]? | return .done ⟨some (.inl (.invalid
    s!"No such constructor {← readName n}")), j, ordered⟩
  if let some ci := c.cidx then
    unless ci == j do
      return .done ⟨some (.inl (.invalid s!"constructor {← readName n} declares cidx {ci}; \
        it is constructor {j} of {← readName T}")), j, ordered⟩
  if let some iw := c.induct then
    let iwn ← st.name iw
    unless iwn == T do
      return .done ⟨some (.inl (.invalid s!"constructor {← readName n} declares induct \
        {← readName iwn}; it is a constructor of {← readName T}")), j, ordered⟩
  let cty ← getDeclD st c.cv.type
  let tele ← indPiTeleLen fuel cty
  unless nPd + c.numFields == tele do
    return .done ⟨some (.inl (.invalid s!"constructor {← readName n} declares \
      {c.numFields} fields at {nPd} parameters; its type has {tele} binders")), j, ordered⟩
  pure (.yield ⟨none, j + 1, ordered.push (c, T)⟩)

def orderTypeCtorsD (st : StateD) (fuel : Nat) (T : NIdx)
    (ctorIx : Std.HashMap NIdx Nat) (ctsA : Array IndCtorRec) (nPd : Nat)
    (ns : List NIdx) (j : Nat) (out : Array (IndCtorRec × NIdx)) :
    AM (MProd (Option VRes) (MProd Nat (Array (IndCtorRec × NIdx)))) :=
  forIn ns ⟨none, j, out⟩ fun n r => orderCtorStepD st fuel T ctorIx ctsA nPd n r.2.1 r.2.2

def orderBlockStepD (st : StateD) (fuel : Nat) (ctorIx : Std.HashMap NIdx Nat)
    (ctsA : Array IndCtorRec) (nPd : Nat) (tn : NIdx × List NIdx) (out : Array (IndCtorRec × NIdx)) :
    AM (ForInStep (MProd (Option VRes) (Array (IndCtorRec × NIdx)))) :=
  match tn with
  | (T, ns) => do
    let r ← orderTypeCtorsD st fuel T ctorIx ctsA nPd ns 0 out
    match r.2 with
    | ⟨_, ordered⟩ =>
      match r.1 with
      | none => pure (.yield ⟨none, ordered⟩)
      | some a => pure (.done ⟨some a, ordered⟩)

def orderBlockCtorsD (st : StateD) (fuel : Nat) (ctorIx : Std.HashMap NIdx Nat)
    (ctsA : Array IndCtorRec) (nPd : Nat) (l : List (NIdx × List NIdx))
    (out : Array (IndCtorRec × NIdx)) : AM (MProd (Option VRes) (Array (IndCtorRec × NIdx))) :=
  forIn l ⟨none, out⟩ fun tn r => orderBlockStepD st fuel ctorIx ctsA nPd tn r.2

def recIndexStepD (fuel : Nat) (rn T : NIdx) (numIndices nPd : Nat) (tt : NIdx × EIdx) :
    AM (ForInStep (MProd (Option VRes) PUnit)) := do
  if tt.1 == T then
    match ← piSortTeleLen? fuel tt.2 with
    | some n =>
      if nPd + numIndices == n then pure (.yield ⟨none, PUnit.unit⟩)
      else
        pure (.done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares \
          {numIndices} indices; {← readName T} has {n - nPd} at {nPd} parameters")),
          PUnit.unit⟩)
    | none => pure (.yield ⟨none, PUnit.unit⟩)
  else pure (.yield ⟨none, PUnit.unit⟩)

def checkRecIndicesD (fuel : Nat) (rn T : NIdx) (numIndices nPd : Nat)
    (l : List (NIdx × EIdx)) : AM (MProd (Option VRes) PUnit) :=
  forIn l ⟨none, PUnit.unit⟩ fun tt _ => recIndexStepD fuel rn T numIndices nPd tt

def recStepD (st : StateD) (fuel : Nat) (tyNames : List NIdx) (tyTypes : List EIdx)
    (nPd nTypes nCtors : Nat) (r : IndRecRec) :
    AM (ForInStep (MProd (Option VRes) PUnit)) := do
  let rn ← st.name r.cv.name
  unless r.numParams == nPd do
    return .done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares {r.numParams} \
      parameters; the block declares {nPd}")), PUnit.unit⟩
  unless r.numMotives == nTypes do
    return .done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares {r.numMotives} \
      motives; the block has {nTypes} inductive types")), PUnit.unit⟩
  unless r.numMinors == nCtors do
    return .done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares {r.numMinors} \
      minor premises; the block has {nCtors} constructors")), PUnit.unit⟩
  match ← viewN rn with
  | .str T "rec" =>
    let r ← checkRecIndicesD fuel rn T r.numIndices nPd (tyNames.zip tyTypes)
    match r.1 with
    | none => pure (.yield ⟨none, PUnit.unit⟩)
    | some a => pure (.done ⟨some a, PUnit.unit⟩)
  | _ => pure (.yield ⟨none, PUnit.unit⟩)

def checkRecRecordsD (st : StateD) (fuel : Nat) (tyNames : List NIdx) (tyTypes : List EIdx)
    (nPd nTypes nCtors : Nat) (rcs : List IndRecRec) :
    AM (MProd (Option VRes) PUnit) :=
  forIn rcs ⟨none, PUnit.unit⟩ fun r _ =>
    recStepD st fuel tyNames tyTypes nPd nTypes nCtors r

theorem validateIndD_unfold (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) :
    validateIndD st tys cts rcs = (do
      if tys.any (·.isUnsafe) then
        return .inl (.declined "unsafe inductive declaration")
      let nPs := tys.map (·.numParams)
      let nPd := nPs.head?.getD 0
      unless nPs.all (· == nPd) do
        return .inl (.declined "inductive block whose type records disagree on numParams")
      let tyNames ← tys.mapM fun t => st.name t.cv.name
      let tyTypes ← tys.mapM fun t => getDeclD st t.cv.type
      let listed ← tys.mapM fun t => t.ctors.mapM st.name
      let ctorNames ← cts.mapM fun c => st.name c.cv.name
      let flat := listed.flatten
      unless flat.Nodup do
        return .inl (.invalid "duplicate constructor name in an inductive type's ctors")
      unless flat.length == cts.length do
        return .inl (.invalid s!"the inductive block lists {flat.length} constructors \
          and carries {cts.length} constructor records")
      let ctorIx : Std.HashMap NIdx Nat :=
        (ctorNames.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
          (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1
      let fuel ← storeFuel
      let r ← orderBlockCtorsD st fuel ctorIx cts.toArray nPd (tyNames.zip listed) #[]
      match r.1 with
      | none =>
        let ctsO := r.2.toList
        let r2 ← checkRecRecordsD st fuel tyNames tyTypes nPd tys.length ctsO.length
          (if tys.any (·.numNested != 0) then [] else rcs)
        match r2.1 with
        | none => pure (.inr (ctsO, nPd))
        | some a => pure a
      | some a => pure a) := by
  rfl

/-! ## Monadic plumbing -/

theorem bind_ok {α β : Type} (x : AM α) (g : α → AM β) (s : AState) (a : α)
    (h : x s = .ok (a, s)) : (x >>= g) s = g a s := by
  show StateT.bind x g s = _
  simp only [StateT.bind, h]
  rfl

theorem pure_run {α : Type} (a : α) (s : AState) : (pure a : AM α) s = .ok (a, s) := rfl

theorem step_ok (st : StateD) (s : AState) (T : NIdx) (ctorIx : Std.HashMap NIdx Nat)
    (cts : List IndCtorRec) (nPd : Nat) (n : NIdx) (k : Nat) (hk : k < cts.length)
    (acc : Array (IndCtorRec × NIdx)) (hix : ctorIx[n]? = some k)
    (hcidx : cts[k].cidx = none ∨ cts[k].cidx = some k)
    (hind : ∀ iw, cts[k].induct = some iw → st.names.get? iw = some T)
    (htele : ∃ ch, st.exprs.get? cts[k].cv.type = some ch ∧
      indPiTeleLen (s.store.nodeCount + 1) ch s = .ok (nPd + cts[k].numFields, s)) :
    orderCtorStepD st (s.store.nodeCount + 1) T ctorIx cts.toArray nPd n k acc s =
      .ok (.yield ⟨none, k + 1, acc.push (cts[k], T)⟩, s) := by
  obtain ⟨ch, hch, ht⟩ := htele
  have hc : cts.toArray[k]? = some cts[k] := by simp [hk]
  unfold orderCtorStepD
  simp only [hix, hc]
  generalize cts[k] = c at hcidx hind hch ht ⊢
  rcases c with ⟨cv, isU, nF, nP, cidx, induct⟩
  simp only at hcidx hind hch ht ⊢
  have hd : getDeclD st cv.type = pure ch := by simp [getDeclD, StateD.expr, hch]
  rcases hcidx with rfl | rfl <;> rcases induct with _ | iw
  all_goals first
    | (have hn : st.name iw = pure T := by simp [StateD.name, hind iw rfl]
       simp only [hd, hn, pure_bind, beq_self_eq_true, ↓reduceIte])
    | simp only [hd, pure_bind, beq_self_eq_true, ↓reduceIte]
  all_goals (rw [bind_ok _ _ s _ ht]; simp only [beq_self_eq_true, ↓reduceIte]; rfl)

theorem inner_ok (st : StateD) (s : AState) (T : NIdx) (ctorIx : Std.HashMap NIdx Nat)
    (cts : List IndCtorRec) (nPd : Nat) (ns : List NIdx) (hns : ns.length = cts.length)
    (hix : ∀ j (hj : j < cts.length), ctorIx[ns[j]'(by omega)]? = some j)
    (hcidx : ∀ j (hj : j < cts.length), cts[j].cidx = none ∨ cts[j].cidx = some j)
    (hind : ∀ j (hj : j < cts.length) iw, cts[j].induct = some iw → st.names.get? iw = some T)
    (htele : ∀ j (hj : j < cts.length), ∃ ch, st.exprs.get? cts[j].cv.type = some ch ∧
      indPiTeleLen (s.store.nodeCount + 1) ch s = .ok (nPd + cts[j].numFields, s)) :
    ∀ d k (acc : Array (IndCtorRec × NIdx)), k + d = cts.length →
      orderTypeCtorsD st (s.store.nodeCount + 1) T ctorIx cts.toArray nPd (ns.drop k) k acc s =
        .ok (⟨none, cts.length, acc ++ ((cts.drop k).map (·, T)).toArray⟩, s) := by
  intro d
  induction d with
  | zero =>
    intro k acc hk
    have h1 : ns.drop k = [] := by simp; omega
    have h2 : cts.drop k = [] := by simp; omega
    simp only [orderTypeCtorsD, h1, h2, List.forIn_nil]
    simp only [Nat.add_zero] at hk
    subst hk
    simp [pure_run]
  | succ d ih =>
    intro k acc hk
    have hkl : k < cts.length := by omega
    rw [List.drop_eq_getElem_cons (by omega : k < ns.length), List.drop_eq_getElem_cons hkl]
    unfold orderTypeCtorsD
    rw [List.forIn_cons]
    dsimp only
    rw [bind_ok _ _ s _ (step_ok st s T ctorIx cts nPd _ k hkl acc (hix k hkl) (hcidx k hkl) (hind k hkl)
      (htele k hkl))]
    have := ih (k + 1) (acc.push (cts[k], T)) (by omega)
    unfold orderTypeCtorsD at this
    dsimp only
    rw [this]
    have ha : acc.push (cts[k], T) ++ ((cts.drop (k + 1)).map (·, T)).toArray =
        acc ++ ((cts[k] :: cts.drop (k + 1)).map (·, T)).toArray := by
      apply Array.toList_inj.mp
      simp only [Array.toList_append, Array.toList_push, List.map_cons,
        List.append_assoc, List.singleton_append]
    rw [ha]

theorem outer_ok (st : StateD) (s : AState) (fuel : Nat) (ctorIx : Std.HashMap NIdx Nat)
    (ctsA : Array IndCtorRec) (nPd : Nat) (T : NIdx) (ns : List NIdx) (m : Nat)
    (out : Array (IndCtorRec × NIdx))
    (h : orderTypeCtorsD st fuel T ctorIx ctsA nPd ns 0 #[] s = .ok (⟨none, m, out⟩, s)) :
    orderBlockCtorsD st fuel ctorIx ctsA nPd [(T, ns)] #[] s = .ok (⟨none, out⟩, s) := by
  have hs : orderBlockStepD st fuel ctorIx ctsA nPd (T, ns) #[] s = .ok (.yield ⟨none, out⟩, s) := by
    unfold orderBlockStepD
    dsimp only
    rw [bind_ok _ _ s _ h]
    rfl
  unfold orderBlockCtorsD
  rw [List.forIn_cons]
  dsimp only
  rw [bind_ok _ _ s _ hs]
  rfl

theorem recIndex_ok (fuel : Nat) (rn T' : NIdx) (ni nPd : Nat) (T : NIdx) (tyh : EIdx) (s : AState)
    (hidx : ∃ o, piSortTeleLen? fuel tyh s = .ok (o, s) ∧ ∀ n, o = some n → nPd + ni = n) :
    recIndexStepD fuel rn T' ni nPd (T, tyh) s = .ok (.yield ⟨none, PUnit.unit⟩, s) := by
  obtain ⟨o, ho, hn⟩ := hidx
  unfold recIndexStepD
  dsimp only
  split
  · rw [bind_ok _ _ s _ ho]
    rcases o with _ | n
    · rfl
    · simp only [hn n rfl, beq_self_eq_true, ↓reduceIte]
      rfl
  · rfl

theorem rec_ok (st : StateD) (s : AState) (T : NIdx) (tyh : EIdx) (nPd nCtors : Nat) (r : IndRecRec)
    (rn : NIdx) (hrn : st.names.get? r.cv.name = some rn) (hview : (s.store.ns.view rn).isSome)
    (hrp : r.numParams = nPd) (hrm : r.numMotives = 1) (hrmin : r.numMinors = nCtors)
    (hidx : ∃ o, piSortTeleLen? (s.store.nodeCount + 1) tyh s = .ok (o, s) ∧
      ∀ n, o = some n → nPd + r.numIndices = n) :
    checkRecRecordsD st (s.store.nodeCount + 1) [T] [tyh] nPd 1 nCtors [r] s =
      .ok (⟨none, PUnit.unit⟩, s) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hview
  have hvn : viewN rn s = .ok (v, s) := by
    unfold viewN
    rw [bind_ok _ _ s s rfl]
    simp only [hv]
    rfl
  have hs : recStepD st (s.store.nodeCount + 1) [T] [tyh] nPd 1 nCtors r s =
      .ok (.yield ⟨none, PUnit.unit⟩, s) := by
    unfold recStepD
    simp only [StateD.name, hrn, hrp, hrm, hrmin, beq_self_eq_true, ↓reduceIte, pure_bind]
    rw [bind_ok _ _ s _ hvn]
    split
    · rename_i _ T'
      simp only [List.zip_cons_cons, List.zip_nil_left]
      have hc : checkRecIndicesD (s.store.nodeCount + 1) rn T' r.numIndices nPd [(T, tyh)] s =
          .ok (⟨none, PUnit.unit⟩, s) := by
        unfold checkRecIndicesD
        rw [List.forIn_cons]
        rw [bind_ok _ _ s _ (recIndex_ok _ _ _ _ _ _ _ s hidx)]
        rfl
      rw [bind_ok _ _ s _ hc]
      rfl
    · rfl
  unfold checkRecRecordsD
  rw [List.forIn_cons]
  rw [bind_ok _ _ s _ hs]
  rfl

/-! ## Reading through the tables -/

theorem mapM_pure_of {α β : Type} (f : α → AM β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = pure (g x)) → l.mapM f = pure (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, h x (by simp), mapM_pure_of f g xs (fun y hy => h y (by simp [hy]))]
    simp

theorem name_ok (st : StateD) (x : Nat) (h : (st.names.get? x).isSome) :
    st.name x = pure ((st.names.get? x).getD default) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  simp [StateD.name, hv]

theorem expr_ok (st : StateD) (x : Nat) (h : (st.exprs.get? x).isSome) :
    getDeclD st x = pure ((st.exprs.get? x).getD default) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  simp [getDeclD, StateD.expr, hv]

theorem parseCVD_ok (st : StateD) (cv : CVRec) (hn : (st.names.get? cv.name).isSome)
    (ht : (st.exprs.get? cv.type).isSome) (hlp : ∀ x ∈ cv.levelParams, (st.names.get? x).isSome) :
    parseCVD st cv = pure (cvOfD st cv) := by
  have hm := mapM_pure_of st.name (fun x => (st.names.get? x).getD default) cv.levelParams
    (fun x hx => name_ok st x (hlp x hx))
  simp [parseCVD, name_ok st _ hn, expr_ok st _ ht, hm, cvOfD]

theorem parseRuleD_ok (st : StateD) (ru : RuleRec) (hn : (st.names.get? ru.ctor).isSome)
    (ht : (st.exprs.get? ru.rhs).isSome) : parseRuleD st ru = pure (ruleOfD st ru) := by
  simp [parseRuleD, name_ok st _ hn, expr_ok st _ ht, ruleOfD]

theorem mapM_name_idx {α : Type} (st : StateD) (f : α → Nat) :
    ∀ (l : List α) (ns : List NIdx) (hl : l.length = ns.length),
      (∀ j (hj : j < l.length), st.names.get? (f l[j]) = some (ns[j]'(by omega))) →
        l.mapM (fun a => st.name (f a)) = pure ns
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: xs, n :: ns', hl, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [List.mapM_cons, mapM_name_idx st f xs ns' (by simpa using hl)
      (fun j hj => by
        have := h (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        exact this)]
    simp [StateD.name, h0]

theorem fold_ix_notin (l : List NIdx) : ∀ (m : Std.HashMap NIdx Nat) (k : Nat) (y : NIdx), y ∉ l →
    (l.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n => (mi.1.insert n mi.2, mi.2 + 1)) (m, k)).1[y]? =
      m[y]? := by
  induction l with
  | nil => intros; rfl
  | cons x xs ih =>
    intro m k y hy
    simp only [List.foldl_cons]
    rw [ih _ _ _ (fun h => hy (List.mem_cons_of_mem _ h)), Std.HashMap.getElem?_insert]
    have : (x == y) = false := by
      simp only [beq_eq_false_iff_ne]
      intro h
      exact hy (h ▸ List.mem_cons_self ..)
    simp [this]

theorem fold_ix (l : List NIdx) (hl : l.Nodup) : ∀ (m : Std.HashMap NIdx Nat) (k j : Nat) (hj : j < l.length),
    (l.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n => (mi.1.insert n mi.2, mi.2 + 1)) (m, k)).1[l[j]]? =
      some (k + j) := by
  induction l with
  | nil => intro _ _ j hj; simp at hj
  | cons x xs ih =>
    intro m k j hj
    rw [List.nodup_cons] at hl
    simp only [List.foldl_cons]
    rcases j with _ | j
    · simp only [List.getElem_cons_zero]
      rw [fold_ix_notin _ _ _ _ hl.1, Std.HashMap.getElem?_insert]
      simp
    · simp only [List.getElem_cons_succ]
      rw [ih hl.2 _ _ j (by simpa using hj)]
      congr 1
      omega

theorem install_ok (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (T : NIdx)
    (nPd : Nat) (hTn : (st.names.get? t.cv.name).isSome) (hTt : (st.exprs.get? t.cv.type).isSome)
    (hlpT : ∀ x ∈ t.cv.levelParams, (st.names.get? x).isSome)
    (hlpC : ∀ c ∈ cts, ∀ x ∈ c.cv.levelParams, (st.names.get? x).isSome)
    (hlpR : ∀ x ∈ r.cv.levelParams, (st.names.get? x).isSome)
    (hcn : ∀ c ∈ cts, (st.names.get? c.cv.name).isSome)
    (hcty : ∀ c ∈ cts, (st.exprs.get? c.cv.type).isSome)
    (hrn : (st.names.get? r.cv.name).isSome) (hrty : (st.exprs.get? r.cv.type).isSome)
    (hrules : ∀ ru ∈ r.rules, (st.names.get? ru.ctor).isSome ∧ (st.exprs.get? ru.rhs).isSome) :
    installIndD st [t] (cts.map (·, T)) [r] nPd =
      pure { st with decls := st.decls.push (.indDecl (indBlockD st t cts r T) nPd) } := by
  have h1 := parseCVD_ok st t.cv hTn hTt hlpT
  have h3 := parseCVD_ok st r.cv hrn hrty hlpR
  have hru := mapM_pure_of (parseRuleD st) (ruleOfD st) r.rules
    (fun ru hru => parseRuleD_ok st ru (hrules ru hru).1 (hrules ru hru).2)
  unfold installIndD
  simp only [List.mapM_cons, List.mapM_nil, h1, h3, hru, pure_bind]
  rw [mapM_pure_of _ (fun p => IConstantInfo.ctorInfo (cvOfD st p.1.cv) p.1.numParams p.1.numFields p.2) _
    (by
      intro p hp
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
      simp [parseCVD_ok st c.cv (hcn c hc) (hcty c hc) (hlpC c hc)])]
  simp [pushDecl, indBlockD, Function.comp_def]

end IndTwin

open IndTwin in
theorem processInd_ok (st : StateD) (s : AState) (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec)
    (T : NIdx) (tyh : EIdx) (rn : NIdx) (ns : List NIdx)
    (hu : t.isUnsafe = false) (hnest : t.numNested = 0)
    (hT : st.names.get? t.cv.name = some T) (hty : st.exprs.get? t.cv.type = some tyh)
    (hlpT : ∀ x ∈ t.cv.levelParams, (st.names.get? x).isSome)
    (hlpC : ∀ c ∈ cts, ∀ x ∈ c.cv.levelParams, (st.names.get? x).isSome)
    (hlpR : ∀ x ∈ r.cv.levelParams, (st.names.get? x).isSome)
    (hlen : t.ctors.length = cts.length) (hns : ns.length = cts.length)
    (hnl : ∀ j (hj : j < cts.length), st.names.get? (t.ctors[j]'(by omega)) = some (ns[j]'(by omega)) ∧
      st.names.get? cts[j].cv.name = some (ns[j]'(by omega)))
    (hnd : ns.Nodup)
    (hcidx : ∀ j (hj : j < cts.length), cts[j].cidx = none ∨ cts[j].cidx = some j)
    (hind : ∀ j (hj : j < cts.length) iw, cts[j].induct = some iw → st.names.get? iw = some T)
    (htele : ∀ j (hj : j < cts.length), ∃ ch, st.exprs.get? cts[j].cv.type = some ch ∧
      indPiTeleLen (s.store.nodeCount + 1) ch s = .ok (t.numParams + cts[j].numFields, s))
    (hrn : st.names.get? r.cv.name = some rn) (hview : (s.store.ns.view rn).isSome)
    (hrty : (st.exprs.get? r.cv.type).isSome)
    (hrp : r.numParams = t.numParams) (hrm : r.numMotives = 1) (hrmin : r.numMinors = cts.length)
    (hidx : ∃ o, piSortTeleLen? (s.store.nodeCount + 1) tyh s = .ok (o, s) ∧
      ∀ n, o = some n → t.numParams + r.numIndices = n)
    (hrules : ∀ ru ∈ r.rules, (st.names.get? ru.ctor).isSome ∧ (st.exprs.get? ru.rhs).isSome)
    (hcty : ∀ c ∈ cts, (st.exprs.get? c.cv.type).isSome) :
    processLineCoreD st (.ind [t] cts [r]) s =
      .ok (.inl { st with decls := st.decls.push (.indDecl (indBlockD st t cts r T) t.numParams) }, s) := by
  have hlist : t.ctors.mapM st.name = pure ns :=
    mapM_name_idx st (fun x => x) t.ctors ns (by omega) (fun j hj => by simpa using (hnl j (by omega)).1)
  have hcn : cts.mapM (fun c => st.name c.cv.name) = pure ns :=
    mapM_name_idx st (fun c => c.cv.name) cts ns (by omega) (fun j hj => (hnl j hj).2)
  have hTn : st.name t.cv.name = pure T := by simp [StateD.name, hT]
  have hTy : getDeclD st t.cv.type = pure tyh := by simp [getDeclD, StateD.expr, hty]
  have hix : ∀ j (hj : j < cts.length), (ns.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
      (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1[ns[j]'(by omega)]? = some j := by
    intro j hj
    rw [fold_ix ns hnd _ _ j (by omega)]
    simp
  have hin := inner_ok st s T _ cts t.numParams ns hns hix hcidx hind htele cts.length 0 #[] (by omega)
  simp only [List.drop_zero] at hin
  have hout := outer_ok st s _ _ cts.toArray t.numParams T ns _ _ hin
  have hcnS : ∀ c ∈ cts, (st.names.get? c.cv.name).isSome := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    simp [(hnl j hj).2]
  have hv : validateIndD st [t] cts [r] s = .ok (.inr (cts.map (·, T), t.numParams), s) := by
    rw [validateIndD_unfold]
    simp only [List.any_cons, List.any_nil, hu, hnest, List.map_cons, List.map_nil, List.head?_cons,
      Option.getD_some, List.all_cons, List.all_nil, List.mapM_cons, List.mapM_nil, hTn, hTy, hlist, hcn,
      pure_bind, List.flatten_cons, List.flatten_nil, List.append_nil, hnd, hns, List.zip_cons_cons,
      List.zip_nil_left, beq_self_eq_true, Bool.or_false, Bool.and_true, ↓reduceIte, Bool.false_eq_true, bne_self_eq_false]
    rw [bind_ok _ _ s _ (rfl : storeFuel s = .ok (s.store.nodeCount + 1, s))]
    rw [bind_ok _ _ s _ hout]
    dsimp only
    have hrec := rec_ok st s T tyh t.numParams
      (#[] ++ (List.map (fun x => (x, T)) cts).toArray).toList.length r rn hrn hview hrp hrm
      (by simp [hrmin]) hidx
    simp only [List.length_singleton]
    rw [bind_ok _ _ s _ hrec]
    simp only [pure_run, Array.toList_append, List.nil_append]
  unfold processLineCoreD
  dsimp only
  rw [bind_ok _ _ s _ hv]
  dsimp only
  rw [install_ok st t cts r T t.numParams (by simp [hT]) (by simp [hty]) hlpT hlpC hlpR hcnS hcty
    (by simp [hrn]) hrty hrules]
  rfl

end ConPanqueque.Front
