import ConPanqueque.V.Two
open ConRon.Arena

/-!
# Each store's `intern` arm as `twoTier`

For every constructor of every con-ron store, `intern` at that view touches
one table per tier and is `twoTier` on them, with the store's skip test
(`eViewHasScratchChild` for expressions, none elsewhere), its derived value,
and handles `Idx.mk tag tier size` (`Idx.mkWide` for `app`).
-/

namespace ConPanqueque.V

/-- Narrow handles at `tag`, per tier. -/
def mkN {k : IdxKind} (tag tier : UInt32) (i : Nat) : Idx k := Idx.mk tag tier (UInt32.ofNat i)

theorem nstore_str (st : NStore) (p : NIdx) (s : String) :
    st.intern (.str p s) =
      let r := twoTier st.pers.strs st.scr.strs st.scratchOn false ⟨p, s⟩ (st.derOfView (.str p s))
        (mkN NTag.str 0) (mkN NTag.str 1)
      ({ st with pers := { st.pers with strs := r.1 }, scr := { st.scr with strs := r.2.1 } }, r.2.2) := by
  obtain ⟨pers, scr, on⟩ := st
  simp only [NStore.intern, NTables.find?, NTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.strs.find? ⟨p, s⟩ <;> simp
  · cases h : pers.strs.find? ⟨p, s⟩ <;> simp only
    cases h2 : scr.strs.find? ⟨p, s⟩ <;> simp

theorem nstore_anon (st : NStore)  :
    st.intern (.anonymous) =
      let r := twoTier st.pers.anons st.scr.anons st.scratchOn false AnonNode.mk (st.derOfView (.anonymous))
        (mkN NTag.anonymous 0) (mkN NTag.anonymous 1)
      ({ st with pers := { st.pers with anons := r.1 }, scr := { st.scr with anons := r.2.1 } }, r.2.2) := by
  obtain ⟨pers, scr, on⟩ := st
  simp only [NStore.intern, NTables.find?, NTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.anons.find? AnonNode.mk <;> simp
  · cases h : pers.anons.find? AnonNode.mk <;> simp only
    cases h2 : scr.anons.find? AnonNode.mk <;> simp

theorem nstore_num (st : NStore) (p : NIdx) (n : Nat) :
    st.intern (.num p n) =
      let r := twoTier st.pers.nums st.scr.nums st.scratchOn false ⟨p, n⟩ (st.derOfView (.num p n))
        (mkN NTag.num 0) (mkN NTag.num 1)
      ({ st with pers := { st.pers with nums := r.1 }, scr := { st.scr with nums := r.2.1 } }, r.2.2) := by
  obtain ⟨pers, scr, on⟩ := st
  simp only [NStore.intern, NTables.find?, NTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.nums.find? ⟨p, n⟩ <;> simp
  · cases h : pers.nums.find? ⟨p, n⟩ <;> simp only
    cases h2 : scr.nums.find? ⟨p, n⟩ <;> simp

theorem lstore_zero (st : LStore)  :
    st.intern (.zero) =
      let r := twoTier st.pers.zeros st.scr.zeros st.scratchOn false ZeroNode.mk (st.derOfView (.zero))
        (mkN LTag.zero 0) (mkN LTag.zero 1)
      ({ st with pers := { st.pers with zeros := r.1 }, scr := { st.scr with zeros := r.2.1 } }, r.2.2) := by
  obtain ⟨ns, pers, scr, on⟩ := st
  simp only [LStore.intern, LTables.find?, LTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.zeros.find? ZeroNode.mk <;> simp
  · cases h : pers.zeros.find? ZeroNode.mk <;> simp only
    cases h2 : scr.zeros.find? ZeroNode.mk <;> simp

theorem lstore_succ (st : LStore) (u : LIdx) :
    st.intern (.succ u) =
      let r := twoTier st.pers.succs st.scr.succs st.scratchOn false ⟨u⟩ (st.derOfView (.succ u))
        (mkN LTag.succ 0) (mkN LTag.succ 1)
      ({ st with pers := { st.pers with succs := r.1 }, scr := { st.scr with succs := r.2.1 } }, r.2.2) := by
  obtain ⟨ns, pers, scr, on⟩ := st
  simp only [LStore.intern, LTables.find?, LTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.succs.find? ⟨u⟩ <;> simp
  · cases h : pers.succs.find? ⟨u⟩ <;> simp only
    cases h2 : scr.succs.find? ⟨u⟩ <;> simp

theorem lstore_max (st : LStore) (u v : LIdx) :
    st.intern (.max u v) =
      let r := twoTier st.pers.maxs st.scr.maxs st.scratchOn false ⟨u, v⟩ (st.derOfView (.max u v))
        (mkN LTag.max 0) (mkN LTag.max 1)
      ({ st with pers := { st.pers with maxs := r.1 }, scr := { st.scr with maxs := r.2.1 } }, r.2.2) := by
  obtain ⟨ns, pers, scr, on⟩ := st
  simp only [LStore.intern, LTables.find?, LTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.maxs.find? ⟨u, v⟩ <;> simp
  · cases h : pers.maxs.find? ⟨u, v⟩ <;> simp only
    cases h2 : scr.maxs.find? ⟨u, v⟩ <;> simp

theorem lstore_imax (st : LStore) (u v : LIdx) :
    st.intern (.imax u v) =
      let r := twoTier st.pers.imaxs st.scr.imaxs st.scratchOn false ⟨u, v⟩ (st.derOfView (.imax u v))
        (mkN LTag.imax 0) (mkN LTag.imax 1)
      ({ st with pers := { st.pers with imaxs := r.1 }, scr := { st.scr with imaxs := r.2.1 } }, r.2.2) := by
  obtain ⟨ns, pers, scr, on⟩ := st
  simp only [LStore.intern, LTables.find?, LTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.imaxs.find? ⟨u, v⟩ <;> simp
  · cases h : pers.imaxs.find? ⟨u, v⟩ <;> simp only
    cases h2 : scr.imaxs.find? ⟨u, v⟩ <;> simp

theorem lstore_param (st : LStore) (n : NIdx) :
    st.intern (.param n) =
      let r := twoTier st.pers.params st.scr.params st.scratchOn false ⟨n⟩ (st.derOfView (.param n))
        (mkN LTag.param 0) (mkN LTag.param 1)
      ({ st with pers := { st.pers with params := r.1 }, scr := { st.scr with params := r.2.1 } }, r.2.2) := by
  obtain ⟨ns, pers, scr, on⟩ := st
  simp only [LStore.intern, LTables.find?, LTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.params.find? ⟨n⟩ <;> simp
  · cases h : pers.params.find? ⟨n⟩ <;> simp only
    cases h2 : scr.params.find? ⟨n⟩ <;> simp

theorem lsstore_list (st : LsStore) (us : List LIdx) :
    st.intern us =
      let r := twoTier st.pers.lists st.scr.lists st.scratchOn false ⟨us⟩ (st.derOfView us)
        (mkN LsTag.list 0) (mkN LsTag.list 1)
      ({ st with pers := { st.pers with lists := r.1 }, scr := { st.scr with lists := r.2.1 } }, r.2.2) := by
  obtain ⟨ls, pers, scr, on⟩ := st
  simp only [LsStore.intern, LsTables.find?, LsTables.push, twoTier, tierInt, mkN, Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.and_false, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.lists.find? ⟨us⟩ <;> simp
  · cases h : pers.lists.find? ⟨us⟩ <;> simp only
    cases h2 : scr.lists.find? ⟨us⟩ <;> simp

/-- Wide handles (`app`), per tier. -/
def mkW {k : IdxKind} (tier : UInt32) (i : Nat) : Idx k := Idx.mkWide tier (UInt32.ofNat i)

theorem estore_bvar (st : EStore) (i : Nat) :
    st.intern (.bvar i) =
      let r := twoTier st.pers.bvars st.scr.bvars st.scratchOn (EStore.eViewHasScratchChild (.bvar i)) ⟨i⟩
        (st.derOfView (.bvar i)) (mkN ETag.bvar 0) (mkN ETag.bvar 1)
      ({ st with pers := { st.pers with bvars := r.1 }, scr := { st.scr with bvars := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.bvars.find? ⟨i⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.bvar i) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.bvars.find? ⟨i⟩ <;> simp only
      cases h2 : scr.bvars.find? ⟨i⟩ <;> simp
    · cases h2 : scr.bvars.find? ⟨i⟩ <;> simp

theorem estore_fvar (st : EStore) (idx : Nat) (ty : EIdx) :
    st.intern (.fvar idx ty) =
      let r := twoTier st.pers.fvars st.scr.fvars st.scratchOn (EStore.eViewHasScratchChild (.fvar idx ty)) ⟨idx, ty⟩
        (st.derOfView (.fvar idx ty)) (mkN ETag.fvar 0) (mkN ETag.fvar 1)
      ({ st with pers := { st.pers with fvars := r.1 }, scr := { st.scr with fvars := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.fvars.find? ⟨idx, ty⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.fvar idx ty) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.fvars.find? ⟨idx, ty⟩ <;> simp only
      cases h2 : scr.fvars.find? ⟨idx, ty⟩ <;> simp
    · cases h2 : scr.fvars.find? ⟨idx, ty⟩ <;> simp

theorem estore_sort (st : EStore) (u : LIdx) :
    st.intern (.sort u) =
      let r := twoTier st.pers.sorts st.scr.sorts st.scratchOn (EStore.eViewHasScratchChild (.sort u)) ⟨u⟩
        (st.derOfView (.sort u)) (mkN ETag.sort 0) (mkN ETag.sort 1)
      ({ st with pers := { st.pers with sorts := r.1 }, scr := { st.scr with sorts := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.sorts.find? ⟨u⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.sort u) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.sorts.find? ⟨u⟩ <;> simp only
      cases h2 : scr.sorts.find? ⟨u⟩ <;> simp
    · cases h2 : scr.sorts.find? ⟨u⟩ <;> simp

theorem estore_const (st : EStore) (n : NIdx) (us : LsIdx) :
    st.intern (.const n us) =
      let r := twoTier st.pers.consts st.scr.consts st.scratchOn (EStore.eViewHasScratchChild (.const n us)) ⟨n, us⟩
        (st.derOfView (.const n us)) (mkN ETag.const 0) (mkN ETag.const 1)
      ({ st with pers := { st.pers with consts := r.1 }, scr := { st.scr with consts := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.consts.find? ⟨n, us⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.const n us) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.consts.find? ⟨n, us⟩ <;> simp only
      cases h2 : scr.consts.find? ⟨n, us⟩ <;> simp
    · cases h2 : scr.consts.find? ⟨n, us⟩ <;> simp

theorem estore_app (st : EStore) (f a : EIdx) :
    st.intern (.app f a) =
      let r := twoTier st.pers.apps st.scr.apps st.scratchOn (EStore.eViewHasScratchChild (.app f a)) ⟨f, a⟩
        (st.derOfView (.app f a)) (mkW 0) (mkW 1)
      ({ st with pers := { st.pers with apps := r.1 }, scr := { st.scr with apps := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.apps.find? ⟨f, a⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.app f a) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.apps.find? ⟨f, a⟩ <;> simp only
      cases h2 : scr.apps.find? ⟨f, a⟩ <;> simp
    · cases h2 : scr.apps.find? ⟨f, a⟩ <;> simp

theorem estore_lam (st : EStore) (ty b : EIdx) :
    st.intern (.lam ty b) =
      let r := twoTier st.pers.lams st.scr.lams st.scratchOn (EStore.eViewHasScratchChild (.lam ty b)) ⟨ty, b⟩
        (st.derOfView (.lam ty b)) (mkN ETag.lam 0) (mkN ETag.lam 1)
      ({ st with pers := { st.pers with lams := r.1 }, scr := { st.scr with lams := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.lams.find? ⟨ty, b⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.lam ty b) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.lams.find? ⟨ty, b⟩ <;> simp only
      cases h2 : scr.lams.find? ⟨ty, b⟩ <;> simp
    · cases h2 : scr.lams.find? ⟨ty, b⟩ <;> simp

theorem estore_forallE (st : EStore) (ty b : EIdx) :
    st.intern (.forallE ty b) =
      let r := twoTier st.pers.foralls st.scr.foralls st.scratchOn (EStore.eViewHasScratchChild (.forallE ty b)) ⟨ty, b⟩
        (st.derOfView (.forallE ty b)) (mkN ETag.forallE 0) (mkN ETag.forallE 1)
      ({ st with pers := { st.pers with foralls := r.1 }, scr := { st.scr with foralls := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.foralls.find? ⟨ty, b⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.forallE ty b) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.foralls.find? ⟨ty, b⟩ <;> simp only
      cases h2 : scr.foralls.find? ⟨ty, b⟩ <;> simp
    · cases h2 : scr.foralls.find? ⟨ty, b⟩ <;> simp

theorem estore_letE (st : EStore) (ty v b : EIdx) :
    st.intern (.letE ty v b) =
      let r := twoTier st.pers.lets st.scr.lets st.scratchOn (EStore.eViewHasScratchChild (.letE ty v b)) ⟨ty, v, b⟩
        (st.derOfView (.letE ty v b)) (mkN ETag.letE 0) (mkN ETag.letE 1)
      ({ st with pers := { st.pers with lets := r.1 }, scr := { st.scr with lets := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.lets.find? ⟨ty, v, b⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.letE ty v b) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.lets.find? ⟨ty, v, b⟩ <;> simp only
      cases h2 : scr.lets.find? ⟨ty, v, b⟩ <;> simp
    · cases h2 : scr.lets.find? ⟨ty, v, b⟩ <;> simp

theorem estore_lit (st : EStore) (l : ConLeche.Literal) :
    st.intern (.lit l) =
      let r := twoTier st.pers.lits st.scr.lits st.scratchOn (EStore.eViewHasScratchChild (.lit l)) ⟨l⟩
        (st.derOfView (.lit l)) (mkN ETag.lit 0) (mkN ETag.lit 1)
      ({ st with pers := { st.pers with lits := r.1 }, scr := { st.scr with lits := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.lits.find? ⟨l⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.lit l) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.lits.find? ⟨l⟩ <;> simp only
      cases h2 : scr.lits.find? ⟨l⟩ <;> simp
    · cases h2 : scr.lits.find? ⟨l⟩ <;> simp

theorem estore_proj (st : EStore) (n : NIdx) (i : Nat) (e : EIdx) :
    st.intern (.proj n i e) =
      let r := twoTier st.pers.projs st.scr.projs st.scratchOn (EStore.eViewHasScratchChild (.proj n i e)) ⟨n, i, e⟩
        (st.derOfView (.proj n i e)) (mkN ETag.proj 0) (mkN ETag.proj 1)
      ({ st with pers := { st.pers with projs := r.1 }, scr := { st.scr with projs := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?, ETables.push, twoTier, tierInt, mkN, mkW,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.projs.find? ⟨n, i, e⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.proj n i e) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.projs.find? ⟨n, i, e⟩ <;> simp only
      cases h2 : scr.projs.find? ⟨n, i, e⟩ <;> simp
    · cases h2 : scr.projs.find? ⟨n, i, e⟩ <;> simp

theorem estore_internLam (st : EStore) (ty b : EIdx) :
    st.internLam ty b =
      let r := twoTier st.pers.lams st.scr.lams st.scratchOn (EStore.bindHasScratchChild ty b) ⟨ty, b⟩
        (st.derOfBindAt 19 ty b) (mkN ETag.lam 0) (mkN ETag.lam 1)
      ({ st with pers := { st.pers with lams := r.1 }, scr := { st.scr with lams := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.internLam, EStore.internBind, EStore.persFindBindMaybe, ETables.findBind, ETables.pushBind,
    twoTier, tierInt, mkN, Idx.tierS, Idx.tierP, show (ETag.lam == ETag.lam) = true from rfl, ite_true]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.lams.find? ⟨ty, b⟩ <;> simp
  · cases EStore.bindHasScratchChild ty b <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.lams.find? ⟨ty, b⟩ <;> simp only
      cases h2 : scr.lams.find? ⟨ty, b⟩ <;> simp
    · cases h2 : scr.lams.find? ⟨ty, b⟩ <;> simp

theorem estore_internForallE (st : EStore) (ty b : EIdx) :
    st.internForallE ty b =
      let r := twoTier st.pers.foralls st.scr.foralls st.scratchOn (EStore.bindHasScratchChild ty b) ⟨ty, b⟩
        (st.derOfBindAt 23 ty b) (mkN ETag.forallE 0) (mkN ETag.forallE 1)
      ({ st with pers := { st.pers with foralls := r.1 }, scr := { st.scr with foralls := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.internForallE, EStore.internBind, EStore.persFindBindMaybe, ETables.findBind, ETables.pushBind,
    twoTier, tierInt, mkN, Idx.tierS, Idx.tierP, show (ETag.forallE == ETag.lam) = false from rfl,
    show (ETag.forallE == ETag.forallE) = true from rfl, ite_true, Bool.false_eq_true, ite_false]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.foralls.find? ⟨ty, b⟩ <;> simp
  · cases EStore.bindHasScratchChild ty b <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.foralls.find? ⟨ty, b⟩ <;> simp only
      cases h2 : scr.foralls.find? ⟨ty, b⟩ <;> simp
    · cases h2 : scr.foralls.find? ⟨ty, b⟩ <;> simp

end ConPanqueque.V
