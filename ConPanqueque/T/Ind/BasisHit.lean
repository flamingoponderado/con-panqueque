import ConPanqueque.T.Ind.BasisPin
import ConPanqueque.T.Ind.IndArm

/-!
# Which pinned basis block a record declares (`basisNameHit`), by its names

`bhitBody(o, n, r)`: the block's names against the reserved list's slices (`bsqBody`), in the twin's order
(`Eq`, `Nat`, `Empty`, `False`): the kind word of the first match (`basisWord`), `0` for none (`hitW`).
`ibkBody`: the block's names free (`ibnBody`) only when no pinned block matched.

Twin facts: at a block under pinned block `k`'s names the `And` pin's test passes (the reserved names are none of
the pinned `And` names) and `basisNamesOk` is `pinListOk` against the pin's interning (a no-op).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.WC
open ConPanqueque.Logic.InternRerun ConPanqueque.Logic.BasisNames

/-! ## The hit's kind word -/

/-- The kind word of the first pinned block whose reserved slice is the block's names (`0` for none). -/
def hitW (blk : List IConstantInfo) (rs : List NIdx) : Nat :=
  if blk.length = 3 then (if bsqVal blk rs 0 0 then 1 else 0)
  else if blk.length = 4 then (if bsqVal blk rs 3 0 then 2 else 0)
  else if blk.length = 2 then (if bsqVal blk rs 7 0 then 3 else if bsqVal blk rs 9 0 then 4 else 0)
  else 0

def bhO := ofString "bh_o"
def bhN := ofString "bh_n"
def bhR := ofString "bh_r"
def bhX := ofString "bh_x"
def fBhit := ofString "basisHit"

def bhitParams : List MlS := [bhO, bhN, bhR]
def bhitLocals : List MlS := [bhX]

/-- One slice test, then `a` on a match, else `rest`. -/
def bhTest (a : Nat) (rest : ProgHOL 64) (w : Nat) : ProgHOL 64 :=
  .seq (.call (some (some (.local, bhX), none)) fBsq [vv bhO, .const 0, vv bhN, vv bhR, .const (BitVec.ofNat 64 a)])
    (.ite (vv bhX) (.return (.const (BitVec.ofNat 64 w))) rest)

def bhitBody : ProgHOL 64 := prologue bhitLocals
  (.ite (.cmp .equal (vv bhN) (.const 3)) (bhTest 0 (.return (.const 0)) 1)
  (.ite (.cmp .equal (vv bhN) (.const 4)) (bhTest 3 (.return (.const 0)) 2)
  (.ite (.cmp .equal (vv bhN) (.const 2)) (bhTest 7 (bhTest 9 (.return (.const 0)) 4) 3)
    (.return (.const 0)))))

def ikO := ofString "ik_o"
def ikN := ofString "ik_n"
def ikR := ofString "ik_r"
def ikL := ofString "ik_l"
def ikK := ofString "ik_k"
def ikX := ofString "ik_x"
def fIbk := ofString "blockNamesFreeK"

def ibkParams : List MlS := [ikO, ikN, ikR, ikL, ikK]
def ibkLocals : List MlS := [ikX]

/-- The block's names free (else hang), when no pinned block matched (`k = 0`). -/
def ibkBody : ProgHOL 64 := prologue ibkLocals
  (.ite (.cmp .equal (vv ikK) (.const 0))
    (.seq (.call (some (some (.local, ikX), none)) fIbn [vv ikO, .const 0, vv ikN, vv ikR, vv ikL])
      (.return (.const 0)))
    (.return (.const 0)))

/-- The hit's code. -/
structure BHCodes (C : Ctx) : Prop where
  bsq : BSQCodes C
  ibn : IBNCodes C
  bhit : C.code.lookup fBhit = some (bhitParams.map (fun p => (p, ShapeHOL.one)), bhitBody, .one)
  ibk : C.code.lookup fIbk = some (ibkParams.map (fun p => (p, ShapeHOL.one)), ibkBody, .one)

/-! ## Slices -/

theorem eq_of_bsqVal {blk : List IConstantInfo} {rs : List NIdx} {a : Nat} (h : bsqVal blk rs a 0 = true)
    (hle : a + blk.length ≤ rs.length) : (rs.drop a).take blk.length = blk.map (·.name) := by
  unfold bsqVal at h
  simp only [List.drop_zero, Nat.add_zero, Nat.sub_zero, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map] at h2
  have hz : (blk[i], (rs.drop a)[i]'(by simp; omega)) ∈ blk.zip (rs.drop a) := by
    have := List.getElem_mem (l := blk.zip (rs.drop a)) (n := i) (by simp; omega)
    simpa using this
  have := h.1 _ hz
  simp only [List.getElem_take, List.getElem_map]
  exact this.symm

theorem bsqVal_of_eq' (blk : List IConstantInfo) (rs : List NIdx) (a : Nat) (hle : a + blk.length ≤ rs.length)
    (he : (rs.drop a).take blk.length = blk.map (·.name)) : bsqVal blk rs a 0 = true := by
  unfold bsqVal
  simp only [List.drop_zero, Nat.add_zero, Nat.sub_zero, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun p hp => ?_, by omega⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  simp only [List.getElem_zip, beq_iff_eq]
  have hi1 : i < blk.length := by simp at hi; omega
  have := congrArg (fun l => l[i]?) he
  simp only [List.getElem?_take, hi1, ↓reduceIte, List.getElem?_drop, List.getElem?_map] at this
  rw [List.getElem?_eq_getElem (by simp at hi; omega), List.getElem?_eq_getElem hi1] at this
  simpa using this.symm

theorem ne_of_bsqVal {blk : List IConstantInfo} {rs : List NIdx} {a : Nat} (h : bsqVal blk rs a 0 = false)
    (hle : a + blk.length ≤ rs.length) : (rs.drop a).take blk.length ≠ blk.map (·.name) := fun e => by
  rw [bsqVal_of_eq' blk rs a hle e] at h; cases h

theorem resSlice_len (k : ConLeche.BasisKind) (rs : List NIdx) (h : rs.length = 16) (hk : k ≠ .quotK) :
    (resSlice k rs).length = (ConLeche.BasisKind.decls k).length := by
  cases k <;> simp [resSlice, h] <;> first | exact absurd rfl hk | decide

/-- **No hit**: no reserved slice is the block's names. -/
theorem noHit_of_hitW {C : Ctx} {blk : List IConstantInfo} (hrs : C.pins.reserved.length = 16)
    (h : hitW blk C.pins.reserved = 0) : NoHit C blk := by
  intro k hk e
  have hl := congrArg List.length e
  simp only [List.length_map] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  unfold hitW at h
  rcases hk with rfl | rfl | rfl | rfl
  · have hl3 : blk.length = 3 := by rw [← hl]; simp [resSlice, hrs]
    simp only [hl3, if_true] at h
    split at h
    · cases h
    · rename_i hb
      exact ne_of_bsqVal (by simpa using hb) (by omega) (by rw [hl3]; exact e)
  · have hl4 : blk.length = 4 := by rw [← hl]; simp [resSlice, hrs]
    simp only [hl4, show (4 : Nat) ≠ 3 by decide, if_false, if_true] at h
    split at h
    · cases h
    · rename_i hb
      exact ne_of_bsqVal (by simpa using hb) (by omega) (by rw [hl4]; exact e)
  · have hl2 : blk.length = 2 := by rw [← hl]; simp [resSlice, hrs]
    simp only [hl2, show (2 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 4 by decide, if_false, if_true] at h
    split at h
    · cases h
    · rename_i hb
      exact ne_of_bsqVal (by simpa using hb) (by omega) (by rw [hl2]; exact e)
  · have hl2 : blk.length = 2 := by rw [← hl]; simp [resSlice, hrs]
    simp only [hl2, show (2 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 4 by decide, if_false, if_true] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i _ hb
        exact ne_of_bsqVal (by simpa using hb) (by omega) (by rw [hl2]; exact e)

/-- What a hit says: the slice of the kind it names is the block's names, and no earlier kind's is. -/
def HitAt (rs : List NIdx) (blk : List IConstantInfo) (k : ConLeche.BasisKind) : Prop :=
  k ≠ .quotK ∧ resSlice k rs = blk.map (·.name) ∧ blk.length = (ConLeche.BasisKind.decls k).length ∧
    ∀ k' ∈ [ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK].take (basisWord k - 1),
      resSlice k' rs ≠ blk.map (·.name)

theorem hitAt_of_hitW {blk : List IConstantInfo} {rs : List NIdx} (hrs : rs.length = 16) (h : hitW blk rs ≠ 0) :
    ∃ k, basisWord k = hitW blk rs ∧ HitAt rs blk k := by
  have neq : ∀ (k : ConLeche.BasisKind) m, (resSlice k rs).length = m → blk.length ≠ m →
      resSlice k rs ≠ blk.map (·.name) := fun k m hm hb e => hb (by rw [← hm, e]; simp)
  unfold hitW at h ⊢
  by_cases h3 : blk.length = 3
  · simp only [h3, if_true] at h ⊢
    split at h
    · rename_i hb
      refine ⟨.eqK, by simp [hb, basisWord], by decide, ?_, by rw [h3]; rfl, fun k' hk' => by simp [basisWord] at hk'⟩
      have := eq_of_bsqVal hb (by omega); rw [h3] at this; simpa [resSlice] using this
    · exact absurd rfl h
  by_cases h4 : blk.length = 4
  · simp only [h4, show (4 : Nat) ≠ 3 by decide, if_false, if_true] at h ⊢
    split at h
    · rename_i hb
      refine ⟨.natK, by simp [hb, basisWord], by decide, ?_, by rw [h4]; rfl, fun k' hk' => ?_⟩
      · have := eq_of_bsqVal hb (by omega); rw [h4] at this; simpa [resSlice] using this
      · simp [basisWord] at hk'; subst hk'; exact neq _ 3 (by simp [resSlice, hrs]) (by omega)
    · exact absurd rfl h
  by_cases h2 : blk.length = 2
  · simp only [h2, show (2 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 4 by decide, if_false, if_true] at h ⊢
    split at h
    · rename_i hb
      refine ⟨.emptyK, by simp [hb, basisWord], by decide, ?_, by rw [h2]; rfl, fun k' hk' => ?_⟩
      · have := eq_of_bsqVal hb (by omega); rw [h2] at this; simpa [resSlice] using this
      · simp [basisWord] at hk'
        rcases hk' with rfl | rfl
        · exact neq _ 3 (by simp [resSlice, hrs]) (by omega)
        · exact neq _ 4 (by simp [resSlice, hrs]) (by omega)
    · rename_i hb7
      split at h
      · rename_i hb
        refine ⟨.falseK, by simp [hb7, hb, basisWord], by decide, ?_, by rw [h2]; rfl, fun k' hk' => ?_⟩
        · have := eq_of_bsqVal hb (by omega); rw [h2] at this; simpa [resSlice] using this
        · simp [basisWord] at hk'
          rcases hk' with rfl | rfl | rfl
          · exact neq _ 3 (by simp [resSlice, hrs]) (by omega)
          · exact neq _ 4 (by simp [resSlice, hrs]) (by omega)
          · have := ne_of_bsqVal (by simpa using hb7) (by omega); rw [h2] at this; simpa [resSlice] using this
      · exact absurd rfl h
  · simp [h3, h4, h2] at h

/-! ## The twin at a hit -/

theorem denoteNL_get {st : EStore} : ∀ (xs : List NIdx) (ns : List ConLeche.Name), denoteNL st xs ns →
    ∀ i (hi : i < xs.length), ∃ h2 : i < ns.length, denoteN st.ns xs[i] = some ns[i]
  | [], _, _, i, hi => by simp at hi
  | x :: xs, n :: ns, h, 0, _ => ⟨by simp, h.1⟩
  | x :: xs, n :: ns, h, i + 1, hi => by
    obtain ⟨h2, h3⟩ := denoteNL_get xs ns h.2 i (by simpa using hi)
    exact ⟨by simp; omega, h3⟩
  | _ :: _, [], h, _, _ => h.elim

set_option maxRecDepth 100000 in
theorem reserved_ne_and : ∀ x ∈ reservedBasisNameValues, x ≠ pinNames[11]! ∧ x ≠ pinNames[48]! ∧ x ≠ pinNames[49]! := by
  decide

/-- The reserved names are none of the pinned `And` names. -/
theorem reserved_not_and {C : Ctx} (hok : CtxOK C) {s : AState} (hp : PinsOK s) (hps : s.pins = C.pins) :
    ∀ n ∈ C.pins.reserved, n ≠ C.pins.names[11]! ∧ n ≠ C.pins.names[48]! ∧ n ≠ C.pins.names[49]! := by
  intro n hn
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
  have hres := hp.reserved
  rw [hps] at hres
  obtain ⟨hj2, hdj⟩ := denoteNL_get _ _ hres j hj
  have hnm := hp.names
  rw [hps] at hnm
  have hsz : C.pins.names.size = pinCount := hok.pinsRel.1
  have hpin : ∀ i, i < pinCount → denoteN s.store.ns C.pins.names[i]! = some pinNames[i]! := by
    intro i hi
    have hi' : i < C.pins.names.toList.length := by simp [hsz]; exact hi
    obtain ⟨h2, h3⟩ := denoteNL_get _ _ hnm i hi'
    have e1 : C.pins.names[i]! = C.pins.names.toList[i] := by
      rw [getElem!_pos C.pins.names i (by omega)]; simp
    rw [e1, h3, getElem!_pos pinNames i h2]
  have hr := reserved_ne_and _ (List.getElem_mem hj2)
  refine ⟨fun e => hr.1 ?_, fun e => hr.2.1 ?_, fun e => hr.2.2 ?_⟩ <;>
  · apply Option.some.inj
    first
    | (rw [← hdj, e]; exact hpin _ (by decide))

theorem blockAndNamed_res {C : Ctx} (hok : CtxOK C) {s : AState} (hp : PinsOK s) (hps : s.pins = C.pins) :
    ∀ (block : List IConstantInfo), (∀ c ∈ block, c.name ∈ C.pins.reserved) →
      blockAndNamed [C.pins.names[11]!, C.pins.names[48]!, C.pins.names[49]!] block = false
  | [], _ => rfl
  | c :: cs, h => by
    obtain ⟨f1, f2, f3⟩ := reserved_not_and hok hp hps c.name (h c (by simp))
    simp only [blockAndNamed, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne]
    exact ⟨⟨f1, f2, f3⟩, blockAndNamed_res hok hp hps cs (fun x hx => h x (by simp [hx]))⟩

theorem names_mem_res {rs : List NIdx} {blk : List IConstantInfo} {k : ConLeche.BasisKind}
    (h : resSlice k rs = blk.map (·.name)) : ∀ c ∈ blk, c.name ∈ rs := by
  intro c hc
  have : c.name ∈ resSlice k rs := by rw [h]; exact List.mem_map_of_mem hc
  cases k <;> simp only [resSlice] at this <;>
    first | exact List.mem_of_mem_drop (List.mem_of_mem_take this) | simp at this

/-- **`andPinOk` at a block under a pinned basis block's names**: `true`, the state kept. -/
theorem andPinOk_hit {C : Ctx} (hok : CtxOK C) {s : AState} (hps : s.pins = C.pins) (hp : PinsOK s)
    (block : List IConstantInfo) (nP : Nat) (hn : ∀ c ∈ block, c.name ∈ C.pins.reserved) :
    andPinOk (.indDecl block nP) s = .ok (true, s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hps i hi
  unfold andPinOk andPinNameHs
  simp only [pinAnd, pinAndIntro, pinAndRec, PIN_AND, PIN_AND_INTRO, PIN_AND_REC]
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, h _ (show 11 < pinCount by decide),
    h _ (show 48 < pinCount by decide), h _ (show 49 < pinCount by decide), blockAndNamed_res hok hp hps block hn]

/-- **`basisNamesOk` at a block under pinned block `k`'s names** is `pinListOk` against the pin's interning. -/
theorem basisNamesOk_hit {σ : Type} {C : Ctx} (hb : BasisInv C) {s : AState} {t : PState σ}
    (hsr : SR C s t) (hoff : Off s.store) (block : List IConstantInfo) (nP : Nat) (k : ConLeche.BasisKind)
    (hk : HitAt C.pins.reserved block k) :
    ∃ r, ConRon.Arena.BasisKind.decls k s = .ok (r, s) ∧
      basisNamesOk (.indDecl block nP) s = pinListOk block r s := by
  obtain ⟨hkq, hsl, -, hpre⟩ := hk
  obtain ⟨r1, h1, n1⟩ := basis_at hb hsr hoff .eqK (by decide)
  obtain ⟨r2, h2, n2⟩ := basis_at hb hsr hoff .natK (by decide)
  obtain ⟨r3, h3, n3⟩ := basis_at hb hsr hoff .emptyK (by decide)
  obtain ⟨r4, h4, n4⟩ := basis_at hb hsr hoff .falseK (by decide)
  have bT : ∀ (r : List IConstantInfo) (k : ConLeche.BasisKind), r.map (·.name) = resSlice k C.pins.reserved →
      resSlice k C.pins.reserved = block.map (·.name) → (blockNames r == blockNames block) = true := by
    intro r k h1 h2; simp only [blockNames, h1, h2, beq_self_eq_true]
  have bF : ∀ (r : List IConstantInfo) (k : ConLeche.BasisKind), r.map (·.name) = resSlice k C.pins.reserved →
      resSlice k C.pins.reserved ≠ block.map (·.name) → (blockNames r == blockNames block) = false := by
    intro r k h1 h2; simp only [blockNames, h1]; exact beq_eq_false_iff_ne.mpr h2
  unfold basisNamesOk basisNameHit
  cases k with
  | eqK =>
    refine ⟨r1, h1, ?_⟩
    simp only [basisNameHitGo, bind, StateT.bind, Except.bind, h1, bT r1 _ n1 hsl, ↓reduceIte, pure,
      StateT.pure, Except.pure]
  | natK =>
    have e1 := hpre .eqK (by simp [basisWord])
    refine ⟨r2, h2, ?_⟩
    simp only [basisNameHitGo, bind, StateT.bind, Except.bind, h1, h2, bF r1 _ n1 e1, bT r2 _ n2 hsl,
      Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure]
  | emptyK =>
    have e1 := hpre .eqK (by simp [basisWord])
    have e2 := hpre .natK (by simp [basisWord])
    refine ⟨r3, h3, ?_⟩
    simp only [basisNameHitGo, bind, StateT.bind, Except.bind, h1, h2, h3, bF r1 _ n1 e1, bF r2 _ n2 e2,
      bT r3 _ n3 hsl, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure]
  | falseK =>
    have e1 := hpre .eqK (by simp [basisWord])
    have e2 := hpre .natK (by simp [basisWord])
    have e3 := hpre .emptyK (by simp [basisWord])
    refine ⟨r4, h4, ?_⟩
    simp only [basisNameHitGo, bind, StateT.bind, Except.bind, h1, h2, h3, h4, bF r1 _ n1 e1, bF r2 _ n2 e2,
      bF r3 _ n3 e3, bT r4 _ n4 hsl, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure]
  | quotK => exact absurd rfl hkq

section
variable {σ : Type}

theorem bhit_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bhitLocals → (ctxEnv C ++ bhitParams.zip vals).get x = none :=
  Knot.params_none C bhitLocals bhitParams vals (by decide) (by decide)

theorem ibk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ibkLocals → (ctxEnv C ++ ibkParams.zip vals).get x = none :=
  Knot.params_none C ibkLocals ibkParams vals (by decide) (by decide)

theorem ofNat_eq_small61 {n m : Nat} (hn : n < 2 ^ 61) (hm : m < 2 ^ 61) :
    (BitVec.ofNat 64 n = BitVec.ofNat 64 m) ↔ n = m := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · rintro rfl; rfl

/-- One slice test: the twin's `bsqVal`, then the hit's word or `rest`. -/
theorem specR_bhTest {α : Type} {C : Ctx} (hok : CtxOK C) (hc : BHCodes C) {s : AState} {Γ : Env}
    {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (blk : List IConstantInfo) (ob : Nat) (hblk : IndBlk C C.H ob blk) (rs : List NIdx) (oR : Nat)
    (hR : EBlk C.EH oR (rs.map Enc.idxW)) (hRl : rs.length < 2 ^ 59) (a w : Nat) (hle : a + blk.length ≤ rs.length)
    (hn : Γ.get bhN = some (BitVec.ofNat 64 blk.length)) (hob : Γ.get bhO = some (cellA C ob))
    (hr : Γ.get bhR = some (ecell C oR)) (hD : bhX ∈ D)
    (hyes : ∀ (Γ' : Env) (H' : List (BitVec 64)), C.H <+: H' → (∀ x, x ≠ bhX → Γ'.get x = Γ.get x) →
      bsqVal blk rs a 0 = true → SpecR (Inv (ctxH C H') s Γ' [] D) (.return (.const (BitVec.ofNat 64 w))) s m R)
    (hno : ∀ (Γ' : Env) (H' : List (BitVec 64)), C.H <+: H' → (∀ x, x ≠ bhX → Γ'.get x = Γ.get x) →
      bsqVal blk rs a 0 = false → SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (bhTest a rest w) s m R := by
  unfold bhTest
  refine specR_callPure (C := C) bhX fBsq bsqParams [vv bhO, .const 0, vv bhN, vv bhR, .const (BitVec.ofNat 64 a)]
    bsqBody [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 blk.length, ecell C oR, BitVec.ofNat 64 a]
    (bsqVal blk rs a 0) (by decide) rfl hD hc.bsq.self
    ⟨by simp [sev, hob], by simp [sev], by simp [sev, hn], by simp [sev, hr], by simp [sev], trivial⟩
    (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bsqParams _ rfl hlk)
      (bsq_spec C hok hc.bsq blk ob hblk rs oR hR a hle hRl _ 0 C.H s rfl (Nat.zero_le _) (List.prefix_refl _)))
    (fun w' H' hp' hw => ?_)
  subst hw
  cases hv : bsqVal blk rs a 0
  · refine specR_ifI _ 0 (by simp [sev, Env.get_cons, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hno _ H' hp' (fun x hx => by simp [Env.get_cons, hx]) hv
  · refine specR_ifI _ 1 (by simp [sev, Env.get_cons, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hyes _ H' hp' (fun x hx => by simp [Env.get_cons, hx]) hv


set_option maxHeartbeats 4000000 in
/-- **The hit's kind word** (`hitW`). -/
theorem bhit_spec (C : Ctx) (hok : CtxOK C) (hc : BHCodes C) (blk : List IConstantInfo) (ob : Nat)
    (hblk : IndBlk C C.H ob blk) (rs : List NIdx) (oR : Nat) (hR : EBlk C.EH oR (rs.map Enc.idxW))
    (hrs : rs.length = 16) (hbl : blk.length < 2 ^ 61) (s : AState) :
    SpecR (σ := σ) (Pre C s (bhitParams.zip [cellA C ob, BitVec.ofNat 64 blk.length, ecell C oR])) bhitBody s
      (pure (hitW blk rs)) (PostNv C) := by
  refine specR_prologue (postNv_locals _) (bhit_none _ _) ?_
  have g1 : ∀ (Γ : Env) (H' : List (BitVec 64)), C.H <+: H' → ∀ w, SpecR (σ := σ) (Inv (ctxH C H') s Γ []
      (ctxLocals ++ bhitLocals)) (.return (.const (BitVec.ofNat 64 w))) s (pure w) (PostNv C) :=
    fun Γ H' hp' w => specR_returnI _ _ rfl (fun t ht => ⟨H', hp', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hD : bhX ∈ ctxLocals ++ bhitLocals := by decide
  have n0 : (ctxEnv C ++ bhitParams.zip [cellA C ob, BitVec.ofNat 64 blk.length, ecell C oR]).get bhN =
      some (BitVec.ofNat 64 blk.length) := by simp +decide [Env.get, bhitParams, ctxEnv]
  have o0 : (ctxEnv C ++ bhitParams.zip [cellA C ob, BitVec.ofNat 64 blk.length, ecell C oR]).get bhO =
      some (cellA C ob) := by simp +decide [Env.get, bhitParams, ctxEnv]
  have r0 : (ctxEnv C ++ bhitParams.zip [cellA C ob, BitVec.ofNat 64 blk.length, ecell C oR]).get bhR =
      some (ecell C oR) := by simp +decide [Env.get, bhitParams, ctxEnv]
  have ne : ∀ m, m < 2 ^ 61 → blk.length ≠ m → BitVec.ofNat 64 blk.length ≠ BitVec.ofNat 64 m :=
    fun m hm h e => h ((ofNat_eq_small61 hbl hm).mp e)
  unfold hitW
  by_cases h3 : blk.length = 3
  · refine specR_ifI _ 1 (by simp +decide [sev, n0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> simp [h3])
      (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_pos h3]
    refine specR_bhTest hok hc blk ob hblk rs oR hR (by omega) 0 1 (by omega) n0 o0 r0 hD
      (fun Γ' H' hp' _ hv => by rw [hv]; exact g1 Γ' H' hp' 1)
      (fun Γ' H' hp' _ hv => by rw [hv]; exact g1 Γ' H' hp' 0)
  refine specR_ifI _ 0 (by simp +decide [sev, n0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ne 3 (by decide) h3)
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases h4 : blk.length = 4
  · refine specR_ifI _ 1 (by simp +decide [sev, n0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> simp [h4])
      (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg h3, if_pos h4]
    refine specR_bhTest hok hc blk ob hblk rs oR hR (by omega) 3 2 (by omega) n0 o0 r0 hD
      (fun Γ' H' hp' _ hv => by rw [hv]; exact g1 Γ' H' hp' 2)
      (fun Γ' H' hp' _ hv => by rw [hv]; exact g1 Γ' H' hp' 0)
  refine specR_ifI _ 0 (by simp +decide [sev, n0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ne 4 (by decide) h4)
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases h2 : blk.length = 2
  · refine specR_ifI _ 1 (by simp +decide [sev, n0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> simp [h2])
      (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg h3, if_neg h4, if_pos h2]
    refine specR_bhTest hok hc blk ob hblk rs oR hR (by omega) 7 3 (by omega) n0 o0 r0 hD
      (fun Γ' H' hp' _ hv => by rw [hv]; exact g1 Γ' H' hp' 3) (fun Γ' H' hp' hag hv => ?_)
    rw [hv]
    have n1 : Γ'.get bhN = some (BitVec.ofNat 64 blk.length) := by rw [hag _ (by decide)]; exact n0
    have o1 : Γ'.get bhO = some (cellA C ob) := by rw [hag _ (by decide)]; exact o0
    have r1 : Γ'.get bhR = some (ecell C oR) := by rw [hag _ (by decide)]; exact r0
    refine specR_bhTest (ctxOK_H hok H') (by ctx_tr hc) blk ob (indBlk_mono hblk hp') rs oR hR (by omega) 9 4
      (by omega) n1 o1 r1 hD
      (fun Γ2 H2 hp2 _ hv2 => by rw [hv2]; exact g1 Γ2 H2 (hp'.trans hp2) 4)
      (fun Γ2 H2 hp2 _ hv2 => by rw [hv2]; exact g1 Γ2 H2 (hp'.trans hp2) 0)
  refine specR_ifI _ 0 (by simp +decide [sev, n0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ne 2 (by decide) h2)
    (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_neg h3, if_neg h4, if_neg h2]
  exact g1 _ C.H (List.prefix_refl _) 0

/-- **The block's names free when no pinned block matched.** -/
theorem ibk_spec (C : Ctx) (hok : CtxOK C) (hc : BHCodes C) (blk : List IConstantInfo) (ob : Nat)
    (hblk : IndBlk C C.H ob blk) (oR : Nat) (hR : EBlk C.EH oR (C.pins.reserved.map Enc.idxW))
    (hRl : C.pins.reserved.length < 2 ^ 62) (k : Nat) (hk : k < 2 ^ 61) (s : AState) :
    SpecR (σ := σ) (Pre C s (ibkParams.zip [cellA C ob, BitVec.ofNat 64 blk.length, ecell C oR,
        BitVec.ofNat 64 C.pins.reserved.length, BitVec.ofNat 64 k])) ibkBody s (pure ())
      (PostKFH C s (k = 0 → ∀ c ∈ blk, NameFree C c.name)) := by
  refine specR_prologue (postKFH_locals _ _ _) (ibk_none _ _) ?_
  by_cases hk0 : k = 0
  · subst hk0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ibkParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIH (C := C) ikX fIbn ibnParams [vv ikO, .const 0, vv ikN, vv ikR, vv ikL] ibnBody
      [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 blk.length, ecell C oR, BitVec.ofNat 64 C.pins.reserved.length]
      (by decide) rfl (by decide) hc.ibn.self
      ⟨by simp +decide [sev, Env.get, ibkParams, ctxEnv], rfl, by simp +decide [sev, Env.get, ibkParams, ctxEnv],
        by simp +decide [sev, Env.get, ibkParams, ctxEnv], by simp +decide [sev, Env.get, ibkParams, ctxEnv], trivial⟩
      (PostKFH C s (∀ c ∈ blk.drop 0, NameFree C c.name))
      (fun _ _ s' _ => s' = s ∧ ∀ c ∈ blk, NameFree C c.name)
      (fun a w s' st ⟨hs', hP, H', hp', hsr⟩ => ⟨H', hp', ⟨hs', fun c hc' => hP c (by simpa using hc')⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibnParams _ rfl hlk)
        (ibn_spec C hok hc.ibn blk ob hblk oR hR hRl _ 0 C.H s rfl (Nat.zero_le _) (List.prefix_refl _)))
      (fun _ w s1 H1 hp1 ⟨hs1, hfree⟩ => ?_)
    subst hs1
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, fun _ => hfree, H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get, ibkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact fun h => hk0 ((ofNat_eq_small61 hk (by decide)).mp h)) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, fun h => absurd h hk0, C.H, List.prefix_refl _,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
