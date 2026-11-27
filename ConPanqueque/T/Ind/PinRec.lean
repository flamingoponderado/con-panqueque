import ConPanqueque.T.Quot.Block
import ConPanqueque.T.Decl.EnvGrow

/-!
# A pinned block's records in the value heap

The twin's pin comparisons (`pinListOk`, `canonEqList`) read a pinned block's interned constants. The port
interns the block's literals (`genCIList`'s steps, the twin's `plainCIList`) and keeps every constant as a
record in the value heap (`genPinBlk`): a pointer block `[n, cellA o₀, …]`, record `i` at `oᵢ` in the
environment's layout without an inductive's capabilities (`PinRec`): `[tag, name, levelParams, type, …]`, a
constructor's counts and former, a recursor's counts, `K` flag and rule block (every rule plain).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.Start ConPanqueque.T.Lit ConPanqueque.Logic.PlainIntern ConPanqueque.T.Quot
open ConPanqueque.T.Decl

/-- A pinned constant's record: the environment's layout (`CIE`) without an inductive's capabilities. -/
def PinRec (EB : BitVec 64) (H : List (BitVec 64)) (o : Nat) (ci : IConstantInfo) : Prop :=
  CVE EB H (o + 1) ci.toConstantVal ∧
  match ci with
  | .indInfo _ _ => H[o]? = some 3
  | .ctorInfo _ np nf ind => H[o]? = some 4 ∧ NatE H (o + 4) np ∧ NatE H (o + 5) nf ∧
      H[o + 6]? = some (Enc.idxW ind)
  | .recInfo _ mi rp isK rules => H[o]? = some 5 ∧ NatE H (o + 4) mi ∧ NatE H (o + 5) rp ∧
      H[o + 6]? = some (boolW isK) ∧ ∃ w, H[o + 7]? = some w ∧ RulesE EB H w rules
  | _ => False

theorem pinRec_mono {EB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {ci : IConstantInfo}
    (h : PinRec EB H o ci) : PinRec EB H' o ci := by
  refine ⟨cve_mono hp h.1, ?_⟩
  have h2 := h.2
  cases ci with
  | indInfo _ _ => exact get_prefix h2 hp
  | ctorInfo _ np nf ind =>
    obtain ⟨a, b, c, d⟩ := h2
    exact ⟨get_prefix a hp, natE_mono hp b, natE_mono hp c, get_prefix d hp⟩
  | recInfo _ mi rp isK rules =>
    obtain ⟨a, b, c, d, ⟨w, hw, hr⟩⟩ := h2
    exact ⟨get_prefix a hp, natE_mono hp b, natE_mono hp c, get_prefix d hp, ⟨w, get_prefix hw hp, rulesE_mono hp hr⟩⟩
  | axiomInfo _ => exact h2.elim
  | defnInfo _ _ _ => exact h2.elim
  | thmInfo _ => exact h2.elim

/-- A pinned block in the value heap: pointer block at `ob`, record `i` at `os[i]`. -/
def PinBlk (C : Ctx) (H : List (BitVec 64)) (ob : Nat) (blk : List IConstantInfo) : Prop :=
  ∃ os : List Nat, os.length = blk.length ∧ BlkAt H ob (os.map (cellA C)) ∧
    ∀ i (hi : i < blk.length) (ho : i < os.length), PinRec C.HB H os[i] blk[i]

theorem pinBlk_mono {C : Ctx} {H H' : List (BitVec 64)} {ob : Nat} {blk : List IConstantInfo}
    (h : PinBlk C H ob blk) (hp : H <+: H') : PinBlk C H' ob blk :=
  let ⟨os, hl, hb, hc⟩ := h; ⟨os, hl, blkAt_mono hb hp, fun i hi ho => pinRec_mono hp (hc i hi ho)⟩


/-! ## Allocate and write (the front end's `allocWr`, at this level) -/

/-- The image after the first `i` stores of `ws` from `o`. -/
def pkcH (H : List (BitVec 64)) (o : Nat) (ws : List (BitVec 64)) : Nat → List (BitVec 64)
  | 0 => H
  | i + 1 => (pkcH H o ws i).set (o + i) (ws.getD i 0)

theorem pkcH_length (H : List (BitVec 64)) (o : Nat) (ws : List (BitVec 64)) :
    ∀ i, (pkcH H o ws i).length = H.length
  | 0 => rfl
  | i + 1 => by simp [pkcH, pkcH_length H o ws i]

theorem pkcH_get (H : List (BitVec 64)) (o : Nat) (ws : List (BitVec 64)) :
    ∀ i c, (pkcH H o ws i)[c]? = if o ≤ c ∧ c < o + i ∧ c < H.length then some (ws.getD (c - o) 0) else H[c]?
  | 0, c => by simp [pkcH]; omega
  | i + 1, c => by
    simp only [pkcH, List.getElem?_set, pkcH_length]
    rw [pkcH_get H o ws i c]
    by_cases e : o + i = c
    · subst e; by_cases hl : o + i < H.length <;> simp [hl]
    · simp only [e, ite_false]
      by_cases h1 : o ≤ c ∧ c < o + i ∧ c < H.length
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem pprefix_set_ge {l L : List (BitVec 64)} (h : l <+: L) (c : Nat) (hc : l.length ≤ c) (w : BitVec 64) :
    l <+: L.set c w := by
  obtain ⟨r, rfl⟩ := h
  refine ⟨r.set (c - l.length) w, ?_⟩
  rw [List.set_append_right _ _ (by omega)]

theorem pprefix_kcH {l H : List (BitVec 64)} (h : l <+: H) (o : Nat) (ho : l.length ≤ o) (ws : List (BitVec 64)) :
    ∀ n, l <+: pkcH H o ws n
  | 0 => h
  | n + 1 => pprefix_set_ge (pprefix_kcH h o ho ws n) _ (by omega) _

def pstoresP (kb : MlS) : Nat → List (ExpHOL 64) → ProgHOL 64 → ProgHOL 64
  | _, [], rest => rest
  | j, e :: es, rest => .seq (.store (.op .add [vv kb, .const (BitVec.ofNat 64 (8 * j))]) e) (pstoresP kb (j + 1) es rest)

/-- Allocate a block for `es` and store them in order; its address in `x`. -/
def allocWr (C : Ctx) (x : MlS) (es : List (ExpHOL 64)) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const (BitVec.ofNat 64 (8 * es.length))) (pstoresP x 0 es rest)

theorem pcellA_add (C : Ctx) (j k : Nat) : cellA C (j + k) = cellA C j + BitVec.ofNat 64 (8 * k) := by
  unfold cellA
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.mul_add, Nat.add_mod]

section
variable {σ : Type}

theorem pstoresP_spec {α : Type} (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (D : List MlS) (kb : MlS)
    (r : Nat) (hkb : Γ.get kb = some (cellA C r)) (ws : List (BitVec 64)) {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64) :
    ∀ (es : List (ExpHOL 64)) (j : Nat) (H : List (BitVec 64)), j + es.length ≤ ws.length →
      r + ws.length ≤ H.length → 8 * (r + ws.length) < 2 ^ 64 →
      (∀ i (hi : i < es.length), sev Γ es[i] = some (ws.getD (j + i) 0)) →
      SpecR (Inv (ctxH C (pkcH H r ws (j + es.length))) s Γ [] D) rest s m R →
      SpecR (Inv (ctxH C (pkcH H r ws j)) s Γ [] D) (pstoresP kb j es rest) s m R
  | [], j, H, _, _, _, _, h => h
  | e :: es, j, H, hl, hH, h8, he, h => by
    simp only [List.length_cons] at hl
    have hlen : (pkcH H r ws j).length = H.length := pkcH_length _ _ _ _
    refine specR_heapStoreI (C := ctxH C (pkcH H r ws j)) (ctxOK_H hok _) _ e (r + j) (by simp only [ctxH]; omega)
      (ws.getD j 0)
      (by simp only [sev, vv, hkb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rw [← pcellA_add]; rfl)
      (by have := he 0 (by simp); simpa using this) ?_
    refine pstoresP_spec C hok s Γ D kb r hkb ws rest es (j + 1) H (by omega) hH h8
      (fun i hi => by have := he (i + 1) (by simp; omega); simpa [show j + (i + 1) = j + 1 + i by omega] using this)
      (by simpa [show j + 1 + es.length = j + (es.length + 1) by omega] using h)

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
  refine pstoresP_spec C hok s _ D x r hkx ws rest es 0 (H2 ++ wsR) (by omega) (by simp [hwl2, r])
    (by have : H2.length + ws.length ≤ C.HN := hcap2; omega)
    (fun i hi => by simpa using hes (cellA C r) i hi) ?_
  have hp0 : C.H <+: H2 ++ wsR := hp2.trans (List.prefix_append _ _)
  refine hk _ r (pprefix_kcH hp0 r (by have := hp2.length_le; omega) ws _) (hp2.length_le)
    (by simp [pkcH_length, hwl2, r]) (fun i hi => ?_)
  rw [show (0 : Nat) + es.length = ws.length by omega, pkcH_get, ite_eq_left ⟨by omega, by omega, by simp [hwl2]; omega⟩,
    show r + i - r = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

end

/-! ## The generator -/

def pbK0 := ofString "pb_k0"
def pbK1 := ofString "pb_k1"
def pbK2 := ofString "pb_k2"
def pbK3 := ofString "pb_k3"

/-- The record pointers' locals. -/
def pbLocs : List MlS := [pbK0, pbK1, pbK2, pbK3]

/-- Zero to two level-parameter names into a fresh block `[n, h₀, …]` at `x`. -/
def genLpsZ (C : Ctx) (x : MlS) : List ConLeche.Name → ProgHOL 64 → ProgHOL 64
  | [], rest => alloc1 C x (.const 0) rest
  | [a], rest => genLpsB C x [a] rest
  | [a, b], rest => genLpsB C x [a, b] rest
  | _, _ => hang

/-- A pin's constant value, its handles kept in `qN`, `qL`, `qT` (zero to two level parameters). -/
def genPinCVZ (C : Ctx) (cv : ConLeche.ConstantVal) (rest : ProgHOL 64) : ProgHOL 64 :=
  nameP C ((strComps cv.name).getD []) (.seq (.assign .local qN (vv vPn))
    (genLpsZ C qL cv.levelParams (genE C 0 cv.type (.seq (.assign .local qT (vv (ge 0))) rest))))

/-- A plain rule's record `[ctor, nfields, 0, 0, 0, rhs]` at `y`. -/
def genRuleRec (C : Ctx) (y : MlS) (rl : ConLeche.RecRule) (rest : ProgHOL 64) : ProgHOL 64 :=
  nameP C ((strComps rl.ctor).getD []) (.seq (.assign .local qU (vv vPn))
    (genE C 0 rl.rhs (allocWr C y [vv qU, .const (BitVec.ofNat 64 rl.nfields), .const 0, .const 0, .const 0,
      vv (ge 0)] rest)))

/-- Up to two plain rules, their block `[n, r₀, …]` at `qU`. -/
def genRulesRec (C : Ctx) : List ConLeche.RecRule → ProgHOL 64 → ProgHOL 64
  | [], rest => allocWr C qU [.const 0] rest
  | [a], rest => genRuleRec C qX a (allocWr C qU [.const 1, vv qX] rest)
  | [a, b], rest => genRuleRec C qX a (genRuleRec C qW b (allocWr C qU [.const 2, vv qX, vv qW] rest))
  | _, _ => hang

/-- A pinned constant's record at `x`. -/
def genPinRec (C : Ctx) (x : MlS) : ConLeche.ConstantInfo → ProgHOL 64 → ProgHOL 64
  | .indInfo v c, rest => genPinCVZ C v (genNames C c.all (genNames C c.ctors
      (allocWr C x [.const 3, vv qN, vv qL, vv qT] rest)))
  | .ctorInfo v nP nF T, rest => genPinCVZ C v (nameP C ((strComps T).getD []) (.seq (.assign .local qX (vv vPn))
      (allocWr C x [.const 4, vv qN, vv qL, vv qT, .const (BitVec.ofNat 64 nP), .const (BitVec.ofNat 64 nF),
        vv qX] rest)))
  | .recInfo v mI rP isK rs, rest => genPinCVZ C v (genRulesRec C rs
      (allocWr C x [.const 5, vv qN, vv qL, vv qT, .const (BitVec.ofNat 64 mI), .const (BitVec.ofNat 64 rP),
        .const (boolW isK), vv qU] rest))
  | _, _ => hang

/-- The records, one per local. -/
def genRecs (C : Ctx) : List MlS → List ConLeche.ConstantInfo → ProgHOL 64 → ProgHOL 64
  | _, [], rest => rest
  | l :: ls, c :: cs, rest => genPinRec C l c (genRecs C ls cs rest)
  | [], _ :: _, _ => hang

/-- **A pinned block's records**, their pointer block at `res`. -/
def genPinBlk (C : Ctx) (res : MlS) (cs : List ConLeche.ConstantInfo) (rest : ProgHOL 64) : ProgHOL 64 :=
  genRecs C pbLocs cs (allocWr C res (.const (BitVec.ofNat 64 cs.length) :: (pbLocs.take cs.length).map vv) rest)

/-! ## Literal conditions -/

/-- A pinned constant the generator takes: an inductive, a constructor or a recursor with at most two plain
rules, at most two level parameters, its counts small. -/
def pinLitB (c : ConLeche.ConstantInfo) : Bool :=
  ciB 0 12 c && decide (c.toConstantVal.levelParams.length ≤ 2) &&
  match c with
  | .indInfo _ _ => true
  | .ctorInfo _ nP nF _ => decide (nP < 2 ^ 63) && decide (nF < 2 ^ 63)
  | .recInfo _ mI rP _ rs => decide (mI < 2 ^ 63) && decide (rP < 2 ^ 63) && decide (rs.length ≤ 2) &&
      rs.all (fun rl => rl.fire == .plain && decide (rl.nfields < 2 ^ 63))
  | _ => false

/-- What the generator's locals must avoid: the literal interner's and the pin handles'. -/
def NotQ (y : MlS) : Prop :=
  (∀ c j, y ≠ gv c j) ∧ y ≠ vPn ∧ y ≠ vKa ∧ y ≠ qN ∧ y ≠ qL ∧ y ≠ qT ∧ y ≠ qU ∧ y ≠ qX ∧ y ≠ qW

theorem notQ_of {y : MlS} (hg : y.explode.head? ≠ some (BitVec.ofNat 8 'g'.toNat))
    (h : y ≠ vPn ∧ y ≠ vKa ∧ y ≠ qN ∧ y ≠ qL ∧ y ≠ qT ∧ y ≠ qU ∧ y ≠ qX ∧ y ≠ qW) : NotQ y :=
  ⟨fun c j e => gv_ne_of (c := c) (d := j) hg e.symm, h⟩

/-- `Γ'` agrees with `Γ` off the generator's locals and `xs`. -/
def AgreeXs (xs : List MlS) (Γ Γ' : Env) : Prop := ∀ y, NotQ y → y ∉ xs → Γ'.get y = Γ.get y

theorem agreeXs_refl (xs : List MlS) (Γ : Env) : AgreeXs xs Γ Γ := fun _ _ _ => rfl

theorem agreeXs_trans {xs : List MlS} {Γ1 Γ2 Γ3 : Env} (h1 : AgreeXs xs Γ1 Γ2) (h2 : AgreeXs xs Γ2 Γ3) :
    AgreeXs xs Γ1 Γ3 := fun y h hy => (h2 y h hy).trans (h1 y h hy)

theorem agreeXs_mono {xs ys : List MlS} {Γ1 Γ2 : Env} (h : AgreeXs xs Γ1 Γ2) (hs : ∀ y ∈ xs, y ∈ ys) :
    AgreeXs ys Γ1 Γ2 := fun y h1 h2 => h y h1 (fun hy => h2 (hs y hy))

theorem agreeXs_of_Q {xs : List MlS} {Γ1 Γ2 : Env} (h : AgreeQ Γ1 Γ2) : AgreeXs xs Γ1 Γ2 :=
  fun y ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ _ => h y h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem agreeXs_of_L {xs : List MlS} {Γ1 Γ2 : Env} {d : Nat} (h : AgreeL Γ1 Γ2 d) : AgreeXs xs Γ1 Γ2 :=
  agreeXs_of_Q (agreeQ_of_L (agreeL_mono h (Nat.zero_le _)))

theorem agreeXs_cons {xs : List MlS} {Γ : Env} {x : MlS} (hx : x ∈ xs ∨ ¬ NotQ x) (w : BitVec 64) :
    AgreeXs xs Γ ((x, w) :: Γ) := fun y hy hyx => by
  have hne : y ≠ x := by
    rintro rfl
    rcases hx with h | h
    · exact hyx h
    · exact h hy
  rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hne)]

theorem notQ_q {x : MlS} (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) : ¬ NotQ x := by
  rintro ⟨-, -, -, h4, h5, h6, h7, h8, h9⟩
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

section
variable {σ : Type}

/-- **`genLpsZ`**: zero to two names interned, their handles a fresh block at `x`. -/
theorem genLpsZ_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (hqU : qU ∈ D) (x : MlS) (hx : x ∈ D) (hxv : x ≠ vPn ∧ x ≠ vKa ∧ x ≠ qU)
    (ns : List ConLeche.Name) (hns : ∀ n ∈ ns, NameLit n) (hl : ns.length ≤ 2)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : List NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ hs s' Γ' H' o, H0 <+: H' → (∀ y, y ≠ vPn → y ≠ vKa → y ≠ qU → y ≠ x → Γ'.get y = Γ.get y) →
      Frontend.internNameList ns s = .ok (hs, s') →
      Γ'.get x = some (cellA C o) → BlkAt H' o (hs.map Enc.idxW) →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k hs) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genLpsZ C x ns rest) s (Frontend.internNameList ns >>= k) R := by
  match ns, hl with
  | [], _ =>
    simp only [genLpsZ, Frontend.internNameList, pure_bind]
    refine specR_alloc1I (C := ctxH C H0) (ctxOK_H G.hok H0) x (.const 0) 0 hx (fun _ => rfl)
      (fun H2 ws hp hws => ?_)
    have hp' : H0 <+: _ := hp.trans (img1_prefix H2 ws (0 : BitVec 64) hws)
    refine hk [] s _ _ H2.length hp' (fun y _ _ _ hyx => ?_) rfl (by simp [Env.get_cons]; rfl)
      ⟨by simpa using img1_get H2 ws (0 : BitVec 64) hws, fun i hi => by simp at hi⟩
    rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hyx)]
  | [a], _ =>
    exact genLpsB_spec ra G hqU x hx hxv [a] hns (Or.inl rfl) H0 rest Γ M s hk
  | [a, b], _ =>
    exact genLpsB_spec ra G hqU x hx hxv [a, b] hns (Or.inr rfl) H0 rest Γ M s hk

/-- **`genPinCVZ`**: the pin's constant value interned (`plainCV`), its handles in `qN`, `qL`, `qT`. -/
theorem genPinCVZ_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D)
    (cv : ConLeche.ConstantVal) (hcv : CVLit 0 12 cv) (hl : cv.levelParams.length ≤ 2)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantVal → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H' o, H0 <+: H' → AgreeQ Γ Γ' → plainCV cv s = .ok (r, s') →
      Γ'.get qN = some (Enc.idxW r.name) → Γ'.get qL = some (cellA C o) → BlkAt H' o (r.levelParams.map Enc.idxW) →
      Γ'.get qT = some (Enc.idxW r.type) → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genPinCVZ C cv rest) s (plainCV cv >>= k) R := by
  obtain ⟨hn, hls, he, hde⟩ := hcv
  unfold genPinCVZ
  simp only [plainCV, bind_assoc]
  refine name_stepP ra G _ hn H0 _ Γ M s (fun h1 s1 Γ1 hf1 hv1 hr1 => ?_)
  refine specR_assignI qN (vv vPn) (Enc.idxW h1) (hq qN (by simp)) (by simp only [sev, sev_vv, hv1]) ?_
  refine genLpsZ_spec ra G (hq qU (by simp)) qL (hq qL (by simp)) ⟨by decide, by decide, by decide⟩
    _ hls hl H0 _ _ [] s1 (fun hs s2 Γ2 H2 o hp2 ag2 hr2 hx2 hb2 => ?_)
  refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa 12 G.hD _ 0 H2 _ Γ2 [] s2 he (by omega)
    (fun h3 s3 Γ3 H3 hp3 ag3 hv3 hr3 => ?_)
  refine specR_assignI qT (vv (ge 0)) (Enc.idxW h3) (hq qT (by simp)) (by simp only [sev, sev_vv, hv3]) ?_
  simp only [pure_bind]
  have hne : ∀ (x : MlS), (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) → ∀ c j, x ≠ gv c j := by
    intro x hx c j e; subst e
    have := gv_ne_q c j
    rcases hx with h | h | h | h | h | h <;> simp_all
  have k3 : ∀ x, (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) → Γ3.get x = Γ2.get x := fun x hx =>
    ag3 x (fun c j _ => hne x hx c j) (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine hk ⟨h1, hs, h3⟩ s3 _ H3 o (hp2.trans hp3) ?_ (bind_ok_of hr1 (bind_ok_of hr2 (bind_ok_of hr3 rfl)))
    ?_ ?_ (blkAt_mono hb2 hp3) (by simp [Env.get_cons])
  · refine agreeQ_trans ?_ (agreeQ_trans (agreeQ_of_L ag3) (agreeQ_cons (Or.inr (Or.inr (Or.inl rfl))) _))
    refine fun y hy h1' h2' hN hL _ hU _ _ => ?_
    rw [ag2 y h1' h2' hU hL, Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hN)]
    exact hf1 y h1' h2'
  · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)), k3 qN (Or.inl rfl),
      ag2 qN (by decide) (by decide) (by decide) (by decide)]
    simp [Env.get_cons]
  · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)), k3 qL (Or.inr (Or.inl rfl))]
    exact hx2

theorem get_q_of_L {Γ Γ' : Env} {d : Nat} (h : AgreeL Γ Γ' d) {x : MlS}
    (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) : Γ'.get x = Γ.get x := agreeL_q h hx

theorem cve_of_words {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {cv : IConstantVal} {w : BitVec 64}
    (h1 : H[o + 1]? = some (Enc.idxW cv.name)) (h2 : H[o + 2]? = some w) (hl : ENList EB H w cv.levelParams)
    (h3 : H[o + 3]? = some (Enc.idxW cv.type)) : CVE EB H (o + 1) cv :=
  ⟨h1, ⟨w, by rwa [show o + 1 + 1 = o + 2 by omega], hl⟩, by rwa [show o + 1 + 2 = o + 3 by omega]⟩

theorem enlist_of_blkAt {C : Ctx} {H : List (BitVec 64)} {o : Nat} {xs : List NIdx}
    (h : BlkAt H o (xs.map Enc.idxW)) : ENList C.HB H (cellA C o) xs := ⟨o, rfl, h⟩

/-- **`genRuleRec`**: a plain rule interned (`plainRule`), its record at `y`. -/
theorem genRuleRec_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) (y : MlS) (hy : y ∈ D)
    (hyq : y = qX ∨ y = qW)
    (rl : ConLeche.RecRule) (hrl : RuleLit 0 12 rl) (hpl : rl.fire = .plain) (hnf : rl.nfields < 2 ^ 63)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IRecRule → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H' o, H0 <+: H' → AgreeQ Γ Γ' → (∀ z, (z = qN ∨ z = qL ∨ z = qT ∨ (z ≠ y ∧ z ≠ qU)) →
        (z = qN ∨ z = qL ∨ z = qT ∨ z = qX ∨ z = qW) → Γ'.get z = Γ.get z) →
      plainRule rl s = .ok (r, s') → Γ'.get y = some (cellA C o) → RuleE C.HB H' o r →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genRuleRec C y rl rest) s (plainRule rl >>= k) R := by
  obtain ⟨hcn, -, hre, hrd⟩ := hrl
  obtain ⟨cn, nf, fire, rhs⟩ := rl
  simp only at hpl hnf hcn hre hrd; subst hpl
  unfold genRuleRec
  simp only [plainRule, plainFire, bind_assoc, pure_bind]
  refine name_stepP ra G cn hcn H0 _ Γ M s (fun hc s1 Γ1 hf1 hv1 hr1 => ?_)
  refine specR_assignI qU (vv vPn) (Enc.idxW hc) (hq qU (by simp)) (by simp only [sev_vv, hv1]) ?_
  refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa 12 G.hD _ 0 H0 _ _ [] s1 hre (by omega)
    (fun hr s2 Γ2 H2 hp2 ag2 hv2 hr2 => ?_)
  have hu2 : Γ2.get qU = some (Enc.idxW hc) := by
    rw [get_q_of_L ag2 (by simp)]; simp [Env.get_cons]
  have hlay := (ctxOK_H G.hok H2).heapLay
  refine specR_allocWrI (C := ctxH C H2) (ctxOK_H G.hok H2) y hy _
    [Enc.idxW hc, BitVec.ofNat 64 nf, 0, 0, 0, Enc.idxW hr] rfl (by simp) (fun v i hi => ?_)
    (fun H3 o hp3 hle3 hlen3 hget3 => ?_)
  · have hyU : y ≠ qU := by rcases hyq with rfl | rfl <;> decide
    have hyE : y ≠ ge 0 := by
      rcases hyq with rfl | rfl
      · exact Ne.symm (gv_ne_q 'e' 0).2.2.2.2.1
      · exact Ne.symm (gv_ne_q 'e' 0).2.2.2.2.2
    simp only [List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | _ | _ | _ | _ | i
    · simp [sev_vv, Env.get_cons, Ne.symm hyU, hu2]
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [sev_vv, Env.get_cons, Ne.symm hyE, hv2]
    · omega
  refine hk ⟨hc, nf, .plain, hr⟩ s2 _ H3 o (hp2.trans hp3) ?_ ?_
    (by simp only [plainRule, plainFire, pure_bind]; exact bind_ok_of hr1 (bind_ok_of hr2 rfl))
    (by simp [Env.get_cons]; rfl) ?_
  · refine agreeQ_trans (fun z _ h1 h2 _ _ _ _ _ _ => hf1 z h1 h2) (agreeQ_trans
      (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _) (agreeQ_trans (agreeQ_of_L ag2)
        (agreeQ_cons (by rcases hyq with rfl | rfl <;> simp) _)))
  · intro z hz hzq
    have hzy : z ≠ y := by
      rcases hz with rfl | rfl | rfl | ⟨h, -⟩
      · rcases hyq with rfl | rfl <;> decide
      · rcases hyq with rfl | rfl <;> decide
      · rcases hyq with rfl | rfl <;> decide
      · exact h
    have hzU : z ≠ qU := by
      rcases hz with rfl | rfl | rfl | ⟨-, h⟩
      · decide
      · decide
      · decide
      · exact h
    have hq' := q_not_gen (x := z) (by rcases hzq with h | h | h | h | h <;> simp [h])
    rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hzy),
      get_q_of_L ag2 (by rcases hzq with h | h | h | h | h <;> simp [h]), Env.get_cons,
      ite_eq_right_iff.mpr (fun e => absurd e hzU), hf1 z hq'.2.1 hq'.2.2]
  · have g := fun i (hi : i < 6) => hget3 i (by simpa using hi)
    refine ⟨by simpa using g 0 (by decide), ⟨by simpa using g 1 (by decide), hnf⟩, by simpa [FireE] using g 2 (by decide),
      by simpa using g 5 (by decide)⟩


theorem q_frame_nl {Γ Γ' : Env} (h : AgreeQ Γ Γ') {x : MlS} (hx : NotQ x) : Γ'.get x = Γ.get x :=
  h x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1
    hx.2.2.2.2.2.2.2.2

theorem rulesE_nil {C : Ctx} {H : List (BitVec 64)} {o : Nat} (h : H[o]? = some (BitVec.ofNat 64 0)) :
    RulesE C.HB H (cellA C o) [] := ⟨o, rfl, by simpa using h, fun i hi => by simp at hi⟩

/-- **`genRulesRec`**: up to two plain rules interned (`plainRules`), their block's address in `qU`. -/
theorem genRulesRec_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D)
    (rs : List ConLeche.RecRule) (hrs : ∀ r ∈ rs, RuleLit 0 12 r ∧ r.fire = .plain ∧ r.nfields < 2 ^ 63)
    (hl : rs.length ≤ 2)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : List IRecRule → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H' w, H0 <+: H' → AgreeQ Γ Γ' → (∀ z, (z = qN ∨ z = qL ∨ z = qT) → Γ'.get z = Γ.get z) →
      plainRules rs s = .ok (r, s') → Γ'.get qU = some w → RulesE C.HB H' w r →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genRulesRec C rs rest) s (plainRules rs >>= k) R := by
  have hU := hq qU (by simp)
  match rs, hl with
  | [], _ =>
    simp only [genRulesRec, plainRules, pure_bind]
    refine specR_allocWrI (C := ctxH C H0) (ctxOK_H G.hok H0) qU hU _ [0] rfl (by simp)
      (fun v i hi => by simp at hi; subst hi; rfl) (fun H3 o hp3 _ _ hget3 => ?_)
    refine hk [] s _ H3 (cellA C o) hp3 (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _)
      (fun z hz => ?_) rfl (by simp [Env.get_cons]; rfl) (rulesE_nil (by simpa using hget3 0 (by simp)))
    rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by rcases hz with rfl | rfl | rfl <;> decide))]
  | [a], _ =>
    obtain ⟨ha1, ha2, ha3⟩ := hrs a (by simp)
    simp only [genRulesRec, plainRules, bind_assoc]
    refine genRuleRec_spec ra G hq qX (hq qX (by simp)) (Or.inl rfl) a ha1 ha2 ha3 H0 _ Γ M s
      (fun r1 s1 Γ1 H1 o1 hp1 ag1 fr1 hr1 hx1 hR1 => ?_)
    simp only [plainRules, pure_bind]
    refine specR_allocWrI (C := ctxH C H1) (ctxOK_H G.hok H1) qU hU _ [1, cellA C o1] rfl (by simp)
      (fun v i hi => ?_) (fun H3 o hp3 _ _ hget3 => ?_)
    · simp only [List.length_cons, List.length_nil] at hi
      rcases i with _ | _ | i
      · rfl
      · simp [sev_vv, Env.get_cons, hx1, show qX ≠ qU by decide] <;> rfl
      · omega
    refine hk [r1] s1 _ H3 (cellA C o) (hp1.trans hp3)
      (agreeQ_trans ag1 (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _)) (fun z hz => ?_)
      (bind_ok_of hr1 rfl) (by simp [Env.get_cons]; rfl)
      ⟨o, rfl, by simpa using hget3 0 (by simp), fun i hi => ?_⟩
    · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by rcases hz with rfl | rfl | rfl <;> decide))]
      exact fr1 z (by rcases hz with h | h | h <;> simp [h]) (by rcases hz with h | h | h <;> simp [h])
    · simp at hi; subst hi
      exact ⟨o1, by simpa [cellA] using hget3 1 (by simp), ruleE_mono hp3 hR1⟩
  | [a, b], _ =>
    obtain ⟨ha1, ha2, ha3⟩ := hrs a (by simp)
    obtain ⟨hb1, hb2, hb3⟩ := hrs b (by simp)
    simp only [genRulesRec, plainRules, bind_assoc]
    refine genRuleRec_spec ra G hq qX (hq qX (by simp)) (Or.inl rfl) a ha1 ha2 ha3 H0 _ Γ M s
      (fun r1 s1 Γ1 H1 o1 hp1 ag1 fr1 hr1 hx1 hR1 => ?_)
    refine genRuleRec_spec ra G hq qW (hq qW (by simp)) (Or.inr rfl) b hb1 hb2 hb3 H1 _ Γ1 [] s1
      (fun r2 s2 Γ2 H2 o2 hp2 ag2 fr2 hr2 hx2 hR2 => ?_)
    simp only [pure_bind]
    have hx1' : Γ2.get qX = some (cellA C o1) := by
      rw [fr2 qX (Or.inr (Or.inr (Or.inr ⟨by decide, by decide⟩))) (by simp)]; exact hx1
    refine specR_allocWrI (C := ctxH C H2) (ctxOK_H G.hok H2) qU hU _ [2, cellA C o1, cellA C o2] rfl
      (by simp) (fun v i hi => ?_) (fun H3 o hp3 _ _ hget3 => ?_)
    · simp only [List.length_cons, List.length_nil] at hi
      rcases i with _ | _ | _ | i
      · rfl
      · simp [sev_vv, Env.get_cons, hx1', show qX ≠ qU by decide] <;> rfl
      · simp [sev_vv, Env.get_cons, hx2, show qW ≠ qU by decide] <;> rfl
      · omega
    refine hk [r1, r2] s2 _ H3 (cellA C o) (hp1.trans (hp2.trans hp3))
      (agreeQ_trans ag1 (agreeQ_trans ag2 (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _)))
      (fun z hz => ?_) (by simp only [plainRules, bind_assoc, pure_bind]; exact bind_ok_of hr1 (bind_ok_of hr2 rfl))
      (by simp [Env.get_cons]; rfl)
      ⟨o, rfl, by simpa using hget3 0 (by simp), fun i hi => ?_⟩
    · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by rcases hz with rfl | rfl | rfl <;> decide)),
        fr2 z (by rcases hz with h | h | h <;> simp [h]) (by rcases hz with h | h | h <;> simp [h])]
      exact fr1 z (by rcases hz with h | h | h <;> simp [h]) (by rcases hz with h | h | h <;> simp [h])
    · simp at hi
      rcases i with _ | _ | i
      · exact ⟨o1, by simpa [cellA] using hget3 1 (by simp), ruleE_mono (hp2.trans hp3) hR1⟩
      · exact ⟨o2, by rw [show o + 1 + 1 = o + 2 by omega]; simpa [cellA] using hget3 2 (by simp), ruleE_mono hp3 hR2⟩
      · omega

/-- A pinned literal's conditions, unpacked. -/
theorem pinLit_parts {c : ConLeche.ConstantInfo} (h : pinLitB c = true) :
    CILit 0 12 c ∧ c.toConstantVal.levelParams.length ≤ 2 ∧
    match c with
    | .indInfo _ _ => True
    | .ctorInfo _ nP nF _ => nP < 2 ^ 63 ∧ nF < 2 ^ 63
    | .recInfo _ mI rP _ rs => mI < 2 ^ 63 ∧ rP < 2 ^ 63 ∧ rs.length ≤ 2 ∧
        ∀ r ∈ rs, r.fire = .plain ∧ r.nfields < 2 ^ 63
    | _ => False := by
  unfold pinLitB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨ciLit_of h1, h2, ?_⟩
  cases c with
  | indInfo _ _ => trivial
  | ctorInfo _ nP nF _ => simpa using h3
  | recInfo _ mI rP _ rs =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h3
    exact ⟨h3.1.1.1, h3.1.1.2, h3.1.2, fun r hr => h3.2 r hr⟩
  | axiomInfo _ => simp at h3
  | defnInfo _ _ _ => simp at h3
  | thmInfo _ => simp at h3

/-- **`genPinRec`**: a pinned constant interned (`plainCI`), its record at `x`. -/
theorem genPinRec_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) (x : MlS) (hx : x ∈ D) (hxq : NotQ x)
    (c : ConLeche.ConstantInfo) (hc : pinLitB c = true)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H' o, H0 <+: H' → AgreeXs [x] Γ Γ' → plainCI c s = .ok (r, s') →
      Γ'.get x = some (cellA C o) → PinRec C.HB H' o r →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genPinRec C x c rest) s (plainCI c >>= k) R := by
  obtain ⟨hlit, hlen, hkind⟩ := pinLit_parts hc
  have hxN : qN ≠ x := fun e => hxq.2.2.2.1 e.symm
  have hxL : qL ≠ x := fun e => hxq.2.2.2.2.1 e.symm
  have hxT : qT ≠ x := fun e => hxq.2.2.2.2.2.1 e.symm
  have hxU : qU ≠ x := fun e => hxq.2.2.2.2.2.2.1 e.symm
  have hxX : qX ≠ x := fun e => hxq.2.2.2.2.2.2.2.1 e.symm
  cases c with
  | indInfo v caps =>
    simp only [genPinRec, plainCI, bind_assoc]
    refine genPinCVZ_spec ra G hq v hlit.1 hlen H0 _ Γ M s (fun r1 s1 Γ1 H1 o hp1 ag1 hr1 h1 h2 h3 h4 => ?_)
    unfold ConRon.Arena.Frontend.internCaps
    simp only [bind_assoc]
    refine genNames_spec ra G 0 _ H1 _ Γ1 [] s1 hlit.2.1 (fun hs s2 Γ2 H2 hp2 ag2 hr2 => ?_)
    refine genNames_spec ra G 0 _ H2 _ Γ2 [] s2 hlit.2.2 (fun hs' s3 Γ3 H3 hp3 ag3 hr3 => ?_)
    simp only [pure_bind]
    have e3 : ∀ z, (z = qN ∨ z = qL ∨ z = qT ∨ z = qU ∨ z = qX ∨ z = qW) → Γ3.get z = Γ1.get z := fun z hz => by
      rw [get_q_of_L ag3 hz, get_q_of_L ag2 hz]
    refine specR_allocWrI (C := ctxH C H3) (ctxOK_H G.hok H3) x hx _
      [3, Enc.idxW r1.name, cellA C o, Enc.idxW r1.type] rfl (by simp) (fun v i hi => ?_)
      (fun H4 o4 hp4 _ _ hget4 => ?_)
    · simp only [List.length_cons, List.length_nil] at hi
      rcases i with _ | _ | _ | _ | i
      · rfl
      · simp [sev_vv, Env.get_cons, hxN, e3 qN (by simp), h1]
      · simp [sev_vv, Env.get_cons, hxL, e3 qL (by simp), h2] <;> rfl
      · simp [sev_vv, Env.get_cons, hxT, e3 qT (by simp), h4]
      · omega
    have hp14 : H1 <+: H4 := hp2.trans (hp3.trans hp4)
    refine hk _ s3 _ H4 o4 (hp1.trans hp14)
      (agreeXs_trans (agreeXs_of_Q ag1) (agreeXs_trans (agreeXs_of_L ag2) (agreeXs_trans (agreeXs_of_L ag3)
        (agreeXs_cons (Or.inl (by simp)) _))))
      (bind_ok_of hr1 (bind_ok_of (A := ConRon.Arena.Frontend.internCaps caps)
        (by unfold ConRon.Arena.Frontend.internCaps; exact bind_ok_of hr2 (bind_ok_of hr3 rfl)) rfl))
      (by simp [Env.get_cons]; rfl) ⟨cve_of_words (cv := r1) (by simpa using hget4 1 (by simp)) (by simpa using hget4 2 (by simp))
        (enlist_of_blkAt (blkAt_mono h3 hp14)) (by simpa using hget4 3 (by simp)), by simpa using hget4 0 (by simp)⟩
  | ctorInfo v nP nF T =>
    obtain ⟨hnP, hnF⟩ := hkind
    simp only [genPinRec, plainCI, bind_assoc]
    refine genPinCVZ_spec ra G hq v hlit.1 hlen H0 _ Γ M s (fun r1 s1 Γ1 H1 o hp1 ag1 hr1 h1 h2 h3 h4 => ?_)
    refine name_stepP ra G T hlit.2 H1 _ Γ1 [] s1 (fun h s2 Γ2 hf2 hv2 hr2 => ?_)
    refine specR_assignI qX (vv vPn) (Enc.idxW h) (hq qX (by simp)) (by simp only [sev_vv, hv2]) ?_
    simp only [pure_bind]
    have e2 : ∀ z, (z = qN ∨ z = qL ∨ z = qT) → Env.get ((qX, Enc.idxW h) :: Γ2) z = Γ1.get z := fun z hz => by
      have hq' := q_not_gen (x := z) (by rcases hz with h | h | h <;> simp [h])
      rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by rcases hz with rfl | rfl | rfl <;> decide)),
        hf2 z hq'.2.1 hq'.2.2]
    refine specR_allocWrI (C := ctxH C H1) (ctxOK_H G.hok H1) x hx _
      [4, Enc.idxW r1.name, cellA C o, Enc.idxW r1.type, BitVec.ofNat 64 nP, BitVec.ofNat 64 nF, Enc.idxW h] rfl
      (by simp) (fun v i hi => ?_) (fun H4 o4 hp4 _ _ hget4 => ?_)
    · simp only [List.length_cons, List.length_nil] at hi
      rcases i with _ | _ | _ | _ | _ | _ | _ | i
      · rfl
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, sev_vv]
        rw [Env.get_cons, if_neg hxN, e2 qN (by simp), h1] <;> rfl
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, sev_vv]
        rw [Env.get_cons, if_neg hxL, e2 qL (by simp), h2] <;> rfl
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, sev_vv]
        rw [Env.get_cons, if_neg hxT, e2 qT (by simp), h4] <;> rfl
      · rfl
      · rfl
      · simp [sev_vv, Env.get_cons, hxX]
      · omega
    refine hk _ s2 _ H4 o4 (hp1.trans hp4)
      (agreeXs_trans (agreeXs_of_Q ag1) (agreeXs_trans (fun z hz _ => hf2 z hz.2.1 hz.2.2.1)
        (agreeXs_trans (agreeXs_cons (Or.inr (notQ_q (by simp))) _) (agreeXs_cons (Or.inl (by simp)) _))))
      (bind_ok_of hr1 (bind_ok_of hr2 rfl))
      (by simp [Env.get_cons]; rfl) ⟨cve_of_words (cv := r1) (by simpa using hget4 1 (by simp)) (by simpa using hget4 2 (by simp))
        (enlist_of_blkAt (blkAt_mono h3 hp4)) (by simpa using hget4 3 (by simp)), by simpa using hget4 0 (by simp),
        ⟨by simpa using hget4 4 (by simp), hnP⟩, ⟨by simpa using hget4 5 (by simp), hnF⟩,
        by simpa using hget4 6 (by simp)⟩
  | recInfo v mI rP isK rs =>
    obtain ⟨hmI, hrP, hrl, hrs⟩ := hkind
    simp only [genPinRec, plainCI, bind_assoc]
    refine genPinCVZ_spec ra G hq v hlit.1 hlen H0 _ Γ M s (fun r1 s1 Γ1 H1 o hp1 ag1 hr1 h1 h2 h3 h4 => ?_)
    refine genRulesRec_spec ra G hq rs (fun r hr => ⟨hlit.2 r hr, hrs r hr⟩) hrl H1 _ Γ1 [] s1
      (fun rr s2 Γ2 H2 w hp2 ag2 fr2 hr2 hu2 hR2 => ?_)
    simp only [pure_bind]
    refine specR_allocWrI (C := ctxH C H2) (ctxOK_H G.hok H2) x hx _
      [5, Enc.idxW r1.name, cellA C o, Enc.idxW r1.type, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, boolW isK, w] rfl
      (by simp) (fun v i hi => ?_) (fun H4 o4 hp4 _ _ hget4 => ?_)
    · simp only [List.length_cons, List.length_nil] at hi
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      · rfl
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, sev_vv, Env.get_cons, hxN, ite_false]
        rw [fr2 qN (by simp)]; simp [h1]
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, sev_vv, Env.get_cons, hxL, ite_false]
        rw [fr2 qL (by simp)]; simp [h2] <;> rfl
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, sev_vv, Env.get_cons, hxT, ite_false]
        rw [fr2 qT (by simp)]; simp [h4]
      · rfl
      · rfl
      · rfl
      · simp [sev_vv, Env.get_cons, hxU, hu2]
      · omega
    have hp24 : H1 <+: H4 := hp2.trans hp4
    refine hk _ s2 _ H4 o4 (hp1.trans hp24)
      (agreeXs_trans (agreeXs_of_Q ag1) (agreeXs_trans (agreeXs_of_Q ag2) (agreeXs_cons (Or.inl (by simp)) _)))
      (bind_ok_of hr1 (bind_ok_of hr2 rfl))
      (by simp [Env.get_cons]; rfl) ⟨cve_of_words (cv := r1) (by simpa using hget4 1 (by simp)) (by simpa using hget4 2 (by simp))
        (enlist_of_blkAt (blkAt_mono h3 hp24)) (by simpa using hget4 3 (by simp)), by simpa using hget4 0 (by simp),
        ⟨by simpa using hget4 4 (by simp), hmI⟩, ⟨by simpa using hget4 5 (by simp), hrP⟩,
        by simpa using hget4 6 (by simp), ⟨w, by simpa using hget4 7 (by simp), rulesE_mono hp4 hR2⟩⟩
  | axiomInfo _ => exact hkind.elim
  | defnInfo _ _ _ => exact hkind.elim
  | thmInfo _ => exact hkind.elim


/-- **`genRecs`**: the pinned constants interned (`plainCIList`), record `i`'s address in the `i`-th local. -/
theorem genRecs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) :
    ∀ (cs : List ConLeche.ConstantInfo) (ls : List MlS) (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env)
      (M : Mem) (s : AState) {β : Type} {k : List IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop},
      cs.length ≤ ls.length → ls.Nodup → (∀ l ∈ ls, l ∈ D ∧ NotQ l) → (∀ c ∈ cs, pinLitB c = true) →
      (∀ r s' Γ' H' (os : List Nat), H0 <+: H' → AgreeXs ls Γ Γ' → plainCIList cs s = .ok (r, s') →
        os.length = cs.length →
        (∀ i (hl : i < ls.length) (ho : i < os.length), Γ'.get ls[i] = some (cellA C os[i])) →
        (∀ i (hi : i < r.length) (ho : i < os.length), PinRec C.HB H' os[i] r[i]) →
        SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) →
      SpecR (Inv (ctxH C H0) s Γ M D) (genRecs C ls cs rest) s (plainCIList cs >>= k) R := by
  intro cs
  induction cs with
  | nil =>
    intro ls H0 rest Γ M s β k R _ _ _ _ hk
    have e : genRecs C ls [] rest = rest := by cases ls <;> rfl
    rw [e]
    simp only [plainCIList, pure_bind]
    intro t ht
    exact hk [] s Γ H0 [] (List.prefix_refl _) (agreeXs_refl _ _) rfl rfl (fun i _ ho => by simp at ho)
      (fun i hi => by simp at hi) t (lit_dropMem ht)
  | cons c cs ih =>
    intro ls H0 rest Γ M s β k R hlen hnd hls hcs hk
    match ls, hlen, hnd, hls with
    | l :: ls, hlen, hnd, hls =>
      simp only [List.length_cons] at hlen
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨hlD, hlQ⟩ := hls l (by simp)
      simp only [genRecs, plainCIList, bind_assoc]
      refine genPinRec_spec ra G hq l hlD hlQ c (hcs c (by simp)) H0 _ Γ M s
        (fun r1 s1 Γ1 H1 o1 hp1 ag1 hr1 hx1 hP1 => ?_)
      refine ih ls H1 rest Γ1 [] s1 (by omega) hnd'.2 (fun y hy => hls y (by simp [hy]))
        (fun y hy => hcs y (by simp [hy])) (fun r s2 Γ2 H2 os hp2 ag2 hr2 hos hget hpin => ?_)
      simp only [pure_bind]
      refine hk (r1 :: r) s2 Γ2 H2 (o1 :: os) (hp1.trans hp2) ?_ (bind_ok_of hr1 (bind_ok_of hr2 rfl))
        (by simp [hos]) (fun i hl ho => ?_) (fun i hi ho => ?_)
      · refine agreeXs_trans (agreeXs_mono ag1 (by simp)) (agreeXs_mono ag2 (fun y hy => by simp [hy]))
      · rcases i with _ | i
        · simp only [List.getElem_cons_zero]
          rw [ag2 l hlQ hnd'.1]; exact hx1
        · simpa using hget i (by simpa using hl) (by simpa using ho)
      · rcases i with _ | i
        · simpa using pinRec_mono hp2 hP1
        · simpa using hpin i (by simpa using hi) (by simpa using ho)

theorem pbLocs_nodup : pbLocs.Nodup := by decide

theorem pbLocs_notQ : ∀ l ∈ pbLocs, NotQ l := by
  intro l hl
  simp only [pbLocs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;>
    exact notQ_of (by decide) ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **`genPinBlk`**: a pinned block interned (`plainCIList`), its records' pointer block at `res`. -/
theorem genPinBlk_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) (hpb : ∀ l ∈ pbLocs, l ∈ D)
    (res : MlS) (hres : res ∈ D) (hresQ : NotQ res) (hresP : res ∉ pbLocs)
    (cs : List ConLeche.ConstantInfo) (hcs : ∀ c ∈ cs, pinLitB c = true) (hlen : cs.length ≤ 4)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : List IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H' o, H0 <+: H' → AgreeXs (res :: pbLocs) Γ Γ' → plainCIList cs s = .ok (r, s') →
      Γ'.get res = some (cellA C o) → PinBlk C H' o r →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genPinBlk C res cs rest) s (plainCIList cs >>= k) R := by
  unfold genPinBlk
  refine genRecs_spec ra G hq cs pbLocs H0 _ Γ M s (by simp [pbLocs]; omega) pbLocs_nodup
    (fun l hl => ⟨hpb l hl, pbLocs_notQ l hl⟩) hcs (fun r s1 Γ1 H1 os hp1 ag1 hr1 hos hget hpin => ?_)
  have hrl : r.length = cs.length := plainCIList_len _ _ _ _ hr1
  have hlay := (ctxOK_H G.hok H1).heapLay
  refine specR_allocWrI (C := ctxH C H1) (ctxOK_H G.hok H1) res hres _
    (BitVec.ofNat 64 cs.length :: os.map (cellA C)) (by simp [hos, pbLocs]; omega) (by simp [hos]; omega)
    (fun v i hi => ?_) (fun H2 o hp2 _ _ hget2 => ?_)
  · rcases i with _ | i
    · rfl
    · simp only [List.length_cons, List.length_map, List.length_take] at hi
      have hi4 : i < pbLocs.length := by simp [pbLocs] at hi ⊢; omega
      have hio : i < os.length := by omega
      simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_take, sev_vv]
      have hne : pbLocs[i] ≠ res := fun e => hresP (e ▸ List.getElem_mem hi4)
      rw [Env.get_cons, if_neg hne, hget i hi4 hio]
      simp [List.getElem?_map, List.getElem?_eq_getElem hio]
  refine hk r s1 _ H2 o (hp1.trans hp2) (agreeXs_trans (agreeXs_mono ag1 (fun y hy => by simp [hy]))
    (agreeXs_cons (Or.inl (by simp)) _)) hr1 (by simp [Env.get_cons]; rfl)
    ⟨os, by omega, ⟨by simpa [hos, hrl] using hget2 0 (by simp), fun i hi => ?_⟩,
      fun i hi ho => pinRec_mono hp2 (hpin i hi ho)⟩
  have := hget2 (i + 1) (by simpa using hi)
  simp only [List.getElem_cons_succ] at this
  rw [show o + 1 + i = o + (i + 1) by omega]; exact this

end

end ConPanqueque.T.Ind
