import ConPanqueque.ConsIns
import ConPanqueque.ConsTbl
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsLoop ConPanqueque.ConsIns ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning an `app` node into one tier

The twin's per-tier step (`ETables.find?` then `ETables.push` at the `app`
constructor): on a hit the existing handle, on a miss the node appended with
handle `mkWide tier size`. In Pancake: the probe loop, then the hit's handle
or the append. The key is the record's two handle words; its home slot is
`(f·M + a) & mask`, a hash computed in Pancake (any function serves
correctness).
-/

namespace ConPanqueque.ConsIntern

/-- An `app` record as two words: its handles' words. -/
def encApp (x : AppNode) : BitVec 64 × BitVec 64 := (x.f.word.toUInt64.toBitVec, x.a.word.toUInt64.toBitVec)

theorem encApp_inj : ∀ x y : AppNode, encApp x = encApp y → x = y := by
  intro ⟨⟨f1⟩, ⟨a1⟩⟩ ⟨⟨f2⟩, ⟨a2⟩⟩ h
  simp only [encApp, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : f1 = f2 := by
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h1; simpa using this
  have e2 : a1 = a2 := by
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h2; simpa using this
  subst e1; subst e2; rfl

/-- The home slot: a multiplicative hash of the two words, masked to `n = 2^b` slots. -/
def homeApp (b : Nat) (x : AppNode) : Nat :=
  ((encApp x).1 * 0x9e3779b97f4a7c15#64 + (encApp x).2).toNat % 2 ^ b

/-- The twin's per-tier `app` intern: the cons probe, then on a miss the append with handle
`mkWide tier size` (the `app` arms of `ETables.find?` and `ETables.push`). -/
def tierApp (tb : Tbl AppNode EIdx UInt64) (x : AppNode) (d : UInt64) (tier : UInt32) :
    Tbl AppNode EIdx UInt64 × EIdx :=
  match tb.find? x with
  | some h => (tb, h)
  | none => (tb.push x d (Idx.mkWide tier (UInt32.ofNat tb.size)), Idx.mkWide tier (UInt32.ofNat tb.size))

def lTier := ofString "ctier"
def lI := ofString "ci"
def vv (n : MlS) : ExpHOL 64 := .var .local n

/-- A wide handle's word from the tier and an index expression. -/
def hwE (idx : ExpHOL 64) : ExpHOL 64 :=
  .op .add [.panop .mul [vv lTier, .const 2147483648], .const 1073741824, idx]

def homeE : ExpHOL 64 :=
  .op .and [.op .add [.panop .mul [vv lKf, .const 0x9e3779b97f4a7c15#64], vv lKa], vv lM]

/-- The per-tier `app` intern in Pancake. -/
def internTier : ProgHOL 64 :=
  .dec lJ .one homeE (.dec lC .one (.op .add [vv lM, .const 1])
   (.dec lG .one (.const 1) (.dec lRes .one (.const 0) (.dec lV .one (.const 0)
    (.seq probeLoop
     (.ite (.cmp .notEqual (vv lRes) (.const 0)) (.return (hwE (.op .sub [vv lRes, .const 1])))
      (.ite (.cmp .equal (vv lC) (.const 0)) hang
       (.dec lI .one (.load .one (vv lC0)) (.seq insBody (.return (hwE (vv lI))))))))))))

theorem at_zero {n h : Nat} (hh : h < n) : at_ n h 0 = h := by
  simp only [at_, Nat.add_zero]; exact Nat.mod_eq_of_lt hh

theorem home_mask (w : BitVec 64) (b : Nat) (hb : b ≤ 56) :
    w &&& BitVec.ofNat 64 (2 ^ b - 1) = BitVec.ofNat 64 (w.toNat % 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ b ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hb
  have h2 : (2 : Nat) ^ 56 < 2 ^ 64 := by decide
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 2 ^ b - 1) (by omega),
    Nat.mod_eq_of_lt (a := w.toNat % 2 ^ b) (by have := Nat.mod_lt w.toNat (Nat.two_pow_pos b); omega)]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat b

/-- The table geometry and inputs `internTier` reads from its locals. -/
structure Locals {σ : Type} (t : PanSemStateFiniteExact 64 σ) (x : AppNode) (n cap : Nat) (C S R D dv tier : BitVec 64) :
    Prop where
  kf : t.locals.lookup lKf = some (.val (.word (encApp x).1))
  ka : t.locals.lookup lKa = some (.val (.word (encApp x).2))
  s : t.locals.lookup lS = some (.val (.word S))
  r : t.locals.lookup lR = some (.val (.word R))
  m : t.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (n - 1))))
  d : t.locals.lookup lD = some (.val (.word D))
  c : t.locals.lookup lC0 = some (.val (.word C))
  cap : t.locals.lookup lCap = some (.val (.word (BitVec.ofNat 64 cap)))
  dv : t.locals.lookup lDv = some (.val (.word dv))
  tier : t.locals.lookup lTier = some (.val (.word tier))

theorem mkWide_word (tier : UInt32) (i : Nat) (ht : tier ≤ 1) (hi : i < 2 ^ 30) :
    (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec =
      tier.toUInt64.toBitVec * 2147483648 + 1073741824 + BitVec.ofNat 64 i := by
  have ht' : tier.toNat ≤ 1 := by simpa [UInt32.le_iff_toNat_le] using ht
  have hw : (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toNat = tier.toNat * 2147483648 + 1073741824 + i := by
    show (tier * 2147483648 + 1073741824 + UInt32.ofNat i).toNat = _
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rcases (by omega : tier.toNat = 0 ∨ tier.toNat = 1) with h | h <;> rw [h] <;> omega
  apply BitVec.eq_of_toNat_eq
  have e1 : (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec.toNat =
      (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toNat := by simp
  have e2 : tier.toUInt64.toBitVec.toNat = tier.toNat := by simp
  have l1 : (2147483648 : BitVec 64).toNat = 2147483648 := rfl
  have l2 : (1073741824 : BitVec 64).toNat = 1073741824 := rfl
  have l3 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
  rw [e1, hw, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, e2, l1, l2, l3]
  rcases (by omega : tier.toNat = 0 ∨ tier.toNat = 1) with h | h <;> rw [h] <;> omega

/-- What `internTier` guarantees about a run: a stop, or the twin's handle with the twin's new
table represented. Insensitive to the final locals (`ires_locals`). -/
def IRes {σ : Type} (t : PanSemStateFiniteExact 64 σ) (tb : Tbl AppNode EIdx UInt64) (n b cap : Nat)
    (C S R D : BitVec 64) (x : AppNode) (dv : UInt64) (tier : UInt32)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨
    (r.1 = some (.returned (.val (.word (tierApp tb x dv tier).2.word.toUInt64.toBitVec))) ∧
      ∃ rows' ders' slots', TMem r.2 encApp rows' ders' slots' n cap C S R D ∧
        Inv (α := AppNode) (homeApp b) rows' slots' n ∧
        TblRel (tierApp tb x dv tier).1 rows' (fun i => Idx.mkWide tier (UInt32.ofNat i)) ∧
        (tierApp tb x dv tier).1.der.toList.map (·.toBitVec) = ders' ∧
        r.2.code = t.code ∧ r.2.globals = t.globals ∧ r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
        ∀ a, ¬ inReg C D cap a → r.2.memory a = t.memory a)

theorem tmem_locals {σ : Type} {st : PanSemStateFiniteExact 64 σ} {α : Type} [DecidableEq α]
    {enc : α → BitVec 64 × BitVec 64} {rows : List α} {ders : List (BitVec 64)} {slots : List Nat} {n cap : Nat}
    {C S R D : BitVec 64} (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : TMem st enc rows ders slots n cap C S R D) :
    TMem { st with locals := L } enc rows ders slots n cap C S R D :=
  ⟨⟨h.mem.slot, h.mem.row⟩, h.cnt, h.dlen, h.der, h.le, h.room, h.layC, h.layS, h.layR, h.layD⟩

theorem tmem_of_eq {σ : Type} {t t' : PanSemStateFiniteExact 64 σ} {α : Type} [DecidableEq α]
    {enc : α → BitVec 64 × BitVec 64} {rows : List α} {ders : List (BitVec 64)} {slots : List Nat} {n cap : Nat}
    {C S R D : BitVec 64} (h : TMem t enc rows ders slots n cap C S R D) (hm : t'.memory = t.memory)
    (hd : t'.memaddrs = t.memaddrs) : TMem t' enc rows ders slots n cap C S R D := by
  obtain ⟨⟨hs, hr⟩, ⟨c1, c2⟩, hdl, hder, hle, hroom, l1, l2, l3, l4⟩ := h
  refine ⟨⟨fun j hj => ?_, fun i hi => ?_⟩, ⟨by rw [hd]; exact c1, by rw [hm]; exact c2⟩, hdl,
    fun i hi => ?_, hle, fun i hi => ?_, l1, l2, l3, l4⟩
  · obtain ⟨v, a1, a2, a3, a4⟩ := hs j hj; exact ⟨v, a1, a2, by rw [hd]; exact a3, by rw [hm]; exact a4⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hr i hi; exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hm]; exact a3, by rw [hm]; exact a4⟩
  · obtain ⟨a1, a2⟩ := hder i hi; exact ⟨by rw [hd]; exact a1, by rw [hm]; exact a2⟩
  · obtain ⟨a1, a2, a3⟩ := hroom i hi; exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hd]; exact a3⟩

theorem ires_locals {σ : Type} {t : PanSemStateFiniteExact 64 σ} {tb : Tbl AppNode EIdx UInt64} {n b cap : Nat}
    {C S R D : BitVec 64} {x : AppNode} {dv : UInt64} {tier : UInt32} {r1 : Option (PanSemResultExact 64)}
    {st : PanSemStateFiniteExact 64 σ} (L : HolFiniteMapExact MlS (ValueHOL 64))
    (h : IRes t tb n b cap C S R D x dv tier (r1, st)) : IRes t tb n b cap C S R D x dv tier (r1, { st with locals := L }) := by
  rcases h with h | ⟨hr, rows', ders', slots', hT, hi, hrel, hd, c1, c2, c3, c4, c5⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr, rows', ders', slots', tmem_locals L hT, hi, hrel, hd, c1, c2, c3, c4, c5⟩

theorem internTier_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (tb : Tbl AppNode EIdx UInt64)
    (rows : List AppNode) (ders : List (BitVec 64)) (slots : List Nat) (n b cap : Nat) (C S R D : BitVec 64)
    (x : AppNode) (dv : UInt64) (tier : UInt32)
    (hn : n = 2 ^ b) (hb : b ≤ 56) (hcap : cap < 2 ^ 30)
    (hT : TMem t encApp rows ders slots n cap C S R D) (hinv : Inv (α := AppNode) (homeApp b) rows slots n)
    (hrel : TblRel tb rows (fun i => Idx.mkWide tier (UInt32.ofNat i)))
    (hder : tb.der.toList.map (·.toBitVec) = ders) (htier : tier ≤ 1)
    (hL : Locals t x n cap C S R D dv.toBitVec tier.toUInt64.toBitVec) (hck : n + 2 ≤ t.clock) :
    IRes t tb n b cap C S R D x dv tier (evaluateHOLFiniteState t internTier) := by
  have hn56 : n ≤ 2 ^ 56 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  have hpos : 0 < n := hinv.pos
  let hx := homeApp b x
  have hxn : hx < n := hinv.home_lt x
  have ehome : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) homeE =
      some (.val (.word (BitVec.ofNat 64 hx))) := by
    simp [homeE, vv, evalHOLExact, evalListHOLExact, hL.kf, hL.ka, hL.m, wordOpHOL, wordOp, panOpHOL, valueIsWord,
      valueWord]
    rw [show (n - 1) = 2 ^ b - 1 by rw [hn]]
    show _ &&& (_ &&& (18446744073709551615#64)) = _
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes, home_mask _ b hb]
    rfl
  unfold internTier
  obtain ⟨L1, e1⟩ := dec_word' t lJ homeE _ _ ehome
  rw [e1]; apply ires_locals
  let t1 := setVarHOLFinite lJ (.val (.word (BitVec.ofNat 64 hx))) t
  have hM1 : t1.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (n - 1)))) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hL.m
  obtain ⟨L2, e2⟩ := dec_word' t1 lC (.op .add [vv lM, .const 1]) (BitVec.ofNat 64 n) _
    (by simp [vv, evalHOLExact, evalListHOLExact, hM1, wordOpHOL, wordOp, valueIsWord, valueWord]
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
  rw [e2]; apply ires_locals
  let t2 := setVarHOLFinite lC (.val (.word (BitVec.ofNat 64 n))) t1
  obtain ⟨L3, e3⟩ := dec_word' t2 lG (.const 1) 1 _ (by simp [evalHOLExact])
  rw [e3]; apply ires_locals
  let t3 := setVarHOLFinite lG (.val (.word 1)) t2
  obtain ⟨L4, e4⟩ := dec_word' t3 lRes (.const 0) 0 _ (by simp [evalHOLExact])
  rw [e4]; apply ires_locals
  let t4 := setVarHOLFinite lRes (.val (.word 0)) t3
  obtain ⟨L5, e5⟩ := dec_word' t4 lV (.const 0) 0 _ (by simp [evalHOLExact])
  rw [e5]; apply ires_locals
  let t5 := setVarHOLFinite lV (.val (.word 0)) t4
  have l5 : ∀ y, y ≠ lV → y ≠ lRes → y ≠ lG → y ≠ lC → y ≠ lJ → t5.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5; simp only [t5, t4, t3, t2, t1]
    rw [lookup_setVar_other _ _ a1, lookup_setVar_other _ _ a2, lookup_setVar_other _ _ a3, lookup_setVar_other _ _ a4,
      lookup_setVar_other _ _ a5]
  let ans := probeR rows slots n x n hx
  have hI : LInv t5 encApp rows slots n S R x ans t5 :=
    ⟨rfl, rfl, rfl, rfl, rfl, by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.s,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.r,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.m,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.kf,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.ka,
      fun _ _ _ _ _ _ => rfl, n, hx, hxn,
      by simp only [t5, t4, t3]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide),
        lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
      by simp only [t5, t4, t3, t2]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide),
        lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
      ⟨0, lookup_setVar_same _ _ _⟩,
      Or.inl ⟨by simp only [t5, t4]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
              by simp only [t5]; rw [lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
              rfl, Nat.le_refl _, by show n + 1 ≤ t.clock; omega, by omega⟩⟩
  have hmem5 : Mem t5 encApp rows slots n S R := ⟨hT.mem.slot, hT.mem.row⟩
  obtain ⟨t6, ev6, hI6, hg6⟩ := probeLoop_spec t5 encApp rows slots n b S R x ans hn (by omega) hmem5
    hinv.named encApp_inj hI
  rw [seq_normal _ ev6]
  obtain ⟨m6, d6, c6, g6, ta6, hS6, hR6, hM6, hKf6, hKa6, hfr6, f, j, hj, hC6, hJ6, hV6, br⟩ := hI6
  obtain ⟨_, hres6, hemp, hfull, _⟩ := br.resolve_left (fun ⟨hg, _⟩ => by rw [hg6] at hg; cases hg)
  have hprobe := probeR_toOpt rows slots n x n hx
  have hfind := find_probe (homeApp b) tb rows slots n _ hrel hinv x
  have hmt6 : t6.memory = t.memory := m6
  have hdt6 : t6.memaddrs = t.memaddrs := d6
  have l6 : ∀ y, t6.locals.lookup y = _ := fun y => rfl
  -- the test on the result
  cases hans : ans with
  | hit i =>
    have hi : rows[i]? = some x := (probe_correct (homeApp b) rows slots n hinv x).1 i (by rw [← hprobe]; show ans.toOpt = _; rw [hans]; rfl)
    have hil : i < rows.length := (List.getElem?_eq_some_iff.mp hi).1
    have hcapl : rows.length ≤ cap := hT.le
    rw [hans] at hres6
    simp only [PR.toOpt, Option.map_some, Option.getD_some] at hres6
    have hne : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.cmp .notEqual (vv lRes) (.const 0)) = some (.val (.word 1)) := by
      simp [vv, evalHOLExact, hres6, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    rw [ite_word t6 _ _ _ _ hne]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    have htw : t6.locals.lookup lTier = some (.val (.word tier.toUInt64.toBitVec)) := by
      rw [hfr6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.tier
    have hw : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (hwE (.op .sub [vv lRes, .const 1])) =
        some (.val (.word (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec)) := by
      rw [mkWide_word tier i htier (by omega)]
      simp [hwE, vv, evalHOLExact, evalListHOLExact, htw, hres6, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      have : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
      rw [this, BitVec.add_assoc]
    have eret : evaluateHOLFiniteState t6 (.return (hwE (.op .sub [vv lRes, .const 1]))) =
        (some (.returned (.val (.word (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec))),
          emptyLocalsHOLFinite t6) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only [hw]; simp [shapeOfHOLExact]
    rw [eret]
    have hfi : tb.find? x = some (Idx.mkWide tier (UInt32.ofNat i)) := by
      rw [hfind, ← hprobe]; show (ans.toOpt).map _ = _; rw [hans]; rfl
    have htA : tierApp tb x dv tier = (tb, Idx.mkWide tier (UInt32.ofNat i)) := by simp only [tierApp, hfi]
    right
    refine ⟨by simp [htA], rows, ders, slots, ?_, hinv, by rw [htA]; exact hrel, by rw [htA]; exact hder, ?_, ?_, ?_, ?_,
      fun a _ => by rw [show (emptyLocalsHOLFinite t6).memory = t6.memory from rfl, hmt6]⟩
    · exact tmem_of_eq hT (by simp [emptyLocalsHOLFinite, hmt6]) (by simp [emptyLocalsHOLFinite, hdt6])
    all_goals (simp [emptyLocalsHOLFinite, c6, g6, d6, ta6]; try rfl)
  | empty j0 =>
    have hjj : j0 = j := hemp j0 hans
    rw [hans] at hres6
    simp only [PR.toOpt, Option.map_none, Option.getD_none] at hres6
    have hne : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.cmp .notEqual (vv lRes) (.const 0)) = some (.val (.word 0)) := by
      simp [vv, evalHOLExact, hres6, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [ite_word t6 _ _ _ _ hne]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    have hce : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.cmp .equal (vv lC) (.const 0)) = some (.val (.word (if BitVec.ofNat 64 f = 0 then 1 else 0))) := by
      simp [vv, evalHOLExact, hC6, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      try (by_cases h : BitVec.ofNat 64 f = 0 <;> simp [h])
    rw [ite_word t6 _ _ _ _ hce]
    by_cases hf0 : BitVec.ofNat 64 f = 0
    · left; simp only [hf0, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact hang_stop t6
    simp only [hf0, ↓reduceIte, ne_eq, not_true_eq_false]
    have hc6 : t6.locals.lookup lC0 = some (.val (.word C)) := by
      rw [hfr6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.c
    have hcm : t6.memaddrs C ∧ t6.memory C = .word (BitVec.ofNat 64 rows.length) := by
      rw [hmt6, hdt6]; exact hT.cnt
    have hld : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.load .one (vv lC0)) = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
      rw [eval_load_word t6 _ C (by simp [vv, evalHOLExact, hc6]) hcm.1, hcm.2]
    obtain ⟨L7, e7⟩ := dec_word' t6 lI _ _ _ hld
    rw [e7]; apply ires_locals
    let t7 := setVarHOLFinite lI (.val (.word (BitVec.ofNat 64 rows.length))) t6
    have l7 : ∀ y, y ≠ lI → y ≠ lJ → y ≠ lC → y ≠ lG → y ≠ lRes → y ≠ lV →
        t7.locals.lookup y = t.locals.lookup y := by
      intro y a0 a1 a2 a3 a4 a5; simp only [t7]
      rw [lookup_setVar_other _ _ a0, hfr6 _ a1 a2 a3 a4 a5, l5 _ a5 a4 a3 a2 a1]
    have hxr : x ∉ rows := (probe_correct (homeApp b) rows slots n hinv x).2.mp
      (by rw [← hprobe]; show ans.toOpt = _; rw [hans]; rfl)
    have hlen := hT.le
    have hslot := hT.mem.slot j hj
    obtain ⟨_, _, _, hsa, _⟩ := hslot
    rcases ins_spec t7 C R D S (encApp x).1 (encApp x).2 dv.toBitVec rows.length cap j (by omega) hlen (by omega)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.c)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.cap)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.r)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.d)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.s)
      (by simp only [t7]; rw [lookup_setVar_other _ _ (by decide)]; exact hJ6)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.kf)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.ka)
      (by rw [l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.dv)
      hcm
      (fun hlt => by
        obtain ⟨r1, r2, r3⟩ := hT.room _ hlt
        exact ⟨by show t6.memaddrs _; rw [hdt6]; exact r1, by show t6.memaddrs _; rw [hdt6]; exact r2,
          by show t6.memaddrs _; rw [hdt6]; exact r3, by show t6.memaddrs _; rw [hdt6]; exact hsa⟩)
      with hs | ⟨hlt, L8, e8, hl8⟩
    · exact Or.inl (seq_stop _ _ _ hs)
    rw [seq_normal _ e8]
    let t8 : PanSemStateFiniteExact 64 σ := { t7 with locals := L8, memory := insMem t7.memory C R D S (encApp x).1 (encApp x).2 dv.toBitVec rows.length j }
    have hi8 : t8.locals.lookup lI = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
      show L8.lookup lI = _; rw [hl8 _ (by decide)]; exact lookup_setVar_same _ _ _
    have htw8 : t8.locals.lookup lTier = some (.val (.word tier.toUInt64.toBitVec)) := by
      show L8.lookup lTier = _
      rw [hl8 _ (by decide), l7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hL.tier
    have hw : @evalHOLExact 64 σ _ t8.toExact (fun a => Classical.propDecidable (t8.memaddrs a))
        (hwE (vv lI)) =
        some (.val (.word (Idx.mkWide (k := .expr) tier (UInt32.ofNat rows.length)).word.toUInt64.toBitVec)) := by
      rw [mkWide_word tier rows.length htier (by omega)]
      simp [hwE, vv, evalHOLExact, evalListHOLExact, htw8, hi8, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      try rw [BitVec.add_assoc]
    have eret : evaluateHOLFiniteState t8 (.return (hwE (vv lI))) =
        (some (.returned (.val (.word (Idx.mkWide (k := .expr) tier (UInt32.ofNat rows.length)).word.toUInt64.toBitVec))),
          emptyLocalsHOLFinite t8) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only [hw]; simp [shapeOfHOLExact]
    rw [eret]
    have hfi : tb.find? x = none := by
      rw [hfind, ← hprobe]; show (ans.toOpt).map _ = _; rw [hans]; rfl
    have hsz : tb.size = rows.length := by
      show tb.nodes.size = _; rw [← hrel.1, Array.length_toList]
    have htA : tierApp tb x dv tier = (tb.push x dv (Idx.mkWide tier (UInt32.ofNat rows.length)),
        Idx.mkWide tier (UInt32.ofNat rows.length)) := by simp only [tierApp, hfi, hsz]
    have hpe : probeR rows slots n x n (at_ n hx 0) = .empty j0 := by
      rw [at_zero hxn]; exact hans
    obtain ⟨d, hd, hjd⟩ := probeR_empty rows slots n hx x hpos n 0 j0 hpe
    obtain ⟨hT8, hI8⟩ := ins_rel t t8 encApp rows ders slots n cap C S R D (homeApp b) hT hinv x hxr dv.toBitVec d hd
      hlt hn56 (by omega) (by show insMem t6.memory _ _ _ _ _ _ _ _ _ = _; rw [hmt6, ← hjj, hjd]) hdt6
    right
    refine ⟨by simp [htA], rows ++ [x], ders ++ [dv.toBitVec], _, tmem_of_eq hT8 rfl rfl, hI8,
      by rw [htA]; exact push_rel tb rows _ hrel x dv hxr, by rw [htA]; simp [Tbl.push, ← hder], ?_, ?_, ?_, ?_,
      fun a ha => by
        show insMem t6.memory _ _ _ _ _ _ _ _ _ a = _
        rw [hmt6]; exact insMem_out _ _ _ _ _ _ _ _ _ _ n cap hT.layC hT.layS hT.layR hT.layD hlt hj a ha⟩
    all_goals (simp [emptyLocalsHOLFinite, t8, t7, setVarHOLFinite, c6, g6, d6, ta6]; try rfl)
  | full =>
    rw [hans] at hres6
    simp only [PR.toOpt, Option.map_none, Option.getD_none] at hres6
    have hne : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.cmp .notEqual (vv lRes) (.const 0)) = some (.val (.word 0)) := by
      simp [vv, evalHOLExact, hres6, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [ite_word t6 _ _ _ _ hne]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    have hce : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.cmp .equal (vv lC) (.const 0)) = some (.val (.word (if BitVec.ofNat 64 f = 0 then 1 else 0))) := by
      simp [vv, evalHOLExact, hC6, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      try (by_cases h : BitVec.ofNat 64 f = 0 <;> simp [h])
    rw [ite_word t6 _ _ _ _ hce]
    by_cases hf0 : BitVec.ofNat 64 f = 0
    · left; simp only [hf0, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact hang_stop t6
    exact absurd ((hfull.mp hans) ▸ rfl : BitVec.ofNat 64 f = 0) hf0

end ConPanqueque.ConsIntern
