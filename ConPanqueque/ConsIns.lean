import ConPanqueque.ConsLoop
import ConPanqueque.Logic.Stop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsLoop

/-!
# Appending to a table in Pancake

After a miss at slot `j`, `insBody` appends the key's row (two words at
`R + 16·cnt`) and its derived word (at `D + 8·cnt`), points slot `j` at it, and
bumps the count word at `C`; a full table (`cnt = cap`) stops (`hang`), a
resource-limit decline. `ins_spec`: the result represents `rows ++ [a]`,
`ders ++ [d]` and `slots.set j (cnt + 1)`, and nothing else in memory moves.
-/

namespace ConPanqueque.ConsIns

def lC0 := ofString "ccnt"
def lCap := ofString "ccap"
def lD := ofString "cd"
def lDv := ofString "cdv"
def lN := ofString "cn"
def vv (n : MlS) : ExpHOL 64 := .var .local n

/-- Append the row `kf, ka` with derived word `dv` and point slot `cj` at it. -/
def insBody : ProgHOL 64 :=
  .dec lN .one (.load .one (vv lC0))
   (.ite (.cmp .equal (vv lN) (vv lCap)) hang
    (.seq (.store (.op .add [vv lR, .shift .lsl (vv lN) (.const 4)]) (vv lKf))
    (.seq (.store (.op .add [vv lR, .shift .lsl (vv lN) (.const 4), .const 8]) (vv lKa))
    (.seq (.store (.op .add [vv lD, .shift .lsl (vv lN) (.const 3)]) (vv lDv))
    (.seq (.store (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)]) (.op .add [vv lN, .const 1]))
     (.store (vv lC0) (.op .add [vv lN, .const 1])))))))

/-- One memory word updated. -/
def upd (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

/-- The memory after the append. -/
def insMem (m : BitVec 64 → HolWordLab 64) (C R D S kf ka dv : BitVec 64) (cnt j : Nat) : BitVec 64 → HolWordLab 64 :=
  upd (upd (upd (upd (upd m (R + BitVec.ofNat 64 (16 * cnt)) kf)
    (R + BitVec.ofNat 64 (16 * cnt) + 8) ka) (D + BitVec.ofNat 64 (8 * cnt)) dv)
    (S + BitVec.ofNat 64 (8 * j)) (BitVec.ofNat 64 (cnt + 1))) C (BitVec.ofNat 64 (cnt + 1))

theorem ins_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (C R D S kf ka dv : BitVec 64) (cnt cap j : Nat)
    (hcap : cap < 2 ^ 56) (hcnt : cnt ≤ cap) (hj : j < 2 ^ 56)
    (lc : t.locals.lookup lC0 = some (.val (.word C))) (lcap : t.locals.lookup lCap = some (.val (.word (BitVec.ofNat 64 cap))))
    (lr : t.locals.lookup lR = some (.val (.word R))) (ld : t.locals.lookup lD = some (.val (.word D)))
    (ls : t.locals.lookup lS = some (.val (.word S))) (lj : t.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))))
    (lkf : t.locals.lookup lKf = some (.val (.word kf))) (lka : t.locals.lookup lKa = some (.val (.word ka)))
    (ldv : t.locals.lookup lDv = some (.val (.word dv)))
    (mc : t.memaddrs C ∧ t.memory C = .word (BitVec.ofNat 64 cnt))
    (dom : cnt < cap → t.memaddrs (R + BitVec.ofNat 64 (16 * cnt)) ∧ t.memaddrs (R + BitVec.ofNat 64 (16 * cnt) + 8) ∧
      t.memaddrs (D + BitVec.ofNat 64 (8 * cnt)) ∧ t.memaddrs (S + BitVec.ofNat 64 (8 * j))) :
    Stop (evaluateHOLFiniteState t insBody).1 ∨
      (cnt < cap ∧ ∃ L, evaluateHOLFiniteState t insBody =
        (none, { t with locals := L, memory := insMem t.memory C R D S kf ka dv cnt j }) ∧
        ∀ y, y ≠ lN → L.lookup y = t.locals.lookup y) := by
  let t1 := setVarHOLFinite lN (.val (.word (BitVec.ofNat 64 cnt))) t
  have hload : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (vv lC0)) = some (.val (.word (BitVec.ofNat 64 cnt))) := by
    rw [eval_load_word t _ C (by simp [vv, evalHOLExact, lc]) mc.1, mc.2]
  have l1 : ∀ x, x ≠ lN → t1.locals.lookup x = t.locals.lookup x := fun x hx => lookup_setVar_other _ _ hx
  have hN : t1.locals.lookup lN = some (.val (.word (BitVec.ofNat 64 cnt))) := lookup_setVar_same _ _ _
  have hc56 : (2 : Nat) ^ 56 < 2 ^ 64 := by decide
  have hcmp : @evalHOLExact 64 σ _ t1.toExact (fun a => Classical.propDecidable (t1.memaddrs a))
      (.cmp .equal (vv lN) (vv lCap)) = some (.val (.word (if cnt = cap then 1 else 0))) := by
    simp [vv, evalHOLExact, hN, l1 lCap (by decide), lcap, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h : cnt = cap
    · simp [h]
    · have : ¬ BitVec.ofNat 64 cnt = BitVec.ofNat 64 cap := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp [h]; exact this
  unfold insBody; rw [dec_word_eq t lN _ _ _ hload]
  rw [ite_word t1 _ _ _ _ hcmp]
  by_cases hfull : cnt = cap
  · left
    simp only [hfull, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [hang_spec _ t1 rfl]; exact Or.inl rfl
  right
  have hlt : cnt < cap := by omega
  refine ⟨hlt, HolFiniteMapExact.resVarEq t1.locals (lN, t.locals.lookup lN), ?_,
    fun y hy => by rw [lookup_resVar_other _ _ _ _ hy]; exact l1 y hy⟩
  simp only [hfull, ↓reduceIte, ne_eq, not_true_eq_false]
  obtain ⟨d1, d2, d3, d4⟩ := dom hlt
  have sh4 : BitVec.ofNat 64 cnt <<< (4 : Nat) = BitVec.ofNat 64 (16 * cnt) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have sh3 : BitVec.ofNat 64 cnt <<< (3 : Nat) = BitVec.ofNat 64 (8 * cnt) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have shj : BitVec.ofNat 64 j <<< (3 : Nat) = BitVec.ofNat 64 (8 * j) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have add1 : BitVec.ofNat 64 cnt + 1 = BitVec.ofNat 64 (cnt + 1) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  -- the five stores
  have es1 := store_word t1 (.op .add [vv lR, .shift .lsl (vv lN) (.const 4)]) (vv lKf) _ kf
    (by simp [vv, evalHOLExact, evalListHOLExact, hN, l1 lR (by decide), lr, wordOpHOL, wordOp, valueIsWord, valueWord,
          wordShiftHOL]; rw [sh4])
    (by simp [vv, evalHOLExact, l1 lKf (by decide), lkf]) d1
  rw [seq_normal _ es1]
  let t2 : PanSemStateFiniteExact 64 σ := { t1 with memory := fun c => if c = R + BitVec.ofNat 64 (16 * cnt) then .word kf else t1.memory c }
  have es2 := store_word t2 (.op .add [vv lR, .shift .lsl (vv lN) (.const 4), .const 8]) (vv lKa)
    (R + BitVec.ofNat 64 (16 * cnt) + 8) ka
    (by simp [t2, vv, evalHOLExact, evalListHOLExact, hN, l1 lR (by decide), lr, wordOpHOL, wordOp, valueIsWord, valueWord,
          wordShiftHOL]; rw [sh4, BitVec.add_assoc])
    (by simp [t2, vv, evalHOLExact, l1 lKa (by decide), lka]) d2
  rw [seq_normal _ es2]
  let t3 : PanSemStateFiniteExact 64 σ := { t2 with memory := fun c => if c = R + BitVec.ofNat 64 (16 * cnt) + 8 then .word ka else t2.memory c }
  have es3 := store_word t3 (.op .add [vv lD, .shift .lsl (vv lN) (.const 3)]) (vv lDv) (D + BitVec.ofNat 64 (8 * cnt)) dv
    (by simp [t3, t2, vv, evalHOLExact, evalListHOLExact, hN, l1 lD (by decide), ld, wordOpHOL, wordOp, valueIsWord,
          valueWord, wordShiftHOL]; rw [sh3])
    (by simp [t3, t2, vv, evalHOLExact, l1 lDv (by decide), ldv]) d3
  rw [seq_normal _ es3]
  let t4 : PanSemStateFiniteExact 64 σ := { t3 with memory := fun c => if c = D + BitVec.ofNat 64 (8 * cnt) then .word dv else t3.memory c }
  have es4 := store_word t4 (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)]) (.op .add [vv lN, .const 1])
    (S + BitVec.ofNat 64 (8 * j)) (BitVec.ofNat 64 (cnt + 1))
    (by simp [t4, t3, t2, vv, evalHOLExact, evalListHOLExact, l1 lJ (by decide), lj, l1 lS (by decide), ls, wordOpHOL,
          wordOp, valueIsWord, valueWord, wordShiftHOL]; rw [shj])
    (by simp [t4, t3, t2, vv, evalHOLExact, evalListHOLExact, hN, wordOpHOL, wordOp, valueIsWord, valueWord]; exact add1) d4
  rw [seq_normal _ es4]
  let t5 : PanSemStateFiniteExact 64 σ := { t4 with memory := fun c => if c = S + BitVec.ofNat 64 (8 * j) then .word (BitVec.ofNat 64 (cnt + 1)) else t4.memory c }
  have es5 := store_word t5 (vv lC0) (.op .add [vv lN, .const 1]) C (BitVec.ofNat 64 (cnt + 1))
    (by simp [t5, t4, t3, t2, vv, evalHOLExact, l1 lC0 (by decide), lc])
    (by simp [t5, t4, t3, t2, vv, evalHOLExact, evalListHOLExact, hN, wordOpHOL, wordOp, valueIsWord, valueWord]; exact add1)
    mc.1
  rw [es5]
  rfl

section
variable {σ : Type} {α : Type} [DecidableEq α]

/-- A table in memory: count word at `C`, then `n` slots at `S`, `cap` two-word rows at `R`, and
`cap` derived words at `D`, contiguous and in this order. -/
structure TMem (t : PanSemStateFiniteExact 64 σ) (enc : α → BitVec 64 × BitVec 64) (rows : List α)
    (ders : List (BitVec 64)) (slots : List Nat) (n cap : Nat) (C S R D : BitVec 64) : Prop where
  mem : Mem t enc rows slots n S R
  cnt : t.memaddrs C ∧ t.memory C = .word (BitVec.ofNat 64 rows.length)
  dlen : ders.length = rows.length
  der : ∀ i (hi : i < rows.length), t.memaddrs (D + BitVec.ofNat 64 (8 * i)) ∧
    t.memory (D + BitVec.ofNat 64 (8 * i)) = .word (ders[i]'(by omega))
  le : rows.length ≤ cap
  room : ∀ i, i < cap → t.memaddrs (R + BitVec.ofNat 64 (16 * i)) ∧ t.memaddrs (R + BitVec.ofNat 64 (16 * i) + 8) ∧
    t.memaddrs (D + BitVec.ofNat 64 (8 * i))
  layC : C.toNat + 8 ≤ S.toNat
  layS : S.toNat + 8 * n ≤ R.toNat
  layR : R.toNat + 16 * cap ≤ D.toNat
  layD : D.toNat + 8 * cap ≤ 2 ^ 64

theorem off8 (B : BitVec 64) (k : Nat) (h : B.toNat + 8 * k < 2 ^ 64) :
    (B + BitVec.ofNat 64 (8 * k)).toNat = B.toNat + 8 * k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) (by omega), Nat.mod_eq_of_lt h]

theorem off16 (B : BitVec 64) (k : Nat) (h : B.toNat + 16 * k + 8 < 2 ^ 64) :
    (B + BitVec.ofNat 64 (16 * k)).toNat = B.toNat + 16 * k ∧
    (B + BitVec.ofNat 64 (16 * k) + 8).toNat = B.toNat + 16 * k + 8 := by
  have h1 : (B + BitVec.ofNat 64 (16 * k)).toNat = B.toNat + 16 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨h1, ?_⟩
  rw [BitVec.toNat_add, h1]; simp; omega


theorem ins_rel (t t' : PanSemStateFiniteExact 64 σ) (enc : α → BitVec 64 × BitVec 64) (rows : List α)
    (ders : List (BitVec 64)) (slots : List Nat) (n cap : Nat) (C S R D : BitVec 64) (home : α → Nat)
    (hT : TMem t enc rows ders slots n cap C S R D) (hinv : Inv (α := α) home rows slots n)
    (a : α) (ha : a ∉ rows) (dv : BitVec 64) (d : Nat) (hd : firstEmpty slots n (home a) n 0 = some d)
    (hlt : rows.length < cap) (hn60 : n ≤ 2 ^ 56) (hcap : cap ≤ 2 ^ 56)
    (hmem : t'.memory = insMem t.memory C R D S (enc a).1 (enc a).2 dv rows.length (at_ n (home a) d))
    (hd' : t'.memaddrs = t.memaddrs) :
    TMem t' enc (rows ++ [a]) (ders ++ [dv]) (slots.set (at_ n (home a) d) (rows.length + 1)) n cap C S R D ∧
    Inv (α := α) home (rows ++ [a]) (slots.set (at_ n (home a) d) (rows.length + 1)) n := by
  refine ⟨?_, insert_inv home rows slots n hinv a ha d hd⟩
  have hjn : at_ n (home a) d < n := Nat.mod_lt _ hinv.pos
  generalize at_ n (home a) d = j at hmem hjn ⊢
  obtain ⟨hm, ⟨cd, cm⟩, hdl, hder, hle, hroom, lC, lS, lR, lD⟩ := hT
  have hC := C.isLt
  -- reading the new memory
  have rd : ∀ x, t'.memory x = (if x = C then .word (BitVec.ofNat 64 (rows.length + 1)) else
      if x = S + BitVec.ofNat 64 (8 * j) then .word (BitVec.ofNat 64 (rows.length + 1)) else
      if x = D + BitVec.ofNat 64 (8 * rows.length) then .word dv else
      if x = R + BitVec.ofNat 64 (16 * rows.length) + 8 then .word (enc a).2 else
      if x = R + BitVec.ofNat 64 (16 * rows.length) then .word (enc a).1 else t.memory x) := by
    intro x; rw [hmem]; rfl
  have ne : ∀ x y : BitVec 64, x.toNat ≠ y.toNat → x ≠ y := fun x y h e => h (by rw [e])
  have sj := off8 S j (by omega)
  have dc := off8 D rows.length (by omega)
  have rc := off16 R rows.length (by omega)
  refine ⟨⟨?_, ?_⟩, ⟨by rw [hd']; exact cd, ?_⟩, by simp [hdl], ?_, by simp; omega, fun i hi => by rw [hd']; exact hroom i hi,
    lC, lS, lR, lD⟩
  · -- slots
    intro k hk
    obtain ⟨v, hv, hv60, sd, sm⟩ := hm.slot k hk
    have sk := off8 S k (by omega)
    by_cases hkj : k = j
    · subst hkj
      refine ⟨rows.length + 1, by rw [List.getElem?_set]; simp [hinv.len, hk], by omega, by rw [hd']; exact sd, ?_⟩
      rw [rd, if_neg (ne _ _ (by rw [sk]; omega)), if_pos rfl]
    · refine ⟨v, by rw [List.getElem?_set]; simp [Ne.symm hkj, hv], hv60, by rw [hd']; exact sd, ?_⟩
      rw [rd, if_neg (ne _ _ (by rw [sk]; omega)),
        if_neg (ne _ _ (by rw [sk, sj]; omega)), if_neg (ne _ _ (by rw [sk, dc]; omega)),
        if_neg (ne _ _ (by rw [sk, rc.2]; omega)), if_neg (ne _ _ (by rw [sk, rc.1]; omega))]
      exact sm
  · -- rows
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    have ri := off16 R i (by omega)
    by_cases hic : i = rows.length
    · subst hic
      refine ⟨by rw [hd']; exact (hroom _ hlt).1, by rw [hd']; exact (hroom _ hlt).2.1, ?_, ?_⟩
      · rw [rd, if_neg (ne _ _ (by rw [rc.1]; omega)), if_neg (ne _ _ (by rw [rc.1, sj]; omega)),
          if_neg (ne _ _ (by rw [rc.1, dc]; omega)), if_neg (ne _ _ (by rw [rc.1, rc.2]; omega)), if_pos rfl]
        simp
      · rw [rd, if_neg (ne _ _ (by rw [rc.2]; omega)), if_neg (ne _ _ (by rw [rc.2, sj]; omega)),
          if_neg (ne _ _ (by rw [rc.2, dc]; omega)), if_pos rfl]
        simp
    · have hi' : i < rows.length := by omega
      obtain ⟨d1, d2, m1, m2⟩ := hm.row i hi'
      refine ⟨by rw [hd']; exact d1, by rw [hd']; exact d2, ?_, ?_⟩
      · rw [rd, if_neg (ne _ _ (by rw [ri.1]; omega)), if_neg (ne _ _ (by rw [ri.1, sj]; omega)),
          if_neg (ne _ _ (by rw [ri.1, dc]; omega)), if_neg (ne _ _ (by rw [ri.1, rc.2]; omega)),
          if_neg (ne _ _ (by rw [ri.1, rc.1]; omega)), m1, List.getElem_append_left hi']
      · rw [rd, if_neg (ne _ _ (by rw [ri.2]; omega)), if_neg (ne _ _ (by rw [ri.2, sj]; omega)),
          if_neg (ne _ _ (by rw [ri.2, dc]; omega)), if_neg (ne _ _ (by rw [ri.2, rc.2]; omega)),
          if_neg (ne _ _ (by rw [ri.2, rc.1]; omega)), m2, List.getElem_append_left hi']
  · rw [rd, if_pos rfl]; simp
  · -- derived words
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    have di := off8 D i (by omega)
    by_cases hic : i = rows.length
    · subst hic
      refine ⟨by rw [hd']; exact (hroom _ hlt).2.2, ?_⟩
      rw [rd, if_neg (ne _ _ (by rw [dc]; omega)), if_neg (ne _ _ (by rw [dc, sj]; omega)), if_pos rfl]
      simp [hdl]
    · have hi' : i < rows.length := by omega
      obtain ⟨dd, dm⟩ := hder i hi'
      refine ⟨by rw [hd']; exact dd, ?_⟩
      rw [rd, if_neg (ne _ _ (by rw [di]; omega)), if_neg (ne _ _ (by rw [di, sj]; omega)),
        if_neg (ne _ _ (by rw [di, dc]; omega)), if_neg (ne _ _ (by rw [di, rc.2]; omega)),
        if_neg (ne _ _ (by rw [di, rc.1]; omega)), dm, List.getElem_append_left (by omega)]
end

/-! ## The table's region

A table occupies `[C, D + 8·cap)`. `tmem_frame`: memory changes outside that
interval keep it represented; `insMem_out`: the append writes only inside it. -/

def inReg (C D : BitVec 64) (cap : Nat) (a : BitVec 64) : Prop := C.toNat ≤ a.toNat ∧ a.toNat < D.toNat + 8 * cap

theorem toNat_add_lt (X Y : BitVec 64) (h : X.toNat + Y.toNat < 2 ^ 64) : (X + Y).toNat = X.toNat + Y.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat_lt (k : Nat) (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

section
variable {σ : Type} {α : Type} [DecidableEq α]

theorem tmem_frame {t t' : PanSemStateFiniteExact 64 σ} {enc : α → BitVec 64 × BitVec 64} {rows : List α}
    {ders : List (BitVec 64)} {slots : List Nat} {n cap : Nat} {C S R D : BitVec 64}
    (h : TMem t enc rows ders slots n cap C S R D) (hm : ∀ a, inReg C D cap a → t'.memory a = t.memory a)
    (hd : t'.memaddrs = t.memaddrs) : TMem t' enc rows ders slots n cap C S R D := by
  obtain ⟨⟨hs, hr⟩, ⟨c1, c2⟩, hdl, hder, hle, hroom, l1, l2, l3, l4⟩ := h
  have hR := R.isLt; have hS := S.isLt; have hD := D.isLt
  refine ⟨⟨fun j hj => ?_, fun i hi => ?_⟩, ⟨by rw [hd]; exact c1, by rw [hm C ⟨Nat.le_refl _, by omega⟩]; exact c2⟩,
    hdl, fun i hi => ?_, hle, fun i hi => ?_, l1, l2, l3, l4⟩
  · obtain ⟨v, a1, a2, a3, a4⟩ := hs j hj
    have e : (S + BitVec.ofNat 64 (8 * j)).toNat = S.toNat + 8 * j := by
      rw [toNat_add_lt _ _ (by rw [toNat_ofNat_lt _ (by omega)]; omega), toNat_ofNat_lt _ (by omega)]
    exact ⟨v, a1, a2, by rw [hd]; exact a3, by rw [hm _ ⟨by omega, by omega⟩]; exact a4⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hr i hi
    have e : (R + BitVec.ofNat 64 (16 * i)).toNat = R.toNat + 16 * i := by
      rw [toNat_add_lt _ _ (by rw [toNat_ofNat_lt _ (by omega)]; omega), toNat_ofNat_lt _ (by omega)]
    have e8 : (R + BitVec.ofNat 64 (16 * i) + 8).toNat = R.toNat + 16 * i + 8 := by
      rw [toNat_add_lt _ _ (by rw [e]; simp; omega), e]; simp
    exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hm _ ⟨by omega, by omega⟩]; exact a3,
      by rw [hm _ ⟨by omega, by omega⟩]; exact a4⟩
  · obtain ⟨a1, a2⟩ := hder i hi
    have e : (D + BitVec.ofNat 64 (8 * i)).toNat = D.toNat + 8 * i := by
      rw [toNat_add_lt _ _ (by rw [toNat_ofNat_lt _ (by omega)]; omega), toNat_ofNat_lt _ (by omega)]
    exact ⟨by rw [hd]; exact a1, by rw [hm _ ⟨by omega, by omega⟩]; exact a2⟩
  · obtain ⟨a1, a2, a3⟩ := hroom i hi; exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hd]; exact a3⟩

theorem insMem_out (m : BitVec 64 → HolWordLab 64) (C R D S kf ka dv : BitVec 64) (cnt j n cap : Nat)
    (lC : C.toNat + 8 ≤ S.toNat) (lS : S.toNat + 8 * n ≤ R.toNat) (lR : R.toNat + 16 * cap ≤ D.toNat)
    (lD : D.toNat + 8 * cap ≤ 2 ^ 64) (hc : cnt < cap) (hj : j < n) (a : BitVec 64) (ha : ¬ inReg C D cap a) :
    insMem m C R D S kf ka dv cnt j a = m a := by
  have eS : (S + BitVec.ofNat 64 (8 * j)).toNat = S.toNat + 8 * j := by
    rw [toNat_add_lt _ _ (by rw [toNat_ofNat_lt _ (by omega)]; omega), toNat_ofNat_lt _ (by omega)]
  have eR : (R + BitVec.ofNat 64 (16 * cnt)).toNat = R.toNat + 16 * cnt := by
    rw [toNat_add_lt _ _ (by rw [toNat_ofNat_lt _ (by omega)]; omega), toNat_ofNat_lt _ (by omega)]
  have eR8 : (R + BitVec.ofNat 64 (16 * cnt) + 8).toNat = R.toNat + 16 * cnt + 8 := by
    rw [toNat_add_lt _ _ (by rw [eR]; simp; omega), eR]; simp
  have eD : (D + BitVec.ofNat 64 (8 * cnt)).toNat = D.toNat + 8 * cnt := by
    rw [toNat_add_lt _ _ (by rw [toNat_ofNat_lt _ (by omega)]; omega), toNat_ofNat_lt _ (by omega)]
  have ne : ∀ b : BitVec 64, inReg C D cap b → a ≠ b := fun b hb e => ha (e ▸ hb)
  simp only [insMem, upd]
  rw [if_neg (ne C ⟨Nat.le_refl _, by omega⟩), if_neg (ne _ ⟨by omega, by omega⟩), if_neg (ne _ ⟨by omega, by omega⟩),
    if_neg (ne _ ⟨by omega, by omega⟩), if_neg (ne _ ⟨by omega, by omega⟩)]
end

end ConPanqueque.ConsIns
