import ConPanqueque.V.Probe
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel

/-!
# Appending to a generic cons table

Layout, contiguous: count word at `C`, heap-top word at `C + 8`, `n` slots at
`S`, `cap` two-word rows at `R`, `cap` two-word derived values at `D`, and a key heap of
`kcap` words at `KH`. `VT` says memory represents `rows`/`ders`/`slots` with
`hu` heap words used. `insBody` appends after a miss at slot `cj`: it stops
(hangs) when the rows or the heap are full, else copies the key to the heap
top and writes the row, derived word, slot, count and heap top.
-/

namespace ConPanqueque.V

def lC0 := ofString "ccnt"
def lCap := ofString "ccap"
def lD := ofString "cd"
def lDv := ofString "cdv"
def lDv2 := ofString "cdv2"
def lKe := ofString "ckend"
def lN := ofString "cn"
def lH := ofString "ch"

structure VGeo where
  n : Nat
  b : Nat
  cap : Nat
  kcap : Nat
  C : BitVec 64
  S : BitVec 64
  R : BitVec 64
  D : BitVec 64
  KH : BitVec 64

/-- The table's region `[C, KH + 8·kcap)`. -/
def inR (g : VGeo) (a : BitVec 64) : Prop := g.C.toNat ≤ a.toNat ∧ a.toNat < g.KH.toNat + 8 * g.kcap

section
variable {σ : Type} {α : Type}

structure VT (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (rows : List α) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (g : VGeo) (hu : Nat) : Prop where
  slot : ∀ j (hj : j < g.n), ∃ v, slots[j]? = some v ∧ v < 2 ^ 60 ∧
    t.memaddrs (g.S + BitVec.ofNat 64 (8 * j)) ∧ t.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word (BitVec.ofNat 64 v)
  row : ∀ i (hi : i < rows.length), ∃ P, t.memaddrs (g.R + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.R + BitVec.ofNat 64 (16 * i) + 8) ∧ t.memory (g.R + BitVec.ofNat 64 (16 * i)) = .word P ∧
    t.memory (g.R + BitVec.ofNat 64 (16 * i) + 8) = .word (BitVec.ofNat 64 (enc rows[i]).length) ∧
    Words t P (enc rows[i]) ∧ g.KH.toNat ≤ P.toNat ∧ P.toNat + 8 * (enc rows[i]).length ≤ g.KH.toNat + 8 * hu
  short : ∀ i (hi : i < rows.length), (enc rows[i]).length < 2 ^ 61
  cnt : t.memaddrs g.C ∧ t.memory g.C = .word (BitVec.ofNat 64 rows.length)
  top : t.memaddrs (g.C + 8) ∧ t.memory (g.C + 8) = .word (g.KH + BitVec.ofNat 64 (8 * hu))
  hu_le : hu ≤ g.kcap
  dlen : ders.length = rows.length
  der : ∀ i (hi : i < rows.length), t.memaddrs (g.D + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.D + BitVec.ofNat 64 (16 * i) + 8) ∧
    t.memory (g.D + BitVec.ofNat 64 (16 * i)) = .word (ders[i]'(by omega)).1 ∧
    t.memory (g.D + BitVec.ofNat 64 (16 * i) + 8) = .word (ders[i]'(by omega)).2
  le : rows.length ≤ g.cap
  room : ∀ i, i < g.cap → t.memaddrs (g.R + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.R + BitVec.ofNat 64 (16 * i) + 8) ∧ t.memaddrs (g.D + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.D + BitVec.ofNat 64 (16 * i) + 8)
  hroom : ∀ k, k < g.kcap → t.memaddrs (g.KH + BitVec.ofNat 64 (8 * k))
  layC : g.C.toNat + 16 ≤ g.S.toNat
  layS : g.S.toNat + 8 * g.n ≤ g.R.toNat
  layR : g.R.toNat + 16 * g.cap ≤ g.D.toNat
  layD : g.D.toNat + 16 * g.cap ≤ g.KH.toNat
  layK : g.KH.toNat + 8 * g.kcap < 2 ^ 64

theorem VT.vmem {t : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {rows : List α}
    {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat} (h : VT t enc rows ders slots g hu) :
    VMem t enc rows slots g.n g.S g.R :=
  ⟨h.slot, fun i hi => by obtain ⟨P, a1, a2, a3, a4, a5, _⟩ := h.row i hi; exact ⟨P, a1, a2, a3, a4, a5⟩, h.short⟩

end

def insCopy : ProgHOL 64 :=
  .seq (.assign .local lWa (vv lK)) (.seq (.assign .local lWb (vv lH))
   (.seq (.assign .local lWn (vv lL)) (.seq (.assign .local lWg (.const 1)) copyLoop)))

def insStores : ProgHOL 64 :=
  .seq (.store (.op .add [vv lR, .shift .lsl (vv lN) (.const 4)]) (vv lH))
  (.seq (.store (.op .add [vv lR, .shift .lsl (vv lN) (.const 4), .const 8]) (vv lL))
  (.seq (.store (.op .add [vv lD, .shift .lsl (vv lN) (.const 4)]) (vv lDv))
  (.seq (.store (.op .add [vv lD, .shift .lsl (vv lN) (.const 4), .const 8]) (vv lDv2))
  (.seq (.store (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)]) (.op .add [vv lN, .const 1]))
  (.seq (.store (vv lC0) (.op .add [vv lN, .const 1]))
    (.store (.op .add [vv lC0, .const 8]) (.op .add [vv lH, .shift .lsl (vv lL) (.const 3)])))))))

def insBody : ProgHOL 64 :=
  .dec lN .one (.load .one (vv lC0))
   (.ite (.cmp .equal (vv lN) (vv lCap)) hang
    (.dec lH .one (.load .one (.op .add [vv lC0, .const 8]))
     (.ite (.cmp .lower (.shift .lsr (.op .sub [vv lKe, vv lH]) (.const 3)) (vv lL)) hang
      (.seq insCopy insStores))))

/-- The memory after the six stores. -/
def insM (m : BitVec 64 → HolWordLab 64) (C R D S B dv dv2 : BitVec 64) (cnt j L : Nat) : BitVec 64 → HolWordLab 64 :=
  upd (upd (upd (upd (upd (upd (upd m (R + BitVec.ofNat 64 (16 * cnt)) B) (R + BitVec.ofNat 64 (16 * cnt) + 8)
    (BitVec.ofNat 64 L)) (D + BitVec.ofNat 64 (16 * cnt)) dv) (D + BitVec.ofNat 64 (16 * cnt) + 8) dv2)
    (S + BitVec.ofNat 64 (8 * j))
    (BitVec.ofNat 64 (cnt + 1))) C (BitVec.ofNat 64 (cnt + 1))) (C + 8) (B + BitVec.ofNat 64 (8 * L))

theorem toNat_ofNat_lt (k : Nat) (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ne_of_toNat {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (by rw [e])

theorem tn (X : BitVec 64) (k : Nat) (h : X.toNat + k < 2 ^ 64) : (X + BitVec.ofNat 64 k).toNat = X.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]; exact Nat.mod_eq_of_lt h

theorem tn8 (X : BitVec 64) (h : X.toNat + 8 < 2 ^ 64) : (X + 8).toNat = X.toNat + 8 := by
  rw [BitVec.toNat_add]; simp; omega

theorem insM_other (m : BitVec 64 → HolWordLab 64) (C R D S B dv dv2 : BitVec 64) (cnt j L : Nat) (c : BitVec 64)
    (h1 : c ≠ R + BitVec.ofNat 64 (16 * cnt)) (h2 : c ≠ R + BitVec.ofNat 64 (16 * cnt) + 8)
    (h3 : c ≠ D + BitVec.ofNat 64 (16 * cnt)) (h3' : c ≠ D + BitVec.ofNat 64 (16 * cnt) + 8)
    (h4 : c ≠ S + BitVec.ofNat 64 (8 * j)) (h5 : c ≠ C) (h6 : c ≠ C + 8) :
    insM m C R D S B dv dv2 cnt j L c = m c := by
  simp only [insM, upd]; rw [if_neg h6, if_neg h5, if_neg h4, if_neg h3', if_neg h3, if_neg h2, if_neg h1]

theorem ofNat_add8 (X : BitVec 64) (a b : Nat) :
    X + BitVec.ofNat 64 (8 * a) + BitVec.ofNat 64 (8 * b) = X + BitVec.ofNat 64 (8 * (a + b)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

section
variable {σ : Type}

theorem insStores_eval (x : PanSemStateFiniteExact 64 σ) (C R D S B dv dv2 : BitVec 64) (cnt j L : Nat)
    (hcnt : cnt < 2 ^ 30) (hj : j < 2 ^ 56) (hL : L < 2 ^ 61)
    (lR' : x.locals.lookup lR = some (.val (.word R))) (lN' : x.locals.lookup lN = some (.val (.word (BitVec.ofNat 64 cnt))))
    (lH' : x.locals.lookup lH = some (.val (.word B))) (lL' : x.locals.lookup lL = some (.val (.word (BitVec.ofNat 64 L))))
    (lD' : x.locals.lookup lD = some (.val (.word D))) (lDv' : x.locals.lookup lDv = some (.val (.word dv)))
    (lDv2' : x.locals.lookup lDv2 = some (.val (.word dv2)))
    (lS' : x.locals.lookup lS = some (.val (.word S))) (lJ' : x.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))))
    (lC' : x.locals.lookup lC0 = some (.val (.word C)))
    (d1 : x.memaddrs (R + BitVec.ofNat 64 (16 * cnt))) (d2 : x.memaddrs (R + BitVec.ofNat 64 (16 * cnt) + 8))
    (d3 : x.memaddrs (D + BitVec.ofNat 64 (16 * cnt))) (d3' : x.memaddrs (D + BitVec.ofNat 64 (16 * cnt) + 8)) (d4 : x.memaddrs (S + BitVec.ofNat 64 (8 * j)))
    (d5 : x.memaddrs C) (d6 : x.memaddrs (C + 8)) :
    evaluateHOLFiniteState x insStores = (none, { x with memory := insM x.memory C R D S B dv dv2 cnt j L }) := by
  have s4 : BitVec.ofNat 64 cnt <<< (4 : BitVec 64).toNat = BitVec.ofNat 64 (16 * cnt) := by
    rw [show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)]
  have s3 : BitVec.ofNat 64 cnt <<< (3 : BitVec 64).toNat = BitVec.ofNat 64 (8 * cnt) := by
    rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
  have sj : BitVec.ofNat 64 j <<< (3 : BitVec 64).toNat = BitVec.ofNat 64 (8 * j) := by
    rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
  have sL : BitVec.ofNat 64 L <<< (3 : BitVec 64).toNat = BitVec.ofNat 64 (8 * L) := by
    rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
  have add1 : BitVec.ofNat 64 cnt + 1 = BitVec.ofNat 64 (cnt + 1) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have c4 : (4 : BitVec 64).toNat < 64 := by decide
  have c3 : (3 : BitVec 64).toNat < 64 := by decide
  unfold insStores
  rw [seq_normal _ (store_word x _ _ _ B (by rw [eval_add2 x _ _ _ _ (eval_vv x lR _ lR') (eval_shl x _ _ _
    (eval_vv x lN _ lN') c4), s4]) (eval_vv x lH _ lH') d1)]
  let x1 : PanSemStateFiniteExact 64 σ := { x with memory := fun c => if c = R + BitVec.ofNat 64 (16 * cnt) then .word B else x.memory c }
  rw [seq_normal _ (store_word x1 _ _ (R + BitVec.ofNat 64 (16 * cnt) + 8) (BitVec.ofNat 64 L)
    (by rw [eval_add3 x1 _ _ _ _ _ _ (eval_vv x1 lR _ lR') (eval_shl x1 _ _ _ (eval_vv x1 lN _ lN') c4)
      (eval_const x1 8), s4]) (eval_vv x1 lL _ lL') d2)]
  let x2 : PanSemStateFiniteExact 64 σ := { x1 with memory := fun c => if c = R + BitVec.ofNat 64 (16 * cnt) + 8 then .word (BitVec.ofNat 64 L) else x1.memory c }
  rw [seq_normal _ (store_word x2 _ _ (D + BitVec.ofNat 64 (16 * cnt)) dv
    (by rw [eval_add2 x2 _ _ _ _ (eval_vv x2 lD _ lD') (eval_shl x2 _ _ _ (eval_vv x2 lN _ lN') c4), s4])
    (eval_vv x2 lDv _ lDv') d3)]
  let x2' : PanSemStateFiniteExact 64 σ := { x2 with memory := fun c => if c = D + BitVec.ofNat 64 (16 * cnt) then .word dv else x2.memory c }
  rw [seq_normal _ (store_word x2' _ _ (D + BitVec.ofNat 64 (16 * cnt) + 8) dv2
    (by rw [eval_add3 x2' _ _ _ _ _ _ (eval_vv x2' lD _ lD') (eval_shl x2' _ _ _ (eval_vv x2' lN _ lN') c4)
      (eval_const x2' 8), s4]) (eval_vv x2' lDv2 _ lDv2') d3')]
  let x3 : PanSemStateFiniteExact 64 σ := { x2' with memory := fun c => if c = D + BitVec.ofNat 64 (16 * cnt) + 8 then .word dv2 else x2'.memory c }
  rw [seq_normal _ (store_word x3 _ _ (S + BitVec.ofNat 64 (8 * j)) (BitVec.ofNat 64 (cnt + 1))
    (by rw [eval_add2 x3 _ _ _ _ (eval_vv x3 lS _ lS') (eval_shl x3 _ _ _ (eval_vv x3 lJ _ lJ') c3), sj])
    (by rw [eval_add2 x3 _ _ _ _ (eval_vv x3 lN _ lN') (eval_const x3 1), add1]) d4)]
  let x4 : PanSemStateFiniteExact 64 σ := { x3 with memory := fun c => if c = S + BitVec.ofNat 64 (8 * j) then .word (BitVec.ofNat 64 (cnt + 1)) else x3.memory c }
  rw [seq_normal _ (store_word x4 _ _ C (BitVec.ofNat 64 (cnt + 1)) (eval_vv x4 lC0 _ lC')
    (by rw [eval_add2 x4 _ _ _ _ (eval_vv x4 lN _ lN') (eval_const x4 1), add1]) d5)]
  let x5 : PanSemStateFiniteExact 64 σ := { x4 with memory := fun c => if c = C then .word (BitVec.ofNat 64 (cnt + 1)) else x4.memory c }
  rw [store_word x5 _ _ (C + 8) (B + BitVec.ofNat 64 (8 * L))
    (eval_add2 x5 _ _ _ _ (eval_vv x5 lC0 _ lC') (eval_const x5 8))
    (by rw [eval_add2 x5 _ _ _ _ (eval_vv x5 lH _ lH') (eval_shl x5 _ _ _ (eval_vv x5 lL _ lL') c3), sL]) d6]
  rfl

end

section
variable {σ : Type} {α : Type}

theorem vt_ins {t t' : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {rows : List α}
    {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat} (hT : VT t enc rows ders slots g hu)
    (a : α) (dv dv2 : BitVec 64) (j : Nat) (hj : j < g.n) (hcnt : rows.length < g.cap) (hcap : g.cap < 2 ^ 30)
    (hKl : (enc a).length < 2 ^ 61) (hroom : hu + (enc a).length ≤ g.kcap)
    (hm : t'.memory = insM (wr t.memory (g.KH + BitVec.ofNat 64 (8 * hu)) (enc a)) g.C g.R g.D g.S
      (g.KH + BitVec.ofNat 64 (8 * hu)) dv dv2 rows.length j (enc a).length)
    (hd : t'.memaddrs = t.memaddrs) :
    VT t' enc (rows ++ [a]) (ders ++ [(dv, dv2)]) (slots.set j (rows.length + 1)) g (hu + (enc a).length) := by
  have lK := hT.layK; have lD := hT.layD; have lR := hT.layR; have lS := hT.layS; have lC := hT.layC
  have hule := hT.hu_le
  generalize hB : g.KH + BitVec.ofNat 64 (8 * hu) = B at hm
  generalize hL : (enc a).length = L at hm hKl hroom
  generalize hc : rows.length = cnt at hm hcnt
  have tS : ∀ j', j' < g.n → (g.S + BitVec.ofNat 64 (8 * j')).toNat = g.S.toNat + 8 * j' :=
    fun j' h => tn _ _ (by omega)
  have tR : ∀ i, i < g.cap → (g.R + BitVec.ofNat 64 (16 * i)).toNat = g.R.toNat + 16 * i :=
    fun i h => tn _ _ (by omega)
  have tR8 : ∀ i, i < g.cap → (g.R + BitVec.ofNat 64 (16 * i) + 8).toNat = g.R.toNat + 16 * i + 8 :=
    fun i h => by rw [tn8 _ (by rw [tR i h]; omega), tR i h]
  have tD : ∀ i, i < g.cap → (g.D + BitVec.ofNat 64 (16 * i)).toNat = g.D.toNat + 16 * i :=
    fun i h => tn _ _ (by omega)
  have tD8 : ∀ i, i < g.cap → (g.D + BitVec.ofNat 64 (16 * i) + 8).toNat = g.D.toNat + 16 * i + 8 :=
    fun i h => by rw [tn8 _ (by rw [tD i h]; omega), tD i h]
  have tC8 : (g.C + 8).toNat = g.C.toNat + 8 := tn8 _ (by omega)
  have tK : ∀ k, k ≤ g.kcap → (g.KH + BitVec.ofNat 64 (8 * k)).toNat = g.KH.toNat + 8 * k :=
    fun k h => tn _ _ (by omega)
  have tB : B.toNat = g.KH.toNat + 8 * hu := by rw [← hB]; exact tK hu hule
  have hBk : ∀ k, B + BitVec.ofNat 64 (8 * k) = g.KH + BitVec.ofNat 64 (8 * (hu + k)) := by
    intro k; rw [← hB, ofNat_add8]
  -- reading below the heap's free part, away from the six stores
  have rd : ∀ c, c.toNat < g.KH.toNat + 8 * hu → c ≠ g.R + BitVec.ofNat 64 (16 * cnt) →
      c ≠ g.R + BitVec.ofNat 64 (16 * cnt) + 8 → c ≠ g.D + BitVec.ofNat 64 (16 * cnt) →
      c ≠ g.D + BitVec.ofNat 64 (16 * cnt) + 8 →
      c ≠ g.S + BitVec.ofNat 64 (8 * j) → c ≠ g.C → c ≠ g.C + 8 → t'.memory c = t.memory c := by
    intro c hlt h1 h2 h3 h3' h4 h5 h6
    rw [hm, insM_other _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h3' h4 h5 h6]
    exact wr_out _ _ _ _ (fun k hk => ne_of_toNat (by rw [hBk, tK _ (by omega)]; omega))
  have low : ∀ c : BitVec 64, c.toNat < g.KH.toNat → c.toNat < g.KH.toNat + 8 * hu := fun c h => by omega
  refine ⟨fun j' hj' => ?_, fun i hi => ?_, fun i hi => ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, by omega, by simp [hT.dlen, hc],
    fun i hi => ?_, by simp; omega, fun i hi => by rw [hd]; exact hT.room i hi,
    fun k hk => by rw [hd]; exact hT.hroom k hk, lC, lS, lR, lD, lK⟩
  · -- slots
    obtain ⟨v, hv, hv60, hsd, hsm⟩ := hT.slot j' hj'
    by_cases e : j' = j
    · subst e
      refine ⟨cnt + 1, ?_, by omega, by rw [hd]; exact hsd, ?_⟩
      · rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hv).1]
      · rw [hm]; simp only [insM, upd]
        rw [if_neg (ne_of_toNat (by rw [tS _ hj', tC8]; omega)), if_neg (ne_of_toNat (by rw [tS _ hj']; omega)),
          ]; simp
    · refine ⟨v, by rw [List.getElem?_set_ne (Ne.symm e)]; exact hv, hv60, by rw [hd]; exact hsd, ?_⟩
      rw [rd (g.S + BitVec.ofNat 64 (8 * j')) (low _ (by rw [tS _ hj']; omega)) (ne_of_toNat (by rw [tS _ hj', tR _ (by omega)]; omega))
        (ne_of_toNat (by rw [tS _ hj', tR8 _ (by omega)]; omega)) (ne_of_toNat (by rw [tS _ hj', tD _ (by omega)]; omega))
        (ne_of_toNat (by rw [tS _ hj', tD8 _ (by omega)]; omega))
        (ne_of_toNat (by rw [tS _ hj', tS _ hj]; omega)) (ne_of_toNat (by rw [tS _ hj']; omega))
        (ne_of_toNat (by rw [tS _ hj', tC8]; omega)), hsm]
  · -- rows
    simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i < cnt
    · have hi' : i < rows.length := by omega
      obtain ⟨P, a1, a2, a3, a4, a5, a6, a7⟩ := hT.row i hi'
      rw [List.getElem_append_left hi']
      have hPk : ∀ k, k < (enc rows[i]).length → (P + BitVec.ofNat 64 (8 * k)).toNat = P.toNat + 8 * k :=
        fun k hk => tn _ _ (by omega)
      have far : ∀ c, g.KH.toNat ≤ c.toNat → c.toNat < g.KH.toNat + 8 * hu → t'.memory c = t.memory c := by
        intro c h1 h2
        exact rd c h2 (ne_of_toNat (by rw [tR _ hcnt]; omega)) (ne_of_toNat (by rw [tR8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tD _ hcnt]; omega)) (ne_of_toNat (by rw [tD8 _ hcnt]; omega)) (ne_of_toNat (by rw [tS _ hj]; omega)) (ne_of_toNat (by omega))
          (ne_of_toNat (by rw [tC8]; omega))
      refine ⟨P, by rw [hd]; exact a1, by rw [hd]; exact a2, ?_, ?_, fun k hk => ⟨by rw [hd]; exact (a5 k hk).1, ?_⟩,
        a6, by omega⟩
      · rw [rd (g.R + BitVec.ofNat 64 (16 * i)) (low _ (by rw [tR _ (by omega)]; omega)) (ne_of_toNat (by rw [tR _ (by omega), tR _ hcnt]; omega))
          (ne_of_toNat (by rw [tR _ (by omega), tR8 _ hcnt]; omega)) (ne_of_toNat (by rw [tR _ (by omega), tD _ hcnt]; omega)) (ne_of_toNat (by rw [tR _ (by omega), tD8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tR _ (by omega), tS _ hj]; omega)) (ne_of_toNat (by rw [tR _ (by omega)]; omega))
          (ne_of_toNat (by rw [tR _ (by omega), tC8]; omega)), a3]
      · rw [rd (g.R + BitVec.ofNat 64 (16 * i) + 8) (low _ (by rw [tR8 _ (by omega)]; omega)) (ne_of_toNat (by rw [tR8 _ (by omega), tR _ hcnt]; omega))
          (ne_of_toNat (by rw [tR8 _ (by omega), tR8 _ hcnt]; omega)) (ne_of_toNat (by rw [tR8 _ (by omega), tD _ hcnt]; omega)) (ne_of_toNat (by rw [tR8 _ (by omega), tD8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tR8 _ (by omega), tS _ hj]; omega)) (ne_of_toNat (by rw [tR8 _ (by omega)]; omega))
          (ne_of_toNat (by rw [tR8 _ (by omega), tC8]; omega)), a4]
      · rw [far (P + BitVec.ofNat 64 (8 * k)) (by rw [hPk k hk]; omega) (by rw [hPk k hk]; omega)]; exact (a5 k hk).2
    · have ei : i = cnt := by omega
      subst ei
      have hel : (rows ++ [a])[i]'(by simp; omega) = a := by
        rw [List.getElem_append_right (by omega)]; simp [hc]
      rw [hel, hL]
      obtain ⟨d1, d2, _, _⟩ := hT.room i hcnt
      refine ⟨B, by rw [hd]; exact d1, by rw [hd]; exact d2, ?_, ?_, fun k hk => ⟨?_, ?_⟩, by omega, by omega⟩
      · rw [hm]; simp only [insM, upd]
        rw [if_neg (ne_of_toNat (by rw [tR _ hcnt, tC8]; omega)), if_neg (ne_of_toNat (by rw [tR _ hcnt]; omega)),
          if_neg (ne_of_toNat (by rw [tR _ hcnt, tS _ hj]; omega)), if_neg (ne_of_toNat (by rw [tR _ hcnt, tD8 _ hcnt]; omega)),
          if_neg (ne_of_toNat (by rw [tR _ hcnt, tD _ hcnt]; omega)),
          if_neg (ne_of_toNat (by rw [tR _ hcnt, tR8 _ hcnt]; omega)), ]; simp
      · rw [hm]; simp only [insM, upd]
        rw [if_neg (ne_of_toNat (by rw [tR8 _ hcnt, tC8]; omega)), if_neg (ne_of_toNat (by rw [tR8 _ hcnt]; omega)),
          if_neg (ne_of_toNat (by rw [tR8 _ hcnt, tS _ hj]; omega)), if_neg (ne_of_toNat (by rw [tR8 _ hcnt, tD8 _ hcnt]; omega)),
          if_neg (ne_of_toNat (by rw [tR8 _ hcnt, tD _ hcnt]; omega)),
          ]; simp
      · rw [hd, hBk]; exact hT.hroom _ (by rw [← hL] at hroom; omega)
      · have tk : (B + BitVec.ofNat 64 (8 * k)).toNat = g.KH.toNat + 8 * (hu + k) := by
          rw [hBk, tK _ (by rw [← hL] at hroom; omega)]
        rw [hm, insM_other _ _ _ _ _ _ _ _ _ _ _ _ (ne_of_toNat (by rw [tk, tR _ hcnt]; omega))
          (ne_of_toNat (by rw [tk, tR8 _ hcnt]; omega)) (ne_of_toNat (by rw [tk, tD _ hcnt]; omega))
          (ne_of_toNat (by rw [tk, tD8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tk, tS _ hj]; omega)) (ne_of_toNat (by rw [tk]; omega)) (ne_of_toNat (by rw [tk, tC8]; omega))]
        exact wr_at _ _ _ (by omega) k hk
  · -- short
    simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i < cnt
    · rw [List.getElem_append_left (by omega)]; exact hT.short i (by omega)
    · rw [List.getElem_append_right (by omega)]; simp [show i - rows.length = 0 by omega, hL]; exact hKl
  · rw [hd]; exact hT.cnt.1
  · rw [hm]; simp only [insM, upd]
    rw [if_neg (ne_of_toNat (by rw [tC8]; omega)), ]; simp [hc]
  · rw [hd]; exact hT.top.1
  · rw [hm]; simp only [insM, upd]; simp [hBk]
  · -- ders
    simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i < cnt
    · have hi' : i < rows.length := by omega
      obtain ⟨a1, a2, a3, a4⟩ := hT.der i hi'
      have hi2 : i < ders.length := by rw [hT.dlen]; exact hi'
      refine ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, ?_, ?_⟩
      · rw [List.getElem_append_left hi2]
        rw [rd (g.D + BitVec.ofNat 64 (16 * i)) (low _ (by rw [tD _ (by omega)]; omega))
          (ne_of_toNat (by rw [tD _ (by omega), tR _ hcnt]; omega)) (ne_of_toNat (by rw [tD _ (by omega), tR8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tD _ (by omega), tD _ hcnt]; omega)) (ne_of_toNat (by rw [tD _ (by omega), tD8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tD _ (by omega), tS _ hj]; omega)) (ne_of_toNat (by rw [tD _ (by omega)]; omega))
          (ne_of_toNat (by rw [tD _ (by omega), tC8]; omega)), a3]
      · rw [List.getElem_append_left hi2]
        rw [rd (g.D + BitVec.ofNat 64 (16 * i) + 8) (low _ (by rw [tD8 _ (by omega)]; omega))
          (ne_of_toNat (by rw [tD8 _ (by omega), tR _ hcnt]; omega)) (ne_of_toNat (by rw [tD8 _ (by omega), tR8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tD8 _ (by omega), tD _ hcnt]; omega)) (ne_of_toNat (by rw [tD8 _ (by omega), tD8 _ hcnt]; omega))
          (ne_of_toNat (by rw [tD8 _ (by omega), tS _ hj]; omega)) (ne_of_toNat (by rw [tD8 _ (by omega)]; omega))
          (ne_of_toNat (by rw [tD8 _ (by omega), tC8]; omega)), a4]
    · have ei : i = cnt := by omega
      subst ei
      obtain ⟨_, _, r3, r4⟩ := hT.room i hcnt
      refine ⟨by rw [hd]; exact r3, by rw [hd]; exact r4, ?_, ?_⟩
      · rw [List.getElem_append_right (by rw [hT.dlen]; omega)]
        simp only [show i - ders.length = 0 by rw [hT.dlen]; omega, List.getElem_singleton]
        rw [hm]; simp only [insM, upd]
        rw [if_neg (ne_of_toNat (by rw [tD _ hcnt, tC8]; omega)), if_neg (ne_of_toNat (by rw [tD _ hcnt]; omega)),
          if_neg (ne_of_toNat (by rw [tD _ hcnt, tS _ hj]; omega)),
          if_neg (ne_of_toNat (by rw [tD _ hcnt, tD8 _ hcnt]; omega))]; simp
      · rw [List.getElem_append_right (by rw [hT.dlen]; omega)]
        simp only [show i - ders.length = 0 by rw [hT.dlen]; omega, List.getElem_singleton]
        rw [hm]; simp only [insM, upd]
        rw [if_neg (ne_of_toNat (by rw [tD8 _ hcnt, tC8]; omega)), if_neg (ne_of_toNat (by rw [tD8 _ hcnt]; omega)),
          if_neg (ne_of_toNat (by rw [tD8 _ hcnt, tS _ hj]; omega))]; simp

end

section
variable {σ : Type} {α : Type}

/-- What `insBody` guarantees relative to `base`, locals agreeing outside `A` and the comparison locals. -/
def IP (base : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (rows : List α) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (g : VGeo) (hu : Nat) (a : α) (dv dv2 : BitVec 64) (j : Nat) (A : List MlS)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨ (r.1 = none ∧ rows.length < g.cap ∧
    VT r.2 enc (rows ++ [a]) (ders ++ [(dv, dv2)]) (slots.set j (rows.length + 1)) g (hu + (enc a).length) ∧
    r.2.memaddrs = base.memaddrs ∧ r.2.code = base.code ∧ r.2.globals = base.globals ∧ r.2.topAddr = base.topAddr ∧
    (∀ c, ¬ inR g c → r.2.memory c = base.memory c) ∧
    (∀ y, y ∉ A → y ∉ cscr → r.2.locals.lookup y = base.locals.lookup y))

theorem ip_dec {s : PanSemStateFiniteExact 64 σ} {x : MlS} {v : BitVec 64} {enc : α → List (BitVec 64)}
    {rows : List α} {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat} {a : α} {dv dv2 : BitVec 64}
    {j : Nat} {A : List MlS} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : IP (setVarHOLFinite x (.val (.word v)) s) enc rows ders slots g hu a dv dv2 j (x :: A) r) :
    IP s enc rows ders slots g hu a dv dv2 j A
      (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (x, s.locals.lookup x) }) := by
  rcases h with h | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, h2, ⟨h3.slot, h3.row, h3.short, h3.cnt, h3.top, h3.hu_le, h3.dlen, h3.der, h3.le, h3.room,
      h3.hroom, h3.layC, h3.layS, h3.layR, h3.layD, h3.layK⟩, h4, h5, h6, h7, h8, fun y hy hc => ?_⟩
    by_cases e : y = x
    · subst e; exact lookup_resVar_same _ _ _
    · rw [lookup_resVar_other _ _ _ _ e, h9 y (by simp [e, hy]) hc]; exact lookup_setVar_other _ _ e

theorem ins_spec (t : PanSemStateFiniteExact 64 σ) (g : VGeo) (enc : α → List (BitVec 64)) (rows : List α)
    (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat) (a : α) (dv dv2 K : BitVec 64) (j : Nat)
    (hT : VT t enc rows ders slots g hu) (hj : j < g.n) (hcap : g.cap < 2 ^ 30) (hn : g.n ≤ 2 ^ 56)
    (hK : Words t K (enc a)) (hKl : (enc a).length < 2 ^ 61)
    (hKout : ∀ i, i < (enc a).length → ¬ inR g (K + BitVec.ofNat 64 (8 * i)))
    (lc : t.locals.lookup lC0 = some (.val (.word g.C)))
    (lcap : t.locals.lookup lCap = some (.val (.word (BitVec.ofNat 64 g.cap))))
    (lr : t.locals.lookup lR = some (.val (.word g.R))) (ld : t.locals.lookup lD = some (.val (.word g.D)))
    (ls : t.locals.lookup lS = some (.val (.word g.S)))
    (lj : t.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))))
    (lK' : t.locals.lookup lK = some (.val (.word K)))
    (ll : t.locals.lookup lL = some (.val (.word (BitVec.ofNat 64 (enc a).length))))
    (ldv : t.locals.lookup lDv = some (.val (.word dv)))
    (ldv2 : t.locals.lookup lDv2 = some (.val (.word dv2)))
    (lke : t.locals.lookup lKe = some (.val (.word (g.KH + BitVec.ofNat 64 (8 * g.kcap)))))
    (hcw : ∀ y, y ∈ cscr → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    IP t enc rows ders slots g hu a dv dv2 j [] (evaluateHOLFiniteState t insBody) := by
  have lKy := hT.layK; have lD' := hT.layD; have lR' := hT.layR; have lS' := hT.layS; have lC' := hT.layC
  have hule := hT.hu_le; have hle := hT.le
  generalize hL : (enc a).length = L at hKl hKout ll
  generalize hc : rows.length = cnt at hle
  have hld : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.load .one (vv lC0)) =
      some (.val (.word (BitVec.ofNat 64 cnt))) := by
    rw [eval_load_word t _ _ (eval_vv t lC0 _ lc) hT.cnt.1, hT.cnt.2, hc]
  unfold insBody; rw [dec_word_eq t lN _ _ _ hld]; apply ip_dec (v := BitVec.ofNat 64 cnt)
  let t1 := setVarHOLFinite lN (.val (.word (BitVec.ofNat 64 cnt))) t
  have hcmp : @evalHOLExact 64 σ _ t1.toExact (fun a => Classical.propDecidable (t1.memaddrs a))
      (.cmp .equal (vv lN) (vv lCap)) = some (.val (.word (bw (cnt = g.cap)))) := by
    rw [ConsLoop.eval_cmp_of t1 .equal _ _ _ _ (eval_vv t1 lN _ (lookup_setVar_same _ _ _))
      (eval_vv t1 lCap _ (by lk [t1]; exact lcap))]
    by_cases h : cnt = g.cap
    · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : ¬ BitVec.ofNat 64 cnt = BitVec.ofNat 64 g.cap := fun e => h (by
        have := congrArg BitVec.toNat e; simp at this; omega)
      simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  rw [ite_word t1 _ _ _ _ hcmp]
  by_cases hfull : cnt = g.cap
  · simp only [bw, hfull, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (Or.inl (hang_spec _ t1 rfl))
  simp only [bw, hfull, ↓reduceIte, ne_eq, not_true_eq_false]
  have hlt : cnt < g.cap := by omega
  have tC8 : (g.C + 8).toNat = g.C.toNat + 8 := tn8 _ (by omega)
  have hld2 : @evalHOLExact 64 σ _ t1.toExact (fun a => Classical.propDecidable (t1.memaddrs a))
      (.load .one (.op .add [vv lC0, .const 8])) = some (.val (.word (g.KH + BitVec.ofNat 64 (8 * hu)))) := by
    rw [eval_load_word t1 _ _ (eval_add2 t1 _ _ _ _ (eval_vv t1 lC0 _ (by lk [t1]; exact lc)) (eval_const t1 8))
      hT.top.1]
    show some (ValueHOL.val (t.memory (g.C + 8))) = _; rw [hT.top.2]
  rw [dec_word_eq t1 lH _ _ _ hld2]; apply ip_dec (v := g.KH + BitVec.ofNat 64 (8 * hu))
  generalize hB : g.KH + BitVec.ofNat 64 (8 * hu) = B
  let t2 := setVarHOLFinite lH (.val (.word B)) t1
  have tK : ∀ k, k ≤ g.kcap → (g.KH + BitVec.ofNat 64 (8 * k)).toNat = g.KH.toNat + 8 * k :=
    fun k h => tn _ _ (by omega)
  have hroomv : (g.KH + BitVec.ofNat 64 (8 * g.kcap) - B) >>> (3 : BitVec 64).toNat =
      BitVec.ofNat 64 (g.kcap - hu) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (3 : BitVec 64).toNat = 3 from rfl, BitVec.toNat_ushiftRight, BitVec.toNat_sub, tK _ (Nat.le_refl _),
      ← hB, tK _ hule, toNat_ofNat_lt _ (by omega), Nat.shiftRight_eq_div_pow]
    omega
  have hcr : @evalHOLExact 64 σ _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
      (.cmp .lower (.shift .lsr (.op .sub [vv lKe, vv lH]) (.const 3)) (vv lL)) =
      some (.val (.word (bw (g.kcap - hu < L)))) := by
    rw [ConsLoop.eval_cmp_of t2 .lower _ _ _ (BitVec.ofNat 64 L)
      (by rw [eval_shr t2 _ _ _ (eval_sub2 t2 _ _ _ _ (eval_vv t2 lKe _ (by lk [t2, t1]; exact lke))
        (eval_vv t2 lH _ (lookup_setVar_same _ _ _))) (by decide), hroomv])
      (eval_vv t2 lL _ (by lk [t2, t1]; exact ll))]
    by_cases h : g.kcap - hu < L
    · have : BitVec.ofNat 64 (g.kcap - hu) < BitVec.ofNat 64 L := by
        rw [BitVec.lt_def, toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by omega)]; exact h
      simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
    · have : ¬ BitVec.ofNat 64 (g.kcap - hu) < BitVec.ofNat 64 L := by
        rw [BitVec.lt_def, toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by omega)]; exact h
      simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  rw [ite_word t2 _ _ _ _ hcr]
  by_cases hro : g.kcap - hu < L
  · simp only [bw, hro, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (Or.inl (hang_spec _ t2 rfl))
  simp only [bw, hro, ↓reduceIte, ne_eq, not_true_eq_false]
  have hroom : hu + L ≤ g.kcap := by omega
  -- the copy
  have cw2 : ∀ y, y ∈ cscr → ∃ w, t2.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    have h1 : y ≠ lH := fun e => by subst e; simp [cscr] at hy; revert hy; decide
    have h2 : y ≠ lN := fun e => by subst e; simp [cscr] at hy; revert hy; decide
    obtain ⟨w, hw⟩ := hcw y hy; exact ⟨w, by lk [t2, t1]; exact hw⟩
  obtain ⟨wa0, ha0⟩ := cw2 lWa (by decide)
  obtain ⟨wb0, hb0⟩ := cw2 lWb (by decide)
  obtain ⟨wn0, hn0⟩ := cw2 lWn (by decide)
  obtain ⟨wg0, hg0⟩ := cw2 lWg (by decide)
  let t3 := setVarHOLFinite lWa (.val (.word K)) t2
  let t4 := setVarHOLFinite lWb (.val (.word B)) t3
  let t5 := setVarHOLFinite lWn (.val (.word (BitVec.ofNat 64 L))) t4
  let t6 := setVarHOLFinite lWg (.val (.word 1)) t5
  have hcopy : evaluateHOLFiniteState t2 insCopy = evaluateHOLFiniteState t6 copyLoop := by
    unfold insCopy
    rw [seq_normal _ (ConsLoop.assign_local t2 lWa _ K wa0 (eval_vv t2 lK _ (by lk [t2, t1]; exact lK')) ha0),
      seq_normal _ (ConsLoop.assign_local t3 lWb _ B wb0 (eval_vv t3 lH _ (by lk [t3, t2])) (by lk [t3]; exact hb0)),
      seq_normal _ (ConsLoop.assign_local t4 lWn _ _ wn0 (eval_vv t4 lL _ (by lk [t4, t3, t2, t1]; exact ll))
        (by lk [t4, t3]; exact hn0)),
      seq_normal _ (ConsLoop.assign_local t5 lWg (.const 1) 1 wg0 (eval_const t5 1) (by lk [t5, t4, t3]; exact hg0))]
  have hBk : ∀ k, B + BitVec.ofNat 64 (8 * k) = g.KH + BitVec.ofNat 64 (8 * (hu + k)) := by
    intro k; rw [← hB, ofNat_add8]
  have hW : Words t6 K (enc a) := hK
  rcases copyLoop_spec t6 K B (enc a) (by omega) hW
      (fun k hk => by rw [hBk]; exact hT.hroom _ (by omega))
      (fun i k hi hk => fun e => hKout i (by omega) (by
        rw [e, hBk, inR, tK _ (by omega)]; constructor <;> omega))
      (by lk [t6, t5, t4, t3]) (by lk [t6, t5, t4]) (by lk [t6, t5]; rw [hL]) (by lk [t6]) with hs | ⟨hn6, hCp, hmem⟩
  · exact Or.inl (seq_stop t2 insCopy insStores (by rw [hcopy]; exact hs))
  generalize hw : evaluateHOLFiniteState t6 copyLoop = wst at hn6 hCp hmem
  obtain ⟨w1, w⟩ := wst
  simp only at hn6 hCp hmem; subst hn6
  rw [seq_normal _ (hcopy.trans hw)]
  obtain ⟨cd, cc, cg, ct, cfr, _⟩ := hCp
  have keep : ∀ y, y ∉ cscr → w.locals.lookup y = t6.locals.lookup y := by
    intro y hy; simp only [cscr, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact cfr y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.2
  have tR : ∀ i, i < g.cap → (g.R + BitVec.ofNat 64 (16 * i)).toNat = g.R.toNat + 16 * i :=
    fun i h => tn _ _ (by omega)
  obtain ⟨r1, r2, r3, r4⟩ := hT.room cnt hlt
  obtain ⟨_, _, _, hsd, _⟩ := hT.slot j hj
  rw [insStores_eval w g.C g.R g.D g.S B dv dv2 cnt j L (by omega) (by omega) (by omega)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact lr)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1])
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2])
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact ll)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact ld)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact ldv)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact ldv2)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact ls)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact lj)
    (by rw [keep _ (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact lc)
    (by rw [cd]; exact r1) (by rw [cd]; exact r2) (by rw [cd]; exact r3) (by rw [cd]; exact r4) (by rw [cd]; exact hsd)
    (by rw [cd]; exact hT.cnt.1) (by rw [cd]; exact hT.top.1)]
  have hmem' : w.memory = wr t.memory B (enc a) := hmem
  refine Or.inr ⟨rfl, by omega, vt_ins hT a dv dv2 j hj (by omega) hcap (by omega) (by omega)
    (by show insM w.memory _ _ _ _ _ _ _ _ _ _ = _; rw [hmem', ← hB, hc, hL]) cd, cd, cc, cg, ct, fun c hcr => ?_,
    fun y hy hc' => by
      rw [keep y hc']
      simp only [cscr, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc'
      obtain ⟨n1, n2, n3, n4, n5⟩ := hc'
      lk [t6, t5, t4, t3]; rfl⟩
  -- memory outside the region
  have tS : (g.S + BitVec.ofNat 64 (8 * j)).toNat = g.S.toNat + 8 * j := tn _ _ (by omega)
  have tD : (g.D + BitVec.ofNat 64 (16 * cnt)).toNat = g.D.toNat + 16 * cnt := tn _ _ (by omega)
  have tD8 : (g.D + BitVec.ofNat 64 (16 * cnt) + 8).toNat = g.D.toNat + 16 * cnt + 8 := by
    rw [tn8 _ (by rw [tD]; omega), tD]
  have tR8 : (g.R + BitVec.ofNat 64 (16 * cnt) + 8).toNat = g.R.toNat + 16 * cnt + 8 := by
    rw [tn8 _ (by rw [tR _ hlt]; omega), tR _ hlt]
  simp only [inR] at hcr
  show insM w.memory _ _ _ _ _ _ _ _ _ _ c = _
  rw [insM_other _ _ _ _ _ _ _ _ _ _ _ _ (ne_of_toNat (by rw [tR _ hlt]; omega)) (ne_of_toNat (by rw [tR8]; omega))
    (ne_of_toNat (by rw [tD]; omega)) (ne_of_toNat (by rw [tD8]; omega)) (ne_of_toNat (by rw [tS]; omega)) (ne_of_toNat (by omega))
    (ne_of_toNat (by rw [tC8]; omega)), hmem']
  exact wr_out _ _ _ _ (fun k hk => ne_of_toNat (by rw [hBk, tK _ (by omega)]; omega))

end

end ConPanqueque.V
