import ConPanqueque.Start.Stores
import ConPanqueque.Start.Boot

/-! # The initial memory image

The words the program's first block stores (everything else is zero, as the harness's fresh
mapping is): every table's descriptor and top word, the two bootstrap rows (the anonymous name in
the anonymous-name table, level zero in the zero table), and the placeholder pin block `P0` at
`PO0` in the environment heap.  The list is in increasing address order (`initL_sorted`), so its
addresses are distinct. -/

open ConRon.Arena ConPanqueque.V ConPanqueque.T ConPanqueque.Code

namespace ConPanqueque.Start

def w64 (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

/-- A descriptor's eight words at `G`. -/
def descL (G : BitVec 64) (g : VGeo) (b : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  (List.range 8).map fun m => (G + w64 (8 * m), (descV g b).getD m 0)

/-- The store tables' descriptors, at `DIR + 64·(19·tier + k)`. -/
def storeDescL : List (BitVec 64 × BitVec 64) :=
  (List.range 38).flatMap fun i => descL (descAddr layout (i % 19) (i / 19)) (layout.geo (i % 19) (i / 19))
    (layout.base (i % 19) (i / 19))

/-- The memo descriptors, at `mG (rOf i)`. -/
def memoDescL : List (BitVec 64 × BitVec 64) :=
  (List.range 37).flatMap fun i => descL (w64 (base + 65536 + 64 * i)) (geoAt (M0 + i * TW)) 1

/-- The anonymous name's and level zero's derived words. -/
def dAnon : BitVec 64 := (NStore.empty.derOfView .anonymous).toBitVec
def dZero : BitVec 64 × BitVec 64 := dWL (LStore.empty.derOfView .zero)

/-- A store table's words: the top word, and for the two bootstrap tables the one row. -/
def tblL (i : Nat) : List (BitVec 64 × BitVec 64) :=
  let g := geoAt (T0 + i * TW)
  if i = 0 then [(g.C, 1), (g.C + 8, g.KH), (g.S, 1), (g.R, g.KH), (g.D, dAnon)]
  else if i = 6 then [(g.C, 1), (g.C + 8, g.KH), (g.S, 1), (g.R, g.KH), (g.D, dZero.1), (g.D + 8, dZero.2)]
  else [(g.C + 8, g.KH)]

def storeTblL : List (BitVec 64 × BitVec 64) := (List.range 38).flatMap tblL

def memoTblL : List (BitVec 64 × BitVec 64) :=
  (List.range 37).map fun i => let g := geoAt (M0 + i * TW); (g.C + 8, g.KH)

/-- The placeholder pin block's index in the environment heap, and the code's (real) one. -/
def PO0 : Nat := 0
def PO1 : Nat := 64

/-- The placeholder environment heap: the pin block of `P0` (all handles word 0), its
`maxNatSize`, and its empty reserved-name list (a zero count at index 57). -/
def EH0 : List (BitVec 64) :=
  (List.range 64).map fun i => if i = 55 then w64 maxNatSizeDefault else if i = 56 then w64 (base + E0 + 8 * 57) else 0

def envL : List (BitVec 64 × BitVec 64) :=
  [(w64 (base + E0 + 8 * 55), w64 maxNatSizeDefault), (w64 (base + E0 + 8 * 56), w64 (base + E0 + 8 * 57))]

def initL : List (BitVec 64 × BitVec 64) := storeDescL ++ memoDescL ++ storeTblL ++ memoTblL ++ envL

/-- Strictly increasing. -/
def incr : List Nat → Bool
  | a :: b :: l => a < b && incr (b :: l)
  | _ => true

theorem incr_lt_all : ∀ (a : Nat) (l : List Nat), incr (a :: l) = true → ∀ x ∈ l, a < x
  | a, [], _, x, hx => by cases hx
  | a, b :: l, h, x, hx => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (incr_lt_all b l h.2 x hx)

theorem incr_nodup : ∀ l : List Nat, incr l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => by simp
  | a :: b :: l, h => by
    refine List.nodup_cons.mpr ⟨fun hm => Nat.lt_irrefl a (incr_lt_all a _ h a hm), incr_nodup _ ?_⟩
    simp only [incr, Bool.and_eq_true] at h; exact h.2

set_option maxRecDepth 100000 in
theorem initL_sorted : incr (initL.map fun p => p.1.toNat) = true := by decide +kernel

theorem initL_nodup : (initL.map Prod.fst).Nodup := by
  have h := incr_nodup _ initL_sorted
  rw [show (initL.map fun p => p.1.toNat) = (initL.map Prod.fst).map BitVec.toNat by simp] at h
  exact List.Pairwise.of_map _ (fun a b hab e => hab (by rw [e])) h

/-! ## The bootstrap store's tables -/
macro "boot_simp" : tactic => `(tactic| simp [bootStore, EStore.empty, NStore.empty, NTables.empty, LTables.empty,
    LStore.empty, LsStore.empty, Tbl.empty, EStore.ns, EStore.ls, EStore.internName, LsStore.internName, LStore.internName,
    EStore.internLevel, LsStore.internLevel, nstore_anon, lstore_zero, twoTier, tierInt, Tbl.push, Tbl.find?, Tbl.size])

theorem bootStore_nsP : bootStore.ns.pers = { NTables.empty with anons := Tbl.push Tbl.empty AnonNode.mk (NStore.empty.derOfView .anonymous) (mkN NTag.anonymous 0 0) } := by boot_simp
theorem bootStore_nsS : bootStore.ns.scr = NTables.empty := by boot_simp
theorem bootStore_lsP : bootStore.ls.pers = { LTables.empty with zeros := Tbl.push Tbl.empty ZeroNode.mk (LStore.empty.derOfView .zero) (mkN LTag.zero 0 0) } := by boot_simp; rfl
theorem bootStore_lsS : bootStore.ls.scr = LTables.empty := by boot_simp
theorem bootStore_lssP : bootStore.lss.pers = LsTables.empty := rfl
theorem bootStore_lssS : bootStore.lss.scr = LsTables.empty := rfl
theorem bootStore_eP : bootStore.pers = ETables.empty := rfl
theorem bootStore_eS : bootStore.scr = ETables.empty := rfl
theorem bootStore_on : bootStore.scratchOn = false ∧ bootStore.lss.scratchOn = false ∧ bootStore.ls.scratchOn = false ∧ bootStore.ns.scratchOn = false := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> boot_simp
theorem dAnon_val : dAnon = 1723 := by decide +kernel
theorem dZero_val : dZero = (1, 0) := by decide +kernel

end ConPanqueque.Start
