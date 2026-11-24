import ConPanqueque.Scan.Model

/-! # The key classifier as a table

con-leche's `keyAt` is an unrolled decision tree: the key's first byte, then its length, then a
chain of literal compares of the rest.  `keyTbl` is that tree as data (generated from the source of
`keyAt`), `evalK` its interpreter, and `keyAt_eq` says they agree on every input; the Pancake
classifier is compiled from the same table. -/

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-- The bytes from `j + k` on are `cs`, by `byteAt` (which reads `0` past the end). -/
def litsAt (b : ByteArray) (j : USize) : List UInt8 → Nat → Bool
  | [], _ => true
  | c :: cs, k => byteAt b (j + USize.ofNat k) == c && litsAt b j cs (k + 1)

def firstLit (b : ByteArray) (j : USize) : List (List UInt8 × Key) → Key
  | [] => .kUnknown
  | (cs, k) :: r => if litsAt b j cs 0 then k else firstLit b j r

abbrev KeyTbl := List (UInt8 × List (USize × List (List UInt8 × Key)))

/-- The length switch of one first byte. -/
def evalLens (b : ByteArray) (j kl : USize) : List (USize × List (List UInt8 × Key)) → Key
  | [] => .kUnknown
  | (l, cs) :: r => if kl == l then firstLit b j cs else evalLens b j kl r

/-- The first-byte switch. -/
def evalBytes (b : ByteArray) (j kl : USize) (x : UInt8) : KeyTbl → Key
  | [] => .kUnknown
  | (y, lens) :: r => if x = y then evalLens b j kl lens else evalBytes b j kl x r

def evalK (b : ByteArray) (i kl : USize) (t : KeyTbl) : Key :=
  evalBytes b (i + 1 + 1) kl (byteAt b (i + 1)) t

def keyTbl : KeyTbl := [
  (97, [(3, [([112, 112], .kApp), ([114, 103], .kArg), ([108, 108], .kAll)]), (5, [([120, 105, 111, 109], .kAxiom)])]),
  (98, [(4, [([111, 100, 121], .kBody), ([118, 97, 114], .kBvar)]), (10, [([105, 110, 100, 101, 114, 73, 110, 102, 111], .kBinderInfo)])]),
  (99, [(5, [([111, 110, 115, 116], .kConst), ([116, 111, 114, 115], .kCtors)]), (4, [([116, 111, 114], .kCtor), ([105, 100, 120], .kCidx)])]),
  (100, [(3, [([101, 102], .kDef)])]),
  (102, [(2, [([110], .kFn)]), (7, [([111, 114, 97, 108, 108, 69], .kForallE)])]),
  (104, [(5, [([105, 110, 116, 115], .kHints)])]),
  (105, [(2, [([101], .kIe), ([110], .kIn), ([108], .kIl)]), (1, [([], .kI)]), (3, [([100, 120], .kIdx)]), (4, [([109, 97, 120], .kImax)]), (9, [([110, 100, 117, 99, 116, 105, 118, 101], .kInductive)]), (5, [([115, 82, 101, 99], .kIsRec)]), (11, [([115, 82, 101, 102, 108, 101, 120, 105, 118, 101], .kIsReflexive)]), (8, [([115, 85, 110, 115, 97, 102, 101], .kIsUnsafe)]), (6, [([110, 100, 117, 99, 116], .kInduct)])]),
  (107, [(4, [([105, 110, 100], .kKind)]), (1, [([], .kK)])]),
  (108, [(3, [([97, 109], .kLam)]), (4, [([101, 116, 69], .kLetE)]), (11, [([101, 118, 101, 108, 80, 97, 114, 97, 109, 115], .kLevelParams)])]),
  (109, [(3, [([97, 120], .kMax)]), (4, [([101, 116, 97], .kMeta)])]),
  (110, [(4, [([97, 109, 101], .kName)]), (3, [([117, 109], .kNum)]), (6, [([97, 116, 86, 97, 108], .kNatVal), ([111, 110, 100, 101, 112], .kNondep)]), (7, [([102, 105, 101, 108, 100, 115], .kNfields)]), (9, [([117, 109, 80, 97, 114, 97, 109, 115], .kNumParams), ([117, 109, 70, 105, 101, 108, 100, 115], .kNumFields), ([117, 109, 77, 105, 110, 111, 114, 115], .kNumMinors), ([117, 109, 78, 101, 115, 116, 101, 100], .kNumNested)]), (10, [([117, 109, 73, 110, 100, 105, 99, 101, 115], .kNumIndices), ([117, 109, 77, 111, 116, 105, 118, 101, 115], .kNumMotives)])]),
  (111, [(6, [([112, 97, 113, 117, 101], .kOpaque)])]),
  (112, [(3, [([114, 101], .kPre)]), (5, [([97, 114, 97, 109], .kParam)]), (4, [([114, 111, 106], .kProj)])]),
  (113, [(4, [([117, 111, 116], .kQuot)])]),
  (114, [(4, [([101, 99, 115], .kRecs)]), (5, [([117, 108, 101, 115], .kRules)]), (3, [([104, 115], .kRhs)]), (7, [([101, 103, 117, 108, 97, 114], .kRegular)])]),
  (115, [(3, [([116, 114], .kStr)]), (4, [([111, 114, 116], .kSort), ([117, 99, 99], .kSucc)]), (6, [([116, 114, 117, 99, 116], .kStruct), ([116, 114, 86, 97, 108], .kStrVal), ([97, 102, 101, 116, 121], .kSafety)])]),
  (116, [(4, [([121, 112, 101], .kType)]), (8, [([121, 112, 101, 78, 97, 109, 101], .kTypeName)]), (3, [([104, 109], .kThm)]), (5, [([121, 112, 101, 115], .kTypes)])]),
  (117, [(2, [([115], .kUs)])]),
  (118, [(5, [([97, 108, 117, 101], .kValue)])])]

theorem litsAt_1 (b : ByteArray) (j : USize) (c0 : UInt8) :
    litsAt b j [c0] 0 = lit1 b j c0 := by
  simp only [litsAt, lit1, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_2 (b : ByteArray) (j : USize) (c0 c1 : UInt8) :
    litsAt b j [c0, c1] 0 = lit2 b j c0 c1 := by
  simp only [litsAt, lit2, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_3 (b : ByteArray) (j : USize) (c0 c1 c2 : UInt8) :
    litsAt b j [c0, c1, c2] 0 = lit3 b j c0 c1 c2 := by
  simp only [litsAt, lit3, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_4 (b : ByteArray) (j : USize) (c0 c1 c2 c3 : UInt8) :
    litsAt b j [c0, c1, c2, c3] 0 = lit4 b j c0 c1 c2 c3 := by
  simp only [litsAt, lit4, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_5 (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 : UInt8) :
    litsAt b j [c0, c1, c2, c3, c4] 0 = lit5 b j c0 c1 c2 c3 c4 := by
  simp only [litsAt, lit5, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_6 (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 : UInt8) :
    litsAt b j [c0, c1, c2, c3, c4, c5] 0 = lit6 b j c0 c1 c2 c3 c4 c5 := by
  simp only [litsAt, lit6, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_7 (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 : UInt8) :
    litsAt b j [c0, c1, c2, c3, c4, c5, c6] 0 = lit7 b j c0 c1 c2 c3 c4 c5 c6 := by
  simp only [litsAt, lit7, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_8 (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 c7 : UInt8) :
    litsAt b j [c0, c1, c2, c3, c4, c5, c6, c7] 0 = lit8 b j c0 c1 c2 c3 c4 c5 c6 c7 := by
  simp only [litsAt, lit8, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_9 (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : UInt8) :
    litsAt b j [c0, c1, c2, c3, c4, c5, c6, c7, c8] 0 = lit9 b j c0 c1 c2 c3 c4 c5 c6 c7 c8 := by
  simp only [litsAt, lit9, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_10 (b : ByteArray) (j : USize) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : UInt8) :
    litsAt b j [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] 0 = lit10 b j c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  simp only [litsAt, lit10, Bool.and_true, Bool.and_assoc]
  have : j + USize.ofNat 0 = j := by rw [show USize.ofNat 0 = 0 from rfl]; simp
  rw [this]; try rfl

theorem litsAt_0 (b : ByteArray) (j : USize) : litsAt b j [] 0 = true := rfl


set_option maxHeartbeats 4000000 in
/-- **`keyAt` is the table's interpreter**, on every input. -/
theorem keyAt_eq (b : ByteArray) (i kl : USize) : keyAt b i kl = evalK b i kl keyTbl := by
  unfold keyAt evalK
  generalize byteAt b (i + 1) = x
  generalize i + 1 + 1 = j
  split <;> simp only [keyTbl, evalBytes, evalLens, firstLit, litsAt_0, litsAt_1, litsAt_2, litsAt_3,
    litsAt_4, litsAt_5, litsAt_6, litsAt_7, litsAt_8, litsAt_9, litsAt_10, ↓reduceIte] <;> simp_all
/-! ## On a list -/

def byteL (bs : List UInt8) (p : Nat) : UInt8 := bs[p]?.getD 0

def litsL (bs : List UInt8) (j : Nat) : List UInt8 → Nat → Bool
  | [], _ => true
  | c :: cs, k => byteL bs (j + k) == c && litsL bs j cs (k + 1)

def firstL (bs : List UInt8) (j : Nat) : List (List UInt8 × Key) → Key
  | [] => .kUnknown
  | (cs, k) :: r => if litsL bs j cs 0 then k else firstL bs j r

def lensL (bs : List UInt8) (j kl : Nat) : List (USize × List (List UInt8 × Key)) → Key
  | [] => .kUnknown
  | (l, cs) :: r => if kl = l.toNat then firstL bs j cs else lensL bs j kl r

def bytesL (bs : List UInt8) (j kl : Nat) (x : UInt8) : KeyTbl → Key
  | [] => .kUnknown
  | (y, lens) :: r => if x = y then lensL bs j kl lens else bytesL bs j kl x r

def evalKL (bs : List UInt8) (i kl : Nat) : Key := bytesL bs (i + 2) kl (byteL bs (i + 1)) keyTbl

theorem usize_add_toNat (h64 : System.Platform.numBits = 64) (a : USize) (k : Nat) (h : a.toNat + k < 2 ^ 64) :
    (a + USize.ofNat k).toNat = a.toNat + k := by
  rw [USize.toNat_add, USize.toNat_ofNat']
  simp only [USize.size_eq_two_pow, h64]
  rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]; exact Nat.mod_eq_of_lt h

theorem litsAt_L {b : ByteArray} (hp : Plat b) (j : USize) :
    ∀ (cs : List UInt8) (k : Nat), j.toNat + k + cs.length < 2 ^ 64 →
      litsAt b j cs k = litsL b.data.toList j.toNat cs k := by
  intro cs
  induction cs with
  | nil => intro k _; rfl
  | cons c cs ih =>
    intro k hk
    simp only [litsAt, litsL, List.length_cons] at hk ⊢
    rw [ih (k + 1) (by omega), byteAt_eq hp, usize_add_toNat hp.bits j k (by omega)]
    rfl

theorem firstLit_L {b : ByteArray} (hp : Plat b) (j : USize) (hj : j.toNat + 16 < 2 ^ 64) :
    ∀ (cands : List (List UInt8 × Key)), (∀ c ∈ cands, c.1.length ≤ 16) →
      firstLit b j cands = firstL b.data.toList j.toNat cands := by
  intro cands
  induction cands with
  | nil => intro _; rfl
  | cons c r ih =>
    intro hl
    obtain ⟨cs, k⟩ := c
    have h1 := hl (cs, k) (List.mem_cons_self ..)
    simp only [firstLit, firstL]
    rw [litsAt_L hp j cs 0 (by simp at h1; omega), ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))]

theorem evalLens_L {b : ByteArray} (hp : Plat b) (j kl : USize) (hj : j.toNat + 16 < 2 ^ 64) :
    ∀ (lens : List (USize × List (List UInt8 × Key))), (∀ l ∈ lens, ∀ c ∈ l.2, c.1.length ≤ 16) →
      evalLens b j kl lens = lensL b.data.toList j.toNat kl.toNat lens := by
  intro lens
  induction lens with
  | nil => intro _; rfl
  | cons l r ih =>
    intro hl
    obtain ⟨len, cs⟩ := l
    simp only [evalLens, lensL]
    have hq : (kl == len) = decide (kl.toNat = len.toNat) := by
      by_cases h : kl = len
      · simp [h]
      · have : ¬ kl.toNat = len.toNat := fun h' => h (USize.toNat_inj.mp h')
        simp [h, this]
    rw [hq, firstLit_L hp j hj cs (hl _ (List.mem_cons_self ..)), ih (fun l hl' => hl l (List.mem_cons_of_mem _ hl'))]
    simp

theorem keyTbl_short : ∀ e ∈ keyTbl, ∀ l ∈ e.2, ∀ c ∈ l.2, c.1.length ≤ 16 := by decide

theorem evalBytes_L {b : ByteArray} (hp : Plat b) (j kl : USize) (x : UInt8) (hj : j.toNat + 16 < 2 ^ 64) :
    ∀ (t : KeyTbl), (∀ e ∈ t, ∀ l ∈ e.2, ∀ c ∈ l.2, c.1.length ≤ 16) →
      evalBytes b j kl x t = bytesL b.data.toList j.toNat kl.toNat x t := by
  intro t
  induction t with
  | nil => intro _; rfl
  | cons e r ih =>
    intro hl
    obtain ⟨y, lens⟩ := e
    simp only [evalBytes, bytesL]
    rw [evalLens_L hp j kl hj lens (hl _ (List.mem_cons_self ..)), ih (fun e he => hl e (List.mem_cons_of_mem _ he))]

/-- **`keyAt` on a list**: away from the top of the address space. -/
theorem keyAt_L {b : ByteArray} (hp : Plat b) (i kl : USize) (hi : i.toNat + 18 < 2 ^ 64) :
    keyAt b i kl = evalKL b.data.toList i.toNat kl.toNat := by
  rw [keyAt_eq, evalK, evalKL]
  have h1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat hp.bits i 1 (by omega)
  have h2 : (i + 1 + 1).toNat = i.toNat + 2 := by
    rw [show (i + 1 + 1) = (i + 1) + USize.ofNat 1 from rfl, usize_add_toNat hp.bits _ 1 (by omega), h1]
  rw [evalBytes_L hp _ kl _ (by omega) keyTbl keyTbl_short, h2, byteAt_eq hp, h1]
  rfl

theorem litsL_shift (bs : List UInt8) (j : Nat) :
    ∀ (cs : List UInt8) (k : Nat), litsL bs j cs (k + 1) = litsL bs (j + 1) cs k := by
  intro cs
  induction cs with
  | nil => intro k; rfl
  | cons c cs ih => intro k; simp only [litsL]; rw [ih (k + 1), show j + (k + 1) = j + 1 + k by omega]

/-- con-leche's `matchLit` against a literal with no `0` byte: the list check `litsL`. -/
theorem matchLit_L {b : ByteArray} (hp : Plat b) (lit : ByteArray) (hl : lit.size < 2 ^ 32)
    (hz : ∀ x ∈ lit.data.toList, x ≠ 0) :
    ∀ n (i k : USize), lit.size - k.toNat = n → i.toNat + (lit.size - k.toNat) < 2 ^ 64 → k.toNat ≤ lit.size →
      ConLeche.Frontend.matchLit b i lit k = litsL b.data.toList i.toNat (lit.data.toList.drop k.toNat) 0 := by
  have hpl : Plat lit := ⟨hp.bits, by omega⟩
  intro n
  induction n with
  | zero =>
    intro i k hn hi hk
    rw [ConLeche.Frontend.matchLit, dif_neg (fun h => by have := (hpl.lt_iff k).mp h; omega)]
    rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl
  | succ n ih =>
    intro i k hn hi hk
    have hkl : k.toNat < lit.size := by omega
    have hkl' : k.toNat < lit.data.toList.length := by simpa using hkl
    rw [ConLeche.Frontend.matchLit, dif_pos ((hpl.lt_iff k).mpr hkl), List.drop_eq_getElem_cons hkl']
    simp only [litsL]
    have hk1 : (k + 1).toNat = k.toNat + 1 := ConLeche.Frontend.usizeStep lit k ((hpl.lt_iff k).mpr hkl)
    have hc : lit.data.toList[k.toNat] ≠ 0 := hz _ (List.getElem_mem _)
    rw [litsL_shift]
    split
    · rename_i h
      have hil : i.toNat < b.size := (hp.lt_iff i).mp h
      have hi1 : (i + 1).toNat = i.toNat + 1 := ConLeche.Frontend.usizeStep b i h
      rw [uget_eq b i hil h, ih (i + 1) (k + 1) (by omega) (by omega) (by omega), hi1, hk1]
      have : byteL b.data.toList (i.toNat + 0) = b.data.toList[i.toNat]'(by simpa using hil) := by
        simp [byteL, List.getElem?_eq_getElem (by simpa using hil : i.toNat < b.data.toList.length)]
      rw [this, uget_eq lit k hkl ((hpl.lt_iff k).mpr hkl)]
    · rename_i h
      have hil : ¬ i.toNat < b.data.toList.length := by
        have : ¬ i.toNat < b.size := fun h' => h ((hp.lt_iff i).mpr h'); simpa using this
      have : byteL b.data.toList (i.toNat + 0) = 0 := by
        simp [byteL, List.getElem?_eq_none (by omega : b.data.toList.length ≤ i.toNat)]
      rw [this]
      have : (0 == lit.data.toList[k.toNat]) = false := beq_eq_false_iff_ne.mpr (Ne.symm hc)
      simp only [this, Bool.false_and]

end ConPanqueque.Scan
