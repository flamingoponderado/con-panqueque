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
end ConPanqueque.Scan
