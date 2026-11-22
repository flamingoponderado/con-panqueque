import ConRon.Arena.Store

/-!
# Encoding records as word sequences

The generic tables key rows by `List (BitVec 64)`; each record type needs an
injective encoding. Fixed-width fields come first and a variable-length part
last: a `Nat` as its canonical base-`2^64` limbs (no trailing zero limb), a
`String` as its UTF-8 byte count then the bytes packed eight to a word.
-/

namespace ConPanqueque.V.Enc

/-- Canonical little-endian base-`2^64` limbs. -/
def limbs (n : Nat) : List (BitVec 64) :=
  if h : n = 0 then [] else BitVec.ofNat 64 (n % 2 ^ 64) :: limbs (n / 2 ^ 64)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The number a limb list denotes. -/
def ofLimbs : List (BitVec 64) → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * ofLimbs ws

theorem ofLimbs_limbs (n : Nat) : ofLimbs (limbs n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold limbs
    by_cases h : n = 0
    · subst h; rfl
    · simp only [h, ↓reduceDIte, ofLimbs]
      rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))]
      simp only [BitVec.toNat_ofNat, Nat.mod_mod]
      exact Nat.mod_add_div n (2 ^ 64)

theorem limbs_inj {m n : Nat} (h : limbs m = limbs n) : m = n := by
  rw [← ofLimbs_limbs m, ← ofLimbs_limbs n, h]

theorem map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ l1 l2 : List α, l1.map f = l2.map f → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj hf as bs h.2]

/-- A string's UTF-8 bytes, one per word (packing is a later optimisation). -/
def strW (s : String) : List (BitVec 64) := s.toByteArray.data.toList.map (fun b => BitVec.ofNat 64 b.toNat)

theorem strW_inj {s t : String} (h : strW s = strW t) : s = t := by
  have hm : ∀ a b : UInt8, BitVec.ofNat 64 a.toNat = BitVec.ofNat 64 b.toNat → a = b := by
    intro a b e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by have := a.toNat_lt; omega), Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)] at this
    exact UInt8.toNat_inj.mp this
  have h1 : s.toByteArray.data.toList = t.toByteArray.data.toList := map_inj hm _ _ h
  have h2 : s.toByteArray.data = t.toByteArray.data := Array.toList_inj.mp h1
  have h3 : s.toByteArray = t.toByteArray := by
    cases hs : s.toByteArray; cases ht : t.toByteArray; rw [hs, ht] at h2; simp only at h2; rw [h2]
  exact String.toByteArray_inj.mp h3

/-- A handle's word. -/
def idxW {k : ConRon.Arena.IdxKind} (i : ConRon.Arena.Idx k) : BitVec 64 := i.word.toUInt64.toBitVec

theorem idxW_inj {k : ConRon.Arena.IdxKind} {i j : ConRon.Arena.Idx k} (h : idxW i = idxW j) : i = j := by
  obtain ⟨wi⟩ := i; obtain ⟨wj⟩ := j
  simp only [idxW] at h
  have : wi = wj := by
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simpa using this
  rw [this]

open ConRon.Arena

def encAnon (_ : AnonNode) : List (BitVec 64) := []
def encStr (x : StrNode) : List (BitVec 64) := idxW x.pre :: strW x.s
def encNum (x : NumNode) : List (BitVec 64) := idxW x.pre :: limbs x.n
def encZero (_ : ZeroNode) : List (BitVec 64) := []
def encSucc (x : SuccNode) : List (BitVec 64) := [idxW x.u]
def encBinL (x : BinLNode) : List (BitVec 64) := [idxW x.u, idxW x.v]
def encParam (x : ParamNode) : List (BitVec 64) := [idxW x.n]
def encList (x : ListNode) : List (BitVec 64) := x.us.map idxW
def encBVar (x : BVarNode) : List (BitVec 64) := limbs x.i
def encFVar (x : FVarNode) : List (BitVec 64) := idxW x.ty :: limbs x.idx
def encSort (x : SortNode) : List (BitVec 64) := [idxW x.u]
def encConst (x : ConstNode) : List (BitVec 64) := [idxW x.n, idxW x.us]
def encApp (x : AppNode) : List (BitVec 64) := [idxW x.f, idxW x.a]
def encBind (x : BindNode) : List (BitVec 64) := [idxW x.ty, idxW x.body]
def encLet (x : LetNode) : List (BitVec 64) := [idxW x.ty, idxW x.val, idxW x.body]
def encLit (x : LitNode) : List (BitVec 64) :=
  match x.l with
  | .natVal n => 0 :: limbs n
  | .strVal s => 1 :: strW s
def encProj (x : ProjNode) : List (BitVec 64) := idxW x.n :: idxW x.e :: limbs x.i

theorem encAnon_inj : ∀ x y, encAnon x = encAnon y → x = y := by intro ⟨⟩ ⟨⟩ _; rfl
theorem encZero_inj : ∀ x y, encZero x = encZero y → x = y := by intro ⟨⟩ ⟨⟩ _; rfl
theorem encStr_inj : ∀ x y, encStr x = encStr y → x = y := by
  intro ⟨p, s⟩ ⟨q, t⟩ h; simp only [encStr, List.cons.injEq] at h; rw [idxW_inj h.1, strW_inj h.2]
theorem encNum_inj : ∀ x y, encNum x = encNum y → x = y := by
  intro ⟨p, m⟩ ⟨q, n⟩ h; simp only [encNum, List.cons.injEq] at h; rw [idxW_inj h.1, limbs_inj h.2]
theorem encSucc_inj : ∀ x y, encSucc x = encSucc y → x = y := by
  intro ⟨u⟩ ⟨v⟩ h; simp only [encSucc, List.cons.injEq, and_true] at h; rw [idxW_inj h]
theorem encBinL_inj : ∀ x y, encBinL x = encBinL y → x = y := by
  intro ⟨a, b⟩ ⟨c, d⟩ h; simp only [encBinL, List.cons.injEq, and_true] at h; rw [idxW_inj h.1, idxW_inj h.2]
theorem encParam_inj : ∀ x y, encParam x = encParam y → x = y := by
  intro ⟨u⟩ ⟨v⟩ h; simp only [encParam, List.cons.injEq, and_true] at h; rw [idxW_inj h]
theorem encList_inj : ∀ x y, encList x = encList y → x = y := by
  intro ⟨us⟩ ⟨vs⟩ h; simp only [encList] at h
  rw [map_inj (fun a b e => idxW_inj e) _ _ h]
theorem encBVar_inj : ∀ x y, encBVar x = encBVar y → x = y := by
  intro ⟨i⟩ ⟨j⟩ h; simp only [encBVar] at h; rw [limbs_inj h]
theorem encFVar_inj : ∀ x y, encFVar x = encFVar y → x = y := by
  intro ⟨i, a⟩ ⟨j, b⟩ h; simp only [encFVar, List.cons.injEq] at h; rw [idxW_inj h.1, limbs_inj h.2]
theorem encSort_inj : ∀ x y, encSort x = encSort y → x = y := by
  intro ⟨u⟩ ⟨v⟩ h; simp only [encSort, List.cons.injEq, and_true] at h; rw [idxW_inj h]
theorem encConst_inj : ∀ x y, encConst x = encConst y → x = y := by
  intro ⟨a, b⟩ ⟨c, d⟩ h; simp only [encConst, List.cons.injEq, and_true] at h; rw [idxW_inj h.1, idxW_inj h.2]
theorem encApp_inj : ∀ x y, encApp x = encApp y → x = y := by
  intro ⟨a, b⟩ ⟨c, d⟩ h; simp only [encApp, List.cons.injEq, and_true] at h; rw [idxW_inj h.1, idxW_inj h.2]
theorem encBind_inj : ∀ x y, encBind x = encBind y → x = y := by
  intro ⟨a, b⟩ ⟨c, d⟩ h; simp only [encBind, List.cons.injEq, and_true] at h; rw [idxW_inj h.1, idxW_inj h.2]
theorem encLet_inj : ∀ x y, encLet x = encLet y → x = y := by
  intro ⟨a, b, c⟩ ⟨d, e, f⟩ h; simp only [encLet, List.cons.injEq, and_true] at h
  rw [idxW_inj h.1, idxW_inj h.2.1, idxW_inj h.2.2]
theorem encLit_inj : ∀ x y, encLit x = encLit y → x = y := by
  intro ⟨l⟩ ⟨m⟩ h
  cases l <;> cases m <;> simp only [encLit, List.cons.injEq] at h
  · rw [limbs_inj h.2]
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · rw [strW_inj h.2]
theorem encProj_inj : ∀ x y, encProj x = encProj y → x = y := by
  intro ⟨a, i, b⟩ ⟨c, j, d⟩ h; simp only [encProj, List.cons.injEq] at h
  rw [idxW_inj h.1, idxW_inj h.2.1, limbs_inj h.2.2]

end ConPanqueque.V.Enc
