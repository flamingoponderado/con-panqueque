import ConPanqueque.Scan.ValueAt

/-! # Strings, soundly restricted

The Pancake scanner accepts a JSON string whose body is printable ASCII with no backslash
(`isPlainN`), and rejects every other string.  Soundness only: when it returns, con-leche's
`scanString` accepts the same string, with the body's bytes as its value (`scanString_plain`); a
string con-leche accepts but the Pancake scanner rejects (escapes, non-ASCII) costs completeness,
not soundness. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

/-- A plain string byte: printable ASCII, not `"` or `\`. -/
def isPlainN (c : Nat) : Bool := decide (32 ≤ c) && decide (c ≤ 126) && !(c == 34) && !(c == 92)

def asciiChars (l : List UInt8) : List Char := l.map Char.ofUInt8

theorem flatMap_ascii (l : List UInt8) (h : ∀ x ∈ l, x.toNat < 128) :
    (asciiChars l).flatMap String.utf8EncodeChar = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    simp only [asciiChars, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hs : (Char.ofUInt8 x).utf8Size = 1 := by
      simp only [Char.utf8Size, Char.ofUInt8]
      have : x.toUInt32 ≤ 127 := by rw [UInt32.le_iff_toNat_le]; simp; omega
      simp [this]
    rw [String.utf8EncodeChar_eq_singleton hs]
    simp [Char.ofUInt8]

/-- An ASCII byte array is valid UTF-8. -/
theorem ascii_valid (b : ByteArray) (h : ∀ x ∈ b.data.toList, x.toNat < 128) : ByteArray.IsValidUTF8 b := by
  refine ⟨asciiChars b.data.toList, ?_⟩
  simp only [List.utf8Encode, flatMap_ascii _ h]
  apply ByteArray.ext; simp [List.data_toByteArray]

theorem strClose_plain {b : ByteArray} (hp : Plat b) (e : USize) (he : e.toNat < b.size)
    (hq : b.data.toList[e.toNat]'(by simpa using he) = 34) :
    ∀ n (j : USize), e.toNat - j.toNat = n → j.toNat ≤ e.toNat →
      (∀ k (hk : k < b.data.toList.length), j.toNat ≤ k → k < e.toNat → isPlainN b.data.toList[k].toNat = true) →
      ConLeche.Frontend.strClose b j = e := by
  intro n
  induction n with
  | zero =>
    intro j hn hj _
    have hje : j = e := USize.toNat_inj.mp (by omega)
    subst hje
    rw [ConLeche.Frontend.strClose, dif_pos ((hp.lt_iff j).mpr he)]
    simp only
    rw [uget_eq b j he ((hp.lt_iff j).mpr he), hq]; rfl
  | succ n ih =>
    intro j hn hj hpl
    have hjl : j.toNat < b.size := by omega
    have hjl' : j.toNat < b.data.toList.length := by simpa using hjl
    have hc := hpl j.toNat hjl' (Nat.le_refl _) (by omega)
    rw [ConLeche.Frontend.strClose, dif_pos ((hp.lt_iff j).mpr hjl)]
    simp only
    rw [uget_eq b j hjl ((hp.lt_iff j).mpr hjl)]
    generalize hx : b.data.toList[j.toNat] = x at hc
    simp only [isPlainN, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hc
    have n34 : (x == 34) = false := by
      rw [show (34 : UInt8) = UInt8.ofNat 34 from rfl, beq_ofNat x 34 (by decide)]; simp; omega
    have n92 : (x == 92) = false := by
      rw [show (92 : UInt8) = UInt8.ofNat 92 from rfl, beq_ofNat x 92 (by decide)]; simp; omega
    have n32 : ¬ x < 32 := by rw [UInt8.lt_iff_toNat_lt]; simp; omega
    simp only [n34, n92, Bool.false_eq_true, ↓reduceIte, n32]
    have hs := ConLeche.Frontend.usizeStep b j ((hp.lt_iff j).mpr hjl)
    exact ih (j + 1) (by rw [hs]; omega) (by rw [hs]; omega)
      (fun k hk h1 h2 => hpl k hk (by rw [hs] at h1; omega) h2)

theorem hasEscape_plain {b : ByteArray} (hp : Plat b) (e : USize) (he : e.toNat ≤ b.size) :
    ∀ n (j : USize), b.size - j.toNat = n →
      (∀ k (hk : k < b.data.toList.length), j.toNat ≤ k → k < e.toNat → isPlainN b.data.toList[k].toNat = true) →
      ConLeche.Frontend.hasEscape b j e = false := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j hn hpl
    rw [ConLeche.Frontend.hasEscape]
    split
    · rename_i h
      have hjl : j.toNat < b.size := (hp.lt_iff j).mp h
      split
      · rename_i hje
        have hje' : j.toNat < e.toNat := USize.lt_iff_toNat_lt.mp hje
        have hjl' : j.toNat < b.data.toList.length := by simpa using hjl
        have hc := hpl j.toNat hjl' (Nat.le_refl _) hje'
        rw [uget_eq b j hjl h]
        generalize hx : b.data.toList[j.toNat] = x at hc
        simp only [isPlainN, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hc
        have n92 : (x == 92) = false := by
          rw [show (92 : UInt8) = UInt8.ofNat 92 from rfl, beq_ofNat x 92 (by decide)]; simp; omega
        simp only [n92, Bool.false_eq_true, ↓reduceIte]
        have hs := ConLeche.Frontend.usizeStep b j h
        exact ih (b.size - (j + 1).toNat) (by omega) (j + 1) rfl
          (fun k hk h1 h2 => hpl k hk (by rw [hs] at h1; omega) h2)
      · rfl
    · rfl

theorem mem_extract_of {b : ByteArray} {a e : Nat} {x : UInt8} (h : x ∈ (b.extract a e).data.toList) :
    ∃ k, ∃ hk : k < b.data.toList.length, a ≤ k ∧ k < e ∧ x = b.data.toList[k] := by
  rw [ByteArray.data_extract, Array.toList_extract, List.mem_iff_getElem] at h
  obtain ⟨k, hk, hx⟩ := h
  simp at hk hx
  refine ⟨a + k, by simp; omega, by omega, by omega, ?_⟩
  rw [← hx]; simp

/-- **con-leche's `scanString` on a plain body**: the opening quote at `i`, plain bytes, the closing
quote at `e`. -/
theorem scanString_plain {b : ByteArray} (hp : Plat b) (i e : USize) (hi : i.toNat < b.size)
    (he : e.toNat < b.size) (hie : i.toNat + 1 ≤ e.toNat)
    (hq0 : b.data.toList[i.toNat]'(by simpa using hi) = 34)
    (hqe : b.data.toList[e.toNat]'(by simpa using he) = 34)
    (hpl : ∀ k (hk : k < b.data.toList.length), i.toNat + 1 ≤ k → k < e.toNat →
      isPlainN b.data.toList[k].toNat = true) :
    ∃ s, ConLeche.Frontend.scanString b i = .ok s (e + 1) ∧
      s.toUTF8 = b.extract (i + 1).toNat e.toNat := by
  have hi1 : (i + 1).toNat = i.toNat + 1 := ConLeche.Frontend.usizeStep b i ((hp.lt_iff i).mpr hi)
  have hclose := strClose_plain hp e he hqe _ (i + 1) rfl (by omega) (by rw [hi1]; exact hpl)
  have hesc := hasEscape_plain hp e (by omega) _ (i + 1) rfl (by rw [hi1]; exact hpl)
  have hval : ByteArray.IsValidUTF8 (b.extract (i + 1).toNat e.toNat) := by
    apply ascii_valid
    intro x hx
    obtain ⟨k, hk, h1, h2, rfl⟩ := mem_extract_of hx
    have := hpl k hk (by omega) h2
    simp only [isPlainN, Bool.and_eq_true, decide_eq_true_eq] at this; omega
  refine ⟨String.fromUTF8 _ hval, ?_, rfl⟩
  rw [ConLeche.Frontend.scanString, byteAt_eq hp, List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some, hq0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hclose, hesc]
  have hne : (e == 0) = false := by
    apply beq_eq_false_iff_ne.mpr; intro h; rw [h] at hie; simp at hie
  simp only [hne, Bool.false_eq_true, ↓reduceIte, String.fromUTF8?, dif_pos hval]

/-- `c` is a plain string byte, as a 0/1 word. -/
def plainTest : ExpHOL 64 :=
  .op .and [.cmp .notLower (vv sC) (.const 32),
    .op .and [.cmp .lower (vv sC) (.const 127),
      .op .and [.cmp .notEqual (vv sC) (.const 34), .cmp .notEqual (vv sC) (.const 92)]]]

theorem plainTest_ok : TestOK isPlainN plainTest := by
  intro σ u c hc h
  have f34 : (BitVec.ofNat 64 c = 34#64) ↔ c = 34 := ofNat_inj c 34 (by omega) (by decide)
  have f92 : (BitVec.ofNat 64 c = 92#64) ↔ c = 92 := ofNat_inj c 92 (by omega) (by decide)
  have l32 : (BitVec.ofNat 64 c < 32#64) ↔ c < 32 := ofNat_lt_iff c 32 (by omega) (by decide)
  have l127 : (BitVec.ofNat 64 c < 127#64) ↔ c < 127 := ofNat_lt_iff c 127 (by omega) (by decide)
  simp only [plainTest, evalHOLExact, evalListHOLExact, vv, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h34 : c = 34 <;> by_cases h92 : c = 92 <;> by_cases h32 : c < 32 <;> by_cases h127 : c < 127 <;>
    simp [h34, h92, h32, h127, f34, f92, l32, l127, isPlainN, bw, wordOpHOL, wordOp, valueIsWord,
      valueWord] <;> first | decide | omega | (rw [if_pos (by omega)]; decide) | (rw [if_neg (by omega)]; decide)

def fSkipPlain := ofString "skipPlain"

def SkipPlainCode {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code.lookup fSkipPlain = some ([(sB, .one), (sN, .one), (sI, .one)], skFun plainTest, .one)

/-- `scanStringPlain(b, n, i)`: the closing quote of the plain string at `i`; any other string is
rejected (`hang`). -/
def ssFun : ProgHOL 64 :=
  .dec sY .one (.const 0) (.dec sE2 .one (.const 0)
    (.seq (bAt sY (vv sI))
      (.ite (.cmp .equal (vv sY) (.const 34))
        (.seq (.call (some (some (.local, sE2), none)) fSkipPlain [vv sB, vv sN, .op .add [vv sI, .const 1]])
          (.seq (bAt sY (vv sE2))
            (.ite (.cmp .equal (vv sY) (.const 34)) (.return (vv sE2)) hang)))
        hang)))

section
variable {σ : Type}

/-- The soundness form of a scanner spec: stop, or return a `w` with `P w` and the frame kept. -/
def RetP (t : PanSemStateFiniteExact 64 σ) (c : ProgHOL 64) (P : BitVec 64 → Prop) : Prop :=
  Stop (evaluateHOLFiniteState t c).1 ∨
    ∃ w, (evaluateHOLFiniteState t c).1 = some (.returned (.val (.word w))) ∧ P w ∧
      (evaluateHOLFiniteState t c).2.memory = t.memory ∧
      (evaluateHOLFiniteState t c).2.memaddrs = t.memaddrs ∧
      (evaluateHOLFiniteState t c).2.globals = t.globals ∧
      (evaluateHOLFiniteState t c).2.code = t.code ∧
      (evaluateHOLFiniteState t c).2.be = t.be

theorem retP_of_retSpec {t : PanSemStateFiniteExact 64 σ} {c : ProgHOL 64} {v : BitVec 64}
    {P : BitVec 64 → Prop} (h : RetSpec t c v) (hv : P v) : RetP t c P := by
  rcases h with hs | ⟨r1, r2, r3, r4, r5, r6⟩
  · exact Or.inl hs
  · exact Or.inr ⟨v, r1, hv, r2, r3, r4, r5, r6⟩

theorem retP_hang (t : PanSemStateFiniteExact 64 σ) (P : BitVec 64 → Prop) : RetP t hang P :=
  Or.inl (by exact hang_stop t)

theorem retP_seq {u u1 : PanSemStateFiniteExact 64 σ} {p q : ProgHOL 64} {P : BitVec 64 → Prop}
    (h : evaluateHOLFiniteState u p = (none, u1)) (hq : RetP u1 q P)
    (m : u1.memory = u.memory) (d : u1.memaddrs = u.memaddrs) (g : u1.globals = u.globals)
    (c : u1.code = u.code) (b : u1.be = u.be) : RetP u (.seq p q) P := by
  unfold RetP at hq ⊢
  rw [seq_normal _ h]
  rcases hq with hs | ⟨w, r1, hp, r2, r3, r4, r5, r6⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, r1, hp, r2.trans m, r3.trans d, r4.trans g, r5.trans c, r6.trans b⟩

theorem retP_ite {u : PanSemStateFiniteExact 64 σ} {e : ExpHOL 64} {p q : ProgHOL 64} {w : BitVec 64}
    {P : BitVec 64 → Prop}
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e =
      some (.val (.word w)))
    (hp : w ≠ 0 → RetP u p P) (hq : w = 0 → RetP u q P) : RetP u (.ite e p q) P := by
  unfold RetP at hp hq ⊢
  rw [ite_word u _ _ _ _ he]
  by_cases hw : w = 0
  · simp only [hw, ne_eq, not_true_eq_false, ↓reduceIte]; exact hq hw
  · simp only [hw, ne_eq, not_false_eq_true, ↓reduceIte]; exact hp hw

theorem retP_dec {u : PanSemStateFiniteExact 64 σ} {x : MlS} {e : ExpHOL 64} {body : ProgHOL 64}
    {w : BitVec 64} {P : BitVec 64 → Prop}
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e =
      some (.val (.word w)))
    (h : RetP (setVarHOLFinite x (.val (.word w)) u) body P) : RetP u (.dec x .one e body) P := by
  unfold RetP at h ⊢
  rw [dec_word_eq u x e w body he]
  exact h

/-- What a returning `ssFun` knows, on the list. -/
def PlainStr (bs : List UInt8) (i e : Nat) : Prop :=
  i < bs.length ∧ e < bs.length ∧ i + 1 ≤ e ∧ bs[i]? = some 34 ∧ bs[e]? = some 34 ∧
    ∀ k (hk : k < bs.length), i + 1 ≤ k → k < e → isPlainN bs[k].toNat = true

theorem ssFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (hi0 : i0 ≤ bs.length) (hc : SkipPlainCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0)))) :
    RetP t ssFun (fun w => ∃ e, w = BitVec.ofNat 64 e ∧ PlainStr bs i0 e) := by
  have hL : bs.length < 2 ^ 64 := by have := hb.2.2.1; omega
  unfold ssFun
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t2 := setVarHOLFinite sE2 (.val (.word 0)) (setVarHOLFinite sY (.val (.word 0)) t)
  have e1 := bAt_spec t2 A bs sY (vv sI) i0 (bytesAt_congr hb rfl rfl rfl) (by omega) 0 (by lk [t2])
    (by lk [t2]; exact lb) (by lk [t2]; exact ln) (eval_vv t2 sI _ (by lk [t2]; exact li))
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let t3 := setVarHOLFinite sY (.val (.word (BitVec.ofNat 64 (byteL bs i0).toNat))) t2
  have hcmp := ConsLoop.eval_cmp_of t3 .equal (vv sY) (.const 34) (BitVec.ofNat 64 (byteL bs i0).toNat)
    (BitVec.ofNat 64 34) (eval_vv t3 sY _ (by lk [t3])) (by simp [evalHOLExact])
  rw [bw_eq _ _ (by have := UInt8.toNat_lt (byteL bs i0); omega) (by decide)] at hcmp
  refine retP_ite hcmp (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq0 : (byteL bs i0).toNat = 34 := by
    cases hh : decide ((byteL bs i0).toNat = 34) <;> simp_all [bw]
  have hi : i0 < bs.length := by
    by_cases h : i0 < bs.length
    · exact h
    · simp [byteL, List.getElem?_eq_none (by omega : bs.length ≤ i0)] at hq0
  have hle := skipL_le_length isPlainN bs _ (i0 + 1) rfl (by omega)
  have hge := skipL_ge isPlainN bs _ (i0 + 1) rfl
  have hall := skipL_all isPlainN bs _ (i0 + 1) rfl
  have hcall := call3_ret t3 sE2 fSkipPlain sB sN sI (skFun plainTest) (vv sB) (vv sN) (.op .add [vv sI, .const 1])
    A (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 (i0 + 1)) (BitVec.ofNat 64 (skipL isPlainN bs (i0 + 1))) 0
    (by decide) (by decide) (by decide) hc (eval_vv t3 sB _ (by lk [t3, t2]; exact lb))
    (eval_vv t3 sN _ (by lk [t3, t2]; exact ln))
    (by rw [eval_add_c t3 sI _ _ (by lk [t3, t2]; exact li)]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) (by lk [t3, t2])
    (fun callee h1 h2 h3 => skFun_spec isPlainN plainTest plainTest_ok _ A bs (i0 + 1)
      (bytesAt_congr hb rfl rfl rfl) (by omega) h1 h2 h3)
  rcases hcall with hs | ⟨u, hu, m1, d1, g1, c1, b1, le1, lo1⟩
  · left; exact seq_stop t3 _ _ hs
  refine retP_seq hu ?_ m1 d1 g1 c1 b1
  obtain ⟨E, hE⟩ : ∃ E, E = skipL isPlainN bs (i0 + 1) := ⟨_, rfl⟩
  rw [← hE] at le1 hle hge
  have e2 := bAt_spec u A bs sY (vv sE2) E (bytesAt_congr hb m1 d1 b1) (by omega) (BitVec.ofNat 64 (byteL bs i0).toNat)
    (by rw [lo1 sY (by decide)]; lk [t3]) (by rw [lo1 sB (by decide)]; lk [t3, t2]; exact lb)
    (by rw [lo1 sN (by decide)]; lk [t3, t2]; exact ln) (eval_vv u sE2 _ le1)
  refine retP_seq e2 ?_ rfl rfl rfl rfl rfl
  let u2 := setVarHOLFinite sY (.val (.word (BitVec.ofNat 64 (byteL bs E).toNat))) u
  have hcmp2 := ConsLoop.eval_cmp_of u2 .equal (vv sY) (.const 34) (BitVec.ofNat 64 (byteL bs E).toNat)
    (BitVec.ofNat 64 34) (eval_vv u2 sY _ (by lk [u2])) (by simp [evalHOLExact])
  rw [bw_eq _ _ (by have := UInt8.toNat_lt (byteL bs E); omega) (by decide)] at hcmp2
  refine retP_ite hcmp2 (fun hw2 => ?_) (fun _ => retP_hang _ _)
  have hqe : (byteL bs E).toNat = 34 := by
    cases hh : decide ((byteL bs E).toNat = 34) <;> simp_all [bw]
  have hEl : E < bs.length := by
    by_cases h : E < bs.length
    · exact h
    · simp [byteL, List.getElem?_eq_none (by omega : bs.length ≤ E)] at hqe
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := return_vv u2 sE2 _ (by lk [u2]; exact le1)
  refine Or.inr ⟨_, r1, ⟨E, rfl, hi, hEl, hge, ?_, ?_, fun k hk h1 h2 => hall k hk h1 (by omega)⟩, r2, r3, r4, r5, r6⟩
  · have : bs[i0]? = some bs[i0] := List.getElem?_eq_getElem hi
    rw [this]; congr 1; apply UInt8.toNat_inj.mp; simp [byteL, this] at hq0; simpa using hq0
  · have : bs[E]? = some bs[E] := List.getElem?_eq_getElem hEl
    rw [this]; congr 1; apply UInt8.toNat_inj.mp; simp [byteL, this] at hqe; simpa using hqe

/-- **The Pancake string scanner is sound for con-leche's `scanString`**: when it returns `e`, the
string at `i` is accepted by `scanString` with the body `[i+1, e)` as its bytes. -/
theorem ssFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi0 : i.toNat ≤ b.size) (hc : SkipPlainCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t ssFun (fun w => ∃ e : USize, w = BitVec.ofNat 64 e.toNat ∧ e.toNat < b.size ∧ ∃ s,
      ConLeche.Frontend.scanString b i = .ok s (e + 1) ∧ s.toUTF8 = b.extract (i + 1).toNat e.toNat) := by
  rcases ssFun_spec t A b.data.toList i.toNat hb (by simpa using hi0) hc lb (by simpa using ln) li with
    hs | ⟨w, r1, ⟨e, rfl, hi', he, hie, hq0, hqe, hpl⟩, r2⟩
  · exact Or.inl hs
  · have heU : (USize.ofNat e).toNat = e := by
      rw [USize.toNat_ofNat']
      simp only [USize.size_eq_two_pow, hp.bits]; apply Nat.mod_eq_of_lt; have := hp.size; simp at he; omega
    refine Or.inr ⟨_, r1, ⟨USize.ofNat e, by rw [heU], by rw [heU]; simpa using he, ?_⟩, r2⟩
    have he' : (USize.ofNat e).toNat < b.size := by rw [heU]; simpa using he
    have hi : i.toNat < b.size := by simpa using hi'
    obtain ⟨s, h1, h2⟩ := scanString_plain hp i (USize.ofNat e) hi he' (by rw [heU]; omega)
      (by rw [List.getElem?_eq_getElem (by simpa using hi)] at hq0; exact Option.some.inj hq0)
      (by rw [List.getElem?_eq_getElem he] at hqe
          simp only [heU]; exact Option.some.inj hqe)
      (fun k hk h1 h2 => hpl k hk h1 (by rw [heU] at h2; exact h2))
    exact ⟨s, h1, h2⟩

/-- `x = f(a1, a2, a3)` at a callee specified in the soundness form. -/
theorem call3_retP (s : PanSemStateFiniteExact 64 σ) (x f x1 x2 x3 : MlS) (body : ProgHOL 64)
    (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 w0 : BitVec 64) (P : BitVec 64 → Prop)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (ha1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a1 =
      some (.val (.word v1)))
    (ha2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 =
      some (.val (.word v2)))
    (ha3 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 =
      some (.val (.word v3)))
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetP (callEntryStateHOLFinite s callee) body P) :
    Stop (evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3])).1 ∨
      ∃ w u, P w ∧ evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3]) = (none, u) ∧
        SetsLocal s x w u := by
  obtain ⟨callee, hlk, hx1, hx2, hx3⟩ := lookupCode3 s f x1 x2 x3 body v1 v2 v3 h12 h13 h23 hcode
  rcases hbody callee hx1 hx2 hx3 with hs | ⟨w, r1, hp, r2⟩
  · have := call_ret s x f [a1, a2, a3] _ body callee 0 w0
      (by simp [evalListHOLFinite, evalListHOLExact, ha1, ha2, ha3]) hlk (Or.inl hs) hx
    rcases this with h | ⟨u, hu, -⟩
    · exact Or.inl h
    · exfalso
      rw [evaluateHOLFiniteState_call] at hu
      simp only [evalListHOLFinite] at hu
      have hcl : s.clock ≠ 0 := by
        intro h0; simp [evalListHOLExact, ha1, ha2, ha3, hlk, h0] at hu
      generalize he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = r at hs
      obtain ⟨r1', r2'⟩ := r
      simp only at hs
      rcases hs with e | ⟨ev, e⟩ <;> subst e <;> simp [evalListHOLExact, ha1, ha2, ha3, hlk, hcl, he] at hu
  · rcases call_ret s x f [a1, a2, a3] _ body callee w w0
      (by simp [evalListHOLFinite, evalListHOLExact, ha1, ha2, ha3]) hlk (Or.inr ⟨r1, r2⟩) hx with h | ⟨u, hu, hs⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, u, hp, hu, hs⟩

end

end ConPanqueque.Scan
