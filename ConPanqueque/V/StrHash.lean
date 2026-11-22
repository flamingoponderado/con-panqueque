import ConPanqueque.V.Ins
import ConPanqueque.Hash
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.Hash

/-!
# `lean_string_hash` in Pancake

A string is held one UTF-8 byte per word (`Enc.strW`). `strHash` computes
MurmurHash64A with seed 11 over those bytes (`Hash.leanStringHash`): a loop
over full eight-byte blocks, a counting-down loop building the tail's
little-endian word, then the final mix. Constant shifts only.
-/

namespace ConPanqueque.V

def lHa := ofString "ha"
def lHn := ofString "hn"
def lHh := ofString "hh"
def lHk := ofString "hk"

def mW : BitVec 64 := 0xc6a4a7935bd1e995#64

/-- The little-endian word of the bytes at `p + 8i`, `i` in the list (last index most significant). -/
def leExp (p : ExpHOL 64) : List Nat → ExpHOL 64
  | [] => .const 0
  | i :: is => .op .or [.shift .lsl (leExp p is) (.const 8), .load .one (.op .add [p, .const (BitVec.ofNat 64 (8 * i))])]

/-- `murmurBlock h k` as an expression. -/
def blockExp (h k : ExpHOL 64) : ExpHOL 64 :=
  let k1 : ExpHOL 64 := .panop .mul [k, .const mW]
  let k2 : ExpHOL 64 := .op .xor [k1, .shift .lsr k1 (.const 47)]
  .panop .mul [.op .xor [h, .panop .mul [k2, .const mW]], .const mW]

def blockBody : ProgHOL 64 :=
  .seq (.assign .local lHk (leExp (vv lHa) [0, 1, 2, 3, 4, 5, 6, 7]))
  (.seq (.assign .local lHh (blockExp (vv lHh) (vv lHk)))
  (.seq (.assign .local lHa (.op .add [vv lHa, .const 64]))
    (.assign .local lHn (.op .sub [vv lHn, .const 8]))))

def tailBody : ProgHOL 64 :=
  .seq (.assign .local lHn (.op .sub [vv lHn, .const 1]))
    (.assign .local lHk (.op .or [.shift .lsl (vv lHk) (.const 8),
      .load .one (.op .add [vv lHa, .shift .lsl (vv lHn) (.const 3)])]))

/-- Expects `hn` = byte count, `ha` = address, `hh`, `hk` holding words. Leaves the hash in `hh`. -/
def strHash : ProgHOL 64 :=
  .seq (.assign .local lHh (.op .xor [.const 11, .panop .mul [vv lHn, .const mW]]))
  (.seq (.while (.cmp .notLower (vv lHn) (.const 8)) blockBody)
  (.seq (.ite (vv lHn)
      (.seq (.assign .local lHk (.const 0))
       (.seq (.while (vv lHn) tailBody)
         (.assign .local lHh (.panop .mul [.op .xor [vv lHh, vv lHk], .const mW]))))
      .skip)
  (.seq (.assign .local lHh (.panop .mul [.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)], .const mW]))
    (.assign .local lHh (.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)])))))

/-- Bytes as the words they are stored as. -/
def byteW (b : UInt8) : BitVec 64 := BitVec.ofNat 64 b.toNat

theorem leWord_cons (b : UInt8) (bs : List UInt8) :
    (leWord (b :: bs)).toBitVec = (leWord bs).toBitVec <<< 8 ||| byteW b := by
  simp only [leWord, List.foldr_cons, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft]
  congr 1
  apply BitVec.eq_of_toNat_eq; simp [byteW]

theorem murmurBlock_bv (h k : UInt64) :
    (murmurBlock h k).toBitVec =
      (h.toBitVec ^^^ ((k.toBitVec * mW) ^^^ ((k.toBitVec * mW) >>> 47)) * mW) * mW := by
  simp [murmurBlock, mW]

section
variable {σ : Type} (s : PanSemStateFiniteExact 64 σ)

local notation "EV" e => @evalHOLExact 64 σ _ (PanSemStateFiniteExact.toExact s)
  (fun a => Classical.propDecidable (PanSemStateFiniteExact.memaddrs s a)) e

theorem eval_or2 (e1 e2 : ExpHOL 64) (v1 v2 : BitVec 64) (h1 : (EV e1) = some (.val (.word v1)))
    (h2 : (EV e2) = some (.val (.word v2))) : (EV (.op .or [e1, e2])) = some (.val (.word (v1 ||| v2))) := by
  rw [evalHOLExact]; simp [evalListHOLExact, h1, h2, wordOpHOL, wordOp, valueIsWord, valueWord]
  show v1 ||| (v2 ||| 0#64) = _; rw [BitVec.or_zero]

theorem eval_xor2 (e1 e2 : ExpHOL 64) (v1 v2 : BitVec 64) (h1 : (EV e1) = some (.val (.word v1)))
    (h2 : (EV e2) = some (.val (.word v2))) : (EV (.op .xor [e1, e2])) = some (.val (.word (v1 ^^^ v2))) := by
  rw [evalHOLExact]; simp [evalListHOLExact, h1, h2, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem eval_mul2 (e1 e2 : ExpHOL 64) (v1 v2 : BitVec 64) (h1 : (EV e1) = some (.val (.word v1)))
    (h2 : (EV e2) = some (.val (.word v2))) : (EV (.panop .mul [e1, e2])) = some (.val (.word (v1 * v2))) := by
  rw [evalHOLExact]; simp [evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord]

theorem eval_blockExp (h k : ExpHOL 64) (hv kv : UInt64) (h1 : (EV h) = some (.val (.word hv.toBitVec)))
    (h2 : (EV k) = some (.val (.word kv.toBitVec))) :
    (EV (blockExp h k)) = some (.val (.word (murmurBlock hv kv).toBitVec)) := by
  have ek1 := eval_mul2 s _ _ _ _ h2 (eval_const s mW)
  rw [blockExp, murmurBlock_bv]
  exact eval_mul2 s _ _ _ _ (eval_xor2 s _ _ _ _ h1 (eval_mul2 s _ _ _ _
    (eval_xor2 s _ _ _ _ ek1 (eval_shr s _ _ _ ek1 (by decide))) (eval_const s mW))) (eval_const s mW)

/-- The bytes `f i` at `P + 8i`. -/
theorem eval_leExp (p : ExpHOL 64) (P : BitVec 64) (hp : (EV p) = some (.val (.word P))) (f : Nat → UInt8) :
    ∀ is : List Nat, (∀ i, i ∈ is → s.memaddrs (P + BitVec.ofNat 64 (8 * i)) ∧
      s.memory (P + BitVec.ofNat 64 (8 * i)) = .word (byteW (f i))) →
      (EV (leExp p is)) = some (.val (.word (leWord (is.map f)).toBitVec))
  | [], _ => by simp [leExp, evalHOLExact, leWord]
  | i :: is, h => by
    rw [leExp, List.map_cons, leWord_cons]
    have hi := h i (by simp)
    exact eval_or2 s _ _ _ _ (eval_shl s _ _ _ (eval_leExp p P hp f is (fun j hj => h j (by simp [hj]))) (by decide))
      (by rw [eval_load_word s _ _ (eval_add2 s _ _ _ _ hp (eval_const s _)) hi.1, hi.2])

end

theorem murmurBlocks_step (H : UInt64) (l : List UInt8) (hl : 8 ≤ l.length) :
    murmurBlocks H l = murmurBlocks (murmurBlock H (leWord (l.take 8))) (l.drop 8) := by
  match l, hl with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ => rfl

theorem murmurBlocks_short (H : UInt64) (l : List UInt8) (hl : l.length < 8) : murmurBlocks H l = (H, l) := by
  match l, hl with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _, _], _ => rfl

theorem take8_map (bs : List UInt8) (o : Nat) (h : o + 8 ≤ bs.length) :
    (bs.drop o).take 8 = [0, 1, 2, 3, 4, 5, 6, 7].map (fun i => bs.getD (o + i) 0) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_cons, List.length_nil] at h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map]
    match i, h2 with
    | 0, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl
    | 1, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl
    | 2, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl
    | 3, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl
    | 4, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl
    | 5, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl
    | 6, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl
    | 7, _ => simp; rw [List.getElem?_eq_getElem (by omega)]; rfl

section
variable {σ : Type}

/-- The block loop's invariant: `q` blocks done, the model's remaining blocks agree. -/
def BI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (h0 : UInt64)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.topAddr = t.topAddr ∧
  (∀ y, y ≠ lHa → y ≠ lHn → y ≠ lHh → y ≠ lHk → u.locals.lookup y = t.locals.lookup y) ∧
  (∃ w, u.locals.lookup lHk = some (.val (.word w))) ∧
  ∃ q H, 8 * q ≤ bs.length ∧ u.locals.lookup lHa = some (.val (.word (A + BitVec.ofNat 64 (8 * (8 * q))))) ∧
    u.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 (bs.length - 8 * q)))) ∧
    u.locals.lookup lHh = some (.val (.word H.toBitVec)) ∧
    murmurBlocks H (bs.drop (8 * q)) = murmurBlocks h0 bs

theorem block_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (h0 : UInt64)
    (hL : bs.length < 2 ^ 61) (hW : Words t A (bs.map byteW))
    (u : PanSemStateFiniteExact 64 σ) (hu : BI t A bs h0 u) (q : Nat)
    (hq : u.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 (bs.length - 8 * q)))))
    (hqa : u.locals.lookup lHa = some (.val (.word (A + BitVec.ofNat 64 (8 * (8 * q))))))
    (H : UInt64) (hH : u.locals.lookup lHh = some (.val (.word H.toBitVec)))
    (hm : murmurBlocks H (bs.drop (8 * q)) = murmurBlocks h0 bs) (h8 : 8 * q + 8 ≤ bs.length) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) blockBody = (none, u') ∧ BI t A bs h0 u' := by
  obtain ⟨m0, d0, c0, g0, ta0, fr, ⟨wk, hk⟩, _⟩ := hu
  let v := decClockHOLFinite u
  let f : Nat → UInt8 := fun i => bs.getD (8 * q + i) 0
  have hk8 : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (leExp (vv lHa) [0, 1, 2, 3, 4, 5, 6, 7]) = some (.val (.word (leWord (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map f)).toBitVec)) := by
    apply eval_leExp v _ _ (eval_vv v lHa _ hqa) f
    intro i hi
    have hi8 : i < 8 := by simp at hi; omega
    have hix : 8 * q + i < bs.length := by omega
    rw [ofNat_add8]
    have hw := hW (8 * q + i) (by simp; exact hix)
    refine ⟨by show u.memaddrs _; rw [d0]; exact hw.1, by show u.memory _ = _; rw [m0, hw.2]; simp [f, hix]⟩
  unfold blockBody
  rw [seq_normal _ (ConsLoop.assign_local v lHk _ _ wk hk8 hk)]
  let v1 := setVarHOLFinite lHk (.val (.word (leWord (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map f)).toBitVec)) v
  let H' := murmurBlock H (leWord (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map f))
  have hH1 : v1.locals.lookup lHh = some (.val (.word H.toBitVec)) := by lk [v1, v]; exact hH
  rw [seq_normal _ (ConsLoop.assign_local v1 lHh _ H'.toBitVec _
    (eval_blockExp v1 _ _ _ _ (eval_vv v1 lHh _ hH1) (eval_vv v1 lHk _ (lookup_setVar_same _ _ _))) hH1)]
  let v2 := setVarHOLFinite lHh (.val (.word H'.toBitVec)) v1
  have ha2 : v2.locals.lookup lHa = some (.val (.word (A + BitVec.ofNat 64 (8 * (8 * q))))) := by lk [v2, v1, v]; exact hqa
  rw [seq_normal _ (ConsLoop.assign_local v2 lHa _ (A + BitVec.ofNat 64 (8 * (8 * (q + 1)))) _
    (by rw [eval_add2 v2 _ _ _ _ (eval_vv v2 lHa _ ha2) (eval_const v2 64)]
        congr 3; rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) ha2)]
  let v3 := setVarHOLFinite lHa (.val (.word (A + BitVec.ofNat 64 (8 * (8 * (q + 1)))))) v2
  have hn3 : v3.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 (bs.length - 8 * q)))) := by
    lk [v3, v2, v1, v]; exact hq
  rw [ConsLoop.assign_local v3 lHn _ (BitVec.ofNat 64 (bs.length - 8 * (q + 1))) _
    (by rw [eval_sub2 v3 _ _ _ _ (eval_vv v3 lHn _ hn3) (eval_const v3 8)]
        congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) hn3]
  refine ⟨_, rfl, m0, d0, c0, g0, ta0, fun y a1 a2 a3 a4 => by lk [v3, v2, v1, v]; exact fr y a1 a2 a3 a4,
    ⟨(leWord (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map f)).toBitVec, by lk [v3, v2, v1]⟩, q + 1, H', by omega, by lk [v3], by lk, by lk [v3, v2], ?_⟩
  rw [← hm, murmurBlocks_step H _ (by simp; omega), take8_map bs _ (by omega), List.drop_drop]
  rw [show 8 * (q + 1) = 8 * q + 8 by omega]

theorem blockLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (h0 : UInt64)
    (hL : bs.length < 2 ^ 61) (hW : Words t A (bs.map byteW)) (u0 : PanSemStateFiniteExact 64 σ)
    (hI : BI t A bs h0 u0) :
    let r := evaluateHOLFiniteState u0 (.while (.cmp .notLower (vv lHn) (.const 8)) blockBody)
    Stop r.1 ∨ (r.1 = none ∧ BI t A bs h0 r.2 ∧ ∃ q H, bs.length - 8 * q < 8 ∧ 8 * q ≤ bs.length ∧
      r.2.locals.lookup lHa = some (.val (.word (A + BitVec.ofNat 64 (8 * (8 * q))))) ∧
      r.2.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 (bs.length - 8 * q)))) ∧
      r.2.locals.lookup lHh = some (.val (.word H.toBitVec)) ∧
      murmurBlocks H (bs.drop (8 * q)) = murmurBlocks h0 bs) := by
  have := while_stop (.cmp .notLower (vv lHn) (.const 8)) blockBody (BI t A bs h0)
    (fun u => BI t A bs h0 u ∧ ∃ q H, bs.length - 8 * q < 8 ∧ 8 * q ≤ bs.length ∧
      u.locals.lookup lHa = some (.val (.word (A + BitVec.ofNat 64 (8 * (8 * q))))) ∧
      u.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 (bs.length - 8 * q)))) ∧
      u.locals.lookup lHh = some (.val (.word H.toBitVec)) ∧
      murmurBlocks H (bs.drop (8 * q)) = murmurBlocks h0 bs)
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, q, H, hq8, hqa, hqn, hH, hm⟩ := id hu
      have hc : @evalHOLFinite 64 σ _ u (fun a => Classical.propDecidable (u.memaddrs a))
          (.cmp .notLower (vv lHn) (.const 8)) = some (.val (.word (bw (8 ≤ bs.length - 8 * q)))) := by
        simp only [evalHOLFinite]
        rw [ConsLoop.eval_cmp_of u .notLower _ _ _ 8 (eval_vv u lHn _ hqn) (eval_const u 8)]
        by_cases h : 8 ≤ bs.length - 8 * q
        · have : ¬ BitVec.ofNat 64 (bs.length - 8 * q) < 8 := by
            rw [BitVec.lt_def]; simp; rw [Nat.mod_eq_of_lt (by omega)]; omega
          simp only [bw, h, ↓reduceIte, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, decide_false,
            Bool.not_false]
        · have : BitVec.ofNat 64 (bs.length - 8 * q) < 8 := by
            rw [BitVec.lt_def]; simp; rw [Nat.mod_eq_of_lt (by omega)]; omega
          simp only [bw, h, ↓reduceIte, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, decide_true,
            Bool.not_true, Bool.false_eq_true]
      by_cases h : 8 ≤ bs.length - 8 * q
      · refine ⟨1, by rw [hc]; simp [bw, h], fun e => absurd e (by decide), fun _ _ => ?_⟩
        obtain ⟨u', e, hu'⟩ := block_step t A bs h0 hL hW u hu q hqn hqa H hH hm (by omega)
        rw [e]; exact Or.inr ⟨rfl, hu'⟩
      · exact ⟨0, by rw [hc]; simp [bw, h], fun _ => ⟨hu, q, H, by omega, hq8, hqa, hqn, hH, hm⟩,
          fun e => absurd rfl e⟩)
    u0 hI
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

end

section
variable {σ : Type}

/-- The tail loop's invariant: `j` tail bytes still to fold, the rest already in `hk`. -/
def TI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (q : Nat) (H : UInt64)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.topAddr = t.topAddr ∧
  (∀ y, y ≠ lHa → y ≠ lHn → y ≠ lHh → y ≠ lHk → u.locals.lookup y = t.locals.lookup y) ∧
  u.locals.lookup lHa = some (.val (.word (A + BitVec.ofNat 64 (8 * (8 * q))))) ∧
  u.locals.lookup lHh = some (.val (.word H.toBitVec)) ∧
  ∃ j, j ≤ (bs.drop (8 * q)).length ∧ u.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 j))) ∧
    u.locals.lookup lHk = some (.val (.word (leWord ((bs.drop (8 * q)).drop j)).toBitVec))

theorem tailLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (q : Nat) (H : UInt64)
    (hL : bs.length < 2 ^ 61) (hW : Words t A (bs.map byteW)) (u0 : PanSemStateFiniteExact 64 σ)
    (hI : TI t A bs q H u0) :
    let r := evaluateHOLFiniteState u0 (.while (vv lHn) tailBody)
    Stop r.1 ∨ (r.1 = none ∧ TI t A bs q H r.2 ∧
      r.2.locals.lookup lHk = some (.val (.word (leWord (bs.drop (8 * q))).toBitVec))) := by
  have := while_stop (vv lHn) tailBody (TI t A bs q H)
    (fun u => TI t A bs q H u ∧ u.locals.lookup lHk = some (.val (.word (leWord (bs.drop (8 * q))).toBitVec)))
    (fun u hu => by
      obtain ⟨m0, d0, c0, g0, ta0, fr, la, lh, j, hj, ln, lkk⟩ := id hu
      have hjw : j < 2 ^ 64 := by simp at hj; omega
      by_cases h0 : j = 0
      · subst h0
        exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, ln], fun _ => ⟨hu, by simpa using lkk⟩,
          fun e => absurd rfl e⟩
      have hne : BitVec.ofNat 64 j ≠ 0 := fun e => h0 (by have := congrArg BitVec.toNat e; simp at this; omega)
      refine ⟨BitVec.ofNat 64 j, by simp [evalHOLFinite, vv, evalHOLExact, ln], fun e => absurd e hne, fun _ _ => ?_⟩
      let v := decClockHOLFinite u
      unfold tailBody
      rw [seq_normal _ (ConsLoop.assign_local v lHn _ (BitVec.ofNat 64 (j - 1)) _
        (by rw [eval_sub2 v _ _ _ _ (eval_vv v lHn _ ln) (eval_const v 1)]
            congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ln)]
      let v1 := setVarHOLFinite lHn (.val (.word (BitVec.ofNat 64 (j - 1)))) v
      have hix : 8 * q + (j - 1) < bs.length := by simp at hj; omega
      have hw := hW (8 * q + (j - 1)) (by simp; exact hix)
      have hld : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
          (.load .one (.op .add [vv lHa, .shift .lsl (vv lHn) (.const 3)])) =
          some (.val (.word (byteW bs[8 * q + (j - 1)]))) := by
        rw [eval_load_word v1 _ (A + BitVec.ofNat 64 (8 * (8 * q + (j - 1))))
          (by rw [eval_add2 v1 _ _ _ _ (eval_vv v1 lHa _ (by lk [v1, v]; exact la))
                (eval_shl v1 _ _ _ (eval_vv v1 lHn _ (lookup_setVar_same _ _ _)) (by decide)),
              show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega), ofNat_add8])
          (by show u.memaddrs _; rw [d0]; exact hw.1)]
        show some (ValueHOL.val (u.memory _)) = _; rw [m0, hw.2]; simp
      have lk1 : v1.locals.lookup lHk = some (.val (.word (leWord ((bs.drop (8 * q)).drop j)).toBitVec)) := by
        lk [v1, v]; exact lkk
      have hdrop : (bs.drop (8 * q)).drop (j - 1) = bs[8 * q + (j - 1)] :: (bs.drop (8 * q)).drop j := by
        rw [List.drop_drop, List.drop_drop, show 8 * q + j = 8 * q + (j - 1) + 1 by omega]
        exact List.drop_eq_getElem_cons hix
      rw [ConsLoop.assign_local v1 lHk _ (leWord ((bs.drop (8 * q)).drop (j - 1))).toBitVec _
        (by rw [eval_or2 v1 _ _ _ _ (eval_shl v1 _ _ _ (eval_vv v1 lHk _ lk1) (by decide)) hld, hdrop, leWord_cons]
            rfl) lk1]
      exact Or.inr ⟨rfl, m0, d0, c0, g0, ta0, fun y a1 a2 a3 a4 => by lk [v1, v]; exact fr y a1 a2 a3 a4,
        by lk [v1, v]; exact la, by lk [v1, v]; exact lh, j - 1, by omega, by lk [v1], by lk⟩)
    u0 hI
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

end

section
variable {σ : Type}

/-- The hash's finish, from the blocks' hash and the tail's word. -/
theorem finish_eq (bs : List UInt8) (H : UInt64) (rest : List UInt8)
    (hm : murmurBlocks (11 ^^^ (UInt64.ofNat bs.length * 0xc6a4a7935bd1e995)) bs = (H, rest)) :
    leanStringHash bs =
      let h2 := if rest = [] then H else (H ^^^ leWord rest) * 0xc6a4a7935bd1e995
      let h3 := (h2 ^^^ (h2 >>> 47)) * 0xc6a4a7935bd1e995
      h3 ^^^ (h3 >>> 47) := by
  simp only [leanStringHash, hm]

/-- After `strHash`: memory and fixed parts as before, other locals unchanged, the hash in `hh`. -/
def SHPost (t : PanSemStateFiniteExact 64 σ) (bs : List UInt8) (y : PanSemStateFiniteExact 64 σ) : Prop :=
  y.memory = t.memory ∧ y.memaddrs = t.memaddrs ∧ y.code = t.code ∧ y.globals = t.globals ∧
  y.topAddr = t.topAddr ∧
  (∀ z, z ≠ lHa → z ≠ lHn → z ≠ lHh → z ≠ lHk → y.locals.lookup z = t.locals.lookup z) ∧
  y.locals.lookup lHh = some (.val (.word (leanStringHash bs).toBitVec))

theorem strHash_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8)
    (hL : bs.length < 2 ^ 61) (hW : Words t A (bs.map byteW))
    (la : t.locals.lookup lHa = some (.val (.word A)))
    (ln : t.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (lh : ∃ w, t.locals.lookup lHh = some (.val (.word w))) (lkk : ∃ w, t.locals.lookup lHk = some (.val (.word w))) :
    let r := evaluateHOLFiniteState t strHash
    Stop r.1 ∨ (r.1 = none ∧ SHPost t bs r.2) := by
  show Stop (evaluateHOLFiniteState t strHash).1 ∨ ((evaluateHOLFiniteState t strHash).1 = none ∧
    SHPost t bs (evaluateHOLFiniteState t strHash).2)
  obtain ⟨wh, hwh⟩ := lh
  let h0 : UInt64 := 11 ^^^ (UInt64.ofNat bs.length * 0xc6a4a7935bd1e995)
  have e0 := ConsLoop.assign_local t lHh _ h0.toBitVec wh
    (by rw [eval_xor2 t _ _ _ _ (eval_const t 11) (eval_mul2 t _ _ _ _ (eval_vv t lHn _ ln) (eval_const t mW))]
        congr 3 <;> (try simp [h0, mW]) <;> (try (apply BitVec.eq_of_toNat_eq; simp))) hwh
  let t1 := setVarHOLFinite lHh (.val (.word h0.toBitVec)) t
  have hI1 : BI t A bs h0 t1 := ⟨rfl, rfl, rfl, rfl, rfl, fun y a1 a2 a3 a4 => by lk [t1], by
      obtain ⟨wk, hk⟩ := lkk; exact ⟨wk, by lk [t1]; exact hk⟩, 0, h0, by omega, by lk [t1]; simpa using la,
    by lk [t1]; simpa using ln, by lk [t1], by simp⟩
  unfold strHash
  rw [seq_normal _ e0]
  rcases blockLoop_spec t A bs h0 hL hW t1 hI1 with hs | ⟨hn2, hBI, q, H, hq8, hql, hqa, hqn, hqH, hm⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  generalize hb : evaluateHOLFiniteState t1 (.while (.cmp .notLower (vv lHn) (.const 8)) blockBody) = bst
    at hn2 hBI hqa hqn hqH
  obtain ⟨b1, u⟩ := bst
  simp only at hn2 hBI hqa hqn hqH; subst hn2
  rw [seq_normal _ hb]
  obtain ⟨m1, d1, c1, g1, ta1, fr1, ⟨wk, hk⟩, _⟩ := hBI
  have hms : murmurBlocks h0 bs = (H, bs.drop (8 * q)) := by
    rw [← hm, murmurBlocks_short _ _ (by simp; omega)]
  -- the finish from a state `x` with `hh = h2`
  have fin : ∀ (x : PanSemStateFiniteExact 64 σ) (h2 : UInt64), x.memory = t.memory → x.memaddrs = t.memaddrs →
      x.code = t.code → x.globals = t.globals → x.topAddr = t.topAddr →
      (∀ y, y ≠ lHa → y ≠ lHn → y ≠ lHh → y ≠ lHk → x.locals.lookup y = t.locals.lookup y) →
      x.locals.lookup lHh = some (.val (.word h2.toBitVec)) →
      h2 = (if bs.drop (8 * q) = [] then H else (H ^^^ leWord (bs.drop (8 * q))) * 0xc6a4a7935bd1e995) →
      Stop (evaluateHOLFiniteState x
        (.seq (.assign .local lHh (.panop .mul [.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)], .const mW]))
          (.assign .local lHh (.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)])))).1 ∨
      ((evaluateHOLFiniteState x
        (.seq (.assign .local lHh (.panop .mul [.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)], .const mW]))
          (.assign .local lHh (.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)])))).1 = none ∧
        SHPost t bs (evaluateHOLFiniteState x
        (.seq (.assign .local lHh (.panop .mul [.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)], .const mW]))
          (.assign .local lHh (.op .xor [vv lHh, .shift .lsr (vv lHh) (.const 47)])))).2) := by
    intro x h2 xm xd xc xg xt xfr xh he
    let h3 : UInt64 := (h2 ^^^ (h2 >>> 47)) * 0xc6a4a7935bd1e995
    rw [seq_normal _ (ConsLoop.assign_local x lHh _ h3.toBitVec _
      (by rw [eval_mul2 x _ _ _ _ (eval_xor2 x _ _ _ _ (eval_vv x lHh _ xh) (eval_shr x _ _ _ (eval_vv x lHh _ xh)
            (by decide))) (eval_const x mW)]; simp [h3, mW]) xh)]
    let x1 := setVarHOLFinite lHh (.val (.word h3.toBitVec)) x
    rw [ConsLoop.assign_local x1 lHh _ (h3 ^^^ (h3 >>> 47)).toBitVec _
      (by rw [eval_xor2 x1 _ _ _ _ (eval_vv x1 lHh _ (lookup_setVar_same _ _ _))
            (eval_shr x1 _ _ _ (eval_vv x1 lHh _ (lookup_setVar_same _ _ _)) (by decide))]; simp [h3])
      (lookup_setVar_same _ _ _)]
    refine Or.inr ⟨rfl, ?_⟩
    exact ⟨xm, xd, xc, xg, xt, fun y a1 a2 a3 a4 => by lk [x1]; exact xfr y a1 a2 a3 a4, by
      lk; rw [finish_eq bs H _ hms, ← he]⟩
  have TP : bs.length - 8 * q < 2 ^ 64 := by omega
  have hdl : (bs.drop (8 * q)).length = bs.length - 8 * q := by simp
  have eite := ite_word u (vv lHn)
    (.seq (.assign .local lHk (.const 0)) (.seq (.while (vv lHn) tailBody)
      (.assign .local lHh (.panop .mul [.op .xor [vv lHh, vv lHk], .const mW])))) .skip _ (eval_vv u lHn _ hqn)
  by_cases hT0 : bs.length - 8 * q = 0
  · have : BitVec.ofNat 64 (bs.length - 8 * q) = 0 := by rw [hT0]; rfl
    simp only [this, ne_eq, not_true_eq_false, ↓reduceIte] at eite
    rw [seq_normal _ (eite.trans (by rw [evaluateHOLFiniteState_eq_evaluate_def]))]
    have hnil : bs.drop (8 * q) = [] := List.eq_nil_of_length_eq_zero (by rw [hdl]; exact hT0)
    rcases fin u H m1 d1 c1 g1 ta1 fr1 hqH (by simp [hnil]) with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hne : BitVec.ofNat 64 (bs.length - 8 * q) ≠ 0 := fun e => hT0 (by
    have := congrArg BitVec.toNat e; simp at this; omega)
  simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte] at eite
  rw [ConsLoop.assign_local u lHk (.const 0) 0 wk (eval_const u 0) hk |> seq_normal _] at eite
  let u1 := setVarHOLFinite lHk (.val (.word 0)) u
  have hTI : TI t A bs q H u1 := ⟨m1, d1, c1, g1, ta1, fun y a1 a2 a3 a4 => by lk [u1]; exact fr1 y a1 a2 a3 a4,
    by lk [u1]; exact hqa, by lk [u1]; exact hqH, bs.length - 8 * q, by omega, by lk [u1]; exact hqn,
    by lk [u1]; rw [List.drop_eq_nil_of_le (by omega)]; rfl⟩
  rcases tailLoop_spec t A bs q H hL hW u1 hTI with hs | ⟨hn3, hTI3, hk3⟩
  · exact Or.inl (seq_stop _ _ _ (by rw [eite]; exact seq_stop _ _ _ hs))
  generalize hw : evaluateHOLFiniteState u1 (.while (vv lHn) tailBody) = wst at hn3 hTI3 hk3
  obtain ⟨w1, w⟩ := wst
  simp only at hn3 hTI3 hk3; subst hn3
  rw [seq_normal _ hw] at eite
  obtain ⟨m3, d3, c3, g3, ta3, fr3, _, lh3, _⟩ := hTI3
  let h2 : UInt64 := (H ^^^ leWord (bs.drop (8 * q))) * 0xc6a4a7935bd1e995
  rw [ConsLoop.assign_local w lHh _ h2.toBitVec H.toBitVec
    (by rw [eval_mul2 w _ _ _ _ (eval_xor2 w _ _ _ _ (eval_vv w lHh _ lh3) (eval_vv w lHk _ hk3)) (eval_const w mW)]
        simp [h2, mW]) lh3] at eite
  rw [seq_normal _ eite]
  have hnn : bs.drop (8 * q) ≠ [] := fun e => hT0 (by rw [← hdl, e]; rfl)
  rcases fin (setVarHOLFinite lHh (.val (.word h2.toBitVec)) w) h2 m3 d3 c3 g3 ta3 (fun y a1 a2 a3 a4 => by lk; exact fr3 y a1 a2 a3 a4) (lookup_setVar_same _ _ _)
      (by simp [hnn, h2]) with h | ⟨h1, h2'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2'⟩

end

end ConPanqueque.V
