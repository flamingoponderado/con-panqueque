import ConPanqueque.T.Core.Whnf
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfCore`'s store chain

The loop's pending keys live in a heap list built by prepending (the last key first). `storeChain` walks it
post-order — the rest first, then the head — which inserts the keys in the twin's array order.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big

theorem sk_eq (arr : Array EIdx) (i : Nat) (v : EIdx) : whnfCoreStoreKeys arr i v =
    if h : i < arr.size then (whnfCoreSet arr[i] v >>= fun _ => whnfCoreStoreKeys arr (i + 1) v) else pure () := by
  rw [whnfCoreStoreKeys]

theorem storeKeys_push (x v : EIdx) : ∀ (k : Nat) (arr : Array EIdx) (i : Nat), arr.size - i = k → i ≤ arr.size →
    whnfCoreStoreKeys (arr.push x) i v = (whnfCoreStoreKeys arr i v >>= fun _ => whnfCoreSet x v) := by
  intro k
  induction k with
  | zero =>
    intro arr i hk hi
    have hi' : i = arr.size := by omega
    subst hi'
    rw [sk_eq (arr.push x) arr.size, dif_pos (by simp), sk_eq (arr.push x) (arr.size + 1), dif_neg (by simp),
      sk_eq arr arr.size, dif_neg (by simp)]
    simp [Array.getElem_push_eq]
  | succ k ih =>
    intro arr i hk hi
    have hlt : i < arr.size := by omega
    rw [sk_eq (arr.push x) i, dif_pos (by simp; omega), sk_eq arr i, dif_pos hlt]
    rw [ih arr (i + 1) (by omega) (by omega)]
    simp [Array.getElem_push_lt hlt, bind_assoc]



theorem skc_eq (arr : Array EIdx) (i : Nat) (v : EIdx) : whnfCoreStoreCheapKeys arr i v =
    if h : i < arr.size then (whnfCoreCheapSet arr[i] v >>= fun _ => whnfCoreStoreCheapKeys arr (i + 1) v) else pure () := by
  rw [whnfCoreStoreCheapKeys]

theorem storeCheapKeys_push (x v : EIdx) : ∀ (k : Nat) (arr : Array EIdx) (i : Nat), arr.size - i = k → i ≤ arr.size →
    whnfCoreStoreCheapKeys (arr.push x) i v = (whnfCoreStoreCheapKeys arr i v >>= fun _ => whnfCoreCheapSet x v) := by
  intro k
  induction k with
  | zero =>
    intro arr i hk hi
    have hi' : i = arr.size := by omega
    subst hi'
    rw [skc_eq (arr.push x) arr.size, dif_pos (by simp), skc_eq (arr.push x) (arr.size + 1), dif_neg (by simp),
      skc_eq arr arr.size, dif_neg (by simp)]
    simp [Array.getElem_push_eq]
  | succ k ih =>
    intro arr i hk hi
    have hlt : i < arr.size := by omega
    rw [skc_eq (arr.push x) i, dif_pos (by simp; omega), skc_eq arr i, dif_pos hlt]
    rw [ih arr (i + 1) (by omega) (by omega)]
    simp [Array.getElem_push_lt hlt, bind_assoc]



theorem storeKeys_rev (x v : EIdx) (xs : List EIdx) :
    whnfCoreStoreKeys (x :: xs).reverse.toArray 0 v =
      (whnfCoreStoreKeys xs.reverse.toArray 0 v >>= fun _ => whnfCoreSet x v) := by
  have e : (xs.reverse ++ [x]).toArray = xs.reverse.toArray.push x := by simp
  rw [List.reverse_cons, e]
  exact storeKeys_push x v _ _ 0 rfl (Nat.zero_le _)

theorem storeCheapKeys_rev (x v : EIdx) (xs : List EIdx) :
    whnfCoreStoreCheapKeys (x :: xs).reverse.toArray 0 v =
      (whnfCoreStoreCheapKeys xs.reverse.toArray 0 v >>= fun _ => whnfCoreCheapSet x v) := by
  have e : (xs.reverse ++ [x]).toArray = xs.reverse.toArray.push x := by simp
  rw [List.reverse_cons, e]
  exact storeCheapKeys_push x v _ _ 0 rfl (Nat.zero_le _)

def scL := ofString "scl"
def scV := ofString "scv"
def scN := ofString "scn"
def scK := ofString "sck"
def scR := ofString "scr"
def scW := ofString "scw"

@[simp] theorem sc_scL_ne_scV : scL ≠ scV := by decide
@[simp] theorem sc_scL_ne_scN : scL ≠ scN := by decide
@[simp] theorem sc_scL_ne_scK : scL ≠ scK := by decide
@[simp] theorem sc_scL_ne_scR : scL ≠ scR := by decide
@[simp] theorem sc_scL_ne_scW : scL ≠ scW := by decide
@[simp] theorem sc_scL_ne_lEo : scL ≠ lEo := by decide
@[simp] theorem sc_lEo_ne_scL : lEo ≠ scL := by decide
@[simp] theorem sc_scL_ne_lKb : scL ≠ lKb := by decide
@[simp] theorem sc_lKb_ne_scL : lKb ≠ scL := by decide
@[simp] theorem sc_scL_ne_lFle : scL ≠ lFle := by decide
@[simp] theorem sc_lFle_ne_scL : lFle ≠ scL := by decide
@[simp] theorem sc_scL_ne_lDir : scL ≠ lDir := by decide
@[simp] theorem sc_lDir_ne_scL : lDir ≠ scL := by decide
@[simp] theorem sc_scV_ne_scL : scV ≠ scL := by decide
@[simp] theorem sc_scV_ne_scN : scV ≠ scN := by decide
@[simp] theorem sc_scV_ne_scK : scV ≠ scK := by decide
@[simp] theorem sc_scV_ne_scR : scV ≠ scR := by decide
@[simp] theorem sc_scV_ne_scW : scV ≠ scW := by decide
@[simp] theorem sc_scV_ne_lEo : scV ≠ lEo := by decide
@[simp] theorem sc_lEo_ne_scV : lEo ≠ scV := by decide
@[simp] theorem sc_scV_ne_lKb : scV ≠ lKb := by decide
@[simp] theorem sc_lKb_ne_scV : lKb ≠ scV := by decide
@[simp] theorem sc_scV_ne_lFle : scV ≠ lFle := by decide
@[simp] theorem sc_lFle_ne_scV : lFle ≠ scV := by decide
@[simp] theorem sc_scV_ne_lDir : scV ≠ lDir := by decide
@[simp] theorem sc_lDir_ne_scV : lDir ≠ scV := by decide
@[simp] theorem sc_scN_ne_scL : scN ≠ scL := by decide
@[simp] theorem sc_scN_ne_scV : scN ≠ scV := by decide
@[simp] theorem sc_scN_ne_scK : scN ≠ scK := by decide
@[simp] theorem sc_scN_ne_scR : scN ≠ scR := by decide
@[simp] theorem sc_scN_ne_scW : scN ≠ scW := by decide
@[simp] theorem sc_scN_ne_lEo : scN ≠ lEo := by decide
@[simp] theorem sc_lEo_ne_scN : lEo ≠ scN := by decide
@[simp] theorem sc_scN_ne_lKb : scN ≠ lKb := by decide
@[simp] theorem sc_lKb_ne_scN : lKb ≠ scN := by decide
@[simp] theorem sc_scN_ne_lFle : scN ≠ lFle := by decide
@[simp] theorem sc_lFle_ne_scN : lFle ≠ scN := by decide
@[simp] theorem sc_scN_ne_lDir : scN ≠ lDir := by decide
@[simp] theorem sc_lDir_ne_scN : lDir ≠ scN := by decide
@[simp] theorem sc_scK_ne_scL : scK ≠ scL := by decide
@[simp] theorem sc_scK_ne_scV : scK ≠ scV := by decide
@[simp] theorem sc_scK_ne_scN : scK ≠ scN := by decide
@[simp] theorem sc_scK_ne_scR : scK ≠ scR := by decide
@[simp] theorem sc_scK_ne_scW : scK ≠ scW := by decide
@[simp] theorem sc_scK_ne_lEo : scK ≠ lEo := by decide
@[simp] theorem sc_lEo_ne_scK : lEo ≠ scK := by decide
@[simp] theorem sc_scK_ne_lKb : scK ≠ lKb := by decide
@[simp] theorem sc_lKb_ne_scK : lKb ≠ scK := by decide
@[simp] theorem sc_scK_ne_lFle : scK ≠ lFle := by decide
@[simp] theorem sc_lFle_ne_scK : lFle ≠ scK := by decide
@[simp] theorem sc_scK_ne_lDir : scK ≠ lDir := by decide
@[simp] theorem sc_lDir_ne_scK : lDir ≠ scK := by decide
@[simp] theorem sc_scR_ne_scL : scR ≠ scL := by decide
@[simp] theorem sc_scR_ne_scV : scR ≠ scV := by decide
@[simp] theorem sc_scR_ne_scN : scR ≠ scN := by decide
@[simp] theorem sc_scR_ne_scK : scR ≠ scK := by decide
@[simp] theorem sc_scR_ne_scW : scR ≠ scW := by decide
@[simp] theorem sc_scR_ne_lEo : scR ≠ lEo := by decide
@[simp] theorem sc_lEo_ne_scR : lEo ≠ scR := by decide
@[simp] theorem sc_scR_ne_lKb : scR ≠ lKb := by decide
@[simp] theorem sc_lKb_ne_scR : lKb ≠ scR := by decide
@[simp] theorem sc_scR_ne_lFle : scR ≠ lFle := by decide
@[simp] theorem sc_lFle_ne_scR : lFle ≠ scR := by decide
@[simp] theorem sc_scR_ne_lDir : scR ≠ lDir := by decide
@[simp] theorem sc_lDir_ne_scR : lDir ≠ scR := by decide
@[simp] theorem sc_scW_ne_scL : scW ≠ scL := by decide
@[simp] theorem sc_scW_ne_scV : scW ≠ scV := by decide
@[simp] theorem sc_scW_ne_scN : scW ≠ scN := by decide
@[simp] theorem sc_scW_ne_scK : scW ≠ scK := by decide
@[simp] theorem sc_scW_ne_scR : scW ≠ scR := by decide
@[simp] theorem sc_scW_ne_lEo : scW ≠ lEo := by decide
@[simp] theorem sc_lEo_ne_scW : lEo ≠ scW := by decide
@[simp] theorem sc_scW_ne_lKb : scW ≠ lKb := by decide
@[simp] theorem sc_lKb_ne_scW : lKb ≠ scW := by decide
@[simp] theorem sc_scW_ne_lFle : scW ≠ lFle := by decide
@[simp] theorem sc_lFle_ne_scW : lFle ≠ scW := by decide
@[simp] theorem sc_scW_ne_lDir : scW ≠ lDir := by decide
@[simp] theorem sc_lDir_ne_scW : lDir ≠ scW := by decide

/-- A heap list of handles from `p`, head first (`0` is the empty list). -/
def LstAt (C : Ctx) (H : List (BitVec 64)) : BitVec 64 → List EIdx → Prop
  | p, [] => p = 0
  | p, x :: xs => ∃ o nx, p = cellA C o ∧ H[o]? = some (Enc.idxW x) ∧ H[o + 1]? = some nx ∧ LstAt C H nx xs

theorem lstAt_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') :
    ∀ (p : BitVec 64) (xs : List EIdx), LstAt C H p xs → LstAt C H' p xs
  | _, [], h => h
  | p, x :: xs, ⟨o, nx, h1, h2, h3, h4⟩ => by
    obtain ⟨r, rfl⟩ := hp
    refine ⟨o, nx, h1, ?_, ?_, lstAt_mono ⟨r, rfl⟩ nx xs h4⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h2).1]; exact h2
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h3).1]; exact h3

theorem lstAt_H {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {xs : List EIdx} :
    LstAt (ctxH C H') H p xs ↔ LstAt C H p xs := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    constructor
    · intro ⟨o, nx, h1, h2, h3, h4⟩; exact ⟨o, nx, h1, h2, h3, ih.mp h4⟩
    · intro ⟨o, nx, h1, h2, h3, h4⟩; exact ⟨o, nx, h1, h2, h3, ih.mpr h4⟩

def scLocals : List MlS := [scN, scK, scR, scW, lEo]
def scParams : List MlS := [scL, scV]

def scBody (k : ModeKE) (C : Ctx) (fself : MlS) : ProgHOL 64 :=
  prologue scLocals (.ite (.cmp .equal (vv scL) (.const 0)) (.return (.const 0))
    (.seq (.assign .local scN (.load .one (.op .add [vv scL, .const 8])))
    (.seq (.assign .local scK (.load .one (vv scL)))
    (.seq (.call (some (some (.local, scR), none)) fself [vv scN, vv scV])
    (modeSetP C k.toK scW (vv scK) (vv scV) (.return (.const 0)))))))

/-- The tag test for `4` (`app`): the tag bits are `4`, or the handle is wide (whose tag is `4`). -/
def tagIs4E (x : MlS) : ExpHOL 64 :=
  .op .or [.cmp .equal (.op .and [.shift .lsr (vv x) (.const 26), .const 31]) (.const 4),
    .op .and [.shift .lsr (vv x) (.const 30), .const 1]]

theorem sev_tagIs4 (Γ : Env) (x : MlS) (h : EIdx) (hx : Γ.get x = some (Enc.idxW h)) :
    ∃ w, sev Γ (tagIs4E x) = some w ∧ (w ≠ 0 ↔ h.tag = 4) := by
  refine ⟨_, by simp only [tagIs4E, sev, sev_vv, hx]; rfl, ?_⟩
  have hw : (Enc.idxW h).toNat = h.word.toNat := by simp [Enc.idxW]
  have hlt : h.word.toNat < 2 ^ 32 := h.word.toNat_lt
  have e31 : (31 : BitVec 64).toNat = 2 ^ 5 - 1 := rfl
  have e1 : (1 : BitVec 64).toNat = 2 ^ 1 - 1 := rfl
  simp only [show (26 : BitVec 64).toNat = 26 from rfl, show (30 : BitVec 64).toNat = 30 from rfl,
    show (64 : Nat) > 26 from by decide, show (64 : Nat) > 30 from by decide, ite_true, Option.map_some,
    Option.bind_eq_bind, Option.pure_def, Option.some.injEq]
  rw [Ne, ← BitVec.toNat_inj]
  simp only [Idx.tag, Idx.isWide, beq_iff_eq]
  by_cases hwd : h.word / 1073741824 % 2 = 1
  · rw [if_pos hwd]
    have hwn : h.word.toNat / 1073741824 % 2 = 1 := by
      have := congrArg UInt32.toNat hwd; simp [UInt32.toNat_div, UInt32.toNat_mod] at this; exact this
    simp only [true_iff]
    simp [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow, e1,
      Nat.and_two_pow_sub_one_eq_mod, hwn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · rw [if_neg hwd]
    have hwn : h.word.toNat / 1073741824 % 2 = 0 := by
      have : ¬ h.word.toNat / 1073741824 % 2 = 1 := by
        intro c; apply hwd; apply UInt32.toNat_inj.mp; simp [UInt32.toNat_div, UInt32.toNat_mod]; omega
      omega
    have hbit : h.word.toNat / 67108864 % 32 = h.word.toNat / 67108864 % 16 := by omega
    have hand31 : ∀ y : Nat, y &&& 31 = y % 32 := fun y => Nat.and_two_pow_sub_one_eq_mod y 5
    have key : (Enc.idxW h >>> (26 : Nat)) &&& 31#64 = 4#64 ↔ h.word / 67108864 % 16 = 4 := by
      constructor
      · intro e; have := congrArg BitVec.toNat e
        simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow, hand31] at this
        apply UInt32.toNat_inj.mp; simp [UInt32.toNat_div, UInt32.toNat_mod]; omega
      · intro e; apply BitVec.eq_of_toNat_eq
        have := congrArg UInt32.toNat e
        simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow, hand31]
        simp [UInt32.toNat_div, UInt32.toNat_mod] at this; omega
    by_cases hk : (Enc.idxW h >>> (26 : Nat)) &&& 31#64 = 4#64
    · have := key.mp hk
      simp [hk, this, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.toNat_or, BitVec.toNat_and,
        BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow, e1, Nat.and_two_pow_sub_one_eq_mod, hwn]
    · have := (not_congr key).mp hk
      simp [hk, this, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.toNat_or, BitVec.toNat_and,
        BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow, e1, Nat.and_two_pow_sub_one_eq_mod, hwn]

section
variable {σ : Type}

def PostS (C : Ctx) (u : Unit) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop := SR C s' st

theorem postS_locals (C : Ctx) : ∀ (a : Unit) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostS C a w s' st → PostS C a w s' { st with locals := L } :=
  fun _ _ _ _ _ h => sr_of_eq h rfl rfl rfl rfl

theorem sc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ scLocals → (ctxEnv C ++ scParams.zip vals).get x = none :=
  Knot.params_none C scLocals scParams vals (by decide) (by decide)

theorem sc_spec (k : ModeKE) (storeOp : Array EIdx → Nat → EIdx → AM Unit) (setOp : EIdx → EIdx → AM Unit)
    (hset : ∀ e r s, setOp e r s = .ok ((), modeSetS k s e r))
    (hrev : ∀ x (xs : List EIdx) v, storeOp (x :: xs).reverse.toArray 0 v =
      (storeOp xs.reverse.toArray 0 v >>= fun _ => setOp x v))
    (hnil : ∀ v, storeOp #[] 0 v = pure ())
    (C : Ctx) (hok : CtxOK C) (fself : MlS)
    (hcs : C.code.lookup fself = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody k C fself, .one))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (v : EIdx) : ∀ (xs : List EIdx) (s : AState) (p : BitVec 64), LstAt C C.H p xs →
    SpecR (σ := σ) (Pre C s (scParams.zip [p, Enc.idxW v])) (scBody k C fself) s (storeOp xs.reverse.toArray 0 v)
      (PostS C)
  | [], s, p, hp => by
    simp only [LstAt] at hp; subst hp
    refine specR_prologue (postS_locals C) (sc_none C _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, scParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [show ([] : List EIdx).reverse.toArray = #[] from rfl, hnil]
    exact specR_returnI _ 0 rfl (fun t ht => sr_of_eq ht.sr rfl rfl rfl rfl)
  | x :: xs, s, p, ⟨o, nx, hpo, hx, hnx, hrest⟩ => by
    subst hpo
    refine specR_prologue (postS_locals C) (sc_none C _) ?_
    refine specR_atEntry fun t0 ht0 => ?_
    have ho : o < C.HN := by
      obtain ⟨H', hp', ha'⟩ := ht0.sr.heap
      have := (List.getElem?_eq_some_iff.mp hx).1; have := hp'.length_le; have := ha'.len; omega
    have hne := ExSP.cellA_ne0 C hok o ho
    have hc0 : sev (ctxEnv C ++ scParams.zip [cellA C o, Enc.idxW v]) (.cmp .equal (vv scL) (.const 0)) = some 0 := by
      simp +decide [sev, Env.get, scParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne
    refine specR_ifI _ 0 hc0 (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' scN _ (o + 1) nx hnx (by decide)
      (by simp +decide [sev, Env.get, scParams, ctxEnv]; exact cellA_add8 C o) ?_
    refine UD.specR_heapLoadI' scK (vv scL) o _ hx (by decide) (by simp +decide [Env.get, scParams, ctxEnv]) ?_
    rw [hrev]
    refine specR_callNIH scR fself scParams [vv scN, vv scV] (scBody k C fself) [nx, Enc.idxW v] (by decide) rfl
      (by decide) hcs ⟨by simp, by simp +decide [sev, Env.get, scParams, ctxEnv], trivial⟩
      (fun u w s' st => storeOp xs.reverse.toArray 0 v s = .ok (u, s') ∧ PostS C u w s' st)
      (fun u w s' H' => H' = C.H ∧ storeOp xs.reverse.toArray 0 v s = .ok (u, s'))
      (fun u w s' st ⟨hrun, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hrun⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu scParams _ rfl hlk)
        (sc_spec k storeOp setOp hset hrev hnil C hok fself hcs hcodeS hcodeI v xs s nx hrest)))
      (fun u w s1 H1 _ ⟨hH, _⟩ => ?_)
    subst hH
    refine specR_congr (m' := setOp x v >>= fun _ => pure ()) (by simp) ?_
    refine specR_modeSetI hok k setOp hset hcodeS hcodeI scW (vv scK) (vv scV) x v (by decide) (by decide)
      (by simp) (by simp +decide [sev, Env.get, scParams, ctxEnv]) (by simp +decide [Env.get, ctxEnv])
      (fun w => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => sr_of_eq ht.sr rfl rfl rfl rfl)

end

def cP := ofString "wcp"
def cQ := ofString "wcq"
def cV := ofString "wcv"
def cR := ofString "wcr"
def fSCF := ofString "storeKeys"
def fSCC := ofString "storeCheapKeys"

@[simp] theorem wcc_cP_ne_cQ : cP ≠ cQ := by decide
@[simp] theorem wcc_cP_ne_cV : cP ≠ cV := by decide
@[simp] theorem wcc_cP_ne_cR : cP ≠ cR := by decide
@[simp] theorem wcc_cP_ne_kC : cP ≠ kC := by decide
@[simp] theorem wcc_kC_ne_cP : kC ≠ cP := by decide
@[simp] theorem wcc_cP_ne_kFu : cP ≠ kFu := by decide
@[simp] theorem wcc_kFu_ne_cP : kFu ≠ cP := by decide
@[simp] theorem wcc_cP_ne_kD : cP ≠ kD := by decide
@[simp] theorem wcc_kD_ne_cP : kD ≠ cP := by decide
@[simp] theorem wcc_cP_ne_kE : cP ≠ kE := by decide
@[simp] theorem wcc_kE_ne_cP : kE ≠ cP := by decide
@[simp] theorem wcc_cP_ne_lEo : cP ≠ lEo := by decide
@[simp] theorem wcc_lEo_ne_cP : lEo ≠ cP := by decide
@[simp] theorem wcc_cP_ne_lKb : cP ≠ lKb := by decide
@[simp] theorem wcc_lKb_ne_cP : lKb ≠ cP := by decide
@[simp] theorem wcc_cP_ne_scL : cP ≠ scL := by decide
@[simp] theorem wcc_scL_ne_cP : scL ≠ cP := by decide
@[simp] theorem wcc_cP_ne_scV : cP ≠ scV := by decide
@[simp] theorem wcc_scV_ne_cP : scV ≠ cP := by decide
@[simp] theorem wcc_cP_ne_scN : cP ≠ scN := by decide
@[simp] theorem wcc_scN_ne_cP : scN ≠ cP := by decide
@[simp] theorem wcc_cP_ne_scK : cP ≠ scK := by decide
@[simp] theorem wcc_scK_ne_cP : scK ≠ cP := by decide
@[simp] theorem wcc_cP_ne_scR : cP ≠ scR := by decide
@[simp] theorem wcc_scR_ne_cP : scR ≠ cP := by decide
@[simp] theorem wcc_cP_ne_scW : cP ≠ scW := by decide
@[simp] theorem wcc_scW_ne_cP : scW ≠ cP := by decide
@[simp] theorem wcc_cQ_ne_cP : cQ ≠ cP := by decide
@[simp] theorem wcc_cQ_ne_cV : cQ ≠ cV := by decide
@[simp] theorem wcc_cQ_ne_cR : cQ ≠ cR := by decide
@[simp] theorem wcc_cQ_ne_kC : cQ ≠ kC := by decide
@[simp] theorem wcc_kC_ne_cQ : kC ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_kFu : cQ ≠ kFu := by decide
@[simp] theorem wcc_kFu_ne_cQ : kFu ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_kD : cQ ≠ kD := by decide
@[simp] theorem wcc_kD_ne_cQ : kD ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_kE : cQ ≠ kE := by decide
@[simp] theorem wcc_kE_ne_cQ : kE ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_lEo : cQ ≠ lEo := by decide
@[simp] theorem wcc_lEo_ne_cQ : lEo ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_lKb : cQ ≠ lKb := by decide
@[simp] theorem wcc_lKb_ne_cQ : lKb ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_scL : cQ ≠ scL := by decide
@[simp] theorem wcc_scL_ne_cQ : scL ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_scV : cQ ≠ scV := by decide
@[simp] theorem wcc_scV_ne_cQ : scV ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_scN : cQ ≠ scN := by decide
@[simp] theorem wcc_scN_ne_cQ : scN ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_scK : cQ ≠ scK := by decide
@[simp] theorem wcc_scK_ne_cQ : scK ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_scR : cQ ≠ scR := by decide
@[simp] theorem wcc_scR_ne_cQ : scR ≠ cQ := by decide
@[simp] theorem wcc_cQ_ne_scW : cQ ≠ scW := by decide
@[simp] theorem wcc_scW_ne_cQ : scW ≠ cQ := by decide
@[simp] theorem wcc_cV_ne_cP : cV ≠ cP := by decide
@[simp] theorem wcc_cV_ne_cQ : cV ≠ cQ := by decide
@[simp] theorem wcc_cV_ne_cR : cV ≠ cR := by decide
@[simp] theorem wcc_cV_ne_kC : cV ≠ kC := by decide
@[simp] theorem wcc_kC_ne_cV : kC ≠ cV := by decide
@[simp] theorem wcc_cV_ne_kFu : cV ≠ kFu := by decide
@[simp] theorem wcc_kFu_ne_cV : kFu ≠ cV := by decide
@[simp] theorem wcc_cV_ne_kD : cV ≠ kD := by decide
@[simp] theorem wcc_kD_ne_cV : kD ≠ cV := by decide
@[simp] theorem wcc_cV_ne_kE : cV ≠ kE := by decide
@[simp] theorem wcc_kE_ne_cV : kE ≠ cV := by decide
@[simp] theorem wcc_cV_ne_lEo : cV ≠ lEo := by decide
@[simp] theorem wcc_lEo_ne_cV : lEo ≠ cV := by decide
@[simp] theorem wcc_cV_ne_lKb : cV ≠ lKb := by decide
@[simp] theorem wcc_lKb_ne_cV : lKb ≠ cV := by decide
@[simp] theorem wcc_cV_ne_scL : cV ≠ scL := by decide
@[simp] theorem wcc_scL_ne_cV : scL ≠ cV := by decide
@[simp] theorem wcc_cV_ne_scV : cV ≠ scV := by decide
@[simp] theorem wcc_scV_ne_cV : scV ≠ cV := by decide
@[simp] theorem wcc_cV_ne_scN : cV ≠ scN := by decide
@[simp] theorem wcc_scN_ne_cV : scN ≠ cV := by decide
@[simp] theorem wcc_cV_ne_scK : cV ≠ scK := by decide
@[simp] theorem wcc_scK_ne_cV : scK ≠ cV := by decide
@[simp] theorem wcc_cV_ne_scR : cV ≠ scR := by decide
@[simp] theorem wcc_scR_ne_cV : scR ≠ cV := by decide
@[simp] theorem wcc_cV_ne_scW : cV ≠ scW := by decide
@[simp] theorem wcc_scW_ne_cV : scW ≠ cV := by decide
@[simp] theorem wcc_cR_ne_cP : cR ≠ cP := by decide
@[simp] theorem wcc_cR_ne_cQ : cR ≠ cQ := by decide
@[simp] theorem wcc_cR_ne_cV : cR ≠ cV := by decide
@[simp] theorem wcc_cR_ne_kC : cR ≠ kC := by decide
@[simp] theorem wcc_kC_ne_cR : kC ≠ cR := by decide
@[simp] theorem wcc_cR_ne_kFu : cR ≠ kFu := by decide
@[simp] theorem wcc_kFu_ne_cR : kFu ≠ cR := by decide
@[simp] theorem wcc_cR_ne_kD : cR ≠ kD := by decide
@[simp] theorem wcc_kD_ne_cR : kD ≠ cR := by decide
@[simp] theorem wcc_cR_ne_kE : cR ≠ kE := by decide
@[simp] theorem wcc_kE_ne_cR : kE ≠ cR := by decide
@[simp] theorem wcc_cR_ne_lEo : cR ≠ lEo := by decide
@[simp] theorem wcc_lEo_ne_cR : lEo ≠ cR := by decide
@[simp] theorem wcc_cR_ne_lKb : cR ≠ lKb := by decide
@[simp] theorem wcc_lKb_ne_cR : lKb ≠ cR := by decide
@[simp] theorem wcc_cR_ne_scL : cR ≠ scL := by decide
@[simp] theorem wcc_scL_ne_cR : scL ≠ cR := by decide
@[simp] theorem wcc_cR_ne_scV : cR ≠ scV := by decide
@[simp] theorem wcc_scV_ne_cR : scV ≠ cR := by decide
@[simp] theorem wcc_cR_ne_scN : cR ≠ scN := by decide
@[simp] theorem wcc_scN_ne_cR : scN ≠ cR := by decide
@[simp] theorem wcc_cR_ne_scK : cR ≠ scK := by decide
@[simp] theorem wcc_scK_ne_cR : scK ≠ cR := by decide
@[simp] theorem wcc_cR_ne_scR : cR ≠ scR := by decide
@[simp] theorem wcc_scR_ne_cR : scR ≠ cR := by decide
@[simp] theorem wcc_cR_ne_scW : cR ≠ scW := by decide
@[simp] theorem wcc_scW_ne_cR : scW ≠ cR := by decide

/-- Store the chain (unless cheap or empty), then return `v`. -/
def scRet : ProgHOL 64 :=
  .ite (.cmp .notEqual (vv kC) (.const 0)) (.return (vv cV))
  (.ite (.cmp .equal (vv cP) (.const 0)) (.return (vv cV))
  (.seq (.call (some (some (.local, cR), none)) fSCF [vv cP, vv cV])
  (.seq (.call (some (some (.local, cR), none)) fSCC [vv cQ, vv cV]) (.return (vv cV)))))

section
variable {σ : Type}

theorem storeKeys_nil (v : EIdx) : whnfCoreStoreKeys #[] 0 v = pure () := by rw [sk_eq]; rfl
theorem storeCheapKeys_nil (v : EIdx) : whnfCoreStoreCheapKeys #[] 0 v = pure () := by rw [skc_eq]; rfl

theorem scRet_spec {C0 : Ctx} (hok : CtxOK C0)
    (hcf : C0.code.lookup fSCF = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody .whnfCore C0 fSCF, .one))
    (hcc : C0.code.lookup fSCC = some (scParams.map (fun p => (p, ShapeHOL.one)),
      scBody .whnfCoreCheap C0 fSCC, .one))
    (hcodeS : C0.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C0.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {D : List MlS} (hpre : C0.H <+: H)
    (cheap : Bool) (xs ys : List EIdx) (p q : BitVec 64) (v : EIdx)
    (hp : LstAt C0 H p xs) (hq : LstAt C0 H q ys)
    (hC : Γ.get kC = some (boolW cheap)) (hP : Γ.get cP = some p) (hQ : Γ.get cQ = some q)
    (hV : Γ.get cV = some (Enc.idxW v)) (hD : cR ∈ D) :
    SpecR (σ := σ) (Inv (ctxH C0 H) s Γ [] D) scRet s
      (whnfCoreStoreChain cheap xs.reverse.toArray ys.reverse.toArray v >>= fun _ => pure v) (PostK C0) := by
  unfold scRet
  have hret : ∀ {s' : AState} {Γ' : Env} {H' : List (BitVec 64)}, C0.H <+: H' → Γ'.get cV = some (Enc.idxW v) →
      SpecR (σ := σ) (Inv (ctxH C0 H') s' Γ' [] D) (.return (vv cV)) s' (pure v) (PostK C0) :=
    fun hp' hv' => specR_returnI _ (Enc.idxW v) (by simp [hv']) (fun t ht => ⟨_, hp', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  cases cheap
  · refine specR_ifI _ 0 (by simp [sev, hC, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    rcases xs with _ | ⟨x, xs'⟩
    · simp only [LstAt] at hp; subst hp
      refine specR_ifI _ 1 (by simp [sev, hP, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      show SpecR _ _ s ((if false then pure () else if (#[] : Array EIdx).size = 0 then pure () else _) >>= _) _
      simp only [Bool.false_eq_true, ite_false, List.reverse_nil]
      exact hret hpre hV
    · obtain ⟨o, nx, rfl, hx0, hnx, hrest⟩ := hp
      refine specR_atEntry fun t0 ht0 => ?_
      have ho : o < C0.HN := by
        obtain ⟨H', hp', ha'⟩ := ht0.sr.heap
        have := (List.getElem?_eq_some_iff.mp hx0).1; have := hp'.length_le; have := ha'.len; simp only [ctxH] at *
        omega
      have hne := ExSP.cellA_ne0 C0 hok o ho
      refine specR_ifI _ 0 (by simp [sev, hP, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      have hsz : ((x :: xs').reverse.toArray).size ≠ 0 := by simp
      show SpecR _ _ s ((if false then pure () else if ((x :: xs').reverse.toArray).size = 0 then pure () else _) >>= _) _
      simp only [Bool.false_eq_true, ite_false, if_neg hsz, bind_assoc]
      refine specR_callNIH (C := ctxH C0 H) cR fSCF scParams [vv cP, vv cV] (scBody .whnfCore C0 fSCF)
        [cellA C0 o, Enc.idxW v] (by decide) rfl hD hcf ⟨by simp [hP], by simp [hV], trivial⟩
        (fun u w s' st => whnfCoreStoreKeys (x :: xs').reverse.toArray 0 v s = .ok (u, s') ∧ PostS (ctxH C0 H) u w s' st)
        (fun u w s' H' => H' = H ∧ whnfCoreStoreKeys (x :: xs').reverse.toArray 0 v s = .ok (u, s'))
        (fun u w s' st ⟨hrun, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, hrun⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu scParams _ rfl hlk)
          (sc_spec .whnfCore whnfCoreStoreKeys whnfCoreSet (fun _ _ _ => rfl) (fun x xs v => storeKeys_rev x v xs) storeKeys_nil
            (ctxH C0 H) (ctxOK_H hok _) fSCF hcf hcodeS hcodeI v (x :: xs') s (cellA C0 o)
            (lstAt_H.mpr ⟨o, nx, rfl, hx0, hnx, hrest⟩))))
        (fun u w s1 H1 _ ⟨hH, _⟩ => ?_)
      subst H1
      refine specR_callNIH (C := ctxH (ctxH C0 H) H) cR fSCC scParams [vv cQ, vv cV] (scBody .whnfCoreCheap C0 fSCC)
        [q, Enc.idxW v] (by decide) rfl hD hcc ⟨by simp [hQ], by simp [hV], trivial⟩
        (fun u w s' st => whnfCoreStoreCheapKeys ys.reverse.toArray 0 v s1 = .ok (u, s') ∧
          PostS (ctxH C0 H) u w s' st)
        (fun u w s' H' => H' = H ∧ whnfCoreStoreCheapKeys ys.reverse.toArray 0 v s1 = .ok (u, s'))
        (fun u w s' st ⟨hrun, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, hrun⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu scParams _ rfl hlk)
          (sc_spec .whnfCoreCheap whnfCoreStoreCheapKeys whnfCoreCheapSet (fun _ _ _ => rfl) (fun x xs v => storeCheapKeys_rev x v xs)
            storeCheapKeys_nil (ctxH C0 H) (ctxOK_H hok _) fSCC hcc hcodeS hcodeI v ys s1 q (lstAt_H.mpr hq))))
        (fun u w s2 H2 _ ⟨hH, _⟩ => ?_)
      subst H2
      exact hret hpre (by simp [hV])
  · refine specR_ifI _ 1 (by simp [sev, hC, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    show SpecR _ _ s ((if true then pure () else _) >>= _) _
    simp only [ite_true]
    exact hret hpre hV

end


/-- Push `key` onto the list in `x` when `b` (a `0`/`1` word); the node is allocated either way. -/
def pushP (C : Ctx) (x nd kb kk : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C nd (.const 16) (.seq (.store (vv nd) (vv kk))
    (.seq (.store (.op .add [vv nd, .const 8]) (vv x))
    (.seq (.assign .local x (.op .add [vv x, .panop .mul [vv kb, .op .sub [vv nd, vv x]]])) rest)))

section
variable {σ : Type}

theorem select_word (b : Bool) (p q : BitVec 64) : p + boolW b * (q - p) = if b then q else p := by
  cases b
  · simp [boolW]
  · simp only [boolW, ite_true]; rw [show (1 : BitVec 64) * (q - p) = q - p from BitVec.one_mul _, BitVec.add_comm, BitVec.sub_add_cancel]

theorem specR_pushI {α : Type} {C0 : Ctx} (hok : CtxOK C0) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x nd kb kk : MlS) (b : Bool) (key : EIdx) (p : BitVec 64) (xs : List EIdx)
    (hne : x ≠ nd ∧ kb ≠ nd ∧ kk ≠ nd) (hxD : x ∈ D) (hnD : nd ∈ D)
    (hx : Γ.get x = some p) (hl : LstAt C0 H p xs) (hb : Γ.get kb = some (boolW b))
    (hk : Γ.get kk = some (Enc.idxW key)) (hpre : C0.H <+: H)
    (hk' : ∀ (H' : List (BitVec 64)) p' w, C0.H <+: H' → H <+: H' → LstAt C0 H' p' (if b then key :: xs else xs) →
      SpecR (Inv (ctxH C0 H') s ((x, p') :: (nd, w) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C0 H) s Γ [] D) (pushP C0 x nd kb kk rest) s m R := by
  unfold pushP
  obtain ⟨h1, h2, h3⟩ := hne
  refine specR_allocI (C := ctxH C0 H) nd (.const 16) 2 (by norm_num) hnD (fun v => by simp [sev])
    (fun H1 ws hp1 hwl _ => ?_)
  have hpl := hp1.length_le
  have hj : H1.length < (ctxH (ctxH C0 H) (H1 ++ ws)).H.length := by show _ < (H1 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv nd) (vv kk) _ hj (Enc.idxW key) (by simp; rfl)
    (by simp [h3, h3.symm, hk]) ?_
  have hj2 : H1.length + 1 < (ctxH (ctxH C0 H) ((H1 ++ ws).set H1.length (Enc.idxW key))).H.length := by
    show _ < ((H1 ++ ws).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ (vv x) _ hj2 p (by simp [sev]; exact cellA_add8 C0 _)
    (by simp [h1, h1.symm, hx]) ?_
  let H2 := ((H1 ++ ws).set H1.length (Enc.idxW key)).set (H1.length + 1) p
  have hpa := prefix_set_ge (List.prefix_append H1 ws) H1.length (Nat.le_refl _) (Enc.idxW key)
  have hpb : H1 <+: H2 := prefix_set_ge hpa (H1.length + 1) (by omega) p
  have hHH2 : H <+: H2 := hp1.trans hpb
  refine specR_assignI x _ (if b then cellA C0 H1.length else p) hxD
    (by simp [sev, h1, h1.symm, h2, h2.symm, hx, hb]; rw [select_word]; rfl) ?_
  refine specR_envWeak (Γb := (x, if b then cellA C0 H1.length else p) :: (nd, cellA C0 H1.length) :: Γ)
    (fun z v hz => hz) ?_
  refine hk' H2 _ _ (hpre.trans hHH2) hHH2 ?_
  have hl2 : LstAt C0 H2 p xs := lstAt_mono hHH2 p xs hl
  cases b
  · exact hl2
  · refine ⟨H1.length, p, rfl, ?_, ?_, hl2⟩
    · show (((H1 ++ ws).set H1.length (Enc.idxW key)).set (H1.length + 1) p)[H1.length]? = _
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    · show (((H1 ++ ws).set H1.length (Enc.idxW key)).set (H1.length + 1) p)[H1.length + 1]? = _
      rw [List.getElem?_set_self (by simp; omega)]

end

end ConPanqueque.T.WC
