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

end ConPanqueque.T.WC
