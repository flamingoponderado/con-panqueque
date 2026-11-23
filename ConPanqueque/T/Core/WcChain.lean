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

end ConPanqueque.T.WC
