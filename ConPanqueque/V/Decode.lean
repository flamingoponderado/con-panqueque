import ConPanqueque.V.DerRead
import ConPanqueque.V.Enc
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic
open ConRon.Arena

/-!
# Decoding a handle word

`decodeH`: from the handle word in `dh`, its tier (`dt`), tag (`dg`) and
index (`di`), exactly as con-ron's `Idx.tier`, `Idx.tag` (a wide word reads
tag 4) and `Idx.idxNat`.
-/

namespace ConPanqueque.V

def lDh := ofString "dh"
def lDt := ofString "dt"
def lDg := ofString "dg"

def decodeH : ProgHOL 64 :=
  .seq (.assign .local lDt (.shift .lsr (vv lDh) (.const 31)))
   (.ite (.op .and [.shift .lsr (vv lDh) (.const 30), .const 1])
     (.seq (.assign .local lDg (.const 4)) (.assign .local lDi (.op .and [vv lDh, .const 0x3fffffff])))
     (.seq (.assign .local lDg (.op .and [.shift .lsr (vv lDh) (.const 26), .const 15]))
       (.assign .local lDi (.op .and [vv lDh, .const 0x3ffffff]))))

theorem and_mask_nat (x : BitVec 64) (k : Nat) (hk : k < 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt (a := 2 ^ k - 1) (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat k

theorem eval_and2' {σ : Type} (s : PanSemStateFiniteExact 64 σ) (e1 e2 : ExpHOL 64) (v1 v2 : BitVec 64)
    (h1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word v1)))
    (h2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word v2))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.op .and [e1, e2]) =
      some (.val (.word (v1 &&& v2))) := by
  rw [evalHOLExact]; simp [evalListHOLExact, h1, h2, wordOpHOL, wordOp, valueIsWord, valueWord]
  show v1 &&& (v2 &&& 18446744073709551615#64) = _
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]

section
variable {σ : Type} {k : IdxKind}

theorem decodeH_spec (t : PanSemStateFiniteExact 64 σ) (i : Idx k)
    (hh : t.locals.lookup lDh = some (.val (.word (Enc.idxW i))))
    (ht : ∃ w, t.locals.lookup lDt = some (.val (.word w))) (hg : ∃ w, t.locals.lookup lDg = some (.val (.word w)))
    (hi : ∃ w, t.locals.lookup lDi = some (.val (.word w))) :
    ∃ L, evaluateHOLFiniteState t decodeH = (none, { t with locals := L }) ∧
      L.lookup lDt = some (.val (.word (BitVec.ofNat 64 i.tier.toNat))) ∧
      L.lookup lDg = some (.val (.word (BitVec.ofNat 64 i.tag.toNat))) ∧
      L.lookup lDi = some (.val (.word (BitVec.ofNat 64 i.idxNat))) ∧
      ∀ y, y ≠ lDt → y ≠ lDg → y ≠ lDi → L.lookup y = t.locals.lookup y := by
  obtain ⟨wt, hwt⟩ := ht; obtain ⟨wg, hwg⟩ := hg; obtain ⟨wi, hwi⟩ := hi
  have hwl : i.word.toNat < 2 ^ 32 := i.word.toNat_lt
  have hW : (Enc.idxW i).toNat = i.word.toNat := by simp [Enc.idxW]
  have etier : (Enc.idxW i >>> (31 : BitVec 64).toNat) = BitVec.ofNat 64 i.tier.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [show (31 : BitVec 64).toNat = 31 from rfl, BitVec.toNat_ushiftRight, hW, Nat.shiftRight_eq_div_pow]
    simp [Idx.tier, UInt32.toNat_div]; omega
  unfold decodeH
  rw [seq_normal _ (ConsLoop.assign_local t lDt _ _ wt (by rw [eval_shr t _ _ _ (eval_vv t lDh _ hh) (by decide), etier]) hwt)]
  let t1 := setVarHOLFinite lDt (.val (.word (BitVec.ofNat 64 i.tier.toNat))) t
  have hh1 : t1.locals.lookup lDh = some (.val (.word (Enc.idxW i))) := by lk [t1]; exact hh
  have ewide : (Enc.idxW i >>> (30 : BitVec 64).toNat &&& 1) = bw (i.isWide = true) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 (2 ^ 1 - 1) from rfl, and_mask_nat _ 1 (by decide),
      show (30 : BitVec 64).toNat = 30 from rfl, BitVec.toNat_ushiftRight, hW, Nat.shiftRight_eq_div_pow]
    by_cases h : i.isWide = true
    · have : i.word.toNat / 2 ^ 30 % 2 = 1 := by
        simp [Idx.isWide] at h; have := congrArg UInt32.toNat h; simpa [UInt32.toNat_div, UInt32.toNat_mod] using this
      simp [bw, h, this]
    · have : i.word.toNat / 2 ^ 30 % 2 = 0 := by
        simp [Idx.isWide] at h
        have h' : ¬ (i.word.toNat / 1073741824 % 2 = 1) := fun e => h (UInt32.toNat_inj.mp (by simpa [UInt32.toNat_div, UInt32.toNat_mod] using e))
        omega
      simp [bw, h, this]
  rw [ite_word t1 _ _ _ _ (by rw [eval_and2' t1 _ _ _ _ (eval_shr t1 _ _ _ (eval_vv t1 lDh _ hh1) (by decide)) (eval_const t1 1), ewide])]
  have restore : ∀ (u : PanSemStateFiniteExact 64 σ) (g x : BitVec 64), u.memory = t1.memory →
      u.locals.lookup lDt = some (.val (.word (BitVec.ofNat 64 i.tier.toNat))) →
      u.locals.lookup lDg = some (.val (.word g)) → u.locals.lookup lDi = some (.val (.word x)) →
      (∀ y, y ≠ lDt → y ≠ lDg → y ≠ lDi → u.locals.lookup y = t.locals.lookup y) →
      g = BitVec.ofNat 64 i.tag.toNat → x = BitVec.ofNat 64 i.idxNat →
      { t with locals := u.locals } = u →
      ∃ L, ((none : Option (PanSemResultExact 64)), u) = (none, { t with locals := L }) ∧
        L.lookup lDt = some (.val (.word (BitVec.ofNat 64 i.tier.toNat))) ∧
        L.lookup lDg = some (.val (.word (BitVec.ofNat 64 i.tag.toNat))) ∧
        L.lookup lDi = some (.val (.word (BitVec.ofNat 64 i.idxNat))) ∧
        ∀ y, y ≠ lDt → y ≠ lDg → y ≠ lDi → L.lookup y = t.locals.lookup y := by
    intro u g x _ a1 a2 a3 a4 eg ex eu
    exact ⟨u.locals, by rw [eu], a1, by rw [a2, eg], by rw [a3, ex], a4⟩
  by_cases hw : i.isWide = true
  · simp only [bw, hw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [seq_normal _ (ConsLoop.assign_local t1 lDg (.const 4) 4 wg (eval_const t1 4) (by lk [t1]; exact hwg))]
    let t2 := setVarHOLFinite lDg (.val (.word 4)) t1
    have hx : Enc.idxW i &&& 0x3fffffff = BitVec.ofNat 64 i.idxNat := by
      apply BitVec.eq_of_toNat_eq
      rw [show (0x3fffffff : BitVec 64) = BitVec.ofNat 64 (2 ^ 30 - 1) from rfl, and_mask_nat _ 30 (by decide), hW]
      simp [Idx.idxNat, Idx.index, hw, UInt32.toNat_mod]; omega
    rw [ConsLoop.assign_local t2 lDi _ _ wi (by rw [eval_and2' t2 _ _ _ _ (eval_vv t2 lDh _ (by lk [t2]; exact hh1))
      (eval_const t2 _), hx]) (by lk [t2, t1]; exact hwi)]
    exact restore _ 4 _ rfl (by lk [t2, t1]) (by lk [t2]) (by lk) (fun y a b c => by lk [t2, t1])
      (by simp [Idx.tag, hw]) rfl rfl
  · simp only [bw, hw, ↓reduceIte, ne_eq, not_true_eq_false, eq_self_iff_true, Bool.false_eq_true]
    have hgv : (Enc.idxW i >>> (26 : BitVec 64).toNat) &&& 15 = BitVec.ofNat 64 i.tag.toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [show (15 : BitVec 64) = BitVec.ofNat 64 (2 ^ 4 - 1) from rfl, and_mask_nat _ 4 (by decide),
        show (26 : BitVec 64).toNat = 26 from rfl, BitVec.toNat_ushiftRight, hW, Nat.shiftRight_eq_div_pow]
      simp [Idx.tag, hw, UInt32.toNat_mod, UInt32.toNat_div]; omega
    rw [seq_normal _ (ConsLoop.assign_local t1 lDg _ _ wg (by
      rw [eval_and2' t1 _ _ _ _ (eval_shr t1 _ _ _ (eval_vv t1 lDh _ hh1) (by decide)) (eval_const t1 15), hgv])
      (by lk [t1]; exact hwg))]
    let t2 := setVarHOLFinite lDg (.val (.word (BitVec.ofNat 64 i.tag.toNat))) t1
    have hx : Enc.idxW i &&& 0x3ffffff = BitVec.ofNat 64 i.idxNat := by
      apply BitVec.eq_of_toNat_eq
      rw [show (0x3ffffff : BitVec 64) = BitVec.ofNat 64 (2 ^ 26 - 1) from rfl, and_mask_nat _ 26 (by decide), hW]
      simp [Idx.idxNat, Idx.index, hw, UInt32.toNat_mod]; omega
    rw [ConsLoop.assign_local t2 lDi _ _ wi (by rw [eval_and2' t2 _ _ _ _ (eval_vv t2 lDh _ (by lk [t2]; exact hh1))
      (eval_const t2 _), hx]) (by lk [t2, t1]; exact hwi)]
    exact restore _ _ _ rfl (by lk [t2, t1]) (by lk [t2]) (by lk) (fun y a b c => by lk [t2, t1]) rfl rfl rfl

end

end ConPanqueque.V
