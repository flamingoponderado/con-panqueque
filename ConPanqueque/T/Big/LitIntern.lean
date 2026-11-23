import ConPanqueque.T.Big.Pow
import ConPanqueque.T.Core.ConstVal
import ConPanqueque.V.LitStrong
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Interning a literal from a value-heap block

`litBlk(x)`: `x` holds the block `[|limbs n|, limbs n…]`. Zeroing its length cell turns it into the literal's key
`0 :: limbs n`, which is interned in place (the key buffer is only three words). The block is spent: the heap
image keeps the zeroed cell.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def iLx := ofString "ilx"

@[simp] theorem lb_iLx_ne_lEn : iLx ≠ lEn := by decide
@[simp] theorem lb_iLx_ne_lNa : iLx ≠ lNa := by decide
@[simp] theorem lb_iLx_ne_lNn : iLx ≠ lNn := by decide
@[simp] theorem lb_iLx_ne_lSrc : iLx ≠ lSrc := by decide
@[simp] theorem lb_iLx_ne_lDst : iLx ≠ lDst := by decide
@[simp] theorem lb_iLx_ne_lCi : iLx ≠ lCi := by decide
@[simp] theorem lb_iLx_ne_lCz : iLx ≠ lCz := by decide
@[simp] theorem lb_iLx_ne_lCn : iLx ≠ lCn := by decide
@[simp] theorem lb_iLx_ne_lKb : iLx ≠ lKb := by decide
@[simp] theorem lb_iLx_ne_lDir : iLx ≠ lDir := by decide
@[simp] theorem lb_iLx_ne_lFle : iLx ≠ lFle := by decide
@[simp] theorem lb_lEn_ne_iLx : lEn ≠ iLx := by decide
@[simp] theorem lb_lEn_ne_lNa : lEn ≠ lNa := by decide
@[simp] theorem lb_lEn_ne_lNn : lEn ≠ lNn := by decide
@[simp] theorem lb_lEn_ne_lSrc : lEn ≠ lSrc := by decide
@[simp] theorem lb_lEn_ne_lDst : lEn ≠ lDst := by decide
@[simp] theorem lb_lEn_ne_lCi : lEn ≠ lCi := by decide
@[simp] theorem lb_lEn_ne_lCz : lEn ≠ lCz := by decide
@[simp] theorem lb_lEn_ne_lCn : lEn ≠ lCn := by decide
@[simp] theorem lb_lEn_ne_lKb : lEn ≠ lKb := by decide
@[simp] theorem lb_lEn_ne_lDir : lEn ≠ lDir := by decide
@[simp] theorem lb_lEn_ne_lFle : lEn ≠ lFle := by decide
@[simp] theorem lb_lNa_ne_iLx : lNa ≠ iLx := by decide
@[simp] theorem lb_lNa_ne_lEn : lNa ≠ lEn := by decide
@[simp] theorem lb_lNa_ne_lNn : lNa ≠ lNn := by decide
@[simp] theorem lb_lNa_ne_lSrc : lNa ≠ lSrc := by decide
@[simp] theorem lb_lNa_ne_lDst : lNa ≠ lDst := by decide
@[simp] theorem lb_lNa_ne_lCi : lNa ≠ lCi := by decide
@[simp] theorem lb_lNa_ne_lCz : lNa ≠ lCz := by decide
@[simp] theorem lb_lNa_ne_lCn : lNa ≠ lCn := by decide
@[simp] theorem lb_lNa_ne_lKb : lNa ≠ lKb := by decide
@[simp] theorem lb_lNa_ne_lDir : lNa ≠ lDir := by decide
@[simp] theorem lb_lNa_ne_lFle : lNa ≠ lFle := by decide
@[simp] theorem lb_lNn_ne_iLx : lNn ≠ iLx := by decide
@[simp] theorem lb_lNn_ne_lEn : lNn ≠ lEn := by decide
@[simp] theorem lb_lNn_ne_lNa : lNn ≠ lNa := by decide
@[simp] theorem lb_lNn_ne_lSrc : lNn ≠ lSrc := by decide
@[simp] theorem lb_lNn_ne_lDst : lNn ≠ lDst := by decide
@[simp] theorem lb_lNn_ne_lCi : lNn ≠ lCi := by decide
@[simp] theorem lb_lNn_ne_lCz : lNn ≠ lCz := by decide
@[simp] theorem lb_lNn_ne_lCn : lNn ≠ lCn := by decide
@[simp] theorem lb_lNn_ne_lKb : lNn ≠ lKb := by decide
@[simp] theorem lb_lNn_ne_lDir : lNn ≠ lDir := by decide
@[simp] theorem lb_lNn_ne_lFle : lNn ≠ lFle := by decide
@[simp] theorem lb_lSrc_ne_iLx : lSrc ≠ iLx := by decide
@[simp] theorem lb_lSrc_ne_lEn : lSrc ≠ lEn := by decide
@[simp] theorem lb_lSrc_ne_lNa : lSrc ≠ lNa := by decide
@[simp] theorem lb_lSrc_ne_lNn : lSrc ≠ lNn := by decide
@[simp] theorem lb_lSrc_ne_lDst : lSrc ≠ lDst := by decide
@[simp] theorem lb_lSrc_ne_lCi : lSrc ≠ lCi := by decide
@[simp] theorem lb_lSrc_ne_lCz : lSrc ≠ lCz := by decide
@[simp] theorem lb_lSrc_ne_lCn : lSrc ≠ lCn := by decide
@[simp] theorem lb_lSrc_ne_lKb : lSrc ≠ lKb := by decide
@[simp] theorem lb_lSrc_ne_lDir : lSrc ≠ lDir := by decide
@[simp] theorem lb_lSrc_ne_lFle : lSrc ≠ lFle := by decide
@[simp] theorem lb_lDst_ne_iLx : lDst ≠ iLx := by decide
@[simp] theorem lb_lDst_ne_lEn : lDst ≠ lEn := by decide
@[simp] theorem lb_lDst_ne_lNa : lDst ≠ lNa := by decide
@[simp] theorem lb_lDst_ne_lNn : lDst ≠ lNn := by decide
@[simp] theorem lb_lDst_ne_lSrc : lDst ≠ lSrc := by decide
@[simp] theorem lb_lDst_ne_lCi : lDst ≠ lCi := by decide
@[simp] theorem lb_lDst_ne_lCz : lDst ≠ lCz := by decide
@[simp] theorem lb_lDst_ne_lCn : lDst ≠ lCn := by decide
@[simp] theorem lb_lDst_ne_lKb : lDst ≠ lKb := by decide
@[simp] theorem lb_lDst_ne_lDir : lDst ≠ lDir := by decide
@[simp] theorem lb_lDst_ne_lFle : lDst ≠ lFle := by decide
@[simp] theorem lb_lCi_ne_iLx : lCi ≠ iLx := by decide
@[simp] theorem lb_lCi_ne_lEn : lCi ≠ lEn := by decide
@[simp] theorem lb_lCi_ne_lNa : lCi ≠ lNa := by decide
@[simp] theorem lb_lCi_ne_lNn : lCi ≠ lNn := by decide
@[simp] theorem lb_lCi_ne_lSrc : lCi ≠ lSrc := by decide
@[simp] theorem lb_lCi_ne_lDst : lCi ≠ lDst := by decide
@[simp] theorem lb_lCi_ne_lCz : lCi ≠ lCz := by decide
@[simp] theorem lb_lCi_ne_lCn : lCi ≠ lCn := by decide
@[simp] theorem lb_lCi_ne_lKb : lCi ≠ lKb := by decide
@[simp] theorem lb_lCi_ne_lDir : lCi ≠ lDir := by decide
@[simp] theorem lb_lCi_ne_lFle : lCi ≠ lFle := by decide
@[simp] theorem lb_lCz_ne_iLx : lCz ≠ iLx := by decide
@[simp] theorem lb_lCz_ne_lEn : lCz ≠ lEn := by decide
@[simp] theorem lb_lCz_ne_lNa : lCz ≠ lNa := by decide
@[simp] theorem lb_lCz_ne_lNn : lCz ≠ lNn := by decide
@[simp] theorem lb_lCz_ne_lSrc : lCz ≠ lSrc := by decide
@[simp] theorem lb_lCz_ne_lDst : lCz ≠ lDst := by decide
@[simp] theorem lb_lCz_ne_lCi : lCz ≠ lCi := by decide
@[simp] theorem lb_lCz_ne_lCn : lCz ≠ lCn := by decide
@[simp] theorem lb_lCz_ne_lKb : lCz ≠ lKb := by decide
@[simp] theorem lb_lCz_ne_lDir : lCz ≠ lDir := by decide
@[simp] theorem lb_lCz_ne_lFle : lCz ≠ lFle := by decide
@[simp] theorem lb_lCn_ne_iLx : lCn ≠ iLx := by decide
@[simp] theorem lb_lCn_ne_lEn : lCn ≠ lEn := by decide
@[simp] theorem lb_lCn_ne_lNa : lCn ≠ lNa := by decide
@[simp] theorem lb_lCn_ne_lNn : lCn ≠ lNn := by decide
@[simp] theorem lb_lCn_ne_lSrc : lCn ≠ lSrc := by decide
@[simp] theorem lb_lCn_ne_lDst : lCn ≠ lDst := by decide
@[simp] theorem lb_lCn_ne_lCi : lCn ≠ lCi := by decide
@[simp] theorem lb_lCn_ne_lCz : lCn ≠ lCz := by decide
@[simp] theorem lb_lCn_ne_lKb : lCn ≠ lKb := by decide
@[simp] theorem lb_lCn_ne_lDir : lCn ≠ lDir := by decide
@[simp] theorem lb_lCn_ne_lFle : lCn ≠ lFle := by decide
@[simp] theorem lb_lKb_ne_iLx : lKb ≠ iLx := by decide
@[simp] theorem lb_lKb_ne_lEn : lKb ≠ lEn := by decide
@[simp] theorem lb_lKb_ne_lNa : lKb ≠ lNa := by decide
@[simp] theorem lb_lKb_ne_lNn : lKb ≠ lNn := by decide
@[simp] theorem lb_lKb_ne_lSrc : lKb ≠ lSrc := by decide
@[simp] theorem lb_lKb_ne_lDst : lKb ≠ lDst := by decide
@[simp] theorem lb_lKb_ne_lCi : lKb ≠ lCi := by decide
@[simp] theorem lb_lKb_ne_lCz : lKb ≠ lCz := by decide
@[simp] theorem lb_lKb_ne_lCn : lKb ≠ lCn := by decide
@[simp] theorem lb_lKb_ne_lDir : lKb ≠ lDir := by decide
@[simp] theorem lb_lKb_ne_lFle : lKb ≠ lFle := by decide
@[simp] theorem lb_lDir_ne_iLx : lDir ≠ iLx := by decide
@[simp] theorem lb_lDir_ne_lEn : lDir ≠ lEn := by decide
@[simp] theorem lb_lDir_ne_lNa : lDir ≠ lNa := by decide
@[simp] theorem lb_lDir_ne_lNn : lDir ≠ lNn := by decide
@[simp] theorem lb_lDir_ne_lSrc : lDir ≠ lSrc := by decide
@[simp] theorem lb_lDir_ne_lDst : lDir ≠ lDst := by decide
@[simp] theorem lb_lDir_ne_lCi : lDir ≠ lCi := by decide
@[simp] theorem lb_lDir_ne_lCz : lDir ≠ lCz := by decide
@[simp] theorem lb_lDir_ne_lCn : lDir ≠ lCn := by decide
@[simp] theorem lb_lDir_ne_lKb : lDir ≠ lKb := by decide
@[simp] theorem lb_lDir_ne_lFle : lDir ≠ lFle := by decide
@[simp] theorem lb_lFle_ne_iLx : lFle ≠ iLx := by decide
@[simp] theorem lb_lFle_ne_lEn : lFle ≠ lEn := by decide
@[simp] theorem lb_lFle_ne_lNa : lFle ≠ lNa := by decide
@[simp] theorem lb_lFle_ne_lNn : lFle ≠ lNn := by decide
@[simp] theorem lb_lFle_ne_lSrc : lFle ≠ lSrc := by decide
@[simp] theorem lb_lFle_ne_lDst : lFle ≠ lDst := by decide
@[simp] theorem lb_lFle_ne_lCi : lFle ≠ lCi := by decide
@[simp] theorem lb_lFle_ne_lCz : lFle ≠ lCz := by decide
@[simp] theorem lb_lFle_ne_lCn : lFle ≠ lCn := by decide
@[simp] theorem lb_lFle_ne_lKb : lFle ≠ lKb := by decide
@[simp] theorem lb_lFle_ne_lDir : lFle ≠ lDir := by decide

def litBlkLocals : List MlS := lEn :: lNa :: lNn :: lSrc :: lDst :: lCi :: lCz :: lCn :: litNatScratch

def litBlkBody (C : Ctx) : ProgHOL 64 :=
  prologue litBlkLocals
   (.seq (.assign .local lNn (.load .one (vv iLx)))
   (.seq (.assign .local lEn (.op .add [vv lNn, .const 1]))
   (allocP C lKb (.panop .mul [vv lEn, .const 8])
   (.seq (.store (vv lKb) (.const 0))
   (.seq (.assign .local lSrc (.op .add [vv iLx, .const 8]))
   (.seq (.assign .local lDst (.op .add [vv lKb, .const 8]))
   (.seq (.assign .local lCi (.const 0))
   (.seq (.assign .local lCn (vv lNn))
   (.seq copyLoop
   (.seq (.assign .local lNa (.op .add [vv lKb, .const 8]))
   (eLitNatWith (rRestE 17 (vv lEn) lFle))))))))))))

theorem cellA_off (C : Ctx) (o j : Nat) : cellA C o + BitVec.ofNat 64 (8 * j) = C.HB + BitVec.ofNat 64 (8 * (o + j)) := by
  unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

/-- A heap range as the key region of the literal intern. -/
theorem sepK_heap {C : Ctx} (hok : CtxOK C) (o w : Nat) (hw : o + w ≤ C.HN) :
    SepK C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) w 17 :=
  ⟨hok.sepLit.pow, hok.sepLit.cap, hok.sepLit.dis, hok.sepLit.oth,
    fun k' tier m h1 h2 h3 => ⟨(hok.sepLit.dsc k' tier m h1 h2 h3).1, (hok.sepLit.dsc k' tier m h1 h2 h3).2.1,
      fun j hj => by rw [cellA_off]; exact (hok.dirHeap (o + j) k' tier m (by omega) h1 h2 h3).symm⟩,
    fun F hF => ⟨(hok.sepLit.fls F hF).1, (hok.sepLit.fls F hF).2.1,
      fun j hj => by rw [cellA_off]; exact (hok.flHeap (o + j) F (by omega) hF).symm⟩,
    fun j k' tier hj h1 h2 hin => hok.heapOut (o + j) (by omega) ⟨k', tier, h1, h2, by rw [← cellA_off]; exact hin⟩⟩

section
variable {σ : Type}

theorem litBlk_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState) (n o : Nat)
    (hb : BlkAt C.H o (limbs n)) :
    SpecR (Pre (σ := σ) C s [(iLx, cellA C o)]) (litBlkBody C) s (internE (.lit (.natVal n))) (Knot.PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (fun x hx => ?_) ?_
  · simp only [litBlkLocals, litNatScratch, bvarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have hbl := blkAt_len hb
  have hl0 : C.H[o]? = some (BitVec.ofNat 64 (limbs n).length) := by simpa using hb.1
  refine UD.specR_heapLoadI' lNn (vv iLx) o _ hl0 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lEn _ (BitVec.ofNat 64 ((limbs n).length + 1)) (by decide)
    (by simp [sev]; exact word_add1_eq _) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsm := blk_small hok ht0.sr hb
  generalize hL : (limbs n).length = len at hbl hl0 hsm
  refine specR_allocI lKb (.panop .mul [vv lEn, .const 8]) (len + 1) (by omega) (by decide)
    (fun v => by simp +decide [sev, Env.get]; exact CV.mul8_eq _) (fun H' ws hpre hwl hcap => ?_)
  have hpl := hpre.length_le
  have hj : H'.length < (ctxH C (H' ++ ws)).H.length := by show _ < (H' ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv lKb) (.const 0) _ hj 0 (by simp; rfl) rfl ?_
  let B0 := (H' ++ ws).set H'.length 0
  have hB0 : B0.length = H'.length + (len + 1) := by simp [B0, hwl]
  refine specR_assignI lSrc _ (cellA C (o + 1 + 0)) (by decide)
    (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI lDst _ (cellA C (H'.length + 1 + 0)) (by decide) (by simp [sev]; exact cellA_add8 C _) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI lCn (vv lNn) (BitVec.ofNat 64 len) (by decide) (by simp [sev, Env.get, hL]) ?_
  let Γc : Env := [(lCn, BitVec.ofNat 64 len), (lKb, cellA C H'.length), (lEn, BitVec.ofNat 64 (len + 1)),
    (lDir, C.L.DIR), (lFle, C.FLe), (lNn, BitVec.ofNat 64 len)]
  refine specR_envWeak (Γb := (lCi, BitVec.ofNat 64 0) :: (lDst, cellA C (H'.length + 1 + 0)) ::
    (lSrc, cellA C (o + 1 + 0)) :: Γc) (fun z v hz => ?_) ?_
  · simp only [Γc, Env.get_cons] at hz ⊢
    by_cases e1 : z = lCi
    · subst e1; simpa using hz
    by_cases e2 : z = lDst
    · subst e2; simpa using hz
    by_cases e3 : z = lSrc
    · subst e3; simpa using hz
    by_cases e4 : z = lCn
    · subst e4; simpa using hz
    by_cases e5 : z = lKb
    · subst e5; simpa using hz
    by_cases e6 : z = lEn
    · subst e6; simpa [hL] using hz
    by_cases e7 : z = lDir
    · subst e7; simp at hz ⊢; simpa +decide [Env.get, ctxEnv] using hz
    by_cases e8 : z = lFle
    · subst e8; simp at hz ⊢; simpa +decide [Env.get, ctxEnv] using hz
    by_cases e9 : z = lNn
    · subst e9; simpa [hL] using hz
    simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, Env.get] at hz
  have hsrc : ∀ j (hj : j < (limbs n).length), B0[o + 1 + j]? = some (limbs n)[j] := by
    intro j hj
    have e1 : B0[o + 1 + j]? = (H' ++ ws)[o + 1 + j]? := List.getElem?_set_ne (by omega)
    rw [e1, List.getElem?_append_left (by omega)]
    obtain ⟨r, hr⟩ := hpre
    rw [← hr, List.getElem?_append_left (by omega), hb.2 j hj]
  refine specR_copyI (ctxOK_H hok _) B0 (limbs n) (o + 1) (H'.length + 1) (by decide) hsrc (by omega)
    (by rw [hB0]; omega) (by omega) (by simp [Γc, hL]) (by decide) (by simp [Γc, Env.get]) ?_
  let Bf := fillI B0 (limbs n) (H'.length + 1) (limbs n).length
  have hBf : Bf.length = B0.length := fillI_length _ _ _ _
  refine specR_assignI lNa _ (cellA C H'.length + 8) (by decide) (by simp [sev, Γc]) ?_
  intro t ht
  obtain ⟨Hh, hp, ha⟩ := ht.sr.heap
  have hp' : Bf <+: Hh := hp
  have hcap' := hok.heapCap
  have hHh : Hh.length ≤ C.HN := ha.len
  have hbf : ∀ k (hk : k < len + 1), Bf[H'.length + k]? = some ((0 :: limbs n)[k]'(by simp; omega)) := by
    intro k hk
    rw [fillI_get?]
    rcases k with _ | k
    · rw [if_neg (by omega), Nat.add_zero]
      exact List.getElem?_set_self (by simp; omega)
    · rw [if_pos ⟨by omega, by omega, by rw [hB0]; omega⟩]
      simp [show H'.length + (k + 1) - (H'.length + 1) = k by omega, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show k < (limbs n).length by omega)]
  have hK' : Words t (cellA C H'.length) (0 :: limbs n) := by
    intro k hk
    simp only [List.length_cons] at hk
    rw [cellA_off]
    refine ⟨ha.dom (H'.length + k) (show H'.length + k < C.HN by omega), ?_⟩
    have hlk : H'.length + k < Hh.length := by have := hp'.length_le; omega
    have hv : t.memory (C.HB + BitVec.ofNat 64 (8 * (H'.length + k))) = .word (Hh[H'.length + k]'hlk) :=
      ha.val (H'.length + k) hlk
    rw [hv]
    congr 1
    have e1 : Hh[H'.length + k]? = Bf[H'.length + k]? := by
      obtain ⟨r, hr⟩ := hp'; rw [← hr, List.getElem?_append_left (by rw [hBf, hB0]; omega)]
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem, e1, hbf k (by omega)]
  have hkey : Enc.encLit ⟨.natVal n⟩ = 0 :: limbs n := rfl
  have hK : Words t (cellA C H'.length) (Enc.encLit ⟨.natVal n⟩) := hK'
  have hS := sepK_heap hok H'.length (Enc.encLit ⟨.natVal n⟩).length (by rw [hkey]; simp only [List.length_cons]; omega)
  have hw : ∀ y, y ∈ litNatScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ (by simp only [litBlkLocals]; simp [hy]))
  rcases eInternLitNat_spec2 ra t C.L C.FLn C.FLl C.FLs C.FLe (cellA C H'.length) s.store n ht.sr.rep hS hK
      (by rw [hkey]; simp; omega) hok.b0Lit hok.b1Lit (ht.env _ _ (by simp [Γc]))
      (ht.env _ _ (by simp [Γc, hkey, hL])) (ht.env _ _ (by simp))
      (ht.env _ _ (by simp [Γc, hL])) (ht.env _ _ (by simp [Γc]))
      (ht.env _ _ (by simp [Γc])) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  have hrun := internNodeE_lit s (.natVal n)
      (Nat.le_trans (tabAt_size_le hsr.e.p8) (hok.sepLit.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s8) (hok.sepLit.cap 1 (by decide)))
  right
  refine ⟨_, hr, (s.store.intern (.lit (.natVal n))).2, { s with store := (s.store.intern (.lit (.natVal n))).1 }, ?_,
    Bf, ?_, rfl, ?_⟩
  · show internNodeE (.lit (.natVal n)) s = _
    exact hrun
  · exact CV.prefix_fillI _ _ _ _ (by omega)
      (prefix_set_ge (hpre.trans (List.prefix_append _ ws)) _ hpl _) _
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk) (fun c hc => hm c (hok.memoOut (.e mk) c hc))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk)) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk) (fun c hc => hm c (hok.memoOut (.n mk) c hc))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk)) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk) (fun c hc => hm c (hok.memoOut (.c mk) c hc))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk)) hd,
      modeAt_frame ht.sr.mode (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk)) hd (by rw [hg]),
      envAt_frame ht.sr.env (fun b c hc => hm c (hok.memoOut (envR b) c hc))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk)) (fun i hi => hm _ (hok.envOut i hi)) hd
        ⟨by rw [hg], by rw [hg]⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi)) hd (by rw [hg]),
        (internNodeE_wf ht.sr.twf viewOK_lit hrun).1, envDen_ext ht.sr.envd (internNodeE_wf ht.sr.twf viewOK_lit hrun).2, cachesOK_ext ht.sr.cok (internNodeE_wf ht.sr.twf viewOK_lit hrun).2 rfl⟩

end

end ConPanqueque.T.Big
