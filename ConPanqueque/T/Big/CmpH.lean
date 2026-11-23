import ConPanqueque.T.Big.Cmp
import ConPanqueque.T.Core.Unfold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Comparing two heap blocks

`bcH(x, y)`: the verdict `cmpN a b` for blocks of `a` and `b`. The counted loop is `Cmp.lean`'s, reading the limbs
through memory facts, which the heap image supplies for the two blocks.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def hbX := ofString "bhx"
def hbY := ofString "bhy"

@[simp] theorem ch_hbX_ne_hbY : hbX ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_hbX : hbY ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bLa : hbX ≠ bLa := by decide
@[simp] theorem ch_bLa_ne_hbX : bLa ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bPa : hbX ≠ bPa := by decide
@[simp] theorem ch_bPa_ne_hbX : bPa ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bQa : hbX ≠ bQa := by decide
@[simp] theorem ch_bQa_ne_hbX : bQa ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bQb : hbX ≠ bQb := by decide
@[simp] theorem ch_bQb_ne_hbX : bQb ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bX : hbX ≠ bX := by decide
@[simp] theorem ch_bX_ne_hbX : bX ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bY : hbX ≠ bY := by decide
@[simp] theorem ch_bY_ne_hbX : bY ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bR : hbX ≠ bR := by decide
@[simp] theorem ch_bR_ne_hbX : bR ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_bI : hbX ≠ bI := by decide
@[simp] theorem ch_bI_ne_hbX : bI ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_lFle : hbX ≠ lFle := by decide
@[simp] theorem ch_lFle_ne_hbX : lFle ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_lDir : hbX ≠ lDir := by decide
@[simp] theorem ch_lDir_ne_hbX : lDir ≠ hbX := by decide
@[simp] theorem ch_hbX_ne_lKb : hbX ≠ lKb := by decide
@[simp] theorem ch_lKb_ne_hbX : lKb ≠ hbX := by decide
@[simp] theorem ch_hbY_ne_bLa : hbY ≠ bLa := by decide
@[simp] theorem ch_bLa_ne_hbY : bLa ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_bPa : hbY ≠ bPa := by decide
@[simp] theorem ch_bPa_ne_hbY : bPa ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_bQa : hbY ≠ bQa := by decide
@[simp] theorem ch_bQa_ne_hbY : bQa ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_bQb : hbY ≠ bQb := by decide
@[simp] theorem ch_bQb_ne_hbY : bQb ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_bX : hbY ≠ bX := by decide
@[simp] theorem ch_bX_ne_hbY : bX ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_bY : hbY ≠ bY := by decide
@[simp] theorem ch_bY_ne_hbY : bY ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_bR : hbY ≠ bR := by decide
@[simp] theorem ch_bR_ne_hbY : bR ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_bI : hbY ≠ bI := by decide
@[simp] theorem ch_bI_ne_hbY : bI ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_lFle : hbY ≠ lFle := by decide
@[simp] theorem ch_lFle_ne_hbY : lFle ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_lDir : hbY ≠ lDir := by decide
@[simp] theorem ch_lDir_ne_hbY : lDir ≠ hbY := by decide
@[simp] theorem ch_hbY_ne_lKb : hbY ≠ lKb := by decide
@[simp] theorem ch_lKb_ne_hbY : lKb ≠ hbY := by decide

def bhParams : List MlS := [hbX, hbY]
def bhLocals : List MlS := [bLa, bPa, bQa, bQb, bX, bY, bR, bI]

def bhCore : ProgHOL 64 :=
  .seq (.assign .local bLa (.load .one (vv hbX)))
  (.seq (.assign .local bPa (.load .one (vv hbY)))
  (.ite (.cmp .lower (vv bLa) (vv bPa)) (.return (.const 0))
  (.ite (.cmp .lower (vv bPa) (vv bLa)) (.return (.const 2))
  (.seq (.assign .local bQa (.op .add [vv hbX, .op .add [.panop .mul [vv bLa, .const 8], .const 8]]))
  (.seq (.assign .local bQb (.op .add [vv hbY, .op .add [.panop .mul [vv bLa, .const 8], .const 8]]))
  (.seq (.assign .local bR (.const 1)) (.seq (.assign .local bI (.const 0))
  (.seq cmpLoop (.return (vv bR))))))))))

def bhBody : ProgHOL 64 := prologue bhLocals bhCore

/-- Memory facts for a block's limbs. -/
def blkMem (P : BitVec 64) : Nat → List (BitVec 64) → Mem
  | _, [] => []
  | j, x :: xs => (P + BitVec.ofNat 64 (8 * (j + 1)), x) :: blkMem P (j + 1) xs

theorem blkMem_get (P : BitVec 64) : ∀ (xs : List (BitVec 64)) (j0 j : Nat) (hj : j < xs.length),
    (P + BitVec.ofNat 64 (8 * (j0 + j + 1)), xs[j]) ∈ blkMem P j0 xs
  | [], _, _, hj => absurd hj (by simp)
  | x :: xs, j0, 0, _ => by simp [blkMem]
  | x :: xs, j0, j + 1, hj => by
    simp only [blkMem, List.mem_cons]
    right
    have := blkMem_get P xs (j0 + 1) j (by simp at hj; omega)
    rw [show j0 + 1 + j + 1 = j0 + (j + 1) + 1 by omega] at this
    simpa using this

theorem blkMem_mem (P : BitVec 64) : ∀ (xs : List (BitVec 64)) (j0 : Nat) (a v : BitVec 64),
    (a, v) ∈ blkMem P j0 xs → ∃ j, ∃ hj : j < xs.length, a = P + BitVec.ofNat 64 (8 * (j0 + j + 1)) ∧ v = xs[j]
  | [], _, _, _, h => absurd h (by simp [blkMem])
  | x :: xs, j0, a, v, h => by
    simp only [blkMem, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨0, by simp, by simp, rfl⟩
    · obtain ⟨j, hj, ha, hv⟩ := blkMem_mem P xs (j0 + 1) a v h
      exact ⟨j + 1, by simp; omega, by rw [ha]; congr 2; omega, by simp [hv]⟩

section
variable {σ : Type}

theorem specR_memAdd {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (M' : Mem)
    (hM : ∀ t : PState σ, Inv C s Γ M D t → ∀ a v, (a, v) ∈ M' → t.memaddrs a ∧ t.memory a = .word v)
    (h : SpecR (Inv C s Γ (M' ++ M) D) c s m R) : SpecR (Inv C s Γ M D) c s m R :=
  fun t ht => h t ⟨ht.sr, ht.env, fun a v hav => (List.mem_append.mp hav).elim (hM t ht a v) (ht.mem a v),
    ht.decl⟩

/-- A block's limbs hold in memory. -/
theorem blkMem_ok {C : Ctx} {s : AState} {t : PState σ} (hsr : SR C s t) {o : Nat} {xs : List (BitVec 64)}
    (hb : BlkAt C.H o xs) : ∀ a v, (a, v) ∈ blkMem (cellA C o) 0 xs → t.memaddrs a ∧ t.memory a = .word v := by
  intro a v hav
  obtain ⟨j, hj, ha, hv⟩ := blkMem_mem _ xs 0 a v hav
  obtain ⟨H', hp, hh⟩ := hsr.heap
  have hbl := blkAt_len hb
  have hpl := hp.length_le
  have hcell : a = C.HB + BitVec.ofNat 64 (8 * (o + 1 + j)) := by
    rw [ha]; unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega
  have hlen := hh.len
  refine ⟨by rw [hcell]; exact hh.dom _ (by omega), ?_⟩
  rw [hcell, hh.val (o + 1 + j) (by omega), hv]
  congr 1
  have e1 : H'[o + 1 + j]? = C.H[o + 1 + j]? := by
    obtain ⟨r, hr⟩ := hp; rw [← hr, List.getElem?_append_left (by omega)]
  apply Option.some_inj.mp
  rw [← List.getElem?_eq_getElem, e1, hb.2 j hj]

theorem blk_small0 {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (hsr : SR C s t) {o : Nat}
    {xs : List (BitVec 64)} (hb : BlkAt C.H o xs) : xs.length < 2 ^ 58 := by
  obtain ⟨H0, hp0, ha0⟩ := hsr.heap
  have hbl := blkAt_len hb
  have hcap := hok.heapCap
  have hlen0 := ha0.len
  have hp0l := hp0.length_le
  omega

theorem bh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bhLocals → (ctxEnv C ++ bhParams.zip vals).get x = none :=
  Knot.params_none C bhLocals bhParams vals (by decide) (by decide)

theorem bh_spec (C : Ctx) (hok : CtxOK C) (s : AState) (a b : Nat) (oa ob : Nat)
    (hba : BlkAt C.H oa (limbs a)) (hbb : BlkAt C.H ob (limbs b)) :
    SpecR (σ := σ) (Pre C s (bhParams.zip [cellA C oa, cellA C ob])) bhBody s (pure (cmpN a b)) (PostW C s) := by
  refine specR_prologue (postW_locals C s) (bh_none C _) ?_
  unfold bhCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs a).length) := hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs b).length) := hbb.1
  refine UD.specR_heapLoadI' bLa (vv hbX) oa _ hla0 (by decide) (by simp +decide [Env.get, bhParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' bPa (vv hbY) ob _ hlb0 (by decide) (by simp +decide [Env.get, bhParams, ctxEnv]) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsa := blk_small0 hok ht0.sr hba
  have hsb := blk_small0 hok ht0.sr hbb
  have hla' : (limbs a).length < B := by unfold B; omega
  have hlb' : (limbs b).length < B := by unfold B; omega
  have w1 := word_lt_iff _ _ hla' hlb'
  have w2 := word_lt_iff _ _ hlb' hla'
  by_cases h1 : (limbs a).length < (limbs b).length
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, w1.mpr h1]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    have : cmpN a b = 0 := by simp [cmpN, lt_of_length_lt h1]
    rw [this]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr w1).mpr h1])
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases h2 : (limbs b).length < (limbs a).length
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, w2.mpr h2]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    have hlt := lt_of_length_lt h2
    have : cmpN a b = 2 := by
      have h3 : ¬ a < b := by omega
      have h4 : a ≠ b := by omega
      simp [cmpN, h3, h4]
    rw [this]
    exact specR_returnI _ 2 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr w2).mpr h2])
    (fun h => absurd rfl h) (fun _ => ?_)
  have heq : (limbs b).length = (limbs a).length := by omega
  refine specR_assignI bQa _ (cellA C oa + BitVec.ofNat 64 (8 * ((limbs a).length + 1))) (by decide)
    (by simp +decide [sev, Env.get, bhParams, ctxEnv]; exact add8_eq _) ?_
  refine specR_assignI bQb _ (cellA C ob + BitVec.ofNat 64 (8 * ((limbs a).length + 1))) (by decide)
    (by simp +decide [sev, Env.get, bhParams, ctxEnv]; exact add8_eq _) ?_
  refine specR_assignI bR (.const 1) 1 (by decide) rfl ?_
  refine specR_assignI bI (.const 0) 0 (by decide) rfl ?_
  refine specR_memAdd (blkMem (cellA C oa) 0 (limbs a) ++ blkMem (cellA C ob) 0 (limbs b))
    (fun t ht a' v hav => (List.mem_append.mp hav).elim (blkMem_ok ht.sr hba a' v) (blkMem_ok ht.sr hbb a' v)) ?_
  refine cmp_loop' a b (limbs a).length (cellA C oa) (cellA C ob) rfl heq (by omega) (by decide) (by simp)
    (by simp +decide [Env.get, bhParams, ctxEnv]) (by simp +decide [Env.get, bhParams, ctxEnv])
    (fun j hj => List.mem_append_left _ (List.mem_append_left _ (by simpa using blkMem_get _ (limbs a) 0 j hj)))
    (fun j hj => List.mem_append_left _ (List.mem_append_right _ (by simpa using blkMem_get _ (limbs b) 0 j hj))) ?_
  exact specR_returnI _ (BitVec.ofNat 64 (cmpN a b)) (by simp [cmpG])
    (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Big
