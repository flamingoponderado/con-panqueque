import ConPanqueque.T.Big.Pow
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

def litBlkLocals : List MlS := lEn :: lNa :: lNn :: litNatScratch

def litBlkBody : ProgHOL 64 :=
  prologue litBlkLocals
   (.seq (.assign .local lNn (.load .one (vv iLx)))
   (.seq (.store (vv iLx) (.const 0))
   (.seq (.assign .local lEn (.op .add [vv lNn, .const 1]))
   (.seq (.assign .local lKb (vv iLx))
   (.seq (.assign .local lNa (.op .add [vv iLx, .const 8]))
   (eLitNatWith (rRestE 17 (vv lEn) lFle)))))))

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
    SpecR (Pre (σ := σ) C s [(iLx, cellA C o)]) litBlkBody s (internE (.lit (.natVal n)))
      (PostE (ctxH C (C.H.set o 0))) := by
  refine specR_prologue (postE_locals _) (fun x hx => ?_) ?_
  · simp only [litBlkLocals, litNatScratch, bvarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have hbl := blkAt_len hb
  have hl0 : C.H[o]? = some (BitVec.ofNat 64 (limbs n).length) := by simpa using hb.1
  refine UD.specR_heapLoadI' lNn (vv iLx) o _ hl0 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_heapStoreI hok (vv iLx) (.const 0) o (by omega) 0 (by simp +decide [sev, Env.get, ctxEnv]) rfl ?_
  refine specR_assignI lEn _ (BitVec.ofNat 64 ((limbs n).length + 1)) (by decide)
    (by simp [sev]; exact word_add1_eq _) ?_
  refine specR_assignI lKb (vv iLx) (cellA C o) (by decide) (by simp +decide [sev, Env.get, ctxEnv]) ?_
  refine specR_assignI lNa _ (cellA C o + 8) (by decide) (by simp +decide [sev, Env.get, ctxEnv]) ?_
  intro t ht
  have hok' := ctxOK_H hok (C.H.set o 0)
  obtain ⟨H', hp, ha⟩ := ht.sr.heap
  have hp' : (C.H.set o 0) <+: H' := hp
  have hpl : (C.H.set o 0).length ≤ H'.length := hp'.length_le
  have hHl : (C.H.set o 0).length = C.H.length := List.length_set ..
  have hcap := hok.heapCap
  have hH'N : H'.length ≤ C.HN := ha.len
  have hbl' : o + 1 + (limbs n).length ≤ C.H.length := by have := hbl; simp at this ⊢; omega
  have hkey : Enc.encLit ⟨.natVal n⟩ = 0 :: limbs n := rfl
  have hK' : Words t (cellA C o) (0 :: limbs n) := by
    intro k hk
    simp only [List.length_cons] at hk
    rw [cellA_off]
    refine ⟨ha.dom (o + k) (show o + k < C.HN by omega), ?_⟩
    have hv : t.memory (C.HB + BitVec.ofNat 64 (8 * (o + k))) = .word H'[o + k] := ha.val (o + k) (by omega)
    rw [hv]
    congr 1
    have e1 : H'[o + k]? = (C.H.set o 0)[o + k]? := by
      obtain ⟨r, hr⟩ := hp'; rw [← hr, List.getElem?_append_left (by rw [hHl]; omega)]
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, e1]
    rcases k with _ | k
    · rw [Nat.add_zero, List.getElem?_set_self (by omega)]; rfl
    · rw [List.getElem?_set_ne (by omega), show o + (k + 1) = o + 1 + k by omega, hb.2 k (by omega)]; simp
  have hK : Words t (cellA C o) (Enc.encLit ⟨.natVal n⟩) := hK'
  have hS := sepK_heap hok o (Enc.encLit ⟨.natVal n⟩).length (by rw [hkey]; simp only [List.length_cons]; omega)
  have hw : ∀ y, y ∈ litNatScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hy))))
  rcases eInternLitNat_spec2 ra t C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) s.store n ht.sr.rep hS hK
      (by rw [hkey]; simp; omega) hok.b0Lit hok.b1Lit (ht.env _ _ (by simp +decide [Env.get]))
      (ht.env _ _ (by simp +decide [Env.get, hkey])) (ht.env _ _ (by simp +decide [Env.get]))
      (ht.env _ _ (by simp +decide [Env.get])) (ht.env _ _ (by simp +decide [Env.get, ctxEnv]))
      (ht.env _ _ (by simp +decide [Env.get, ctxEnv])) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.lit (.natVal n))).2, { s with store := (s.store.intern (.lit (.natVal n))).1 }, ?_,
    rfl, ?_⟩
  · show internNodeE (.lit (.natVal n)) s = _
    exact internNodeE_lit s _
      (Nat.le_trans (tabAt_size_le hsr.e.p8) (hok.sepLit.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s8) (hok.sepLit.cap 1 (by decide)))
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
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi)) hd (by rw [hg])⟩

end

end ConPanqueque.T.Big
