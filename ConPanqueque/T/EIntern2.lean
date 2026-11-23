import ConPanqueque.T.Intern
import ConPanqueque.V.ESort
import ConPanqueque.V.EConst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-! # Interning `sort` and `const` nodes over the invariant -/

namespace ConPanqueque.T

variable {σ : Type}

def fInternSort := ofString "internSort"
def sortBody : ProgHOL 64 := prologue sortScratch eInternSort

theorem sort_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState) (u : LIdx) :
    SpecR (Pre (σ := σ) C s [(lEu, Enc.idxW u)]) sortBody s (internSortE u) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [sortScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ sortScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  have KB0 : C.KB + BitVec.ofNat 64 (8 * 0) = C.KB := by simp
  rcases eInternSort_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store u ht.sr.rep hok.sepSort
      (by simpa using ht.sr.kbuf 0 (by decide)) hok.b0Sort hok.b1Sort (ht.env _ _ rfl) (ht.env _ _ rfl)
      (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.sort u)).2, { s with store := (s.store.intern (.sort u)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.sort u) s = _
    exact internNodeE_sort s u
      (Nat.le_trans (tabAt_size_le hsr.e.p2) (hok.sepSort.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s2) (hok.sepSort.cap 1 (by decide)))
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun e => hok.kbMemo (.e mk) 0 (by decide) (by rw [KB0, ← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (by rw [← KB0]; exact hok.kbMdesc (.e mk) k 0 hk (by decide))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun e => hok.kbMemo (.n mk) 0 (by decide) (by rw [KB0, ← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (by rw [← KB0]; exact hok.kbMdesc (.n mk) k 0 hk (by decide))) hd,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (by rw [← KB0]; exact hok.kbHeap i 0 hi (by decide))) hd
        (by rw [hg])⟩

def fInternConst := ofString "internConst"
def constBody : ProgHOL 64 := prologue constScratch eInternConst

theorem const_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState) (n : NIdx)
    (us : LsIdx) :
    SpecR (Pre (σ := σ) C s [(lEn, Enc.idxW n), (lEus, Enc.idxW us)]) constBody s (internConstE n us) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [constScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ constScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases eInternConst_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store n us ht.sr.rep hok.sepConst
      ⟨by simpa using ht.sr.kbuf 0 (by decide), by simpa using ht.sr.kbuf 1 (by decide)⟩ (kb_ne_kb8 C.KB)
      hok.b0Const hok.b1Const (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl)
      (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.const n us)).2, { s with store := (s.store.intern (.const n us)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.const n us) s = _
    exact internNodeE_const s n us
      (Nat.le_trans (tabAt_size_le hsr.e.p3) (hok.sepConst.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s3) (hok.sepConst.cap 1 (by decide)))
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg])⟩

end ConPanqueque.T
