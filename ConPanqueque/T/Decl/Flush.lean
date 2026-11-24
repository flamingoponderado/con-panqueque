import ConPanqueque.T.Decl.Flags
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Flushing the caches (and the memos)

`checkDeclStep` flushes the per-declaration caches and starts from empty memos; `checkDecl` flushes the caches
again after the declaration's own checks. The port clears each mirrored table (`clearCode`) in turn: after a
list of regions, those hold the empty table and memory outside them is as it was.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- Clear the tables of regions `rs` in turn. -/
def flushCode (C : Ctx) : List Region → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | r :: rs, rest => clearCode (C.mg r) (flushCode C rs rest)

/-- The regions the port mirrors a table in (the side's mode memos, the eager ones, the fixed caches). -/
def cacheRegions : List Region :=
  [.c .constTy, .c .constVal, .c .ruleBody,
   .m false .whnfCore, .m false .whnfCoreCheap, .m false .whnf, .m false .infer, .m false .inferIO, .m false .defeq,
   .m true .whnfCore, .m true .whnfCoreCheap, .m true .whnf, .m true .infer, .m true .inferIO, .m true .defeq]

def memoRegions : List Region :=
  [.e .inst1, .e .instL, .e .lift, .e .abs1, .e .inst1L, .e .instLP, .n .bvarB, .n .fvarB]

section
variable {σ : Type}

/-- Region `r` holds the empty table. -/
def EmptyAt (t : PState σ) (C : Ctx) : Region → Prop
  | .e k => MemoAt t (C.mG (.e k)) (C.mg (.e k)) ∅
  | .n k => MemoAtN t (C.mG (.n k)) (C.mg (.n k)) ∅
  | .c k => CacheAt t C Caches.empty k
  | .m b k => CacheAtM t C b ModeMemos.empty k
  | .env | .tbl => True

/-- Region `r` holds some table of its kind (what `clearCode` needs). -/
def SomeAt (t : PState σ) (C : Ctx) : Region → Prop
  | .e k => ∃ m, MemoAt t (C.mG (.e k)) (C.mg (.e k)) m
  | .n k => ∃ m, MemoAtN t (C.mG (.n k)) (C.mg (.n k)) m
  | .c k => ∃ cs, CacheAt t C cs k
  | .m b k => ∃ mm, CacheAtM t C b mm k
  | .env | .tbl => True

theorem someAt_frame {C : Ctx} {t u : PState σ} {r : Region} (h : SomeAt t C r)
    (hm : ∀ c, inR (C.mg r) c → u.memory c = t.memory c)
    (hdsc : ∀ j, j < 8 → u.memory (C.mG r + BitVec.ofNat 64 (8 * j)) = t.memory (C.mG r + BitVec.ofNat 64 (8 * j)))
    (hd : u.memaddrs = t.memaddrs) : SomeAt u C r := by
  cases r with
  | e k => obtain ⟨m, hm'⟩ := h; exact ⟨m, memoAtG_frame hm' hm hdsc hd⟩
  | n k => obtain ⟨m, hm'⟩ := h; exact ⟨m, memoAtN_frame hm' hm hdsc hd⟩
  | c k => obtain ⟨cs, hc⟩ := h; exact ⟨cs, cacheAt_frame hc hm hdsc hd⟩
  | m b k =>
    obtain ⟨mm, hc⟩ := h
    refine ⟨mm, ?_⟩
    cases k <;> first | trivial | exact memoAtG_frame hc hm hdsc hd
  | env => trivial
  | tbl => trivial

theorem emptyAt_frame {C : Ctx} {t u : PState σ} {r : Region} (h : EmptyAt t C r)
    (hm : ∀ c, inR (C.mg r) c → u.memory c = t.memory c)
    (hdsc : ∀ j, j < 8 → u.memory (C.mG r + BitVec.ofNat 64 (8 * j)) = t.memory (C.mG r + BitVec.ofNat 64 (8 * j)))
    (hd : u.memaddrs = t.memaddrs) : EmptyAt u C r := by
  cases r with
  | e k => exact memoAtG_frame h hm hdsc hd
  | n k => exact memoAtN_frame h hm hdsc hd
  | c k => exact cacheAt_frame h hm hdsc hd
  | m b k => cases k <;> first | trivial | exact memoAtG_frame h hm hdsc hd
  | env => trivial
  | tbl => trivial

/-- One clear: region `r`'s table emptied, memory outside it and its descriptor untouched. -/
theorem clear_one {C : Ctx} (hok : CtxOK C) (t : PState σ) (r : Region) (hcl : r ∈ cacheRegions ++ memoRegions)
    (hr : SomeAt t C r) (rest : ProgHOL 64)
    (w0 : BitVec 64) (hw0 : t.locals.lookup lJ0 = some (.val (.word w0))) :
    Stop (evaluateHOLFiniteState t (clearCode (C.mg r) rest)).1 ∨
    ∃ t4 : PState σ, evaluateHOLFiniteState t (clearCode (C.mg r) rest) = evaluateHOLFiniteState t4 rest ∧
      EmptyAt t4 C r ∧ (∀ c, ¬ inR (C.mg r) c → t4.memory c = t.memory c) ∧
      t4.memaddrs = t.memaddrs ∧ t4.globals = t.globals ∧ t4.code = t.code ∧
      (∀ y, y ≠ lJ0 → t4.locals.lookup y = t.locals.lookup y) ∧ ∃ w, t4.locals.lookup lJ0 = some (.val (.word w)) := by
  have hG := fun j (hj : j < 8) => hok.mdescMemo r r j hj
  cases r with
  | e k =>
    obtain ⟨m, hm⟩ := hr
    rcases clearCode_core t _ _ m hm rest w0 hw0 hG with hs | ⟨t4, he, hmem, rest'⟩
    · exact Or.inl hs
    · exact Or.inr ⟨t4, he, hmem, rest'⟩
  | n k =>
    obtain ⟨m, hm⟩ := hr
    rcases clearCode_core t _ _ m hm.1 rest w0 hw0 hG with hs | ⟨t4, he, hmem, rest'⟩
    · exact Or.inl hs
    · exact Or.inr ⟨t4, he, ⟨hmem, fun _ _ h => by simp at h⟩, rest'⟩
  | c k =>
    obtain ⟨cs, hc⟩ := hr
    cases k
    all_goals first
      | (rcases clearCode_core t _ _ _ hc rest w0 hw0 hG with hs | ⟨t4, he, hmem, rest'⟩
         · exact Or.inl hs
         · exact Or.inr ⟨t4, he, hmem, rest'⟩)
      | (exfalso; simp [cacheRegions, memoRegions] at hcl)
  | m b k =>
    obtain ⟨mm, hc⟩ := hr
    cases k
    all_goals first
      | (rcases clearCode_core t _ _ _ hc rest w0 hw0 hG with hs | ⟨t4, he, hmem, rest'⟩
         · exact Or.inl hs
         · exact Or.inr ⟨t4, he, hmem, rest'⟩)
      | (exfalso; cases b <;> simp [cacheRegions, memoRegions] at hcl)
  | env => exfalso; simp [cacheRegions, memoRegions] at hcl
  | tbl => exfalso; simp [cacheRegions, memoRegions] at hcl

end

end ConPanqueque.T.Decl
