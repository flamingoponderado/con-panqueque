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


/-- The clears of a list of distinct regions: each emptied, memory outside all of them untouched. -/
theorem flush_core {C : Ctx} (hok : CtxOK C) (rest : ProgHOL 64) :
    ∀ (rs : List Region), (∀ r ∈ rs, r ∈ cacheRegions ++ memoRegions) → rs.Nodup →
    ∀ (t : PState σ), (∀ r ∈ rs, SomeAt t C r) → ∀ w0, t.locals.lookup lJ0 = some (.val (.word w0)) →
    Stop (evaluateHOLFiniteState t (flushCode C rs rest)).1 ∨
    ∃ t' : PState σ, evaluateHOLFiniteState t (flushCode C rs rest) = evaluateHOLFiniteState t' rest ∧
      (∀ r ∈ rs, EmptyAt t' C r) ∧ (∀ c, (∀ r ∈ rs, ¬ inR (C.mg r) c) → t'.memory c = t.memory c) ∧
      t'.memaddrs = t.memaddrs ∧ t'.globals = t.globals ∧ t'.code = t.code ∧
      (∀ y, y ≠ lJ0 → t'.locals.lookup y = t.locals.lookup y) ∧ ∃ w, t'.locals.lookup lJ0 = some (.val (.word w))
  | [], _, _, t, _, w0, hw0 => Or.inr ⟨t, rfl, fun _ h => by simp at h, fun _ _ => rfl, rfl, rfl, rfl,
      fun _ _ => rfl, w0, hw0⟩
  | r :: rs, hsub, hnd, t, hsome, w0, hw0 => by
    have hrn : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
    rcases clear_one hok t r (hsub r (by simp)) (hsome r (by simp)) (flushCode C rs rest) w0 hw0 with
      hs | ⟨t4, he4, hemp4, hout4, hd4, hg4, hc4, hl4, w4, hw4⟩
    · exact Or.inl hs
    have hsome4 : ∀ r' ∈ rs, SomeAt t4 C r' := fun r' hr' => by
      have hne : r' ≠ r := fun e => hrn (e ▸ hr')
      exact someAt_frame (hsome r' (by simp [hr'])) (fun c hc => hout4 c (hok.memoDis r' r c hne hc))
        (fun j hj => hout4 _ (hok.mdescMemo r r' j hj)) hd4
    rcases flush_core hok rest rs (fun r' hr' => hsub r' (by simp [hr'])) hnd' t4 hsome4 w4 hw4 with
      hs | ⟨t', he', hemp', hout', hd', hg', hc', hl', w', hw'⟩
    · left; show Stop (evaluateHOLFiniteState t (clearCode (C.mg r) (flushCode C rs rest))).1
      rw [he4]; exact hs
    refine Or.inr ⟨t', by show evaluateHOLFiniteState t (clearCode (C.mg r) (flushCode C rs rest)) = _; rw [he4, he'],
      fun r' hr' => ?_, fun c hc => ?_, hd'.trans hd4, hg'.trans hg4, hc'.trans hc4,
      fun y hy => (hl' y hy).trans (hl4 y hy), w', hw'⟩
    · rcases List.mem_cons.mp hr' with e | hr'
      · subst e
        refine emptyAt_frame hemp4 (fun c hc => hout' c (fun r'' hr'' hin => ?_))
          (fun j hj => hout' _ (fun r'' hr'' => hok.mdescMemo r'' r' j hj)) hd'
        have hne : r'' ≠ r' := fun e => hrn (e ▸ hr'')
        exact hok.memoDis r' r'' c (Ne.symm hne) hc hin
      · exact hemp' r' hr'
    · rw [hout' c (fun r' hr' => hc r' (by simp [hr'])), hout4 c (hc r (by simp))]


/-- The flush against a twin operation `op` taking `s` to `sF`; `hsr'` rebuilds `SR` at `sF` from the cleared
tables. -/
theorem specR_flushI {β : Type} {C : Ctx} (hok : CtxOK C) (rs : List Region)
    (hsub : ∀ r ∈ rs, r ∈ cacheRegions ++ memoRegions) (hnd : rs.Nodup) {s sF : AState}
    (hrep : ∀ u : PState σ, SR C s u → ∀ r ∈ rs, SomeAt u C r)
    (hsr' : ∀ u u' : PState σ, SR C s u → (∀ r ∈ rs, EmptyAt u' C r) →
      (∀ c, (∀ r ∈ rs, ¬ inR (C.mg r) c) → u'.memory c = u.memory c) → u'.memaddrs = u.memaddrs →
      u'.globals = u.globals → u'.code = u.code → SR C sF u')
    (op : AM Unit) (hop : op s = .ok ((), sF))
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (hj : lJ0 ∈ D)
    (hk : SpecR (Inv C sF (Γ.kill [lJ0]) [] D) rest sF (k ()) R) :
    SpecR (Inv C s Γ M D) (flushCode C rs rest) s (op >>= k) R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl lJ0 hj
  rcases flush_core hok rest rs hsub hnd t (hrep t ht.sr) w0 hw0 with
    hs | ⟨t', he, hemp, hout, hd, hg, hc, hl, hj'⟩
  · exact Or.inl hs
  rw [he]
  rcases hk t' (inv_after_clear ht (hsr' t t' ht.sr hemp hout hd hg hc) hl hj') with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← op s; match r with | (a, s) => k a s) = _
  rw [hop]; exact hk'


/-- The regions a flush clears: the caches' always, the memos' when `mem`. -/
def flushRegions (mem : Bool) : List Region := cacheRegions ++ (if mem then memoRegions else [])

/-- The twin's state after the flush. -/
def flushedS (mem : Bool) (s : AState) : AState :=
  { s with caches := Caches.empty, memos := if mem then Memos.empty else s.memos }

theorem flushRegions_sub (mem : Bool) : ∀ r ∈ flushRegions mem, r ∈ cacheRegions ++ memoRegions := by
  cases mem <;> simp [flushRegions] <;> exact fun r hr => Or.inl hr

theorem flushRegions_nodup (mem : Bool) : (flushRegions mem).Nodup := by
  cases mem <;> decide

theorem cachesOK_empty (s : AState) (hc : s.caches = Caches.empty) : CachesOK s := by
  refine ⟨fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_⟩ <;>
    rw [hc] at h <;> simp [Caches.empty] at h

theorem cachesOK_empty_old (s : AState) (cs : Caches) (hc : cs = Caches.empty) :
    CachesOK { s with caches := cs } := by
  subst hc
  exact ⟨fun _ _ h => by simp [Caches.empty] at h, fun _ _ h => by simp [Caches.empty] at h,
    fun _ _ h => by simp [Caches.empty] at h, fun _ _ h => by simp [Caches.empty] at h,
    fun _ _ h => by simp [Caches.empty] at h⟩

theorem memoSel_empty (k : MemoK) : memoSel k Memos.empty = ∅ := by cases k <;> rfl
theorem memoSelN_empty (k : MemoNK) : memoSelN k Memos.empty = ∅ := by cases k <;> rfl

/-- `SR` after the flush, on the plain side. -/
theorem sr_flushed {C : Ctx} (hok : CtxOK C) (hpl : C.saved = none) (mem : Bool) {s : AState} {u u' : PState σ}
    (hsr : SR C s u) (hemp : ∀ r ∈ flushRegions mem, EmptyAt u' C r)
    (hout : ∀ c, (∀ r ∈ flushRegions mem, ¬ inR (C.mg r) c) → u'.memory c = u.memory c)
    (hd : u'.memaddrs = u.memaddrs) (hg : u'.globals = u.globals) (hc : u'.code = u.code) :
    SR C (flushedS mem s) u' := by
  -- a region outside the flushed ones is framed
  have fr : ∀ (X : Region), (∀ r ∈ flushRegions mem, r ≠ X) → ∀ c, inR (C.mg X) c → u'.memory c = u.memory c :=
    fun X hX c hc => hout c (fun r hr hin => hok.memoDis X r c (Ne.symm (hX r hr)) hc hin)
  have frd : ∀ (X : Region) j, j < 8 → u'.memory (C.mG X + BitVec.ofNat 64 (8 * j)) =
      u.memory (C.mG X + BitVec.ofNat 64 (8 * j)) :=
    fun X j hj => hout _ (fun r hr => hok.mdescMemo r X j hj)
  refine ⟨srep_frame hsr.rep ⟨hout _ (fun r _ => hok.flMemo r _ (Or.inl rfl)),
      hout _ (fun r _ => hok.flMemo r _ (Or.inr (Or.inl rfl))),
      hout _ (fun r _ => hok.flMemo r _ (Or.inr (Or.inr (Or.inl rfl)))),
      hout _ (fun r _ => hok.flMemo r _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hout _ (fun r _ => hok.dirMemo r kk tier mm hk1 hk2 hm),
        fun c hc => hout c (fun r _ hin => hok.memoOut r c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩),
    by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll, by rw [hg]; exact hsr.gfls,
    by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd]; exact hsr.kbuf j hj, fun k => ?_, fun k => ?_, fun k => ?_, ?_,
    envAt_frame hsr.env (fun b c hc => fr (envR b) (by cases mem <;> cases b <;> decide) c hc)
      (fun b j hj => frd (envR b) j hj) (fun i hi => hout _ (fun r _ => hok.envMemo r i hi)) hd ⟨by rw [hg], by rw [hg]⟩,
    hsr.pins, heapEx_frame hsr.heap (fun i hi => hout _ (fun r _ => hok.heapMemo r i hi)) hd (by rw [hg]),
    hsr.twf, hsr.envd, hsr.floor, cachesOK_empty _ rfl⟩
  · -- the memos
    cases mem
    · exact memoAt_frame (hsr.memo k) (fr (.e k) (by cases k <;> decide)) (frd (.e k)) hd
    · show MemoAt u' _ _ (memoSel k Memos.empty)
      rw [memoSel_empty]
      exact hemp (.e k) (by cases k <;> decide)
  · cases mem
    · exact memoAtN_frame (hsr.memoN k) (fr (.n k) (by cases k <;> decide)) (frd (.n k)) hd
    · show MemoAtN u' _ _ (memoSelN k Memos.empty)
      rw [memoSelN_empty]
      exact hemp (.n k) (by cases k <;> decide)
  · -- the fixed caches
    cases k
    all_goals first
      | trivial
      | exact hemp (.c .constTy) (by cases mem <;> decide)
      | exact hemp (.c .constVal) (by cases mem <;> decide)
      | exact hemp (.c .ruleBody) (by cases mem <;> decide)
  · -- the mode memos (plain side)
    obtain ⟨hgeo, _, _⟩ := hsr.mode
    refine ⟨by rw [hg]; exact hgeo, ?_, ?_⟩
    · have hs : C.side = false := by simp [Ctx.side, hpl]
      rw [hs]
      intro k
      cases k
      all_goals first
        | trivial
        | exact hemp (.m false .whnfCore) (by cases mem <;> decide)
        | exact hemp (.m false .whnfCoreCheap) (by cases mem <;> decide)
        | exact hemp (.m false .whnf) (by cases mem <;> decide)
        | exact hemp (.m false .infer) (by cases mem <;> decide)
        | exact hemp (.m false .inferIO) (by cases mem <;> decide)
        | exact hemp (.m false .defeq) (by cases mem <;> decide)
    · rw [hpl]
      intro k
      cases k
      all_goals first
        | trivial
        | exact hemp (.m true .whnfCore) (by cases mem <;> decide)
        | exact hemp (.m true .whnfCoreCheap) (by cases mem <;> decide)
        | exact hemp (.m true .whnf) (by cases mem <;> decide)
        | exact hemp (.m true .infer) (by cases mem <;> decide)
        | exact hemp (.m true .inferIO) (by cases mem <;> decide)
        | exact hemp (.m true .defeq) (by cases mem <;> decide)


theorem someAt_of_sr {C : Ctx} (hpl : C.saved = none) {s : AState} {u : PState σ} (hsr : SR C s u) (r : Region) :
    SomeAt u C r := by
  cases r with
  | e k => exact ⟨_, hsr.memo k⟩
  | n k => exact ⟨_, hsr.memoN k⟩
  | c k => exact ⟨_, hsr.cache k⟩
  | m b k =>
    obtain ⟨_, h1, h2⟩ := hsr.mode
    have hs : C.side = false := by simp [Ctx.side, hpl]
    rw [hs] at h1; rw [hpl] at h2
    cases b
    · exact ⟨_, h1 k⟩
    · exact ⟨_, h2 k⟩
  | env => trivial
  | tbl => trivial

/-- **The flush** (plain side): the twin's flush `op` takes `s` to `flushedS mem s`. -/
theorem specR_flushTopI {β : Type} {C : Ctx} (hok : CtxOK C) (hpl : C.saved = none) (mem : Bool) {s : AState}
    (op : AM Unit) (hop : op s = .ok ((), flushedS mem s))
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (hj : lJ0 ∈ D)
    (hk : SpecR (Inv C (flushedS mem s) (Γ.kill [lJ0]) [] D) rest (flushedS mem s) (k ()) R) :
    SpecR (Inv C s Γ M D) (flushCode C (flushRegions mem) rest) s (op >>= k) R :=
  specR_flushI hok (flushRegions mem) (flushRegions_sub mem) (flushRegions_nodup mem)
    (fun u hu r _ => someAt_of_sr hpl hu r)
    (fun u u' hsr hemp hout hd hg hc => sr_flushed hok hpl mem hsr hemp hout hd hg hc) op hop hj hk

end

end ConPanqueque.T.Decl
