import ConPanqueque.T.Intern
import ConPanqueque.V.ESort
import ConPanqueque.V.EConst
import ConPanqueque.V.EVar
import ConPanqueque.T.MemoRep
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
    ⟨hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internNodeE_sort s u
      (Nat.le_trans (tabAt_size_le hsr.e.p2) (hok.sepSort.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s2) (hok.sepSort.cap 1 (by decide)))
  right
  refine ⟨_, hr, (s.store.intern (.sort u)).2, { s with store := (s.store.intern (.sort u)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.sort u) s = _
    exact hrun
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun e => hok.kbMemo (.e mk) 0 (by decide) (by rw [KB0, ← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (by rw [← KB0]; exact hok.kbMdesc (.e mk) k 0 hk (by decide))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun e => hok.kbMemo (.n mk) 0 (by decide) (by rw [KB0, ← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (by rw [← KB0]; exact hok.kbMdesc (.n mk) k 0 hk (by decide))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun e => hok.kbMemo (.c mk) 0 (by decide) (by rw [KB0, ← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (by rw [← KB0]; exact hok.kbMdesc (.c mk) k 0 hk (by decide))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun e => hok.kbMemo (.m b mk) 0 (by decide) (by rw [KB0, ← e]; exact hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (by rw [← KB0]; exact hok.kbMdesc (.m b mk) k 0 hk (by decide))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun e => hok.kbMemo (envR b) 0 (by decide) (by rw [KB0, ← e]; exact hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (by rw [← KB0]; exact hok.kbMdesc (envR b) k 0 hk (by decide)))
        (fun i hi => hm _ (hok.envOut i hi) (by rw [← KB0]; exact hok.kbEnv i 0 hi (by decide))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (by rw [← KB0]; exact hok.kbHeap i 0 hi (by decide))) hd
        (by rw [hg]), (internNodeE_wf ht.sr.twf (viewOK_sort hv) hrun).1, envDen_ext ht.sr.envd (internNodeE_wf ht.sr.twf (viewOK_sort hv) hrun).2, cachesOK_ext ht.sr.cok (internNodeE_wf ht.sr.twf (viewOK_sort hv) hrun).2 rfl⟩

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
    ⟨hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internNodeE_const s n us
      (Nat.le_trans (tabAt_size_le hsr.e.p3) (hok.sepConst.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s3) (hok.sepConst.cap 1 (by decide)))
  right
  refine ⟨_, hr, (s.store.intern (.const n us)).2, { s with store := (s.store.intern (.const n us)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.const n us) s = _
    exact hrun
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun j hj e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (fun j hj => hok.kbMdesc (.c mk) k j hk (by omega))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun j hj e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (fun j hj => hok.kbMdesc (.m b mk) k j hk (by omega))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj => hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj => hok.kbEnv i j hi (by omega))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg]), (internNodeE_wf ht.sr.twf (viewOK_const hv) hrun).1, envDen_ext ht.sr.envd (internNodeE_wf ht.sr.twf (viewOK_const hv) hrun).2, cachesOK_ext ht.sr.cok (internNodeE_wf ht.sr.twf (viewOK_const hv) hrun).2 rfl⟩

def fInternFVar := ofString "internFVar"
def fvarLocals : List MlS := lEn :: fvarScratch

def fvarBody : ProgHOL 64 :=
  prologue fvarLocals (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv lEty))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (vv lIw))
    (.seq (.assign .local lEn (.op .add [.const 1, .cmp .notEqual (vv lIw) (.const 0)]))
      (eFVarWith (rRestE 10 (vv lEn) lFle)))))

theorem encFVar_small (idx : Nat) (ty : EIdx) (hi : idx < 2 ^ 64) :
    Enc.encFVar ⟨idx, ty⟩ = Enc.idxW ty :: (if idx = 0 then [] else [BitVec.ofNat 64 idx]) := by
  simp [Enc.encFVar, limbs_small idx hi]

theorem fvar_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState) (idx : Nat)
    (ty : EIdx) (hi : idx < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(lEty, Enc.idxW ty), (lIw, (UInt64.ofNat idx).toBitVec)]) fvarBody s
      (internFVarE idx ty) (PostE C) := by
  have hiw : (UInt64.ofNat idx).toBitVec = BitVec.ofNat 64 idx := rfl
  have hlen : (Enc.encFVar ⟨idx, ty⟩).length ≤ 2 := by rw [encFVar_small idx ty (by omega)]; split <;> simp
  have hlenW : (1 : BitVec 64) + (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (UInt64.ofNat idx).toBitVec 0 then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (Enc.encFVar ⟨idx, ty⟩).length := by
    rw [encFVar_small idx ty (by omega), hiw]
    by_cases h0 : idx = 0
    · subst h0; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : BitVec.ofNat 64 idx ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp [h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [fvarLocals, fvarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  refine specR_storeKB2I hok (vv lEty) (vv lIw) (Enc.idxW ty) (UInt64.ofNat idx).toBitVec rfl rfl rfl ?_
  refine specR_assignI lEn _ (BitVec.ofNat 64 (Enc.encFVar ⟨idx, ty⟩).length) (by decide)
    (by rw [← hlenW]; rfl) ?_
  intro t ht
  have hw : ∀ y, y ∈ fvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
  have hK : Words t C.KB (Enc.encFVar ⟨idx, ty⟩) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · have e0 : (Enc.encFVar ⟨idx, ty⟩)[0]'hj = Enc.idxW ty := by simp [Enc.encFVar]
      rw [e0]; exact ht.mem _ _ (by simp)
    · have h0 : idx ≠ 0 := by intro e; subst e; simp [Enc.encFVar, Enc.limbs] at hj
      have e1 : (Enc.encFVar ⟨idx, ty⟩)[1]'hj = BitVec.ofNat 64 idx := by
        simp only [encFVar_small idx ty (by omega), h0, ite_false]; rfl
      rw [e1, ← hiw]; exact ht.mem _ _ (by simp)
  rcases eInternFVar_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store idx ty hi ht.sr.rep
      (sepK_mono hok.sepFVar hlen) hK (by omega) hok.b0FVar hok.b1FVar (ht.env _ _ rfl) (ht.env _ _ rfl)
      (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    ⟨hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internNodeE_fvar s idx ty
      (Nat.le_trans (tabAt_size_le hsr.e.p1) (hok.sepFVar.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s1) (hok.sepFVar.cap 1 (by decide)))
  right
  refine ⟨_, hr, (s.store.intern (.fvar idx ty)).2, { s with store := (s.store.intern (.fvar idx ty)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.fvar idx ty) s = _
    exact hrun
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun j hj e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (fun j hj => hok.kbMdesc (.c mk) k j hk (by omega))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun j hj e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (fun j hj => hok.kbMdesc (.m b mk) k j hk (by omega))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj => hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj => hok.kbEnv i j hi (by omega))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg]), (internNodeE_wf ht.sr.twf (viewOK_fvar hv) hrun).1, envDen_ext ht.sr.envd (internNodeE_wf ht.sr.twf (viewOK_fvar hv) hrun).2, cachesOK_ext ht.sr.cok (internNodeE_wf ht.sr.twf (viewOK_fvar hv) hrun).2 rfl⟩

end ConPanqueque.T
