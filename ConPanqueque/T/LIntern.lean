import ConPanqueque.T.Intern
import ConPanqueque.V.LBin
import ConPanqueque.V.LParam
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Interning level nodes, over the invariant

One Pancake function per level constructor, wrapping the `V` procedures; each refines the twin's
`internLNode` at that view.
-/

namespace ConPanqueque.T

/-- `internLNode`'s capacity test passes (or the probe hits). -/
def LCap (ls : LStore) (v : LNodeView) : Prop :=
  ls.find? v = none → (if ls.scratchOn then ls.scr.sizeOf v else ls.pers.sizeOf v) < Idx.idxCap

theorem LTables.sizeOf_push_self (t : LTables) (v : LNodeView) (d : LDer) (tr : UInt32) :
    (t.push v d tr).1.sizeOf v = t.sizeOf v + 1 := by
  cases v <;> simp [LTables.push, LTables.sizeOf, Tbl.size, Tbl.push] <;> split <;> simp

theorem lcap_of (ls : LStore) (v : LNodeView)
    (hP : ls.scratchOn = false → (ls.intern v).1.pers.sizeOf v ≤ 2 ^ 26)
    (hS : ls.scratchOn = true → (ls.intern v).1.scr.sizeOf v ≤ 2 ^ 26) : LCap ls v := by
  intro hf
  unfold LStore.find? at hf
  cases hp : ls.pers.find? v with
  | some i => rw [hp] at hf; simp at hf
  | none =>
    rw [hp] at hf
    cases hon : ls.scratchOn with
    | true =>
      rw [hon] at hf; simp only [ite_true] at hf
      have h := hS hon
      simp only [LStore.intern, hp, hon, hf, ite_true] at h
      rw [LTables.sizeOf_push_self] at h
      simp only [ite_true, Idx.idxCap]; omega
    | false =>
      have h := hP hon
      simp only [LStore.intern, hp, hon, Bool.false_eq_true, ite_false] at h
      rw [LTables.sizeOf_push_self] at h
      simp only [Bool.false_eq_true, ite_false, Idx.idxCap]; omega

theorem LStore.intern_of_find' {st : LStore} {v : LNodeView} {h : LIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  simp only [LStore.find?] at hf
  simp only [LStore.intern]
  split at hf
  · simp only [Option.some.injEq] at hf; rw [hf]
  · split at hf
    · rename_i hon
      rw [if_pos hon]
      cases hs : st.scr.find? v with
      | some i => simp only [hs, Option.some.injEq] at hf; rw [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp at hf

theorem internLNode_ok (s : AState) (v : LNodeView) (hcap : LCap s.store.ls v) :
    internLNode v s = .ok ((s.store.ls.intern v).2, { s with store := withL s.store (s.store.ls.intern v).1 }) := by
  unfold internLNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure]
  cases hf : s.store.ls.find? v with
  | some h =>
    simp only [hf]
    rw [LStore.intern_of_find' hf]; rfl
  | none =>
    simp only [hf, if_pos (hcap hf)]
    rfl

variable {σ : Type}

/-- The post of a level-building call: the handle, and the new state represented. -/
def PostL (C : Ctx) (h : LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = Enc.idxW h ∧ SR C s' st

theorem postL_locals (C : Ctx) : ∀ (a : LIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostL C a w s' st → PostL C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

def fInternLParam := ofString "internLParam"
def internLParamBody : ProgHOL 64 := prologue paramScratch (lParamWith (rRest 7 1 lFll))

theorem internLParam_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (n : NIdx) :
    SpecR (Pre (σ := σ) C s [(lEn, Enc.idxW n)]) internLParamBody s (internLNode (.param n)) (PostL C) := by
  refine specR_prologue (postL_locals C) (fun x hx => ?_) ?_
  · simp only [paramScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ paramScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases lInternParam_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store n ht.sr.rep hok.sepLP
      (by simpa using ht.sr.kbuf 0 (by decide)) hok.b0LP hok.b1LP (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl)
      (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    ⟨hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internLNode_ok s (.param n) (lcap_of _ _ (fun _ => Nat.le_trans (tabAt_size_le hsr.l.pp) (hok.sepLP.cap 0 (by decide))) (fun _ => Nat.le_trans (tabAt_size_le hsr.l.sp) (hok.sepLP.cap 1 (by decide))))
  right
  refine ⟨_, hr, (s.store.ls.intern (.param n)).2, { s with store := withL s.store (s.store.ls.intern (.param n)).1 },
    ?_, rfl, ?_⟩
  · exact hrun
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
        (by rw [hg]), (internLNode_wf ht.sr.twf (lviewOK_param hv) hrun).1, envDen_ext ht.sr.envd (internLNode_wf ht.sr.twf (lviewOK_param hv) hrun).2, Ext.trans ht.sr.floor (internLNode_wf ht.sr.twf (lviewOK_param hv) hrun).2, cachesOK_ext ht.sr.cok (internLNode_wf ht.sr.twf (lviewOK_param hv) hrun).2 rfl⟩

def fInternLZero := ofString "internLZero"
def internLZeroBody : ProgHOL 64 := prologue zeroScratch (lZeroWith (rRest 3 0 lFll))

theorem internLZero_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
     :
    SpecR (Pre (σ := σ) C s []) internLZeroBody s (internLNode (.zero)) (PostL C) := by
  refine specR_prologue (postL_locals C) (fun x hx => ?_) ?_
  · simp only [zeroScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ zeroScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases lInternZero_spec t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store ht.sr.rep hok.sepLZ hok.b0LZ hok.b1LZ
      (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  have hrun := internLNode_ok s (.zero) (lcap_of _ _ (fun _ => Nat.le_trans (tabAt_size_le hsr.l.pz) (hok.sepLZ.cap 0 (by decide))) (fun _ => Nat.le_trans (tabAt_size_le hsr.l.sz) (hok.sepLZ.cap 1 (by decide))))
  right
  refine ⟨_, hr, (s.store.ls.intern (.zero)).2, { s with store := withL s.store (s.store.ls.intern (.zero)).1 },
    ?_, rfl, ?_⟩
  · exact hrun
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
        (by rw [hg]), (internLNode_wf ht.sr.twf (lviewOK_zero) hrun).1, envDen_ext ht.sr.envd (internLNode_wf ht.sr.twf (lviewOK_zero) hrun).2, Ext.trans ht.sr.floor (internLNode_wf ht.sr.twf (lviewOK_zero) hrun).2, cachesOK_ext ht.sr.cok (internLNode_wf ht.sr.twf (lviewOK_zero) hrun).2 rfl⟩

def fInternLSucc := ofString "internLSucc"
def internLSuccBody : ProgHOL 64 := prologue succScratch (lSuccWith (rRest 4 1 lFll))

theorem internLSucc_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (u : LIdx) :
    SpecR (Pre (σ := σ) C s [(lEu, Enc.idxW u)]) internLSuccBody s (internLNode (.succ u)) (PostL C) := by
  refine specR_prologue (postL_locals C) (fun x hx => ?_) ?_
  · simp only [succScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ succScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases lInternSucc_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store u ht.sr.rep hok.sepLS
      (by simpa using ht.sr.kbuf 0 (by decide)) hok.b0LS hok.b1LS (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    ⟨hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internLNode_ok s (.succ u) (lcap_of _ _ (fun _ => Nat.le_trans (tabAt_size_le hsr.l.ps) (hok.sepLS.cap 0 (by decide))) (fun _ => Nat.le_trans (tabAt_size_le hsr.l.ss) (hok.sepLS.cap 1 (by decide))))
  right
  refine ⟨_, hr, (s.store.ls.intern (.succ u)).2, { s with store := withL s.store (s.store.ls.intern (.succ u)).1 },
    ?_, rfl, ?_⟩
  · exact hrun
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
        (by rw [hg]), (internLNode_wf ht.sr.twf (lviewOK_succ hv) hrun).1, envDen_ext ht.sr.envd (internLNode_wf ht.sr.twf (lviewOK_succ hv) hrun).2, Ext.trans ht.sr.floor (internLNode_wf ht.sr.twf (lviewOK_succ hv) hrun).2, cachesOK_ext ht.sr.cok (internLNode_wf ht.sr.twf (lviewOK_succ hv) hrun).2 rfl⟩

def fInternLMax := ofString "internLMax"
def internLMaxBody : ProgHOL 64 := prologue lbin2Scratch (lBin2With maxHashE (rRest 5 2 lFll))

theorem internLMax_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (u v : LIdx) :
    SpecR (Pre (σ := σ) C s [(lEu, Enc.idxW u), (lEv, Enc.idxW v)]) internLMaxBody s (internLNode (.max u v)) (PostL C) := by
  refine specR_prologue (postL_locals C) (fun x hx => ?_) ?_
  · simp only [lbin2Scratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ lbin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases lInternMax_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store u v ht.sr.rep hok.sepLM
      ⟨by simpa using ht.sr.kbuf 0 (by decide), by simpa using ht.sr.kbuf 1 (by decide)⟩ (kb_ne_kb8 C.KB)
      hok.b0LM hok.b1LM (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    ⟨hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internLNode_ok s (.max u v) (lcap_of _ _ (fun _ => Nat.le_trans (tabAt_size_le hsr.l.pm) (hok.sepLM.cap 0 (by decide))) (fun _ => Nat.le_trans (tabAt_size_le hsr.l.sm) (hok.sepLM.cap 1 (by decide))))
  right
  refine ⟨_, hr, (s.store.ls.intern (.max u v)).2, { s with store := withL s.store (s.store.ls.intern (.max u v)).1 },
    ?_, rfl, ?_⟩
  · exact hrun
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
        (by rw [hg]), (internLNode_wf ht.sr.twf (lviewOK_max hv) hrun).1, envDen_ext ht.sr.envd (internLNode_wf ht.sr.twf (lviewOK_max hv) hrun).2, Ext.trans ht.sr.floor (internLNode_wf ht.sr.twf (lviewOK_max hv) hrun).2, cachesOK_ext ht.sr.cok (internLNode_wf ht.sr.twf (lviewOK_max hv) hrun).2 rfl⟩

def fInternLImax := ofString "internLImax"
def internLImaxBody : ProgHOL 64 := prologue lbin2Scratch (lBin2With imaxHashE (rRest 6 2 lFll))

theorem internLImax_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (u v : LIdx) :
    SpecR (Pre (σ := σ) C s [(lEu, Enc.idxW u), (lEv, Enc.idxW v)]) internLImaxBody s (internLNode (.imax u v)) (PostL C) := by
  refine specR_prologue (postL_locals C) (fun x hx => ?_) ?_
  · simp only [lbin2Scratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ lbin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases lInternImax_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store u v ht.sr.rep hok.sepLI
      ⟨by simpa using ht.sr.kbuf 0 (by decide), by simpa using ht.sr.kbuf 1 (by decide)⟩ (kb_ne_kb8 C.KB)
      hok.b0LI hok.b1LI (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    ⟨hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internLNode_ok s (.imax u v) (lcap_of _ _ (fun _ => Nat.le_trans (tabAt_size_le hsr.l.pi) (hok.sepLI.cap 0 (by decide))) (fun _ => Nat.le_trans (tabAt_size_le hsr.l.si) (hok.sepLI.cap 1 (by decide))))
  right
  refine ⟨_, hr, (s.store.ls.intern (.imax u v)).2, { s with store := withL s.store (s.store.ls.intern (.imax u v)).1 },
    ?_, rfl, ?_⟩
  · exact hrun
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
        (by rw [hg]), (internLNode_wf ht.sr.twf (lviewOK_imax hv) hrun).1, envDen_ext ht.sr.envd (internLNode_wf ht.sr.twf (lviewOK_imax hv) hrun).2, Ext.trans ht.sr.floor (internLNode_wf ht.sr.twf (lviewOK_imax hv) hrun).2, cachesOK_ext ht.sr.cok (internLNode_wf ht.sr.twf (lviewOK_imax hv) hrun).2 rfl⟩

end ConPanqueque.T
