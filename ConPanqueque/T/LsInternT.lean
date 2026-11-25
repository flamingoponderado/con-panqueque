import ConPanqueque.T.LIntern
import ConPanqueque.T.Heap
import ConPanqueque.T.Blk
import ConPanqueque.V.LsIntern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Interning a level list over the invariant

The key is a block of handle words in the heap. The procedure may touch the key words, so afterwards
the context's image is cut back to a prefix that ends before the block.
-/

namespace ConPanqueque.T

def LsCap (lss : LsStore) (v : LsNodeView) : Prop :=
  lss.find? v = none → (if lss.scratchOn then lss.scr.sizeOf v else lss.pers.sizeOf v) < Idx.idxCap

theorem LsTables.sizeOf_push_self (t : LsTables) (v : LsNodeView) (d : LDer) (tr : UInt32) :
    (t.push v d tr).1.sizeOf v = t.sizeOf v + 1 := by
  simp [LsTables.push, LsTables.sizeOf, Tbl.size, Tbl.push]

theorem lscap_of (lss : LsStore) (v : LsNodeView)
    (hP : lss.scratchOn = false → (lss.intern v).1.pers.sizeOf v ≤ 2 ^ 26)
    (hS : lss.scratchOn = true → (lss.intern v).1.scr.sizeOf v ≤ 2 ^ 26) : LsCap lss v := by
  intro hf
  unfold LsStore.find? at hf
  cases hp : lss.pers.find? v with
  | some i => rw [hp] at hf; simp at hf
  | none =>
    rw [hp] at hf
    cases hon : lss.scratchOn with
    | true =>
      rw [hon] at hf; simp only [ite_true] at hf
      have h := hS hon
      simp only [LsStore.intern, hp, hon, hf, ite_true] at h
      rw [LsTables.sizeOf_push_self] at h
      simp only [ite_true, Idx.idxCap]; omega
    | false =>
      have h := hP hon
      simp only [LsStore.intern, hp, hon, Bool.false_eq_true, ite_false] at h
      rw [LsTables.sizeOf_push_self] at h
      simp only [Bool.false_eq_true, ite_false, Idx.idxCap]; omega

theorem LsStore.intern_of_find' {st : LsStore} {v : LsNodeView} {h : LsIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  simp only [LsStore.find?] at hf
  simp only [LsStore.intern]
  split at hf
  · simp only [Option.some.injEq] at hf; rw [hf]
  · split at hf
    · rename_i hon
      rw [ite_eq_left hon]
      cases hs : st.scr.find? v with
      | some i => simp only [hs, Option.some.injEq] at hf; rw [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp at hf

theorem internLsNode_ok (s : AState) (v : LsNodeView) (hcap : LsCap s.store.lss v) :
    internLsNode v s = .ok ((s.store.lss.intern v).2, { s with store := withLs s.store (s.store.lss.intern v).1 }) := by
  unfold internLsNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure]
  cases hf : s.store.lss.find? v with
  | some h =>
    simp only [hf]
    rw [LsStore.intern_of_find' hf]; rfl
  | none =>
    simp only [hf, ite_eq_left (hcap hf)]
    rfl

def pKey := ofString "lskey"
def fInternLs := ofString "internLs"
def internLsBody : ProgHOL 64 :=
  prologue lsScratch (.seq (.assign .local lKb (vv pKey)) (lsInternWith (rRestE 8 (vv lEc) lFls)))

theorem cellA_off (C : Ctx) (o k : Nat) : cellA C o + BitVec.ofNat 64 (8 * k) = cellA C (o + k) := by
  simp only [cellA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem cellA_ne (C : Ctx) (i j : Nat) (hi : i < C.HN) (hj : j < C.HN) (hlay : C.HB.toNat + 8 * (C.HN + 2) < 2 ^ 64)
    (h : i ≠ j) : cellA C i ≠ cellA C j := by
  intro e
  have := congrArg BitVec.toNat e
  simp [cellA, BitVec.toNat_add] at this
  omega

variable {σ : Type}

def PostLs (C : Ctx) (h : LsIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = Enc.idxW h ∧ SR C s' st

theorem postLs_locals (C : Ctx) : ∀ (a : LsIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLs C a w s' st → PostLs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

theorem heapEx_prefix {t : PState σ} {HB : BitVec 64} {HN : Nat} {H H0 : List (BitVec 64)} (h : HeapEx t HB HN H)
    (hp : H0 <+: H) : HeapEx t HB HN H0 := let ⟨H', hp', ha⟩ := h; ⟨H', hp.trans hp', ha⟩

theorem internLs_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (hs : List LIdx) (o : Nat) (H0 : List (BitVec 64)) (hp0 : H0 <+: C.H) (ho0 : H0.length ≤ o)
    (hko : o + hs.length ≤ C.H.length) (hlen : hs.length < 2 ^ 60)
    (hkey : ∀ j (hj : j < hs.length), C.H[o + j]? = some (Enc.idxW hs[j])) :
    SpecR (Pre (σ := σ) C s [(pKey, cellA C o), (lEc, BitVec.ofNat 64 hs.length)]) internLsBody s (internLsNode hs)
      (PostLs (ctxH C H0)) := by
  refine specR_prologue (postLs_locals _) (fun x hx => ?_) ?_
  · simp only [lsScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hHN : C.H.length ≤ C.HN := inv_heapLen ht
  have hlay := hok.heapLay
  obtain ⟨wk, hwk⟩ := ht.decl lKb (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lKb _ (cellA C o) wk (inv_ev ht (by simp +decide [ctxEnv])) hwk)]
  let t1 := setVarHOLFinite lKb (.val (.word (cellA C o))) t
  have hw : ∀ y, y ∈ lsScratch → ∃ w, t1.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    obtain ⟨w, hw⟩ := ht.decl y (List.mem_append_right _ hy)
    have hne : y ≠ lKb := by
      simp only [lsScratch, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact ⟨w, by simp only [t1]; rw [lookup_setVar_other _ _ hne]; exact hw⟩
  have hW : Words t1 (cellA C o) (hs.map Enc.idxW) := by
    intro k hk
    simp only [List.length_map] at hk
    have hk' : o + k < C.H.length := by omega
    have := heap_cell ht.sr (o + k) hk'
    have e := hkey k hk
    rw [List.getElem?_eq_getElem hk'] at e
    simp only [Option.some.injEq] at e
    rw [cellA_off, List.getElem_map]
    exact ⟨this.1, by rw [← e]; exact this.2⟩
  have hS : SepK C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) hs.length 8 := by
    have S := hok.sepLs
    refine ⟨S.pow, S.cap, S.dis, S.oth, fun k' tier m h1 h2 h3 => ⟨(S.dsc k' tier m h1 h2 h3).1,
      (S.dsc k' tier m h1 h2 h3).2.1, fun j hj => ?_⟩, fun F hF => ⟨(S.fls F hF).1, (S.fls F hF).2.1, fun j hj => ?_⟩,
      fun j k' tier hj h1 h2 => ?_⟩
    · rw [cellA_off]; exact fun e => hok.dirHeap (o + j) k' tier m (by omega) h1 h2 h3 e.symm
    · rw [cellA_off]; exact fun e => hok.flHeap (o + j) F (by omega) hF e.symm
    · rw [cellA_off]; exact fun hr => hok.heapOut (o + j) (by omega) ⟨k', tier, h1, h2, hr⟩
  rcases lsIntern_spec ra t1 C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) s.store hs (sr_of_eq (u := t1) ht.sr rfl rfl rfl rfl).rep hS hW hlen hok.b0Ls hok.b1Ls
      (lookup_setVar_same _ _ _) (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact ht.env _ _ rfl)
      (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact ht.env _ _ rfl)
      (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact ht.env _ _ rfl)
      (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact ht.env _ _ rfl) hw with
    ⟨hs' | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs'
  have hv := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hrun := internLsNode_ok s hs (lscap_of _ _ (fun _ => Nat.le_trans (tabAt_size_le hsr.ls.pl) (hok.sepLs.cap 0 (by decide)))
    (fun _ => Nat.le_trans (tabAt_size_le hsr.ls.sl) (hok.sepLs.cap 1 (by decide))))
  right
  have keyne : ∀ c, (∃ i, i < C.HN ∧ c = C.HB + BitVec.ofNat 64 (8 * i) ∧ (i < o ∨ o + hs.length ≤ i)) →
      ∀ j, j < hs.length → c ≠ cellA C o + BitVec.ofNat 64 (8 * j) := by
    rintro c ⟨i, hi, rfl, hio⟩ j hj
    rw [cellA_off]
    exact cellA_ne C i (o + j) hi (by omega) hlay (by omega)
  refine ⟨_, hr, (s.store.lss.intern hs).2, { s with store := withLs s.store (s.store.lss.intern hs).1 }, ?_, rfl, ?_⟩
  · exact hrun
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.heapMemo (.e mk) (o + j) (by omega)
          (by rw [cellA_off] at e; unfold cellA at e; rw [← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj e => hok.mdescHeap (.e mk) (o + j) k (by omega) hk
          (by rw [cellA_off] at e; unfold cellA at e; exact e.symm))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.heapMemo (.n mk) (o + j) (by omega)
          (by rw [cellA_off] at e; unfold cellA at e; rw [← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj e => hok.mdescHeap (.n mk) (o + j) k (by omega) hk
          (by rw [cellA_off] at e; unfold cellA at e; exact e.symm))) hd,
      fun ck => cacheAt_frame (ht.sr.cache ck)
        (fun c hc => hm c (hok.memoOut (.c ck) c hc) (fun j hj e => hok.heapMemo (.c ck) (o + j) (by omega)
          (by rw [cellA_off] at e; unfold cellA at e; rw [← e]; exact hc)))
        (fun k hk => hm _ (hok.mdescOut (.c ck) k hk) (fun j hj e => hok.mdescHeap (.c ck) (o + j) k (by omega) hk
          (by rw [cellA_off] at e; unfold cellA at e; exact e.symm))) hd,
      modeAt_frame ht.sr.mode
        (fun b ck c hc => hm c (hok.memoOut (.m b ck) c hc) (fun j hj e => hok.heapMemo (.m b ck) (o + j) (by omega)
          (by rw [cellA_off] at e; unfold cellA at e; rw [← e]; exact hc)))
        (fun b ck k hk => hm _ (hok.mdescOut (.m b ck) k hk) (fun j hj e => hok.mdescHeap (.m b ck) (o + j) k (by omega) hk
          (by rw [cellA_off] at e; unfold cellA at e; exact e.symm))) hd (by rw [hg]; rfl),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.heapMemo (envR b) (o + j) (by omega)
          (by rw [cellA_off] at e; unfold cellA at e; rw [← e]; exact hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj e => hok.mdescHeap (envR b) (o + j) k (by omega) hk
          (by rw [cellA_off] at e; unfold cellA at e; exact e.symm)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj e => hok.heapEnv (o + j) i (by omega) hi
          (by rw [cellA_off] at e; unfold cellA at e; exact e.symm))) hd ⟨by rw [hg]; rfl, by rw [hg]; rfl⟩, ht.sr.pins,
      heapEx_reframe (heapEx_prefix ht.sr.heap hp0)
        (fun i hi => by
          have hi' : i < H0.length := hi
          have := hp0.length_le
          exact hm _ (hok.heapOut i (by omega)) (keyne _ ⟨i, by omega, rfl, Or.inl (by omega)⟩)) hd (by rw [hg]; rfl),
      (internLsNode_wf ht.sr.twf hv hrun).1, envDen_ext ht.sr.envd (internLsNode_wf ht.sr.twf hv hrun).2, Ext.trans ht.sr.floor (internLsNode_wf ht.sr.twf hv hrun).2, cachesOK_ext ht.sr.cok (internLsNode_wf ht.sr.twf hv hrun).2 rfl⟩

end ConPanqueque.T
