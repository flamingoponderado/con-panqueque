import ConPanqueque.Front.NameTwin
import ConPanqueque.T.LsInternT

/-! # Interning a name node: the Pancake side

`nameStrBody` wraps the ported `nInternStr` with its key in heap cells from `o`: the prefix
handle, then the string's bytes, one per word (`Enc.encStr`).  The key's separation from the stores
is the frontend's own context fact `FrontOK` (kept out of `CtxOK`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T

variable {σ : Type}

/-- The frontend's layout facts: the name tables' separation and bases. -/
structure FrontOK (C : Ctx) : Prop where
  sepNS : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 0 1
  b0NS : C.L.base 1 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.str.toUInt64.toBitVec * 67108864
  b1NS : C.L.base 1 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.str.toUInt64.toBitVec * 67108864
  sepNN : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 0 2
  b0NN : C.L.base 2 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.num.toUInt64.toBitVec * 67108864
  b1NN : C.L.base 2 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.num.toUInt64.toBitVec * 67108864

theorem NTables.sizeOf_push_self (t : NTables) (v : NNodeView) (d : UInt64) (tr : UInt32) :
    (t.push v d tr).1.sizeOf v = t.sizeOf v + 1 := by
  cases v <;> simp [NTables.push, NTables.sizeOf, Tbl.size, Tbl.push]

theorem ncap_of (ns : NStore) (v : NNodeView)
    (hP : ns.scratchOn = false → (ns.intern v).1.pers.sizeOf v ≤ 2 ^ 26)
    (hS : ns.scratchOn = true → (ns.intern v).1.scr.sizeOf v ≤ 2 ^ 26) : NCap ns v := by
  intro hf
  unfold NStore.find? at hf
  cases hp : ns.pers.find? v with
  | some i => rw [hp] at hf; simp at hf
  | none =>
    rw [hp] at hf
    cases hon : ns.scratchOn with
    | true =>
      rw [hon] at hf; simp only [ite_true] at hf
      have h := hS hon
      simp only [NStore.intern, hp, hon, hf, ite_true] at h
      rw [NTables.sizeOf_push_self] at h
      simp only [ite_true, Idx.idxCap]; omega
    | false =>
      have h := hP hon
      simp only [NStore.intern, hp, hon, Bool.false_eq_true, ite_false] at h
      rw [NTables.sizeOf_push_self] at h
      simp only [Bool.false_eq_true, ite_false, Idx.idxCap]; omega

def PostNm (C : Ctx) (h : NIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = Enc.idxW h ∧ SR C s' st

theorem postNm_locals (C : Ctx) : ∀ (a : NIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNm C a w s' st → PostNm C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

def pKeyN := ofString "nkey"
def fInternNStr := ofString "internNStr"
def nameStrScratch : List MlS := lHa :: strScratch
def nameStrBody : ProgHOL 64 :=
  prologue nameStrScratch (.seq (.assign .local lKb (vv pKeyN))
    (.seq (.assign .local lHa (.op .add [vv pKeyN, .const 8])) (nStrWith (rRestE 1 (vv lEn) lFln))))

theorem nameStr_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (s : AState) (p : NIdx) (str : String) (o : Nat) (H0 : List (BitVec 64)) (hp0 : H0 <+: C.H) (ho0 : H0.length ≤ o)
    (hko : o + (Enc.encStr ⟨p, str⟩).length ≤ C.H.length) (hlen : (Enc.encStr ⟨p, str⟩).length < 2 ^ 60)
    (hkey : ∀ j (hj : j < (Enc.encStr ⟨p, str⟩).length), C.H[o + j]? = some ((Enc.encStr ⟨p, str⟩)[j])) :
    SpecR (Pre (σ := σ) C s [(pKeyN, cellA C o), (lEn, BitVec.ofNat 64 (Enc.encStr ⟨p, str⟩).length),
      (lEp, Enc.idxW p), (lHn, BitVec.ofNat 64 str.toByteArray.data.toList.length)])
      nameStrBody s (internNNode (.str p str)) (PostNm (ctxH C H0)) := by
  refine specR_prologue (postNm_locals _) (fun x hx => ?_) ?_
  · simp only [nameStrScratch, strScratch, numScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hHN : C.H.length ≤ C.HN := inv_heapLen ht
  have hlay := hok.heapLay
  obtain ⟨wk, hwk⟩ := ht.decl lKb (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lKb _ (cellA C o) wk (inv_ev ht (by simp +decide [ctxEnv])) hwk)]
  let t1 := setVarHOLFinite lKb (.val (.word (cellA C o))) t
  have lk0 : t.locals.lookup pKeyN = some (.val (.word (cellA C o))) := ht.env _ _ (by simp +decide [ctxEnv, Env.get])
  obtain ⟨wa, hwa⟩ := ht.decl lHa (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lHa _ (cellA C o + 8) wa
    (eval_add_c t1 pKeyN _ _ (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact lk0))
    (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hwa))]
  let t2 := setVarHOLFinite lHa (.val (.word (cellA C o + 8))) t1
  have L2 : ∀ y, y ≠ lHa → y ≠ lKb → t2.locals.lookup y = t.locals.lookup y := fun y h1 h2 => by
    simp only [t2, t1]; rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2]
  have hw : ∀ y, y ∈ strScratch → ∃ w, t2.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    obtain ⟨w, hw⟩ := ht.decl y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
    have hne : y ≠ lKb ∧ y ≠ lHa := by
      simp only [strScratch, numScratch, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact ⟨w, by rw [L2 y hne.2 hne.1]; exact hw⟩
  have hW : Words t2 (cellA C o) (Enc.encStr ⟨p, str⟩) := by
    intro k hk
    have hk' : o + k < C.H.length := by omega
    have := heap_cell ht.sr (o + k) hk'
    have e := hkey k hk
    rw [List.getElem?_eq_getElem hk'] at e
    simp only [Option.some.injEq] at e
    rw [cellA_off]
    exact ⟨this.1, by rw [← e]; exact this.2⟩
  have hS : SepK C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) (Enc.encStr ⟨p, str⟩).length 1 := by
    have S := hf.sepNS
    refine ⟨S.pow, S.cap, S.dis, S.oth, fun k' tier m h1 h2 h3 => ⟨(S.dsc k' tier m h1 h2 h3).1,
      (S.dsc k' tier m h1 h2 h3).2.1, fun j hj => ?_⟩, fun F hF => ⟨(S.fls F hF).1, (S.fls F hF).2.1, fun j hj => ?_⟩,
      fun j k' tier hj h1 h2 => ?_⟩
    · rw [cellA_off]; exact fun e => hok.dirHeap (o + j) k' tier m (by omega) h1 h2 h3 e.symm
    · rw [cellA_off]; exact fun e => hok.flHeap (o + j) F (by omega) hF e.symm
    · rw [cellA_off]; exact fun hr => hok.heapOut (o + j) (by omega) ⟨k', tier, h1, h2, hr⟩
  rcases nInternStr_spec ra t2 C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) s.store p str
      (sr_of_eq (u := t2) ht.sr rfl rfl rfl rfl).rep hS hW (by omega) hf.b0NS hf.b1NS
      (by simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _)
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (lookup_setVar_same _ _ _)
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get])) hw with
    ⟨hs' | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs'
  have hvp := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hv : s.store.ns.ViewOK (.str p str) := by
    intro c hc
    simp [NNodeView.children] at hc
    subst hc; exact hvp
  have hrun := internNNode_ok s (.str p str) (ncap_of _ _
    (fun _ => Nat.le_trans (tabAt_size_le hsr.n.ps) (hf.sepNS.cap 0 (by decide)))
    (fun _ => Nat.le_trans (tabAt_size_le hsr.n.ss) (hf.sepNS.cap 1 (by decide))))
  right
  have keyne : ∀ c, (∃ i, i < C.HN ∧ c = C.HB + BitVec.ofNat 64 (8 * i) ∧ (i < o ∨ o + (Enc.encStr ⟨p, str⟩).length ≤ i)) →
      ∀ j, j < (Enc.encStr ⟨p, str⟩).length → c ≠ cellA C o + BitVec.ofNat 64 (8 * j) := by
    rintro c ⟨i, hi, rfl, hio⟩ j hj
    rw [cellA_off]
    exact cellA_ne C i (o + j) hi (by omega) hlay (by omega)
  refine ⟨_, hr, (s.store.ns.intern (.str p str)).2, { s with store := withN s.store (s.store.ns.intern (.str p str)).1 }, ?_, rfl, ?_⟩
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
      (internNNode_wf ht.sr.twf hv hrun).1, envDen_ext ht.sr.envd (internNNode_wf ht.sr.twf hv hrun).2, Ext.trans ht.sr.floor (internNNode_wf ht.sr.twf hv hrun).2, cachesOK_ext ht.sr.cok (internNNode_wf ht.sr.twf hv hrun).2 rfl⟩


def fInternNNum := ofString "internNNum"
def nameNumBody : ProgHOL 64 :=
  prologue numScratch (.seq (.assign .local lKb (vv pKeyN)) (nNumWith (rRestE 2 (vv lEn) lFln)))

theorem nameNum_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (s : AState) (p : NIdx) (n : Nat) (o : Nat) (H0 : List (BitVec 64)) (hp0 : H0 <+: C.H) (ho0 : H0.length ≤ o)
    (hko : o + (Enc.encNum ⟨p, n⟩).length ≤ C.H.length) (hlen : (Enc.encNum ⟨p, n⟩).length < 2 ^ 60)
    (hkey : ∀ j (hj : j < (Enc.encNum ⟨p, n⟩).length), C.H[o + j]? = some ((Enc.encNum ⟨p, n⟩)[j])) :
    SpecR (Pre (σ := σ) C s [(pKeyN, cellA C o), (lEn, BitVec.ofNat 64 (Enc.encNum ⟨p, n⟩).length),
      (lEp, Enc.idxW p), (lNw, (UInt64.ofNat n).toBitVec)])
      nameNumBody s (internNNode (.num p n)) (PostNm (ctxH C H0)) := by
  refine specR_prologue (postNm_locals _) (fun x hx => ?_) ?_
  · simp only [numScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hHN : C.H.length ≤ C.HN := inv_heapLen ht
  have hlay := hok.heapLay
  obtain ⟨wk, hwk⟩ := ht.decl lKb (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lKb _ (cellA C o) wk (inv_ev ht (by simp +decide [ctxEnv])) hwk)]
  let t1 := setVarHOLFinite lKb (.val (.word (cellA C o))) t
  let t2 := t1
  have L2 : ∀ y, y ≠ lKb → t2.locals.lookup y = t.locals.lookup y := fun y h1 => by
    simp only [t2, t1]; rw [lookup_setVar_other _ _ h1]
  have hw : ∀ y, y ∈ numScratch → ∃ w, t2.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    obtain ⟨w, hw⟩ := ht.decl y (List.mem_append_right _ hy)
    have hne : y ≠ lKb := by
      simp only [numScratch, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact ⟨w, by rw [L2 y hne]; exact hw⟩
  have hW : Words t2 (cellA C o) (Enc.encNum ⟨p, n⟩) := by
    intro k hk
    have hk' : o + k < C.H.length := by omega
    have := heap_cell ht.sr (o + k) hk'
    have e := hkey k hk
    rw [List.getElem?_eq_getElem hk'] at e
    simp only [Option.some.injEq] at e
    rw [cellA_off]
    exact ⟨this.1, by rw [← e]; exact this.2⟩
  have hS : SepK C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) (Enc.encNum ⟨p, n⟩).length 2 := by
    have S := hf.sepNN
    refine ⟨S.pow, S.cap, S.dis, S.oth, fun k' tier m h1 h2 h3 => ⟨(S.dsc k' tier m h1 h2 h3).1,
      (S.dsc k' tier m h1 h2 h3).2.1, fun j hj => ?_⟩, fun F hF => ⟨(S.fls F hF).1, (S.fls F hF).2.1, fun j hj => ?_⟩,
      fun j k' tier hj h1 h2 => ?_⟩
    · rw [cellA_off]; exact fun e => hok.dirHeap (o + j) k' tier m (by omega) h1 h2 h3 e.symm
    · rw [cellA_off]; exact fun e => hok.flHeap (o + j) F (by omega) hF e.symm
    · rw [cellA_off]; exact fun hr => hok.heapOut (o + j) (by omega) ⟨k', tier, h1, h2, hr⟩
  rcases nInternNum_spec ra t2 C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) s.store p n
      (sr_of_eq (u := t2) ht.sr rfl rfl rfl rfl).rep hS hW (by omega) hf.b0NN hf.b1NN
      (lookup_setVar_same _ _ _)
      (by rw [L2 _ (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get])) hw with
    ⟨hs' | ⟨hr, hsr, hc, hg, hd, _, hm⟩, hV⟩
  · exact Or.inl hs'
  have hvp := hV.resolve_left (fun hs => stop_ne_returned hs _ hr)
  have hv : s.store.ns.ViewOK (.num p n) := by
    intro c hc
    simp [NNodeView.children] at hc
    subst hc; exact hvp
  have hrun := internNNode_ok s (.num p n) (ncap_of _ _
    (fun _ => Nat.le_trans (tabAt_size_le hsr.n.pn) (hf.sepNN.cap 0 (by decide)))
    (fun _ => Nat.le_trans (tabAt_size_le hsr.n.sn) (hf.sepNN.cap 1 (by decide))))
  right
  have keyne : ∀ c, (∃ i, i < C.HN ∧ c = C.HB + BitVec.ofNat 64 (8 * i) ∧ (i < o ∨ o + (Enc.encNum ⟨p, n⟩).length ≤ i)) →
      ∀ j, j < (Enc.encNum ⟨p, n⟩).length → c ≠ cellA C o + BitVec.ofNat 64 (8 * j) := by
    rintro c ⟨i, hi, rfl, hio⟩ j hj
    rw [cellA_off]
    exact cellA_ne C i (o + j) hi (by omega) hlay (by omega)
  refine ⟨_, hr, (s.store.ns.intern (.num p n)).2, { s with store := withN s.store (s.store.ns.intern (.num p n)).1 }, ?_, rfl, ?_⟩
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
      (internNNode_wf ht.sr.twf hv hrun).1, envDen_ext ht.sr.envd (internNNode_wf ht.sr.twf hv hrun).2, Ext.trans ht.sr.floor (internNNode_wf ht.sr.twf hv hrun).2, cachesOK_ext ht.sr.cok (internNNode_wf ht.sr.twf hv hrun).2 rfl⟩

end ConPanqueque.Front
