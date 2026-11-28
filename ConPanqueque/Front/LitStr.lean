import ConPanqueque.Front.NameIntern
import ConPanqueque.V.EVar

/-! # Interning a string literal: the Pancake side

`litStrBody` wraps the ported literal intern (`eLitStrWith`) with its key in heap cells from `o`: the
word `1`, then the string's bytes, one per word (`Enc.encLit (.strVal s)`).  The frontend builds the
key from the input buffer, as for a name's string. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T

variable {σ : Type}

def fInternLitStr := ofString "internLitStr"
def litStrLocals : List MlS := lHa :: litStrScratch

def litStrBody : ProgHOL 64 :=
  prologue litStrLocals (.seq (.assign .local lKb (vv pKeyN))
    (.seq (.assign .local lHa (.op .add [vv pKeyN, .const 8])) (eLitStrWith (rRestE 17 (vv lEn) lFle))))

/-- A heap range as the key region of the literal intern. -/
theorem sepK_heapL {C : Ctx} (hok : CtxOK C) (o w : Nat) (hw : o + w ≤ C.HN) :
    SepK C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) w 17 := by
  have S := hok.sepLit
  refine ⟨S.pow, S.cap, S.dis, S.oth, fun k' tier m h1 h2 h3 => ⟨(S.dsc k' tier m h1 h2 h3).1,
    (S.dsc k' tier m h1 h2 h3).2.1, fun j hj => ?_⟩, fun F hF => ⟨(S.fls F hF).1, (S.fls F hF).2.1, fun j hj => ?_⟩,
    fun j k' tier hj h1 h2 => ?_⟩
  · rw [cellA_off]; exact fun e => hok.dirHeap (o + j) k' tier m (by omega) h1 h2 h3 e.symm
  · rw [cellA_off]; exact fun e => hok.flHeap (o + j) F (by omega) hF e.symm
  · rw [cellA_off]; exact fun hr => hok.heapOut (o + j) (by omega) ⟨k', tier, h1, h2, hr⟩

theorem litStr_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (s : AState) (str : String) (o : Nat) (H0 : List (BitVec 64)) (hp0 : H0 <+: C.H) (ho0 : H0.length ≤ o)
    (hko : o + (Enc.encLit ⟨.strVal str⟩).length ≤ C.H.length) (hlen : (Enc.encLit ⟨.strVal str⟩).length < 2 ^ 60)
    (hkey : ∀ j (hj : j < (Enc.encLit ⟨.strVal str⟩).length), C.H[o + j]? = some ((Enc.encLit ⟨.strVal str⟩)[j])) :
    SpecR (Pre (σ := σ) C s [(pKeyN, cellA C o), (lEn, BitVec.ofNat 64 (Enc.encLit ⟨.strVal str⟩).length),
      (lHn, BitVec.ofNat 64 str.toByteArray.data.toList.length)])
      litStrBody s (internE (.lit (.strVal str))) (PostE (ctxH C H0)) := by
  refine specR_prologue (postE_locals _) (fun x hx => ?_) ?_
  · simp only [litStrLocals, litStrScratch, bvarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
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
  have hw : ∀ y, y ∈ litStrScratch → ∃ w, t2.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    obtain ⟨w, hw⟩ := ht.decl y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
    have hne : y ≠ lKb ∧ y ≠ lHa := by
      simp only [litStrScratch, bvarScratch, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact ⟨w, by rw [L2 y hne.2 hne.1]; exact hw⟩
  have hW : Words t2 (cellA C o) (Enc.encLit ⟨.strVal str⟩) := by
    intro k hk
    have hk' : o + k < C.H.length := by omega
    have := heap_cell ht.sr (o + k) hk'
    have e := hkey k hk
    rw [List.getElem?_eq_getElem hk'] at e
    simp only [Option.some.injEq] at e
    rw [cellA_off]
    exact ⟨this.1, by rw [← e]; exact this.2⟩
  have hS := sepK_heapL hok o (Enc.encLit ⟨.strVal str⟩).length (by omega)
  rcases eInternLitStr_spec ra t2 C.L C.FLn C.FLl C.FLs C.FLe (cellA C o) s.store str
      (sr_of_eq (u := t2) ht.sr rfl rfl rfl rfl).rep hS hW (by omega) hok.b0Lit hok.b1Lit
      (by simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _)
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (lookup_setVar_same _ _ _)
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get]))
      (by rw [L2 _ (by decide) (by decide)]; exact ht.env _ _ (by simp +decide [ctxEnv, Env.get])) hw with
    hs' | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs'
  have hrun := internNodeE_lit s (.strVal str)
      (Nat.le_trans (tabAt_size_le hsr.e.p8) (hok.sepLit.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s8) (hok.sepLit.cap 1 (by decide)))
  right
  have keyne : ∀ c, (∃ i, i < C.HN ∧ c = C.HB + BitVec.ofNat 64 (8 * i) ∧ (i < o ∨ o + (Enc.encLit ⟨.strVal str⟩).length ≤ i)) →
      ∀ j, j < (Enc.encLit ⟨.strVal str⟩).length → c ≠ cellA C o + BitVec.ofNat 64 (8 * j) := by
    rintro c ⟨i, hi, rfl, hio⟩ j hj
    rw [cellA_off]
    exact cellA_ne C i (o + j) hi (by omega) hlay (by omega)
  refine ⟨_, hr, (s.store.intern (.lit (.strVal str))).2, { s with store := (s.store.intern (.lit (.strVal str))).1 },
    ?_, rfl, ?_⟩
  · show internNodeE (.lit (.strVal str)) s = _
    exact hrun
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
      (internNodeE_wf ht.sr.twf viewOK_lit hrun).1, envDen_ext ht.sr.envd (internNodeE_wf ht.sr.twf viewOK_lit hrun).2,
      Ext.trans ht.sr.floor (internNodeE_wf ht.sr.twf viewOK_lit hrun).2,
      cachesOK_ext ht.sr.cok (internNodeE_wf ht.sr.twf viewOK_lit hrun).2 rfl⟩

end ConPanqueque.Front
