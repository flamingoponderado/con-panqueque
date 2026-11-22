import ConPanqueque.V.Layout
import ConPanqueque.V.Der
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.Hash
open ConRon.Arena

/-!
# A level list's derived record

`lsDer` folds con-ron's `LsStore.derOfView` from the end of the list: for each
level handle (words at `la`, `ln` of them) it reads the level's derived record
(`storeDerived 3 5`, the level store's read) and mixes it in.
-/

namespace ConPanqueque.V

def lLa := ofString "la"
def lLn := ofString "ln"
def lLr := ofString "lr"
def lLp := ofString "lp"

def lsStep : ProgHOL 64 :=
  .seq (.assign .local lLn (.op .sub [vv lLn, .const 1]))
  (.seq (.assign .local lDh (.load .one (.op .add [vv lLa, .shift .lsl (vv lLn) (.const 3)])))
  (.seq (storeDerived 3 5)
  (.seq (.assign .local lLr (mixExp (vv lDo1) (vv lLr)))
    (.assign .local lLp (.op .or [vv lLp, vv lDo2])))))

def lsDer : ProgHOL 64 :=
  .seq (.assign .local lLr (.const 13)) (.seq (.assign .local lLp (.const 0)) (.while (vv lLn) lsStep))

theorem dWL_cons_snd (a b : Bool) :
    ((if a then (1 : BitVec 64) else 0) ||| (if b then 1 else 0)) = (if b || a then 1 else 0) := by
  cases a <;> cases b <;> decide

section
variable {σ : Type}

theorem lRep_eq {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : LStore}
    (h : LRep t L FL st) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) : LRep u L FL st :=
  ⟨⟨by rw [hd]; exact h.fl.1, by rw [hm]; exact h.fl.2⟩, tabAt_eq h.pz hm hd, tabAt_eq h.ps hm hd,
    tabAt_eq h.pm hm hd, tabAt_eq h.pi hm hd, tabAt_eq h.pp hm hd, tabAt_eq h.sz hm hd, tabAt_eq h.ss hm hd,
    tabAt_eq h.sm hm hd, tabAt_eq h.si hm hd, tabAt_eq h.sp hm hd⟩

/-- The level-list fold with the runtime's mix. -/
def lsModel (st : LStore) : List LIdx → UInt64 × Bool
  | [] => (13, false)
  | u :: us => (leanMixHash (st.derived u).hash (lsModel st us).1, (st.derived u).hasParam || (lsModel st us).2)

theorem lsModel_eq (ra : RuntimeAssumptions) (st : LsStore) :
    ∀ us : List LIdx, st.derOfView us = ⟨(lsModel st.ls us).1, (lsModel st.ls us).2⟩
  | [] => rfl
  | u :: us => by
    simp only [LsStore.derOfView, lsModel, ra.mixHash]
    rw [lsModel_eq ra st us]

def bit (b : Bool) : BitVec 64 := if b then 1 else 0

/-- The fold loop's invariant: `j` handles still to fold. -/
def LsI (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL A : BitVec 64) (st : LStore) (us : List LIdx)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧ u.topAddr = t.topAddr ∧
  (∀ y, y ≠ lLn → y ≠ lLr → y ≠ lLp → y ≠ lDh → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDo1 → y ≠ lDo2 →
    u.locals.lookup y = t.locals.lookup y) ∧
  (∀ y, y = lDh ∨ y = lDt ∨ y = lDg ∨ y = lDi ∨ y = lDo1 ∨ y = lDo2 → ∃ w, u.locals.lookup y = some (.val (.word w))) ∧
  ∃ j, j ≤ us.length ∧ u.locals.lookup lLn = some (.val (.word (BitVec.ofNat 64 j))) ∧
    u.locals.lookup lLr = some (.val (.word (lsModel st (us.drop j)).1.toBitVec)) ∧
    u.locals.lookup lLp = some (.val (.word (bit (lsModel st (us.drop j)).2)))

end

section
variable {σ : Type}

theorem ls_step (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL A : BitVec 64) (st : LStore) (us : List LIdx)
    (hR : LRep t L FL st) (hW : Words t A (us.map Enc.idxW)) (hL : us.length < 2 ^ 60)
    (hla : t.locals.lookup lLa = some (.val (.word A)))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (u : PanSemStateFiniteExact 64 σ) (hu : LsI t L FL A st us u)
    (hnz : ∀ w, u.locals.lookup lLn = some (.val (.word w)) → w ≠ 0) :
    (evaluateHOLFiniteState (decClockHOLFinite u) lsStep).1 = none ∧
      LsI t L FL A st us (evaluateHOLFiniteState (decClockHOLFinite u) lsStep).2 := by
  obtain ⟨m0, d0, c0, g0, ta0, fr, cw, j, hjl, hj, hr, hp⟩ := hu
  have hj0 : j ≠ 0 := fun e => hnz _ hj (by rw [e]; rfl)
  let v := decClockHOLFinite u
  have hjx : j - 1 < us.length := by omega
  unfold lsStep
  rw [seq_normal _ (ConsLoop.assign_local v lLn _ (BitVec.ofNat 64 (j - 1)) _
    (by rw [eval_sub2 v _ _ _ _ (eval_vv v lLn _ hj) (eval_const v 1)]
        congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) hj)]
  let v1 := setVarHOLFinite lLn (.val (.word (BitVec.ofNat 64 (j - 1)))) v
  obtain ⟨wh, hwh⟩ := cw lDh (Or.inl rfl)
  have hw := hW (j - 1) (by simp; exact hjx)
  have hld : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.load .one (.op .add [vv lLa, .shift .lsl (vv lLn) (.const 3)])) = some (.val (.word (Enc.idxW us[j - 1]))) := by
    rw [eval_load_word v1 _ (A + BitVec.ofNat 64 (8 * (j - 1)))
      (by rw [eval_add2 v1 _ _ _ _ (eval_vv v1 lLa _ (by lk [v1, v]; rw [fr _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hla))
            (eval_shl v1 _ _ _ (eval_vv v1 lLn _ (lookup_setVar_same _ _ _)) (by decide)),
          show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)])
      (by show u.memaddrs _; rw [d0]; exact hw.1)]
    show some (ValueHOL.val (u.memory _)) = _; rw [m0, hw.2]; simp
  rw [seq_normal _ (ConsLoop.assign_local v1 lDh _ (Enc.idxW us[j - 1]) wh hld (by lk [v1, v]; exact hwh))]
  let v2 := setVarHOLFinite lDh (.val (.word (Enc.idxW us[j - 1]))) v1
  have back : ∀ y, y ≠ lLn → y ≠ lLr → y ≠ lLp → y ≠ lDh → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDo1 → y ≠ lDo2 →
      v2.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9; lk [v2, v1, v]; exact fr y a1 a2 a3 a4 a5 a6 a7 a8 a9
  have cw2 : ∀ y, y = lDt ∨ y = lDg ∨ y = lDi ∨ y = lDo1 ∨ y = lDo2 → ∃ w, v2.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    obtain ⟨w, hw⟩ := cw y (Or.inr hy)
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact ⟨w, by lk [v2, v1, v]; exact hw⟩
  have hD := lDerived_spec v2 L FL st (lRep_eq hR m0 d0) us[j - 1] (lookup_setVar_same _ _ _)
    (by rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hdir)
    (by rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hfl)
    (cw2 lDt (Or.inl rfl)) (cw2 lDg (Or.inr (Or.inl rfl))) (cw2 lDi (Or.inr (Or.inr (Or.inl rfl))))
    (cw2 lDo1 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (cw2 lDo2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  obtain ⟨hn3, m3, d3, c3, g3, ta3, ck3, o1, o2, fr3, w3c⟩ := hD
  generalize hs3 : evaluateHOLFiniteState v2 (storeDerived 3 5) = st3 at hn3 m3 d3 c3 g3 ta3 ck3 o1 o2 fr3 w3c
  obtain ⟨r3, w3⟩ := st3
  simp only at hn3 m3 d3 c3 g3 ta3 ck3 o1 o2 fr3 w3c; subst hn3
  rw [seq_normal _ hs3]
  let dd := st.derived us[j - 1]
  have lr3 : w3.locals.lookup lLr = some (.val (.word (lsModel st (us.drop j)).1.toBitVec)) := by
    rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [v2, v1, v]; exact hr
  rw [seq_normal _ (ConsLoop.assign_local w3 lLr _ (leanMixHash dd.hash (lsModel st (us.drop j)).1).toBitVec _
    (eval_mixExp w3 _ _ _ _ (eval_vv w3 lDo1 _ o1) (eval_vv w3 lLr _ lr3)) lr3)]
  let w4 := setVarHOLFinite lLr (.val (.word (leanMixHash dd.hash (lsModel st (us.drop j)).1).toBitVec)) w3
  have lp4 : w4.locals.lookup lLp = some (.val (.word (bit (lsModel st (us.drop j)).2))) := by
    lk [w4]; rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [v2, v1, v]; exact hp
  have hdrop : us.drop (j - 1) = us[j - 1] :: us.drop j := by
    have := List.drop_eq_getElem_cons (l := us) (i := j - 1) hjx
    rwa [show j - 1 + 1 = j by omega] at this
  rw [ConsLoop.assign_local w4 lLp _ (bit (lsModel st (us.drop (j - 1))).2) _
    (by rw [eval_or2 w4 _ _ _ _ (eval_vv w4 lLp _ lp4) (eval_vv w4 lDo2 _ (by lk [w4]; exact o2)), hdrop]
        simp only [lsModel, bit, dWL]; rw [dWL_cons_snd]; rfl) lp4]
  refine ⟨rfl, m3.trans m0, d3.trans d0, c3.trans c0, g3.trans g0, ta3.trans ta0,
    fun y a1 a2 a3 a4 a5 a6 a7 a8 a9 => ?_, fun y hy => ?_, j - 1, by omega, ?_, ?_, by lk⟩
  · lk [w4]; rw [fr3 y a8 a9 a5 a6 a7]; exact back y a1 a2 a3 a4 a5 a6 a7 a8 a9
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Enc.idxW us[j - 1], by lk [w4]; rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [v2]⟩
    · obtain ⟨w, hw⟩ := w3c lDt (Or.inl rfl); exact ⟨w, by lk [w4]; exact hw⟩
    · obtain ⟨w, hw⟩ := w3c lDg (Or.inr (Or.inl rfl)); exact ⟨w, by lk [w4]; exact hw⟩
    · obtain ⟨w, hw⟩ := w3c lDi (Or.inr (Or.inr rfl)); exact ⟨w, by lk [w4]; exact hw⟩
    · exact ⟨_, by lk [w4]; exact o1⟩
    · exact ⟨_, by lk [w4]; exact o2⟩
  · lk [w4]; rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [v2, v1]
  · lk [w4]; rw [hdrop]; rfl

end

section
variable {σ : Type}

theorem lsDer_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL A : BitVec 64) (st : LStore) (us : List LIdx)
    (hR : LRep t L FL st) (hW : Words t A (us.map Enc.idxW)) (hL : us.length < 2 ^ 60)
    (hla : t.locals.lookup lLa = some (.val (.word A)))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (hln : t.locals.lookup lLn = some (.val (.word (BitVec.ofNat 64 us.length))))
    (hlr : ∃ w, t.locals.lookup lLr = some (.val (.word w))) (hlp : ∃ w, t.locals.lookup lLp = some (.val (.word w)))
    (hw6 : ∀ y, y = lDh ∨ y = lDt ∨ y = lDg ∨ y = lDi ∨ y = lDo1 ∨ y = lDo2 →
      ∃ w, t.locals.lookup y = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t lsDer).1 ∨ ((evaluateHOLFiniteState t lsDer).1 = none ∧
      LsI t L FL A st us (evaluateHOLFiniteState t lsDer).2 ∧
      (evaluateHOLFiniteState t lsDer).2.locals.lookup lLr = some (.val (.word (lsModel st us).1.toBitVec)) ∧
      (evaluateHOLFiniteState t lsDer).2.locals.lookup lLp = some (.val (.word (bit (lsModel st us).2)))) := by
  obtain ⟨wr, hwr⟩ := hlr; obtain ⟨wp, hwp⟩ := hlp
  unfold lsDer
  rw [seq_normal _ (ConsLoop.assign_local t lLr (.const 13) 13 wr (eval_const t 13) hwr)]
  let t1 := setVarHOLFinite lLr (.val (.word 13)) t
  rw [seq_normal _ (ConsLoop.assign_local t1 lLp (.const 0) 0 wp (eval_const t1 0) (by lk [t1]; exact hwp))]
  let t2 := setVarHOLFinite lLp (.val (.word 0)) t1
  have hI : LsI t L FL A st us t2 := ⟨rfl, rfl, rfl, rfl, rfl, fun y a1 a2 a3 _ _ _ _ _ _ => by lk [t2, t1],
    fun y hy => by
      obtain ⟨w, hw⟩ := hw6 y hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨w, by lk [t2, t1]; exact hw⟩,
    us.length, Nat.le_refl _, by lk [t2, t1]; exact hln, by rw [List.drop_length]; lk [t2, t1]; rfl,
    by rw [List.drop_length]; exact lookup_setVar_same _ _ _⟩
  have := while_stop (vv lLn) lsStep (LsI t L FL A st us)
    (fun u => LsI t L FL A st us u ∧ u.locals.lookup lLn = some (.val (.word 0)))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, j, hj, hjn, _, _⟩ := id hu
      by_cases h0 : BitVec.ofNat 64 j = 0
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hjn, h0], fun _ => ⟨hu, by rw [hjn, h0]⟩,
          fun e => absurd rfl e⟩
      · refine ⟨BitVec.ofNat 64 j, by simp [evalHOLFinite, vv, evalHOLExact, hjn], fun e => absurd e h0, fun _ _ => ?_⟩
        have := ls_step t L FL A st us hR hW hL hla hdir hfl u hu (fun w hw => by
          rw [hjn] at hw; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hw
          rw [← hw]; exact h0)
        exact Or.inr this)
    t2 hI
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  refine Or.inr ⟨h1, h2, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, j, hj, hjn, hr, hp⟩ := h2
  have : j = 0 := by
    rw [hjn] at h3; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at h3
    have := congrArg BitVec.toNat h3; simp at this; omega
  subst this
  rw [List.drop_zero] at hr hp; exact ⟨hr, hp⟩

end

end ConPanqueque.V
