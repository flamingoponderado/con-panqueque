import ConPanqueque.V.View
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Viewing a level handle

`lViewP`: the twin's `LStore.view`. A wide handle decodes to the `param` tag but is dangling (the twin
answers `none`), so it halts first; then `storeRow 3 5` reads the row from the level tables.
-/

namespace ConPanqueque.V

def encLView : LNodeView → List (BitVec 64)
  | .zero => Enc.encZero ⟨⟩
  | .succ u => Enc.encSucc ⟨u⟩
  | .max u v => Enc.encBinL ⟨u, v⟩
  | .imax u v => Enc.encBinL ⟨u, v⟩
  | .param n => Enc.encParam ⟨n⟩

def _root_.ConRon.Arena.LNodeView.tagN : LNodeView → Nat
  | .zero => 0 | .succ _ => 1 | .max _ _ => 2 | .imax _ _ => 3 | .param _ => 4

def lViewP : ProgHOL 64 :=
  .seq (.ite (.op .and [.shift .lsr (vv lDh) (.const 30), .const 1]) hang .skip) (storeRow 3 5)

theorem wide_iff {k : IdxKind} (i : Idx k) : (Enc.idxW i >>> (30 : Nat)) &&& 1 ≠ 0 ↔ i.isWide = true := by
  have hw : (Enc.idxW i).toNat = i.word.toNat := by simp [Enc.idxW]
  have hlt : i.word.toNat < 2 ^ 32 := i.word.toNat_lt
  have e1 : ((Enc.idxW i >>> (30 : Nat)) &&& 1 ≠ 0) ↔ i.word.toNat / 1073741824 % 2 = 1 := by
    rw [Ne, ← BitVec.toNat_inj]
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow]
    have e : (1 : BitVec 64).toNat = 2 ^ 1 - 1 := rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod]; simp
  rw [e1]
  simp only [Idx.isWide, beq_iff_eq]
  constructor
  · intro h; apply UInt32.toNat_inj.mp; simp [UInt32.toNat_div, UInt32.toNat_mod]; omega
  · intro h; have := congrArg UInt32.toNat h; simp [UInt32.toNat_div, UInt32.toNat_mod] at this; omega

section
variable {σ : Type}

theorem lView_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL : BitVec 64) (st : LStore)
    (hR : LRep t L FL st) (i : LIdx)
    (hh : t.locals.lookup lDh = some (.val (.word (Enc.idxW i))))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (ht : ∃ w, t.locals.lookup lDt = some (.val (.word w))) (hg : ∃ w, t.locals.lookup lDg = some (.val (.word w)))
    (hi : ∃ w, t.locals.lookup lDi = some (.val (.word w)))
    (h1 : ∃ w, t.locals.lookup lRp = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lRn = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t lViewP).1 ∨ ∃ v, st.view i = some v ∧ v.tagN = i.tag.toNat ∧
      RowRes t i.tier.toNat i.tag.toNat i.idxNat (encLView v) (evaluateHOLFiniteState t lViewP) := by
  have hidx : i.idxNat < 2 ^ 30 := by
    simp only [Idx.idxNat, Idx.index]; split <;> simp [UInt32.toNat_mod] <;> omega
  unfold lViewP
  have hc : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .and [.shift .lsr (vv lDh) (.const 30), .const 1]) =
      some (.val (.word ((Enc.idxW i >>> (30 : Nat)) &&& 1))) :=
    eval_and2' t _ _ _ _ (eval_shr t _ _ _ (eval_vv t lDh _ hh) (by decide)) (eval_const t 1)
  by_cases hn : (Enc.idxW i >>> (30 : Nat)) &&& 1 ≠ 0
  · left
    apply seq_stop
    rw [ite_word t _ _ _ _ hc, if_pos hn]
    exact hang_stop t
  have hnw : i.isWide = false := by
    cases e : i.isWide
    · rfl
    · exact absurd ((wide_iff i).mpr e) hn
  have hsk : evaluateHOLFiniteState t (.ite (.op .and [.shift .lsr (vv lDh) (.const 30), .const 1]) hang .skip) =
      (none, t) := by
    rw [ite_word t _ _ _ _ hc, if_neg hn]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
  rw [seq_normal _ hsk]
  refine storeRow_gen t L FL st.scratchOn 3 5 (by decide) i (fun r => ∃ v, st.view i = some v ∧ v.tagN = i.tag.toNat ∧
    RowRes t i.tier.toNat i.tag.toNat i.idxNat (encLView v) r) hh hdir hfl hR.fl ht hg hi h1 h2 ?_
  intro htag hlive u um ud uc ug uta udir udt udg udi uo1 uo2 ufr
  have pick : ∃ (tr : UInt32) (lt : LTables), st.view i = lt.get i ∧
      TabAt t L 3 i.tier.toNat Enc.encZero dWL lt.zeros (mkN LTag.zero tr) ∧
      TabAt t L 4 i.tier.toNat Enc.encSucc dWL lt.succs (mkN LTag.succ tr) ∧
      TabAt t L 5 i.tier.toNat Enc.encBinL dWL lt.maxs (mkN LTag.max tr) ∧
      TabAt t L 6 i.tier.toNat Enc.encBinL dWL lt.imaxs (mkN LTag.imax tr) ∧
      TabAt t L 7 i.tier.toNat Enc.encParam dWL lt.params (mkN LTag.param tr) := by
    have htl := Idx.tier_lt i
    rcases (by omega : i.tier.toNat = 0 ∨ i.tier.toNat = 1) with h0 | h0
    · have e0 : i.tier = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
      refine ⟨0, st.pers, ?_, ?_⟩
      · simp only [LStore.view, Idx.isPersistent, beq_iff_eq]; rw [if_pos e0]
      · rw [h0]; exact ⟨hR.pz, hR.ps, hR.pm, hR.pi, hR.pp⟩
    · have hnp : ¬ i.isPersistent = true := by
        simp only [Idx.isPersistent, beq_iff_eq]; intro e; rw [e] at h0; simp at h0
      have hon : st.scratchOn = true := by rcases hlive with h | h; omega; exact h
      refine ⟨1, st.scr, ?_, ?_⟩
      · simp only [LStore.view]; rw [if_neg hnp, hon]; rfl
      · rw [h0]; exact ⟨hR.sz, hR.ss, hR.sm, hR.si, hR.sp⟩
  obtain ⟨tr, lt, hview, hT0, hT1, hT2, hT3, hT4⟩ := pick
  have htl := Idx.tier_lt i
  obtain ⟨m, hm, hmt⟩ := tag_cases i 5 htag
  have hgm : u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 m))) := by
    rw [show (BitVec.ofNat 64 m) = BitVec.ofNat 64 i.tag.toNat by rw [hmt]; simp; rw [Nat.mod_eq_of_lt (by omega)]]
    exact udg
  have htm : i.tag.toNat = m := by rw [hmt]; simp; omega
  simp only [htm]
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl
  · rcases rowAt_spec t u L 3 0 i.tier.toNat i.idxNat Enc.encZero dWL lt.zeros _ (tabAt_eq hT0 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.zero, ?_, ?_, hr⟩
    · rw [hview]; simp [LTables.get, Tbl.node?, hmt, LTag.zero, Array.getElem?_eq_getElem hlt]
    · simp [LNodeView.tagN, hmt]
  · rcases rowAt_spec t u L 3 1 i.tier.toNat i.idxNat Enc.encSucc dWL lt.succs _ (tabAt_eq hT1 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.succ (lt.succs.nodes[i.idxNat]'hlt).u, ?_, ?_, hr⟩
    · rw [hview]; simp [LTables.get, Tbl.node?, hmt, LTag.zero, LTag.succ, Array.getElem?_eq_getElem hlt]
    · simp [LNodeView.tagN, hmt]
  · rcases rowAt_spec t u L 3 2 i.tier.toNat i.idxNat Enc.encBinL dWL lt.maxs _ (tabAt_eq hT2 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.max (lt.maxs.nodes[i.idxNat]'hlt).u (lt.maxs.nodes[i.idxNat]'hlt).v, ?_, ?_, hr⟩
    · rw [hview]; simp [LTables.get, Tbl.node?, hmt, LTag.zero, LTag.succ, LTag.max, Array.getElem?_eq_getElem hlt]
    · simp [LNodeView.tagN, hmt]
  · rcases rowAt_spec t u L 3 3 i.tier.toNat i.idxNat Enc.encBinL dWL lt.imaxs _ (tabAt_eq hT3 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.imax (lt.imaxs.nodes[i.idxNat]'hlt).u (lt.imaxs.nodes[i.idxNat]'hlt).v, ?_, ?_, hr⟩
    · rw [hview]; simp [LTables.get, Tbl.node?, hmt, LTag.zero, LTag.succ, LTag.max, LTag.imax,
        Array.getElem?_eq_getElem hlt]
    · simp [LNodeView.tagN, hmt]
  · rcases rowAt_spec t u L 3 4 i.tier.toNat i.idxNat Enc.encParam dWL lt.params _ (tabAt_eq hT4 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.param (lt.params.nodes[i.idxNat]'hlt).n, ?_, ?_, hr⟩
    · rw [hview]; simp [LTables.get, Tbl.node?, hmt, LTag.zero, LTag.succ, LTag.max, LTag.imax, LTag.param, hnw,
        Array.getElem?_eq_getElem hlt]
    · simp [LNodeView.tagN, hmt]

end

end ConPanqueque.V
