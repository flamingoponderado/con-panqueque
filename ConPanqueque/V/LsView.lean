import ConPanqueque.V.NView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Viewing a level-list handle

`lsViewP`: the twin's `LsStore.view`, `storeRow 8 1` over the level-list tables: the row is the
list's handle words.
-/

namespace ConPanqueque.V

def lsViewP : ProgHOL 64 := storeRow 8 1

section
variable {σ : Type}

theorem lsView_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL : BitVec 64) (st : LsStore)
    (hR : LsRep t L FL st) (i : LsIdx)
    (hh : t.locals.lookup lDh = some (.val (.word (Enc.idxW i))))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (ht : ∃ w, t.locals.lookup lDt = some (.val (.word w))) (hg : ∃ w, t.locals.lookup lDg = some (.val (.word w)))
    (hi : ∃ w, t.locals.lookup lDi = some (.val (.word w)))
    (h1 : ∃ w, t.locals.lookup lRp = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lRn = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t lsViewP).1 ∨ ∃ v, st.view i = some v ∧ i.tag.toNat = 0 ∧
      RowRes t i.tier.toNat 0 i.idxNat (v.map Enc.idxW) (evaluateHOLFiniteState t lsViewP) := by
  have hidx : i.idxNat < 2 ^ 30 := by
    simp only [Idx.idxNat, Idx.index]; split <;> simp [UInt32.toNat_mod] <;> omega
  unfold lsViewP
  refine storeRow_gen t L FL st.scratchOn 8 1 (by decide) i (fun r => ∃ v, st.view i = some v ∧ i.tag.toNat = 0 ∧
    RowRes t i.tier.toNat 0 i.idxNat (v.map Enc.idxW) r) hh hdir hfl hR.fl ht hg hi h1 h2 ?_
  intro htag hlive u um ud uc ug uta udir udt udg udi uo1 uo2 ufr
  have pick : ∃ (tr : UInt32) (nt : LsTables), st.view i = nt.get i ∧
      TabAt t L 8 i.tier.toNat Enc.encList dWL nt.lists (mkN LsTag.list tr) := by
    have htl := Idx.tier_lt i
    rcases (by omega : i.tier.toNat = 0 ∨ i.tier.toNat = 1) with h0 | h0
    · have e0 : i.tier = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
      refine ⟨0, st.pers, ?_, ?_⟩
      · simp only [LsStore.view, Idx.isPersistent, beq_iff_eq]; rw [if_pos e0]
      · rw [h0]; exact hR.pl
    · have hnp : ¬ i.isPersistent = true := by
        simp only [Idx.isPersistent, beq_iff_eq]; intro e; rw [e] at h0; simp at h0
      have hon : st.scratchOn = true := by rcases hlive with h | h; omega; exact h
      refine ⟨1, st.scr, ?_, ?_⟩
      · simp only [LsStore.view]; rw [if_neg hnp, hon]; rfl
      · rw [h0]; exact hR.sl
  obtain ⟨tr, nt, hview, hT0⟩ := pick
  have htl := Idx.tier_lt i
  obtain ⟨m, hm, hmt⟩ := tag_cases i 1 htag
  have hgm : u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 m))) := by
    rw [show (BitVec.ofNat 64 m) = BitVec.ofNat 64 i.tag.toNat by rw [hmt]; simp; rw [Nat.mod_eq_of_lt (by omega)]]
    exact udg
  have htm : i.tag.toNat = m := by rw [hmt]; simp; omega
  obtain rfl : m = 0 := by omega
  rcases rowAt_spec t u L 8 0 i.tier.toNat i.idxNat Enc.encList dWL nt.lists _ (tabAt_eq hT0 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
  · exact Or.inl hs
  right
  refine ⟨(nt.lists.nodes[i.idxNat]'hlt).us, ?_, htm, hr⟩
  rw [hview]; simp [LsTables.get, Tbl.node?, hmt, LsTag.list, Array.getElem?_eq_getElem hlt]

end

end ConPanqueque.V
