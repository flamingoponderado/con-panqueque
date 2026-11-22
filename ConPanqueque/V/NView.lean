import ConPanqueque.V.LView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Viewing a name handle

`nViewP`: the twin's `NStore.view`, `storeRow 0 3` over the name tables (a wide handle's tag is out
of range, so the row read halts on it).
-/

namespace ConPanqueque.V

def encNView : NNodeView → List (BitVec 64)
  | .anonymous => Enc.encAnon ⟨⟩
  | .str p x => Enc.encStr ⟨p, x⟩
  | .num p n => Enc.encNum ⟨p, n⟩

def _root_.ConRon.Arena.NNodeView.tagN : NNodeView → Nat
  | .anonymous => 0 | .str _ _ => 1 | .num _ _ => 2

def nViewP : ProgHOL 64 := storeRow 0 3

section
variable {σ : Type}

theorem nView_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL : BitVec 64) (st : NStore)
    (hR : NRep t L FL st) (i : NIdx)
    (hh : t.locals.lookup lDh = some (.val (.word (Enc.idxW i))))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (ht : ∃ w, t.locals.lookup lDt = some (.val (.word w))) (hg : ∃ w, t.locals.lookup lDg = some (.val (.word w)))
    (hi : ∃ w, t.locals.lookup lDi = some (.val (.word w)))
    (h1 : ∃ w, t.locals.lookup lRp = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lRn = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t nViewP).1 ∨ ∃ v, st.view i = some v ∧ v.tagN = i.tag.toNat ∧
      RowRes t i.tier.toNat i.tag.toNat i.idxNat (encNView v) (evaluateHOLFiniteState t nViewP) := by
  have hidx : i.idxNat < 2 ^ 30 := by
    simp only [Idx.idxNat, Idx.index]; split <;> simp [UInt32.toNat_mod] <;> omega
  unfold nViewP
  refine storeRow_gen t L FL st.scratchOn 0 3 (by decide) i (fun r => ∃ v, st.view i = some v ∧ v.tagN = i.tag.toNat ∧
    RowRes t i.tier.toNat i.tag.toNat i.idxNat (encNView v) r) hh hdir hfl hR.fl ht hg hi h1 h2 ?_
  intro htag hlive u um ud uc ug uta udir udt udg udi uo1 uo2 ufr
  have pick : ∃ (tr : UInt32) (nt : NTables), st.view i = nt.get i ∧
      TabAt t L 0 i.tier.toNat Enc.encAnon dWN nt.anons (mkN NTag.anonymous tr) ∧
      TabAt t L 1 i.tier.toNat Enc.encStr dWN nt.strs (mkN NTag.str tr) ∧
      TabAt t L 2 i.tier.toNat Enc.encNum dWN nt.nums (mkN NTag.num tr) := by
    have htl := Idx.tier_lt i
    rcases (by omega : i.tier.toNat = 0 ∨ i.tier.toNat = 1) with h0 | h0
    · have e0 : i.tier = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
      refine ⟨0, st.pers, ?_, ?_⟩
      · simp only [NStore.view, Idx.isPersistent, beq_iff_eq]; rw [if_pos e0]
      · rw [h0]; exact ⟨hR.pa, hR.ps, hR.pn⟩
    · have hnp : ¬ i.isPersistent = true := by
        simp only [Idx.isPersistent, beq_iff_eq]; intro e; rw [e] at h0; simp at h0
      have hon : st.scratchOn = true := by rcases hlive with h | h; omega; exact h
      refine ⟨1, st.scr, ?_, ?_⟩
      · simp only [NStore.view]; rw [if_neg hnp, hon]; rfl
      · rw [h0]; exact ⟨hR.sa, hR.ss, hR.sn⟩
  obtain ⟨tr, nt, hview, hT0, hT1, hT2⟩ := pick
  have htl := Idx.tier_lt i
  obtain ⟨m, hm, hmt⟩ := tag_cases i 3 htag
  have hgm : u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 m))) := by
    rw [show (BitVec.ofNat 64 m) = BitVec.ofNat 64 i.tag.toNat by rw [hmt]; simp; rw [Nat.mod_eq_of_lt (by omega)]]
    exact udg
  have htm : i.tag.toNat = m := by rw [hmt]; simp; omega
  simp only [htm]
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · rcases rowAt_spec t u L 0 0 i.tier.toNat i.idxNat Enc.encAnon dWN nt.anons _ (tabAt_eq hT0 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.anonymous, ?_, ?_, hr⟩
    · rw [hview]; simp [NTables.get, Tbl.node?, hmt, NTag.anonymous, Array.getElem?_eq_getElem hlt]
    · simp [NNodeView.tagN, hmt]
  · rcases rowAt_spec t u L 0 1 i.tier.toNat i.idxNat Enc.encStr dWN nt.strs _ (tabAt_eq hT1 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.str (nt.strs.nodes[i.idxNat]'hlt).pre (nt.strs.nodes[i.idxNat]'hlt).s, ?_, ?_, hr⟩
    · rw [hview]; simp [NTables.get, Tbl.node?, hmt, NTag.anonymous, NTag.str, Array.getElem?_eq_getElem hlt]
    · simp [NNodeView.tagN, hmt]
  · rcases rowAt_spec t u L 0 2 i.tier.toNat i.idxNat Enc.encNum dWN nt.nums _ (tabAt_eq hT2 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.num (nt.nums.nodes[i.idxNat]'hlt).pre (nt.nums.nodes[i.idxNat]'hlt).n, ?_, ?_, hr⟩
    · rw [hview]; simp [NTables.get, Tbl.node?, hmt, NTag.anonymous, NTag.str, NTag.num, Array.getElem?_eq_getElem hlt]
    · simp [NNodeView.tagN, hmt]

end

end ConPanqueque.V
