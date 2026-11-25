import ConPanqueque.V.RowRead
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Viewing an expression handle

`eViewP`: the twin's `EStore.view`. A narrow handle carrying the `app` tag is dangling (the
twin answers `none`), so it halts first; then `storeRow 9 10` reads the row. The result says which
view the twin sees, that its constructor is the handle's tag, and where its fields are.
-/

namespace ConPanqueque.V

/-- A view's fields, as its constructor's table stores them. -/
def encEView : ENodeView → List (BitVec 64)
  | .bvar i => Enc.encBVar ⟨i⟩
  | .fvar idx ty => Enc.encFVar ⟨idx, ty⟩
  | .sort u => Enc.encSort ⟨u⟩
  | .const n us => Enc.encConst ⟨n, us⟩
  | .app f a => Enc.encApp ⟨f, a⟩
  | .lam ty b => Enc.encBind ⟨ty, b⟩
  | .forallE ty b => Enc.encBind ⟨ty, b⟩
  | .letE ty v b => Enc.encLet ⟨ty, v, b⟩
  | .lit l => Enc.encLit ⟨l⟩
  | .proj n i e => Enc.encProj ⟨n, i, e⟩

/-- A view's constructor number (= `ETag`). -/
def _root_.ConRon.Arena.ENodeView.tagN : ENodeView → Nat
  | .bvar _ => 0 | .fvar _ _ => 1 | .sort _ => 2 | .const _ _ => 3 | .app _ _ => 4
  | .lam _ _ => 5 | .forallE _ _ => 6 | .letE _ _ _ => 7 | .lit _ => 8 | .proj _ _ _ => 9

def eViewP : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.op .and [.shift .lsr (vv lDh) (.const 26), .const 31]) (.const 4)) hang .skip)
    (storeRow 9 10)

theorem narrow_app_iff {k : IdxKind} (i : Idx k) :
    (Enc.idxW i >>> (26 : Nat)) &&& 31 = 4 ↔ (i.isWide = false ∧ i.tag = 4) := by
  have hw : (Enc.idxW i).toNat = i.word.toNat := by simp [Enc.idxW]
  have hlt : i.word.toNat < 2 ^ 32 := i.word.toNat_lt
  have e1 : ((Enc.idxW i >>> (26 : Nat)) &&& 31 = 4) ↔ i.word.toNat / 67108864 % 32 = 4 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow] at this
      have e : (31 : BitVec 64).toNat = 2 ^ 5 - 1 := rfl
      rw [e, Nat.and_two_pow_sub_one_eq_mod] at this; simpa using this
    · intro h; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow]
      have e : (31 : BitVec 64).toNat = 2 ^ 5 - 1 := rfl
      rw [e, Nat.and_two_pow_sub_one_eq_mod]; simpa using h
  rw [e1]
  simp only [Idx.isWide, Idx.tag, beq_iff_eq]
  constructor
  · intro h
    have hnw : ¬ (i.word / 1073741824 % 2 = 1) := by
      intro c; have := congrArg UInt32.toNat c; simp [UInt32.toNat_div, UInt32.toNat_mod] at this; omega
    refine ⟨by simpa using hnw, ?_⟩
    rw [if_neg hnw]; apply UInt32.toNat_inj.mp; simp [UInt32.toNat_div, UInt32.toNat_mod]; omega
  · rintro ⟨h1, h2⟩
    have hnw : ¬ (i.word / 1073741824 % 2 = 1) := by simpa using h1
    rw [if_neg hnw] at h2
    have a := congrArg UInt32.toNat h2
    have b : ¬ (i.word.toNat / 1073741824 % 2 = 1) := by
      intro c; apply hnw; apply UInt32.toNat_inj.mp; simp [UInt32.toNat_div, UInt32.toNat_mod]; omega
    simp [UInt32.toNat_div, UInt32.toNat_mod] at a; omega

section
variable {σ : Type}

theorem eView_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL : BitVec 64) (st : EStore)
    (hR : ERep t L FL st) (i : EIdx)
    (hh : t.locals.lookup lDh = some (.val (.word (Enc.idxW i))))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (ht : ∃ w, t.locals.lookup lDt = some (.val (.word w))) (hg : ∃ w, t.locals.lookup lDg = some (.val (.word w)))
    (hi : ∃ w, t.locals.lookup lDi = some (.val (.word w)))
    (h1 : ∃ w, t.locals.lookup lRp = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lRn = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t eViewP).1 ∨ ∃ v, st.view i = some v ∧ v.tagN = i.tag.toNat ∧
      RowRes t i.tier.toNat i.tag.toNat i.idxNat (encEView v) (evaluateHOLFiniteState t eViewP) := by
  have hidx : i.idxNat < 2 ^ 30 := by
    simp only [Idx.idxNat, Idx.index]; split <;> simp [UInt32.toNat_mod] <;> omega
  unfold eViewP
  have hc : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .equal (.op .and [.shift .lsr (vv lDh) (.const 26), .const 31]) (.const 4)) =
      some (.val (.word (bw ((Enc.idxW i >>> (26 : Nat)) &&& 31 = 4)))) := by
    rw [ConsLoop.eval_cmp_of t .equal _ _ _ 4 (eval_and2' t _ _ _ _ (eval_shr t _ _ _ (eval_vv t lDh _ hh) (by decide))
      (eval_const t 31)) (eval_const t 4)]
    simp only [show (26 : BitVec 64).toNat = 26 from rfl]
    by_cases h : (Enc.idxW i >>> (26 : Nat)) &&& 31 = 4
    · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hn : (Enc.idxW i >>> (26 : Nat)) &&& 31 = 4
  · left
    apply seq_stop
    rw [ite_word t _ _ _ _ hc]
    simp only [bw, hn, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact hang_stop t
  have hwide : i.tag = 4 → i.isWide = true := fun h4 => by
    cases hw : i.isWide
    · exact absurd ((narrow_app_iff i).mpr ⟨hw, h4⟩) hn
    · rfl
  have hsk : evaluateHOLFiniteState t (.ite (.cmp .equal (.op .and [.shift .lsr (vv lDh) (.const 26), .const 31])
      (.const 4)) hang .skip) = (none, t) := by
    rw [ite_word t _ _ _ _ hc]
    simp only [bw, hn, ↓reduceIte, ne_eq, not_true_eq_false]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
  rw [seq_normal _ hsk]
  refine storeRow_gen t L FL st.scratchOn 9 10 (by decide) i (fun r => ∃ v, st.view i = some v ∧ v.tagN = i.tag.toNat ∧
    RowRes t i.tier.toNat i.tag.toNat i.idxNat (encEView v) r) hh hdir hfl hR.fl ht hg hi h1 h2 ?_
  intro htag hlive u um ud uc ug uta udir udt udg udi uo1 uo2 ufr
  have pick : ∃ (tr : UInt32) (et : ETables), st.view i = et.get i ∧
      TabAt t L 9 i.tier.toNat Enc.encBVar dWN et.bvars (mkN ETag.bvar tr) ∧
      TabAt t L 10 i.tier.toNat Enc.encFVar dWN et.fvars (mkN ETag.fvar tr) ∧
      TabAt t L 11 i.tier.toNat Enc.encSort dWN et.sorts (mkN ETag.sort tr) ∧
      TabAt t L 12 i.tier.toNat Enc.encConst dWN et.consts (mkN ETag.const tr) ∧
      TabAt t L 13 i.tier.toNat Enc.encApp dWN et.apps (mkW tr) ∧
      TabAt t L 14 i.tier.toNat Enc.encBind dWN et.lams (mkN ETag.lam tr) ∧
      TabAt t L 15 i.tier.toNat Enc.encBind dWN et.foralls (mkN ETag.forallE tr) ∧
      TabAt t L 16 i.tier.toNat Enc.encLet dWN et.lets (mkN ETag.letE tr) ∧
      TabAt t L 17 i.tier.toNat Enc.encLit dWN et.lits (mkN ETag.lit tr) ∧
      TabAt t L 18 i.tier.toNat Enc.encProj dWN et.projs (mkN ETag.proj tr) := by
    have htl := Idx.tier_lt i
    rcases (by omega : i.tier.toNat = 0 ∨ i.tier.toNat = 1) with h0 | h0
    · have e0 : i.tier = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
      refine ⟨0, st.pers, ?_, ?_⟩
      · simp only [EStore.view, Idx.isPersistent, beq_iff_eq]; rw [if_pos e0]
      · rw [h0]; exact ⟨hR.p0, hR.p1, hR.p2, hR.p3, hR.p4, hR.p5, hR.p6, hR.p7, hR.p8, hR.p9⟩
    · have hnp : ¬ i.isPersistent = true := by
        simp only [Idx.isPersistent, beq_iff_eq]; intro e; rw [e] at h0; simp at h0
      have hon : st.scratchOn = true := by rcases hlive with h | h; omega; exact h
      refine ⟨1, st.scr, ?_, ?_⟩
      · simp only [EStore.view]; rw [if_neg hnp, hon]; rfl
      · rw [h0]; exact ⟨hR.s0, hR.s1, hR.s2, hR.s3, hR.s4, hR.s5, hR.s6, hR.s7, hR.s8, hR.s9⟩
  obtain ⟨tr, et, hview, hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9⟩ := pick
  have htl := Idx.tier_lt i
  obtain ⟨m, hm, hmt⟩ := tag_cases i 10 htag
  have hgm : u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 m))) := by
    rw [show (BitVec.ofNat 64 m) = BitVec.ofNat 64 i.tag.toNat by rw [hmt]; simp; rw [Nat.mod_eq_of_lt (by omega)]]
    exact udg
  have htm : i.tag.toNat = m := by rw [hmt]; simp; omega
  simp only [htm]
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases rowAt_spec t u L 9 0 i.tier.toNat i.idxNat Enc.encBVar dWN et.bvars _ (tabAt_eq hT0 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.bvar (et.bvars.nodes[i.idxNat]'hlt).i, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 1 i.tier.toNat i.idxNat Enc.encFVar dWN et.fvars _ (tabAt_eq hT1 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.fvar (et.fvars.nodes[i.idxNat]'hlt).idx (et.fvars.nodes[i.idxNat]'hlt).ty, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 2 i.tier.toNat i.idxNat Enc.encSort dWN et.sorts _ (tabAt_eq hT2 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.sort (et.sorts.nodes[i.idxNat]'hlt).u, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 3 i.tier.toNat i.idxNat Enc.encConst dWN et.consts _ (tabAt_eq hT3 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.const (et.consts.nodes[i.idxNat]'hlt).n (et.consts.nodes[i.idxNat]'hlt).us, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 4 i.tier.toNat i.idxNat Enc.encApp dWN et.apps _ (tabAt_eq hT4 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.app (et.apps.nodes[i.idxNat]'hlt).f (et.apps.nodes[i.idxNat]'hlt).a, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, hwide, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 5 i.tier.toNat i.idxNat Enc.encBind dWN et.lams _ (tabAt_eq hT5 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.lam (et.lams.nodes[i.idxNat]'hlt).ty (et.lams.nodes[i.idxNat]'hlt).body, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 6 i.tier.toNat i.idxNat Enc.encBind dWN et.foralls _ (tabAt_eq hT6 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.forallE (et.foralls.nodes[i.idxNat]'hlt).ty (et.foralls.nodes[i.idxNat]'hlt).body, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 7 i.tier.toNat i.idxNat Enc.encLet dWN et.lets _ (tabAt_eq hT7 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.letE (et.lets.nodes[i.idxNat]'hlt).ty (et.lets.nodes[i.idxNat]'hlt).val (et.lets.nodes[i.idxNat]'hlt).body, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 8 i.tier.toNat i.idxNat Enc.encLit dWN et.lits _ (tabAt_eq hT8 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.lit (et.lits.nodes[i.idxNat]'hlt).l, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]
  · rcases rowAt_spec t u L 9 9 i.tier.toNat i.idxNat Enc.encProj dWN et.projs _ (tabAt_eq hT9 um ud) htl (by decide)
      hidx udir udt hgm udi uo1 uo2 um ud uc ug uta ufr with hs | ⟨hlt, hr⟩
    · exact Or.inl hs
    right
    refine ⟨.proj (et.projs.nodes[i.idxNat]'hlt).n (et.projs.nodes[i.idxNat]'hlt).i (et.projs.nodes[i.idxNat]'hlt).e, ?_, ?_, hr⟩
    · rw [hview]; simp [ETables.get, Tbl.node?, hmt, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Array.getElem?_eq_getElem hlt]
    · simp [ENodeView.tagN, hmt]

end

end ConPanqueque.V
