import ConPanqueque.V.Decode
import ConPanqueque.V.StrHash
import ConPanqueque.V.StoreEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The stores' fixed layout

Every table keeps its geometry for the whole run (a full table hangs, and
dropping the scratch tier empties tables in place). A directory at `DIR`
holds one eight-word descriptor per (kind, tier) at `DIR + 64·(19·tier + kind)`;
the kinds are names 0–2, levels 3–7, level lists 8, expressions 9–18, each a
store's base kind plus the handle's tag. `TabAt` says a twin table is
represented at its kind and tier.
-/

namespace ConPanqueque.V

structure Layout where
  DIR : BitVec 64
  geo : Nat → Nat → VGeo
  base : Nat → Nat → BitVec 64

def descAddr (L : Layout) (k tier : Nat) : BitVec 64 := L.DIR + BitVec.ofNat 64 (64 * (19 * tier + k))

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

/-- The twin's table `tb` is represented at kind `k`, tier `tier`. -/
def TabAt (t : PanSemStateFiniteExact 64 σ) (L : Layout) (k tier : Nat) (enc : α → List (BitVec 64))
    (dW : δ → BitVec 64 × BitVec 64) (tb : Tbl α ι δ) (mkI : Nat → ι) : Prop :=
  DescV t (descAddr L k tier) (L.geo k tier) (L.base k tier) ∧ (L.geo k tier).cap < 2 ^ 30 ∧
    ∃ rows ders slots hu, TierRepV t enc dW (L.geo k tier) tb rows ders slots hu mkI

theorem tabAt_eq {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {k tier : Nat} {enc : α → List (BitVec 64)}
    {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ} {mkI : Nat → ι} (h : TabAt t L k tier enc dW tb mkI)
    (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) : TabAt u L k tier enc dW tb mkI := by
  obtain ⟨hdesc, hcap, rows, ders, slots, hu, hR⟩ := h
  exact ⟨fun k hk => by rw [hm, hd]; exact hdesc k hk, hcap, rows, ders, slots, hu,
    tierRepV_frame hR (fun c _ => by rw [hm]) hd⟩

end

/-- A name table's derived word as a pair. -/
def dWN (d : UInt64) : BitVec 64 × BitVec 64 := (d.toBitVec, 0)

/-- The descriptor pointer for the handle's tier `dt` and tag `dg`, at base kind `kb`. -/
def descE (dir : MlS) (kb : Nat) : ExpHOL 64 :=
  .op .add [vv dir, .shift .lsl (.op .add [.panop .mul [vv lDt, .const 19], vv lDg, .const (BitVec.ofNat 64 kb)])
    (.const 6)]

def lDir := ofString "sdir"
def lFl := ofString "sfl"
def lDG := ofString "dgp"

def zeros : ProgHOL 64 := .seq (.assign .local lDo1 (.const 0)) (.assign .local lDo2 (.const 0))

/-- A store's derived read: decode the handle, then for a valid tag in a live tier read the row's
derived pair through its descriptor, else zeros. `nt` tags from base kind `kb`; `sfl` points at the
store's scratch flag word. -/
def storeDerived (kb nt : Nat) : ProgHOL 64 :=
  .seq decodeH
   (.ite (.cmp .lower (vv lDg) (.const (BitVec.ofNat 64 nt)))
     (.ite (vv lDt)
       (.ite (.load .one (vv lFl)) (.dec lDG .one (descE lDir kb) (derRead lDG)) zeros)
       (.dec lDG .one (descE lDir kb) (derRead lDG)))
     zeros)

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] [Inhabited δ]

/-- Post of a derived read: memory and fixed parts as before, only `do1`, `do2` (and decode scratch)
written, with the given pair. -/
def DRes (t : PanSemStateFiniteExact 64 σ) (p : BitVec 64 × BitVec 64)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  r.1 = none ∧ r.2.memory = t.memory ∧ r.2.memaddrs = t.memaddrs ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    r.2.topAddr = t.topAddr ∧ r.2.clock = t.clock ∧
    r.2.locals.lookup lDo1 = some (.val (.word p.1)) ∧ r.2.locals.lookup lDo2 = some (.val (.word p.2)) ∧
    ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → r.2.locals.lookup y = t.locals.lookup y

theorem readAt (t u : PanSemStateFiniteExact 64 σ) (L : Layout) (kb tag tier idx : Nat) (enc : α → List (BitVec 64))
    (dW : δ → BitVec 64 × BitVec 64) (hdef : dW default = (0, 0)) (tb : Tbl α ι δ) (mkI : Nat → ι)
    (hT : TabAt u L (kb + tag) tier enc dW tb mkI) (htier : tier < 2) (htag : kb + tag < 19) (hidx : idx < 2 ^ 30)
    (hdir : u.locals.lookup lDir = some (.val (.word L.DIR)))
    (hdt : u.locals.lookup lDt = some (.val (.word (BitVec.ofNat 64 tier))))
    (hdg : u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 tag))))
    (hdi : u.locals.lookup lDi = some (.val (.word (BitVec.ofNat 64 idx))))
    (h1 : ∃ w, u.locals.lookup lDo1 = some (.val (.word w))) (h2 : ∃ w, u.locals.lookup lDo2 = some (.val (.word w)))
    (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code) (hg : u.globals = t.globals)
    (hta : u.topAddr = t.topAddr) (hck : u.clock = t.clock)
    (hfr : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → u.locals.lookup y = t.locals.lookup y) :
    DRes t (dW (tb.derAt idx)) (evaluateHOLFiniteState u (.dec lDG .one (descE lDir kb) (derRead lDG))) := by
  obtain ⟨hdesc, hcap, rows, ders, slots, hu, hR⟩ := hT
  have he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) (descE lDir kb) =
      some (.val (.word (descAddr L (kb + tag) tier))) := by
    unfold descE
    rw [eval_add2 u _ _ _ _ (eval_vv u lDir _ hdir) (eval_shl u _ _ _ (eval_add3 u _ _ _ _ _ _
      (eval_mul2 u _ _ _ _ (eval_vv u lDt _ hdt) (eval_const u 19)) (eval_vv u lDg _ hdg) (eval_const u _)) (by decide))]
    congr 3; unfold descAddr; congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, Nat.shiftLeft_eq]
    omega
  rw [dec_word_eq u lDG _ _ _ he]
  let u1 := setVarHOLFinite lDG (.val (.word (descAddr L (kb + tag) tier))) u
  obtain ⟨Lc, e, l1, l2, lfr⟩ := derRead_spec u1 enc dW hdef (L.geo (kb + tag) tier) tb rows ders slots hu mkI
    (descAddr L (kb + tag) tier) (L.base (kb + tag) tier) lDG idx (tierRepV_frame hR (fun _ _ => rfl) rfl) (fun k hk => hdesc k hk) hcap (lookup_setVar_same _ _ _)
    ⟨by decide, by decide⟩ (by lk [u1]; exact hdi) (by omega)
    (by obtain ⟨w, hw⟩ := h1; exact ⟨w, by lk [u1]; exact hw⟩) (by obtain ⟨w, hw⟩ := h2; exact ⟨w, by lk [u1]; exact hw⟩)
  rw [e]
  refine ⟨rfl, hm, hd, hc, hg, hta, hck, ?_, ?_, fun y y1 y2 y3 y4 y5 => ?_⟩
  · rw [lookup_resVar_other _ _ _ _ (by decide)]; exact l1
  · rw [lookup_resVar_other _ _ _ _ (by decide)]; exact l2
  · by_cases eg : y = lDG
    · subst eg; rw [lookup_resVar_same]; exact hfr _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [lookup_resVar_other _ _ _ _ eg, lfr y y1 y2]; lk [u1]; exact hfr y y1 y2 y3 y4 y5

end

open Enc in
/-- The name store in memory: its scratch flag word, and its six tables. -/
structure NRep {σ : Type} (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL : BitVec 64) (st : NStore) : Prop where
  fl : t.memaddrs FL ∧ t.memory FL = .word (if st.scratchOn then 1 else 0)
  pa : TabAt t L 0 0 encAnon dWN st.pers.anons (mkN NTag.anonymous 0)
  ps : TabAt t L 1 0 encStr dWN st.pers.strs (mkN NTag.str 0)
  pn : TabAt t L 2 0 encNum dWN st.pers.nums (mkN NTag.num 0)
  sa : TabAt t L 0 1 encAnon dWN st.scr.anons (mkN NTag.anonymous 1)
  ss : TabAt t L 1 1 encStr dWN st.scr.strs (mkN NTag.str 1)
  sn : TabAt t L 2 1 encNum dWN st.scr.nums (mkN NTag.num 1)

section
variable {σ : Type}

theorem zeros_spec (t u : PanSemStateFiniteExact 64 σ)
    (h1 : ∃ w, u.locals.lookup lDo1 = some (.val (.word w))) (h2 : ∃ w, u.locals.lookup lDo2 = some (.val (.word w)))
    (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code) (hg : u.globals = t.globals)
    (hta : u.topAddr = t.topAddr) (hck : u.clock = t.clock)
    (hfr : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → u.locals.lookup y = t.locals.lookup y) :
    DRes t (0, 0) (evaluateHOLFiniteState u zeros) := by
  obtain ⟨w1, hw1⟩ := h1; obtain ⟨w2, hw2⟩ := h2
  unfold zeros
  rw [seq_normal _ (ConsLoop.assign_local u lDo1 (.const 0) 0 w1 (eval_const u 0) hw1)]
  let u1 := setVarHOLFinite lDo1 (.val (.word 0)) u
  rw [ConsLoop.assign_local u1 lDo2 (.const 0) 0 w2 (eval_const u1 0) (by lk [u1]; exact hw2)]
  exact ⟨rfl, hm, hd, hc, hg, hta, hck, by lk [u1], by lk, fun y y1 y2 y3 y4 y5 => by lk [u1]; exact hfr y y1 y2 y3 y4 y5⟩

theorem tag_cases {k : IdxKind} (i : Idx k) (n : Nat) (h : i.tag.toNat < n) : ∃ m, m < n ∧ i.tag = UInt32.ofNat m :=
  ⟨i.tag.toNat, h, by simp⟩

theorem nDerived_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL : BitVec 64) (st : NStore)
    (hR : NRep t L FL st) (i : NIdx)
    (hh : t.locals.lookup lDh = some (.val (.word (Enc.idxW i))))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (ht : ∃ w, t.locals.lookup lDt = some (.val (.word w))) (hg : ∃ w, t.locals.lookup lDg = some (.val (.word w)))
    (hi : ∃ w, t.locals.lookup lDi = some (.val (.word w)))
    (h1 : ∃ w, t.locals.lookup lDo1 = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lDo2 = some (.val (.word w))) :
    DRes t (dWN (st.derived i)) (evaluateHOLFiniteState t (storeDerived 0 3)) := by
  obtain ⟨L1, e1, lt, lg, li, lfr⟩ := decodeH_spec t i hh ht hg hi
  unfold storeDerived
  rw [seq_normal _ e1]
  let u : PanSemStateFiniteExact 64 σ := { t with locals := L1 }
  have uo1 : ∃ w, u.locals.lookup lDo1 = some (.val (.word w)) := by
    obtain ⟨w, hw⟩ := h1; exact ⟨w, by show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hw⟩
  have uo2 : ∃ w, u.locals.lookup lDo2 = some (.val (.word w)) := by
    obtain ⟨w, hw⟩ := h2; exact ⟨w, by show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hw⟩
  have ufr : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → u.locals.lookup y = t.locals.lookup y :=
    fun y _ _ a b c => lfr y a b c
  have udir : u.locals.lookup lDir = some (.val (.word L.DIR)) := by
    show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hdir
  have tagw : i.tag.toNat < 2 ^ 32 := i.tag.toNat_lt
  have hcmp : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
      (.cmp .lower (vv lDg) (.const (BitVec.ofNat 64 3))) = some (.val (.word (bw (i.tag.toNat < 3)))) := by
    rw [ConsLoop.eval_cmp_of u .lower _ _ _ _ (eval_vv u lDg _ lg) (eval_const u _)]
    have e : (BitVec.ofNat 64 i.tag.toNat < BitVec.ofNat 64 3) ↔ i.tag.toNat < 3 := by
      rw [BitVec.lt_def, toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by omega)]
    by_cases h : i.tag.toNat < 3
    · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]
    · have : ¬ BitVec.ofNat 64 i.tag.toNat < BitVec.ofNat 64 3 := fun x => h (e.mp x)
      simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  rw [ite_word u _ _ _ _ hcmp]
  have hidx : i.idxNat < 2 ^ 30 := by
    simp only [Idx.idxNat, Idx.index]; split <;> simp [UInt32.toNat_mod] <;> omega
  -- a twin table's derAt at the decoded index, for a valid tag
  have hz : ∀ (nt : NTables), (i.tag.toNat < 3 → False) → nt.derAt i = 0 := by
    intro nt hn; simp only [NTables.derAt]
    have : ¬ (i.tag = NTag.anonymous ∨ i.tag = NTag.str ∨ i.tag = NTag.num) := by
      rintro (h | h | h) <;> (rw [h] at hn; exact hn (by decide))
    simp only [beq_iff_eq]
    rw [if_neg (fun h => this (Or.inl h)), if_neg (fun h => this (Or.inr (Or.inl h))),
      if_neg (fun h => this (Or.inr (Or.inr h)))]
  have huo : u.memory = t.memory ∧ u.memaddrs = t.memaddrs := ⟨rfl, rfl⟩
  -- one tier's tables, read at the decoded tag
  have arm : ∀ (tier : Nat) (tr : UInt32) (nt : NTables), tier < 2 → i.tag.toNat < 3 →
      TabAt t L 0 tier Enc.encAnon dWN nt.anons (mkN NTag.anonymous tr) →
      TabAt t L 1 tier Enc.encStr dWN nt.strs (mkN NTag.str tr) →
      TabAt t L 2 tier Enc.encNum dWN nt.nums (mkN NTag.num tr) →
      u.locals.lookup lDt = some (.val (.word (BitVec.ofNat 64 tier))) →
      DRes t (dWN (nt.derAt i)) (evaluateHOLFiniteState u (.dec lDG .one (descE lDir 0) (derRead lDG))) := by
    intro tier tr nt htr htg hA hS hN hdt
    obtain ⟨m, hm, hmt⟩ := tag_cases i 3 htg
    have hgm : u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 m))) := by
      rw [show (BitVec.ofNat 64 m) = BitVec.ofNat 64 i.tag.toNat by rw [hmt]; simp; rw [Nat.mod_eq_of_lt (by omega)]]
      exact lg
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
    · have e : nt.derAt i = nt.anons.derAt i.idxNat := by simp [NTables.derAt, hmt, NTag.anonymous]
      rw [e]
      exact readAt t u L 0 0 tier i.idxNat Enc.encAnon dWN rfl nt.anons _ (tabAt_eq hA rfl rfl) htr (by decide) hidx udir hdt hgm li
        uo1 uo2 rfl rfl rfl rfl rfl rfl ufr
    · have e : nt.derAt i = nt.strs.derAt i.idxNat := by simp [NTables.derAt, hmt, NTag.anonymous, NTag.str]
      rw [e]
      exact readAt t u L 0 1 tier i.idxNat Enc.encStr dWN rfl nt.strs _ (tabAt_eq hS rfl rfl) htr (by decide) hidx udir hdt hgm li
        uo1 uo2 rfl rfl rfl rfl rfl rfl ufr
    · have e : nt.derAt i = nt.nums.derAt i.idxNat := by
        simp [NTables.derAt, hmt, NTag.anonymous, NTag.str, NTag.num]
      rw [e]
      exact readAt t u L 0 2 tier i.idxNat Enc.encNum dWN rfl nt.nums _ (tabAt_eq hN rfl rfl) htr (by decide) hidx udir hdt hgm li
        uo1 uo2 rfl rfl rfl rfl rfl rfl ufr
  by_cases htag : i.tag.toNat < 3
  · simp only [bw, htag, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have htl := Idx.tier_lt i
    rw [ite_word u _ _ _ _ (eval_vv u lDt _ lt)]
    rcases (by omega : i.tier.toNat = 0 ∨ i.tier.toNat = 1) with h0 | h0
    · simp only [h0, show BitVec.ofNat 64 0 = 0 from rfl, ne_eq, not_true_eq_false, ↓reduceIte]
      have hp : st.derived i = st.pers.derAt i := by
        simp only [NStore.derived, Idx.isPersistent, beq_iff_eq]
        have e0 : i.tier = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
        rw [if_pos e0]
      rw [hp]
      exact arm 0 0 st.pers (by decide) htag hR.pa hR.ps hR.pn (by rw [← h0]; exact lt)
    · simp only [h0, show ¬ BitVec.ofNat 64 1 = 0 from by decide, ne_eq, not_false_eq_true, ↓reduceIte]
      have hnp : ¬ i.isPersistent = true := by
        simp only [Idx.isPersistent, beq_iff_eq]; intro e; rw [e] at h0; simp at h0
      have hld : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
          (.load .one (vv lFl)) = some (.val (.word (if st.scratchOn then 1 else 0))) := by
        rw [eval_load_word u _ _ (eval_vv u lFl _ (by show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hfl))
          hR.fl.1]
        show some (ValueHOL.val (t.memory FL)) = _; rw [hR.fl.2]
      rw [ite_word u _ _ _ _ hld]
      cases hon : st.scratchOn
      · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
        have hz0 : st.derived i = 0 := by simp only [NStore.derived]; rw [if_neg hnp, hon]; rfl
        rw [hz0]
        exact zeros_spec t u uo1 uo2 rfl rfl rfl rfl rfl rfl ufr
      · simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
        have hs : st.derived i = st.scr.derAt i := by simp only [NStore.derived]; rw [if_neg hnp, hon]; rfl
        rw [hs]
        exact arm 1 1 st.scr (by decide) htag hR.sa hR.ss hR.sn (by rw [← h0]; exact lt)
  · simp only [bw, htag, ↓reduceIte, ne_eq, not_true_eq_false]
    have hz0 : st.derived i = 0 := by
      simp only [NStore.derived]
      split
      · exact hz _ htag
      · split
        · exact hz _ htag
        · rfl
    rw [hz0]
    exact zeros_spec t u uo1 uo2 rfl rfl rfl rfl rfl rfl ufr

end

end ConPanqueque.V
