import ConPanqueque.T.Ind.RecRules

/-!
# The generated recursors' names: the pushed names and each class's recursor

`cvnBody`: the names of a block of constant records, as a block (the pushed names `cvGs.map (·.name)`).
`frcBody`: the first recursor at class `t` (`recCls[r] = t`), or the recursor count.  `rnbBody`: for every class
`t < k`, the name of its first recursor (`classRecOf recCls cvGs t`); a class with no recursor hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## The names of a block of constants -/

def cvnO := ofString "cvn_o"
def cvnI := ofString "cvn_i"
def cvnN := ofString "cvn_n"
def cvnQ := ofString "cvn_q"
def cvnX := ofString "cvn_x"
def fCvn := ofString "constNames"

def cvnParams : List MlS := [cvnO, cvnI, cvnN]
def cvnLocals : List MlS := gaaLocals ++ [cvnQ, cvnX]

def cvnBody (C : Ctx) : ProgHOL 64 := prologue cvnLocals
  (.ite (.cmp .lower (vv cvnI) (vv cvnN))
    (.seq (.assign .local cvnQ (.load .one (.op .add [vv cvnO, .op .add [.panop .mul [vv cvnI, .const 8], .const 8]])))
    (.seq (.assign .local cvnX (.load .one (vv cvnQ)))
    (.seq (.call (some (some (.local, ExS.lY), none)) fCvn [vv cvnO, .op .add [vv cvnI, .const 1], vv cvnN])
    (prependP C cvnX))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem cvn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cvnLocals → (ctxEnv C ++ cvnParams.zip vals).get x = none :=
  Knot.params_none C cvnLocals cvnParams vals (by decide) (by decide)

/-- A list of names, as a block. -/
def PostNBlk (C : Ctx) (ns : List NIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o (ns.map Enc.idxW) ∧ SR (ctxH C H') s' st

theorem postNBlk_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNBlk C a w s' st → PostNBlk C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

set_option maxHeartbeats 8000000 in
/-- **The names of the constants from `i` on.** -/
theorem cvn_spec (C : Ctx) (hok : CtxOK C) (hc : C.code.lookup fCvn = some (cvnParams.map (fun p => (p, ShapeHOL.one)), cvnBody C, .one))
    (cvs : List IConstantVal) (ocv : Nat) (hcv : PRep C C.H ocv (fun H o cv => CVRep C H o cv) cvs) :
    ∀ f i (H : List (BitVec 64)) (s : AState), cvs.length - i = f → i ≤ cvs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cvnParams.zip [cellA C ocv, BitVec.ofNat 64 i, BitVec.ofNat 64 cvs.length]))
        (cvnBody C) s (pure ((cvs.drop i).map (·.name))) (PostNBlk (ctxH C H)) := by
  obtain ⟨ovs, hovl, hovb, hovr⟩ := hcv
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = cvs.length := by omega
    subst hin
    refine specR_prologue (postNBlk_locals _) (cvn_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hcvl := blk_len_lt hok (Nat.le_trans (List.IsPrefix.length_le hp) hHN) hovb
    simp only [List.length_map] at hcvl
    have hlw := nd_lt_iff cvs.length cvs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cvnParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < cvs.length := by omega
    refine specR_prologue (postNBlk_locals _) (cvn_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hcvl := blk_len_lt hok (Nat.le_trans (List.IsPrefix.length_le hp) hHN) hovb
    simp only [List.length_map] at hcvl
    have hlw := nd_lt_iff i cvs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cvnParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hvi := hovb.2 i (by simp; omega)
    simp only [List.getElem_map] at hvi
    have hcvi : CVRep C C.H ovs[i] cvs[i] := hovr i hin (by omega)
    refine UD.specR_heapLoadI' (C := ctxH C H) cvnQ _ (ocv + 1 + i) _ (get_prefix hvi hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cvnParams, ctxEnv]; exact cellA_mulIdx C ocv i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cvnX (vv cvnQ) ovs[i] _ (get_prefix hcvi.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    rw [List.drop_eq_getElem_cons hin, List.map_cons]
    refine specR_congr (m' := pure ((cvs.drop (i + 1)).map (·.name)) >>= fun ns => pure (cvs[i].name :: ns))
      (by rw [pure_bind]) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fCvn cvnParams [vv cvnO, .op .add [vv cvnI, .const 1], vv cvnN]
      (cvnBody C) [cellA C ocv, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cvs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cvnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cvnParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cvnParams, ctxEnv], trivial⟩
      (PostNBlk (ctxH C H)) (fun ns w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ns.map Enc.idxW))
      (fun ns w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cvnParams _ rfl hlk)
        (ih (i + 1) H s (by omega) (by omega) hp))
      (fun ns w s1 H1 hp1 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine ExPre.prepend_spec C hok (H := H1) cvnX (Enc.idxW cvs[i].name) oy (ns.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hry (by decide)
      (by simp +decide [Env.get_cons, Env.get, cvnParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, hp1'.trans hp', rfl, by simpa using hb, hsr⟩

end

/-! ## The first recursor at a class -/

def frcO := ofString "frc_o"
def frcT := ofString "frc_t"
def frcR := ofString "frc_r"
def frcN := ofString "frc_n"
def frcC := ofString "frc_c"
def frcX := ofString "frc_x"
def fFrc := ofString "firstRecAt"

def frcParams : List MlS := [frcO, frcT, frcR, frcN]
def frcLocals : List MlS := [frcC, frcX]

def frcBody : ProgHOL 64 := prologue frcLocals
  (.ite (.cmp .lower (vv frcR) (vv frcN))
    (.seq (.assign .local frcC (.load .one (.op .add [vv frcO, .op .add [.panop .mul [vv frcR, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv frcC) (vv frcT))
      (.return (vv frcR))
      (.seq (.call (some (some (.local, frcX), none)) fFrc [vv frcO, vv frcT, .op .add [vv frcR, .const 1], vv frcN])
      (.return (vv frcX)))))
    (.return (vv frcN)))

/-- The first `r ∈ [i, n)` with `recCls[r] = t`, or `n`. -/
def firstRecFrom (recCls : List Nat) (t n : Nat) (i : Nat) : Nat :=
  ((List.range' i (n - i)).find? (fun r => recCls.getD r 0 == t)).getD n

theorem firstRecFrom_stop (recCls : List Nat) (t n i : Nat) (hi : n ≤ i) : firstRecFrom recCls t n i = n := by
  simp [firstRecFrom, Nat.sub_eq_zero_of_le hi]

theorem firstRecFrom_hit (recCls : List Nat) (t n i : Nat) (hi : i < n) (h : recCls.getD i 0 = t) :
    firstRecFrom recCls t n i = i := by
  unfold firstRecFrom
  rw [show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ, List.find?_cons]
  have hb : (recCls.getD i 0 == t) = true := beq_iff_eq.mpr h
  rw [hb]; rfl

theorem firstRecFrom_miss (recCls : List Nat) (t n i : Nat) (hi : i < n) (h : recCls.getD i 0 ≠ t) :
    firstRecFrom recCls t n i = firstRecFrom recCls t n (i + 1) := by
  unfold firstRecFrom
  rw [show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ, List.find?_cons]
  have hb : (recCls.getD i 0 == t) = false := by simpa using h
  rw [hb]

/-- A found recursor is the one `classRecOf` reads. -/
theorem classRecOf_of_first (recCls : List Nat) (cvGs : List IConstantVal) (t : Nat)
    (h : firstRecFrom recCls t cvGs.length 0 < cvGs.length) :
    classRecOf recCls cvGs t = some (cvGs[firstRecFrom recCls t cvGs.length 0]'h).name := by
  unfold classRecOf
  have e : List.range cvGs.length = List.range' 0 (cvGs.length - 0) := by rw [List.range_eq_range', Nat.sub_zero]
  rw [e]
  revert h
  unfold firstRecFrom
  rcases hf : (List.range' 0 (cvGs.length - 0)).find? (fun r => recCls.getD r 0 == t) with _ | r
  · intro h; simp at h
  · intro h
    have h' : r < cvGs.length := by simpa using h
    simp only [Option.getD_some, Option.map_some]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h']

section
variable {σ : Type}

theorem frc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ frcLocals → (ctxEnv C ++ frcParams.zip vals).get x = none :=
  Knot.params_none C frcLocals frcParams vals (by decide) (by decide)

/-- A natural number, the heap unchanged. -/
def PostNat (C : Ctx) (v : Nat) (w : BitVec 64) (_ : AState) (_ : PState σ) : Prop := w = BitVec.ofNat 64 v

set_option maxHeartbeats 8000000 in
/-- **The first recursor at class `t` from `r` on** (the classes as words; `n ≤ |recCls|`). -/
theorem frc_spec (C : Ctx) (hok : CtxOK C) (hc : C.code.lookup fFrc = some (frcParams.map (fun p => (p, ShapeHOL.one)), frcBody, .one))
    (recCls : List Nat) (orc : Nat) (hRC : BlkAt C.H orc (recCls.map (BitVec.ofNat 64))) (hrcb : ∀ c ∈ recCls, c < 2 ^ 63)
    (t n : Nat) (ht : t < 2 ^ 63) (hn : n ≤ recCls.length) :
    ∀ f r (s : AState), n - r = f → r ≤ n →
      SpecR (σ := σ) (Pre C s (frcParams.zip [cellA C orc, BitVec.ofNat 64 t, BitVec.ofNat 64 r, BitVec.ofNat 64 n]))
        frcBody s (pure (firstRecFrom recCls t n r)) (fun _ w s' st => w = BitVec.ofNat 64 (firstRecFrom recCls t n r) ∧ SR C s' st) := by
  intro f
  induction f with
  | zero =>
    intro r s hf hr
    have hin : r = n := by omega
    subst hin
    refine specR_prologue (fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩) (frc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hrcl : recCls.length < 2 ^ 61 := by
      have := blk_len_lt hok hHN hRC; simp at this; omega
    have hlw := nd_lt_iff r r (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [firstRecFrom_stop recCls t r r (Nat.le_refl _)]
    exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro r s hf hr
    have hin : r < n := by omega
    refine specR_prologue (fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩) (frc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hrcl : recCls.length < 2 ^ 61 := by
      have := blk_len_lt hok hHN hRC; simp at this; omega
    have hlw := nd_lt_iff r n (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hrl : r < recCls.length := by omega
    have hci := hRC.2 r (by simp; omega)
    simp only [List.getElem_map] at hci
    refine UD.specR_heapLoadI' (C := C) frcC _ (orc + 1 + r) _ hci (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv]; exact cellA_mulIdx C orc r (by omega)) ?_
    have hcb := hrcb _ (List.getElem_mem hrl)
    have hgd : recCls.getD r 0 = recCls[r] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl]
    by_cases hct : recCls[r] = t
    · rw [firstRecFrom_hit recCls t n r hin (by rw [hgd, hct])]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hct])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv])
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : BitVec.ofNat 64 recCls[r] ≠ BitVec.ofNat 64 t := fun e => hct (by
        have h2 := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at h2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2; exact h2)
      rw [firstRecFrom_miss recCls t n r hin (by rw [hgd]; exact hct)]
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_congr (m' := pure (firstRecFrom recCls t n (r + 1)) >>= fun v => pure v) (by rw [pure_bind]) ?_
      refine specR_callNIM frcX fFrc frcParams [vv frcO, vv frcT, .op .add [vv frcR, .const 1], vv frcN] frcBody
        [cellA C orc, BitVec.ofNat 64 t, BitVec.ofNat 64 (r + 1), BitVec.ofNat 64 n] (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv]; exact word_add1_eq r,
          by simp +decide [sev, Env.get_cons, Env.get, frcParams, ctxEnv], trivial⟩
        (fun _ w s' st => w = BitVec.ofNat 64 (firstRecFrom recCls t n (r + 1)) ∧ SR C s' st) (fun _ _ _ _ h => h.2)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu frcParams _ rfl hlk) (ih (r + 1) s (by omega) (by omega)))
        (fun v w s1 st ⟨hw, _⟩ => ?_)
      subst hw
      exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## Every class's recursor name -/

def rnbO := ofString "rnb_o"
def rnbCv := ofString "rnb_cv"
def rnbT := ofString "rnb_t"
def rnbK := ofString "rnb_k"
def rnbN := ofString "rnb_n"
def rnbR := ofString "rnb_r"
def rnbQ := ofString "rnb_q"
def rnbX := ofString "rnb_x"
def fRnb := ofString "classRecNames"

def rnbParams : List MlS := [rnbO, rnbCv, rnbT, rnbK, rnbN]
def rnbLocals : List MlS := gaaLocals ++ [rnbR, rnbQ, rnbX]

def rnbBody (C : Ctx) : ProgHOL 64 := prologue rnbLocals
  (.ite (.cmp .lower (vv rnbT) (vv rnbK))
    (.seq (.call (some (some (.local, rnbR), none)) fFrc [vv rnbO, vv rnbT, .const 0, vv rnbN])
    (.ite (.cmp .lower (vv rnbR) (vv rnbN))
      (.seq (.assign .local rnbQ (.load .one (.op .add [vv rnbCv, .op .add [.panop .mul [vv rnbR, .const 8], .const 8]])))
      (.seq (.assign .local rnbX (.load .one (vv rnbQ)))
      (.seq (.call (some (some (.local, ExS.lY), none)) fRnb [vv rnbO, vv rnbCv, .op .add [vv rnbT, .const 1], vv rnbK, vv rnbN])
      (prependP C rnbX))))
      hang))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure RNBCodes (C : Ctx) : Prop where
  frc : C.code.lookup fFrc = some (frcParams.map (fun p => (p, ShapeHOL.one)), frcBody, .one)
  self : C.code.lookup fRnb = some (rnbParams.map (fun p => (p, ShapeHOL.one)), rnbBody C, .one)

section
variable {σ : Type}

theorem rnb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rnbLocals → (ctxEnv C ++ rnbParams.zip vals).get x = none :=
  Knot.params_none C rnbLocals rnbParams vals (by decide) (by decide)

/-- The recursor names of classes `t0 … k-1`, as a block. -/
def PostRNB (C : Ctx) (recCls : List Nat) (cvGs : List IConstantVal) (t0 k : Nat) (_ : Unit) (w : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, ∃ rns : List NIdx, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o (rns.map Enc.idxW) ∧ rns.length = k - t0 ∧
    (∀ j (hj : j < rns.length), classRecOf recCls cvGs (t0 + j) = some rns[j]) ∧ SR (ctxH C H') s' st

theorem postRNB_locals (C : Ctx) (recCls : List Nat) (cvGs : List IConstantVal) (t0 k : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRNB C recCls cvGs t0 k a w s' st → PostRNB C recCls cvGs t0 k a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, rns, h1, h2, h3, h4, h5, h6⟩ => ⟨H', o, rns, h1, h2, h3, h4, h5, sr_of_eq h6 rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **Every class's recursor name from class `t` on** (`|cvGs| ≤ |recCls|`; a class with no recursor hangs). -/
theorem rnb_spec (C : Ctx) (hok : CtxOK C) (hc : RNBCodes C)
    (recCls : List Nat) (orc : Nat) (hRC : BlkAt C.H orc (recCls.map (BitVec.ofNat 64))) (hrcb : ∀ c ∈ recCls, c < 2 ^ 63)
    (cvGs : List IConstantVal) (ocv : Nat) (hcv : PRep C C.H ocv (fun H o cv => CVRep C H o cv) cvGs)
    (hn : cvGs.length ≤ recCls.length) (k : Nat) (hk : k < 2 ^ 63) :
    ∀ f t (H : List (BitVec 64)) (s : AState), k - t = f → t ≤ k → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (rnbParams.zip [cellA C orc, cellA C ocv, BitVec.ofNat 64 t, BitVec.ofNat 64 k,
        BitVec.ofNat 64 cvGs.length])) (rnbBody C) s (pure ()) (PostRNB (ctxH C H) recCls cvGs t k) := by
  obtain ⟨ovs, hovl, hovb, hovr⟩ := hcv
  intro f
  induction f with
  | zero =>
    intro t H s hf ht hp
    have hin : t = k := by omega
    subst hin
    refine specR_prologue (postRNB_locals _ _ _ _ _) (rnb_none _ _) ?_
    have hlw := nd_lt_iff t t (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t' ht' => ⟨_, H2.length, [],
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, by simp,
        fun j hj => absurd hj (by simp), sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro t H s hf ht hp
    have hin : t < k := by omega
    refine specR_prologue (postRNB_locals _ _ _ _ _) (rnb_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHC : C.H.length ≤ C.HN := Nat.le_trans (List.IsPrefix.length_le hp) hHN
    have hcvl := blk_len_lt hok hHC hovb
    simp only [List.length_map] at hcvl
    have hlw := nd_lt_iff t k (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_congr (m' := pure (firstRecFrom recCls t cvGs.length 0) >>= fun _ => pure ()) (by rw [pure_bind]) ?_
    refine specR_callNIM (C := ctxH C H) rnbR fFrc frcParams [vv rnbO, vv rnbT, .const 0, vv rnbN] frcBody
      [cellA C orc, BitVec.ofNat 64 t, BitVec.ofNat 64 0, BitVec.ofNat 64 cvGs.length] (by decide) rfl (by decide) hc.frc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv],
        rfl, by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv], trivial⟩
      (fun _ w s' st => w = BitVec.ofNat 64 (firstRecFrom recCls t cvGs.length 0) ∧ SR (ctxH C H) s' st) (fun _ _ _ _ h => h.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu frcParams _ rfl hlk)
        (frc_spec (ctxH C H) (ctxOK_H hok H) hc.frc recCls orc (blkAt_mono hRC hp) hrcb t cvGs.length (by omega) hn
          (cvGs.length - 0) 0 s rfl (Nat.zero_le _)))
      (fun v w s1 st ⟨hw, _⟩ => ?_)
    subst hw
    have hvle : firstRecFrom recCls t cvGs.length 0 ≤ cvGs.length := by
      unfold firstRecFrom
      rcases hf : (List.range' 0 (cvGs.length - 0)).find? (fun r => recCls.getD r 0 == t) with _ | r
      · simp
      · have := List.mem_range'_1.mp (List.mem_of_find?_eq_some hf); simp; omega
    have hlw2 := nd_lt_iff (firstRecFrom recCls t cvGs.length 0) cvGs.length (by omega) (by omega)
    by_cases hfd : firstRecFrom recCls t cvGs.length 0 < cvGs.length
    swap
    · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr hfd]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hcro := classRecOf_of_first recCls cvGs t hfd
    generalize firstRecFrom recCls t cvGs.length 0 = r at hfd hcro
    have hvi := hovb.2 r (by simp; omega)
    simp only [List.getElem_map] at hvi
    have hcvi : CVRep C C.H ovs[r] cvGs[r] := hovr r hfd (by omega)
    refine UD.specR_heapLoadI' (C := ctxH C H) rnbQ _ (ocv + 1 + r) _ (get_prefix hvi hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv]; exact cellA_mulIdx C ocv r (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rnbX (vv rnbQ) ovs[r] _ (get_prefix hcvi.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    refine specR_congr (m' := pure () >>= fun _ => pure ()) (by rw [pure_bind]) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fRnb rnbParams [vv rnbO, vv rnbCv, .op .add [vv rnbT, .const 1], vv rnbK, vv rnbN]
      (rnbBody C) [cellA C orc, cellA C ocv, BitVec.ofNat 64 (t + 1), BitVec.ofNat 64 k, BitVec.ofNat 64 cvGs.length]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv]; exact word_add1_eq t,
        by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rnbParams, ctxEnv], trivial⟩
      (PostRNB (ctxH C H) recCls cvGs (t + 1) k)
      (fun _ w _ H' => ∃ o, ∃ rns : List NIdx, w = cellA C o ∧ BlkAt H' o (rns.map Enc.idxW) ∧ rns.length = k - (t + 1) ∧
        ∀ j (hj : j < rns.length), classRecOf recCls cvGs (t + 1 + j) = some rns[j])
      (fun a w s' st ⟨H', o, rns, hp', hw, hb, hl, hr, hsr⟩ => ⟨H', hp', ⟨o, rns, hw, hb, hl, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rnbParams _ rfl hlk)
        (ih (t + 1) H s1 (by omega) (by omega) hp))
      (fun _ w s2 H2 hp2 ⟨oy, rns, hw, hry, hrl, hrr⟩ => ?_)
    subst hw
    have hp2' : H <+: H2 := hp2
    refine ExPre.prepend_spec C hok (H := H2) rnbX (Enc.idxW cvGs[r].name) oy (rns.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hry (by decide)
      (by simp +decide [Env.get_cons, Env.get, rnbParams, ctxEnv]) (by decide) (fun H' o t' hp' hb hsr => ?_)
    refine ⟨H', o, cvGs[r].name :: rns, hp2'.trans hp', rfl, by simpa using hb, by simp; omega, fun j hj => ?_, hsr⟩
    rcases j with _ | j
    · simpa using hcro
    · have := hrr j (by simpa using hj)
      rw [show t + (j + 1) = t + 1 + j by omega]; simpa using this

end

end ConPanqueque.T.Ind
