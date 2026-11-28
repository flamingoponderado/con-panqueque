import ConPanqueque.T.Ind.ClassConst

/-!
# `classRecTysOk`: every recursor's generated type

`crsBody`: a loop over the stream's recursor records (a `PtrsRep` block) and the recursors' classes (a word block),
running `classRecTyOk` (`croBody`) on recursor `i` at class `recCls[i]` and collecting the generated constants into a
block of pointers.  A class list shorter than the recursor list hangs (the twin fails).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def crsOr := ofString "crs_or"
def crsI := ofString "crs_i"
def crsN := ofString "crs_n"
def crsOc := ofString "crs_oc"
def crsNS := ofString "crs_ns"
def crsPre := ofString "crs_pre"
def crsPrl := ofString "crs_prl"
def crsNP := ofString "crs_np"
def crsOms := ofString "crs_oms"
def crsFts := ofString "crs_fts"
def crsOsl := ofString "crs_osl"
def crsQ := ofString "crs_q"
def crsR := ofString "crs_r"
def crsC := ofString "crs_c"
def crsX := ofString "crs_x"
def fCrs := ofString "classRecTysOk"

def crsParams : List MlS := [crsOr, crsI, crsN, crsOc, crsNS, crsPre, crsPrl, crsNP, crsOms, crsFts, crsOsl]
def crsLocals : List MlS := gaaLocals ++ [crsQ, crsR, crsC, crsX]

def crsBody (C : Ctx) : ProgHOL 64 := prologue crsLocals
  (.ite (.cmp .lower (vv crsI) (vv crsN))
    (.seq (.assign .local crsQ (.load .one (vv crsOc)))
    (.ite (.cmp .lower (vv crsI) (vv crsQ))
    (.seq (.assign .local crsR (.load .one (.op .add [vv crsOr, .op .add [.panop .mul [vv crsI, .const 8], .const 8]])))
    (.seq (.assign .local crsC (.load .one (.op .add [vv crsOc, .op .add [.panop .mul [vv crsI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, crsX), none)) fCro
      [vv crsR, vv crsNS, vv crsPre, vv crsPrl, vv crsNP, vv crsOms, vv crsFts, vv crsOsl, vv crsC])
    (.seq (.call (some (some (.local, ExS.lY), none)) fCrs
      [vv crsOr, .op .add [vv crsI, .const 1], vv crsN, vv crsOc, vv crsNS, vv crsPre, vv crsPrl, vv crsNP, vv crsOms,
        vv crsFts, vv crsOsl])
    (prependP C crsX)))))
    hang))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure CRSCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  cro : CROCodes mode C
  self : C.code.lookup fCrs = some (crsParams.map (fun p => (p, ShapeHOL.one)), crsBody C, .one)

section
variable {σ : Type}

theorem crs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crsLocals → (ctxEnv C ++ crsParams.zip vals).get x = none :=
  Knot.params_none C crsLocals crsParams vals (by decide) (by decide)

/-- A list of constant values, as a block of pointers to their records. -/
def PostCVGs (C : Ctx) (cvs : List IConstantVal) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ PRep C H' o (fun H o cv => CVRep C H o cv) cvs ∧ SR (ctxH C H') s' st

theorem postCVGs_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCVGs C a w s' st → PostCVGs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

/-- A block of pointers in the heap is shorter than `2 ^ 61`. -/
theorem ptrsRep_len_lt {α : Type} {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} (hHN : H.length ≤ C.HN) {o : Nat}
    {Rep : Nat → α → Prop} {xs : List α} (h : PtrsRep C H o Rep xs) : xs.length < 2 ^ 61 := by
  have hlay := hok.heapLay
  have := (List.getElem?_eq_some_iff.mp h.1).1
  rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
  · omega
  · obtain ⟨oi, h1, -⟩ := h.2 (xs.length - 1) (by omega)
    have := (List.getElem?_eq_some_iff.mp h1).1
    omega

set_option maxHeartbeats 16000000 in
/-- **`classRecTysOk`** from recursor `i` on: recursor `j` at class `recCls[j]`, against its own stream type. -/
theorem crs_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CRSCodes mode C)
    (g : ClassGen) (opre : Nat)
    (hprl : g.pre.length < 2 ^ 56) (hpre : BlkAt C.H opre (g.pre.map Enc.idxW))
    (oms fts osl : Nat) (hT : TMBlkR C C.H oms g.cls) (hfts : BlkAt C.H fts (g.formerTys.map Enc.idxW))
    (hsb : SlotBlk C C.H osl g.slots) (hnP : g.nP < 2 ^ 56)
    (hsll : g.slots.length < 2 ^ 56) (kk : Nat) (rcs : List RecShape) (orl : Nat)
    (hR : PtrsRep C C.H orl (RecRep C C.H) rcs) (recCls : List Nat) (orc : Nat)
    (hRC : BlkAt C.H orc (recCls.map (BitVec.ofNat 64))) (hcb : ∀ c ∈ recCls, c < 2 ^ 63)
    (hrl : ∀ rc ∈ rcs, rc.cvR.levelParams.length < 2 ^ 62)
    (hks : ∀ rc ∈ rcs, ∃ ks : List ConLeche.Name, ∃ _ : ks.length = rc.cvR.levelParams.length,
      ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (ks[j]'(by omega))) :
    ∀ f i (H : List (BitVec 64)) (s : AState), rcs.length - i = f → i ≤ rcs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (crsParams.zip [cellA C orl, BitVec.ofNat 64 i, BitVec.ofNat 64 rcs.length,
        cellA C orc, BitVec.ofNat 64 (g.nP + g.slots.length), cellA C opre, BitVec.ofNat 64 g.pre.length,
        BitVec.ofNat 64 g.nP, cellA C oms, cellA C fts, cellA C osl])) (crsBody C) s
        (classRecTysOk mode C.fe g kk (rcs.drop i) ((rcs.map (·.cvR)).drop i) (recCls.drop i)) (PostCVGs (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = rcs.length := by omega
    subst hin
    refine specR_prologue (postCVGs_locals _) (crs_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hrcsl := ptrsRep_len_lt hok (Nat.le_trans (List.IsPrefix.length_le hp) hHN) hR
    have hlw := nd_lt_iff rcs.length rcs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    simp only [classRecTysOk]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
        fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < rcs.length := by omega
    refine specR_prologue (postCVGs_locals _) (crs_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hrcsl := ptrsRep_len_lt hok (Nat.le_trans (List.IsPrefix.length_le hp) hHN) hR
    have hlw := nd_lt_iff i rcs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hrc0 := get_prefix hRC.1 hp
    simp only [List.length_map] at hrc0
    refine UD.specR_heapLoadI' (C := ctxH C H) crsQ (vv crsOc) orc _ hrc0 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv]; rfl) ?_
    have hrcl : recCls.length < 2 ^ 61 := by
      have := blk_len_lt hok hHN' (blkAt_mono hRC hp); simp at this; omega
    have hlw2 := nd_lt_iff i recCls.length (by omega) (by omega)
    by_cases hic : i < recCls.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crsParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crsParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr hic]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨orr, horr, hrr⟩ := hR.2 i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) crsR _ (orl + 1 + i) _ (get_prefix horr hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv]; exact cellA_mulIdx C orl i (by omega)) ?_
    have hci := hRC.2 i (by simp; omega)
    simp only [List.getElem_map] at hci
    refine UD.specR_heapLoadI' (C := ctxH C H) crsC _ (orc + 1 + i) _ (get_prefix hci hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv]; exact cellA_mulIdx C orc i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin, List.drop_eq_getElem_cons (show i < (rcs.map (·.cvR)).length by simp; omega), List.drop_eq_getElem_cons hic]
    simp only [classRecTysOk, bind_assoc, List.getElem_map]
    have hmem := List.getElem_mem hin
    obtain ⟨ks, hkl, hks'⟩ := hks _ hmem
    have hcl := hcb _ (List.getElem_mem hic)
    refine specR_callNIH (C := ctxH C H) crsX fCro croParams
      [vv crsR, vv crsNS, vv crsPre, vv crsPrl, vv crsNP, vv crsOms, vv crsFts, vv crsOsl, vv crsC] (croBody C)
      [cellA C orr, BitVec.ofNat 64 (g.nP + g.slots.length), cellA C opre, BitVec.ofNat 64 g.pre.length,
        BitVec.ofNat 64 g.nP, cellA C oms, cellA C fts, cellA C osl, BitVec.ofNat 64 recCls[i]] (by decide) rfl
      (by decide) hc.cro.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostCVG (ctxH C H)) (fun cv w _ H' => ∃ o, w = cellA C o ∧ CVRep C H' o cv)
      (fun cv w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu croParams _ rfl hlk)
        (cro_spec mode ra (ctxH C H) (ctxOK_H hok H) hs (by ctx_tr hc.cro) g recCls[i] hcl opre hprl (blkAt_mono hpre hp)
          oms fts osl (tmBlkR_mono hp hT) (blkAt_mono hfts hp) (slotBlk_mono hp hsb) hnP hsll kk rcs[i] orr
          (recRep_mono hp hrr) (hrl _ hmem) ks hkl hks' s))
      (fun cvG w s1 H1 hp1 ⟨ox, hw, hcvx⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fCrs crsParams
      [vv crsOr, .op .add [vv crsI, .const 1], vv crsN, vv crsOc, vv crsNS, vv crsPre, vv crsPrl, vv crsNP, vv crsOms,
        vv crsFts, vv crsOsl] (crsBody C)
      [cellA C orl, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rcs.length, cellA C orc,
        BitVec.ofNat 64 (g.nP + g.slots.length), cellA C opre, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP,
        cellA C oms, cellA C fts, cellA C osl] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crsParams, ctxEnv], trivial⟩
      (PostCVGs (ctxH C H1))
      (fun cvs w _ H' => ∃ o, w = cellA C o ∧ PRep C H' o (fun H o cv => CVRep C H o cv) cvs)
      (fun cvs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crsParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun cvs w s2 H2 hp2 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    obtain ⟨oss, hossl, hossb, hossr⟩ := hry
    refine ExPre.prepend_spec C hok (H := H2) crsX (cellA C ox) oy (oss.map (cellA C)) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hossb (by decide)
      (by simp +decide [Env.get_cons, Env.get, crsParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, hp1'.trans (hp2'.trans hp'), rfl,
      ⟨ox :: oss, by simp [hossl], hb, fun j hj hjo => by
        rcases j with _ | j
        · exact cvRep_mono (hp2'.trans hp') hcvx
        · exact cvRep_mono hp' (hossr j (by simpa using hj) (by simpa using hjo))⟩, hsr⟩

end

end ConPanqueque.T.Ind
