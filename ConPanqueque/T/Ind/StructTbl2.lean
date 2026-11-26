import ConPanqueque.T.Ind.StructTbl
import ConPanqueque.T.Ind.IotaCtor

/-!
# A structure's projection bodies (`structProjBodies`)

`spbBody`: the constructor type's parameters stripped (none hangs), the parameter spine `structProjPs`, then
the bodies (`structProjBodiesGo`).  The values' and fields' total is bounded at run time (else a hang).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC ConPanqueque.T.ExIL

def spbT := ofString "spb_t"
def spbNp := ofString "spb_np"
def spbNf := ofString "spb_nf"
def spbC := ofString "spb_c"
def spbY := ofString "spb_y"
def spbN1 := ofString "spb_n1"
def spbR := ofString "spb_r"
def spbNp1 := ofString "spb_np1"
def spbPs := ofString "spb_ps"
def spbPl := ofString "spb_pl"
def spbBs := ofString "spb_bs"
def fSpb := ofString "structProjBodies"

def spbParams : List MlS := [spbT, spbNp, spbNf, spbC]
def spbLocals : List MlS := [spbY, spbN1, spbR, spbNp1, spbPs, spbPl, spbBs]

def spbBody : ProgHOL 64 := prologue spbLocals
  (.seq (.call (some (some (.local, spbY), none)) fStripPis [vv spbNp, vv spbC])
  (.ite (.cmp .equal (vv spbY) (.const 0)) hang
  (.seq (.assign .local spbN1 (.load .one (vv spbY)))
  (.seq (.assign .local spbR (.load .one (.op .add [vv spbY, .shift .lsl (vv spbN1) (.const 3)])))
  (.seq (.assign .local spbNp1 (.op .add [vv spbNp, .const 1]))
  (.seq (.call (some (some (.local, spbPs), none)) fIotaBVars [vv spbNp1, vv spbNp, .const 0])
  (.seq (.assign .local spbPl (.load .one (vv spbPs)))
  (.ite (.cmp .lower (.op .add [vv spbPl, vv spbNf]) (.const (BitVec.ofNat 64 (2 ^ 57))))
    (.seq (.call (some (some (.local, spbBs), none)) fSpg [vv spbT, vv spbPs, vv spbPl, vv spbNf, .const 0, vv spbR])
      (.return (vv spbBs)))
    hang))))))))

structure SPBCodes (C : Ctx) : Prop where
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  ib : C.code.lookup fIotaBVars = some (ibParams.map (fun p => (p, ShapeHOL.one)), ibBody C, .one)
  bv : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  spg : SPGCodes C
  self : C.code.lookup fSpb = some (spbParams.map (fun p => (p, ShapeHOL.one)), spbBody, .one)

section
variable {σ : Type}

theorem spb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ spbLocals → (ctxEnv C ++ spbParams.zip vals).get x = none :=
  Knot.params_none C spbLocals spbParams vals (by decide) (by decide)

/-- Some array of handles, past the value heap. -/
def PostSA (C : Ctx) (o : Option (Array EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ arr H' ob, o = some arr ∧ C.H <+: H' ∧ w = cellA C ob ∧ BlkAt H' ob (arr.toList.map Enc.idxW) ∧ SR (ctxH C H') s' st

theorem postSA_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSA C a w s' st → PostSA C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨arr, H', ob, h0, h1, h2, h3, h4⟩ => ⟨arr, H', ob, h0, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

set_option maxHeartbeats 32000000 in
/-- **`structProjBodies`**. -/
theorem spb_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : SPBCodes C)
    (T : NIdx) (nP nF : Nat) (hnP : nP < 2 ^ 57) (hnF : nF < 2 ^ 57) (cty : EIdx) (s : AState) :
    SpecR (σ := σ) (Pre C s (spbParams.zip [Enc.idxW T, BitVec.ofNat 64 nP, BitVec.ofNat 64 nF, Enc.idxW cty])) spbBody s
      (structProjBodies T nP nF cty) (PostSA C) := by
  refine specR_prologue (postSA_locals C) (spb_none C _) ?_
  unfold structProjBodies
  refine specR_callNIH (C := ctxH C C.H) spbY fStripPis [pFu, pH] [vv spbNp, vv spbC] (stripBody C fStripPis 6)
    [BitVec.ofNat 64 nP, Enc.idxW cty] (by decide) rfl (by decide) hc.sp
    ⟨by simp +decide [sev, Env.get, spbParams, ctxEnv], by simp +decide [sev, Env.get, spbParams, ctxEnv], trivial⟩
    (PostSP (ctxH C C.H)) (fun o w s' H' => (o = none → w = 0) ∧
      ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact stripPis_spec C hok hc.sp nP (by omega) C.H s cty _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun o w s1 H1 hp1 ⟨hn0, hsm⟩ => ?_)
  have hp1' : C.H <+: H1 := hp1
  rcases o with _ | ⟨tys, bb⟩
  · have e0 := hn0 rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob', rfl, hblk⟩ := hsm tys bb rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hblk
  have hHN' : H1.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hne : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  have hl0 : (ctxH C H1).H[ob']? = some (BitVec.ofNat 64 (tys.length + 1)) := by
    show H1[ob']? = _; rw [hblk.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H1) spbN1 (vv spbY) ob' _ hl0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hidx : ob' + 1 + tys.length < H1.length := by
    have := hblk.2 tys.length (by simp)
    exact (List.getElem?_eq_some_iff.mp this).1
  have htl : tys.length + 2 < 2 ^ 61 := by omega
  have hbw : (ctxH C H1).H[ob' + 1 + tys.length]? = some (Enc.idxW bb) := by
    show H1[ob' + 1 + tys.length]? = _
    have := hblk.2 tys.length (by simp); simpa using this
  refine UD.specR_heapLoadI' (C := ctxH C H1) spbR _ (ob' + 1 + tys.length) _ hbw (by decide)
    (by simp +decide [sev, Env.get_cons]; rw [cellA_shl3]; show cellA C _ = cellA C _; congr 1; omega) ?_
  refine specR_assignI spbNp1 _ (BitVec.ofNat 64 (1 + nP)) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, spbParams, ctxEnv]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) ?_
  rw [structProjPs, structPsAt_eq]
  refine specR_callNIH (C := ctxH C H1) spbPs fIotaBVars ibParams [vv spbNp1, vv spbNp, .const 0] (ibBody C)
    [BitVec.ofNat 64 (1 + nP), BitVec.ofNat 64 nP, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ib
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, spbParams, ctxEnv], rfl, trivial⟩
    (PostA (ctxH C H1)) (fun ps w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ps.map Enc.idxW))
    (fun ps w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibParams _ rfl hlk)
      (ib_spec ra C hok hc.ib hc.bv (1 + nP) nP (by omega) (by omega) nP 0 H1 s1 (by omega) (by omega)))
    (fun ps w s2 H2 hp2 ⟨ops, hw, hpsb⟩ => ?_)
  subst hw
  have hp2' : H1 <+: H2 := hp2
  have hpl0 : (ctxH C H2).H[ops]? = some (BitVec.ofNat 64 ps.length) := by
    show H2[ops]? = _; rw [hpsb.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H2) spbPl (vv spbPs) ops _ hpl0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN2 => ?_)
  have hHN2' : H2.length ≤ C.HN := hHN2
  have hpsl : ps.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos ps.length with h0 | hpos
    · omega
    · have h1 := hpsb.2 (ps.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  have hlw := nd_lt_iff (ps.length + nF) (2 ^ 57) (by omega) (by omega)
  by_cases hg : ps.length + nF < 2 ^ 57
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, spbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [← BitVec.ofNat_add, BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, spbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [← BitVec.ofNat_add, BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega)
    (fun _ => ?_) (fun h => absurd h (by decide))
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  refine specR_callNIH (C := ctxH C H2) spbBs fSpg spgParams [vv spbT, vv spbPs, vv spbPl, vv spbNf, .const 0, vv spbR]
    (spgBody C) [Enc.idxW T, cellA C ops, BitVec.ofNat 64 ps.toArray.size, BitVec.ofNat 64 nF, BitVec.ofNat 64 0,
      Enc.idxW bb] (by decide) rfl (by decide) hc.spg.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, spbParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, spbParams, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostSL (ctxH C H2)) (fun o w _ H' => ∃ ds ob, o = some ds ∧ w = cellA C ob ∧ BlkAt H' ob (ds.map Enc.idxW))
    (fun o w s' st ⟨ds, H', ob, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, ob, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu spgParams _ rfl hlk)
      (spg_spec ra C hok hc.spg T nF ps.toArray ops 0 H2 s2 bb hpC2 (by simpa using hpsb) (by simp; omega) (by omega)))
    (fun o w s3 H3 hp3 ⟨ds, ob, ho, hw, hb⟩ => ?_)
  subst ho hw
  simp only
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨ds.toArray, H3, ob, rfl,
    hpC2.trans hp3, rfl, by simpa using hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
