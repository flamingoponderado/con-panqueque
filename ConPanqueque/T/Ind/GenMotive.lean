import ConPanqueque.T.Ind.GenPre

/-!
# The generator's pieces: `ClassGen.major`, `ClassGen.motiveTy` (one class)

`mjrBody`: the class's former instantiated at its parameters, its indices opened at `d`, the major `I.{us} D⃗ ı⃗`
(a telescope that does not open, or opens to another index count, hangs).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def mjrDs := ofString "mjr_ds"
def mjrDn := ofString "mjr_dn"
def mjrFt := ofString "mjr_ft"
def mjrNi := ofString "mjr_ni"
def mjrD := ofString "mjr_d"
def mjrInd := ofString "mjr_ind"
def mjrLv := ofString "mjr_lv"
def mjrTy := ofString "mjr_ty"
def mjrX := ofString "mjr_x"
def mjrIf := ofString "mjr_if"
def mjrLi := ofString "mjr_li"
def mjrHd := ofString "mjr_hd"
def mjrA1 := ofString "mjr_a1"
def mjrL1 := ofString "mjr_l1"
def mjrMj := ofString "mjr_mj"
def mjrR := ofString "mjr_r"
def mjrOms := ofString "mjr_oms"
def mjrFts := ofString "mjr_fts"
def mjrCl := ofString "mjr_cl"
def mjrQ := ofString "mjr_q"
def fMjr := ofString "classMajor"

def mjrParams : List MlS := [mjrOms, mjrFts, mjrCl, mjrD]
def mjrLocals : List MlS := [mjrTy, mjrX, mjrIf, mjrLi, mjrHd, mjrA1, mjrL1, mjrMj, mjrR, mjrDs, mjrDn, mjrFt, mjrNi,
  mjrInd, mjrLv, mjrQ]

def mjrBody (C : Ctx) : ProgHOL 64 := prologue mjrLocals
  (.seq (.assign .local mjrQ (.load .one (vv mjrOms)))
  (.ite (.cmp .lower (vv mjrCl) (vv mjrQ))
  (.seq (.assign .local mjrQ (.load .one (vv mjrFts)))
  (.ite (.cmp .lower (vv mjrCl) (vv mjrQ))
  (.seq (.assign .local mjrFt (.load .one (.op .add [vv mjrFts, .op .add [.panop .mul [vv mjrCl, .const 8], .const 8]])))
  (.seq (.assign .local mjrQ (.load .one (.op .add [vv mjrOms, .op .add [.panop .mul [vv mjrCl, .const 8], .const 8]])))
  (.seq (.assign .local mjrNi (.load .one (vv mjrQ)))
  (.seq (.assign .local mjrQ (.load .one (.op .add [vv mjrQ, .const 24])))
  (.seq (.assign .local mjrInd (.load .one (vv mjrQ)))
  (.seq (.assign .local mjrLv (.load .one (.op .add [vv mjrQ, .const 8])))
  (.seq (.assign .local mjrDs (.load .one (.op .add [vv mjrQ, .const 16])))
  (.seq (.assign .local mjrDn (.load .one (vv mjrDs)))
  (guardP mjrNi 56 (guardP mjrDn 56
  (.seq (.call (some (some (.local, mjrTy), none)) fInstPis [vv mjrDs, .const 0, vv mjrDn, vv mjrFt])
  (.seq (.call (some (some (.local, mjrX), none)) fOpenFvars [vv mjrNi, vv mjrTy, vv mjrD])
  (.ite (.cmp .equal (vv mjrX) (.const 0))
  hang
  (.seq (.assign .local mjrIf (.load .one (vv mjrX)))
  (.seq (.assign .local mjrLi (.load .one (vv mjrIf)))
  (.ite (.cmp .equal (vv mjrLi) (vv mjrNi))
  (.seq (.call (some (some (.local, mjrHd), none)) fInternConst [vv mjrInd, vv mjrLv])
  (.seq (.call (some (some (.local, mjrA1), none)) fCat [vv mjrDs, vv mjrIf, .const 0])
  (.seq (.assign .local mjrL1 (.load .one (vv mjrA1)))
  (.seq (.call (some (some (.local, mjrMj), none)) ExK.fMka [vv mjrHd, vv mjrA1, .const 0, vv mjrL1])
  (alloc2 C mjrR (vv mjrIf) (vv mjrMj) (.return (vv mjrR)))))))
  hang))))))))))))))))
  hang))
  hang))

structure MJRCodes (C : Ctx) : Prop where
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  ipw : C.code.lookup fInstPis = some (ipwParams.map (fun p => (p, ShapeHOL.one)), ipwBody, .one)
  i1f : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  i1c : Codes C (ExI.body C)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  cat : CatCodes C
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  self : C.code.lookup fMjr = some (mjrParams.map (fun p => (p, ShapeHOL.one)), mjrBody C, .one)

section
variable {σ : Type}

theorem mjr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mjrLocals → (ctxEnv C ++ mjrParams.zip vals).get x = none :=
  Knot.params_none C mjrLocals mjrParams vals (by decide) (by decide)

/-- A `some (ifs, maj)`, as `[ifs block, maj]`. -/
def PostMJ (C : Ctx) (o : Option (List EIdx × EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' ifs maj ob oi, C.H <+: H' ∧ o = some (ifs, maj) ∧ w = cellA C ob ∧ H'[ob]? = some (cellA C oi) ∧
    BlkAt H' oi (ifs.map Enc.idxW) ∧ H'[ob + 1]? = some (Enc.idxW maj) ∧ ifs.length < 2 ^ 56 ∧ SR (ctxH C H') s' st

theorem postMJ_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostMJ C a w s' st → PostMJ C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', ifs, maj, ob, oi, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
    ⟨H', ifs, maj, ob, oi, h1, h2, h3, h4, h5, h6, h7, sr_of_eq h8 rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **`ClassGen.major c d`**: class `c`'s record read off the class block, its former type off the former-type block
(a class or former type past the blocks hangs). -/
theorem mjr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : MJRCodes C)
    (g : ClassGen) (cl oms fts : Nat) (hcl : cl < 2 ^ 63) (hT : TMBlkR C C.H oms g.cls)
    (hfts : BlkAt C.H fts (g.formerTys.map Enc.idxW)) (d : Nat) (hd : d < 2 ^ 61) (s : AState) :
    SpecR (σ := σ) (Pre C s (mjrParams.zip [cellA C oms, cellA C fts, BitVec.ofNat 64 cl, BitVec.ofNat 64 d]))
      (mjrBody C) s (g.major cl d) (PostMJ C) := by
  refine specR_prologue (postMJ_locals _) (mjr_none _ _) ?_
  unfold ClassGen.major
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN0 => ?_)
  have hHN0' : C.H.length ≤ C.HN := hHN0
  have hlay := hok.heapLay
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := id hT
  have hcl0 : C.H[oms]? = some (BitVec.ofNat 64 g.cls.length) := by simpa [hpsl] using hpsb.1
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrQ (vv mjrOms) oms _ hcl0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv]; rfl) ?_
  have hclen : g.cls.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN0' hpsb; simp at this; omega
  have hlwc := nd_lt_iff cl g.cls.length (by omega) (by omega)
  by_cases hcl' : cl < g.cls.length
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mjrParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mjrParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwc.mpr hcl']) (fun _ => ?_) (fun h => absurd h (by decide))
  have hftl0 : C.H[fts]? = some (BitVec.ofNat 64 g.formerTys.length) := by simpa using hfts.1
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrQ (vv mjrFts) fts _ hftl0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv]; rfl) ?_
  have hftlen : g.formerTys.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN0' hfts; simp at this; omega
  have hlwf := nd_lt_iff cl g.formerTys.length (by omega) (by omega)
  by_cases hcf : cl < g.formerTys.length
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mjrParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mjrParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwf.mpr hcf]) (fun _ => ?_) (fun h => absurd h (by decide))
  have hfx := hfts.2 cl (by simp; omega)
  simp only [List.getElem_map] at hfx
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrFt _ (fts + 1 + cl) _ hfx (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv]; exact cellA_mulIdx C fts cl (by omega)) ?_
  obtain ⟨op, hop, hrep⟩ := hpsr cl hcl'
  have hq := hpsb.2 cl (by simp; omega)
  simp only [List.getElem_map] at hq
  have hpi : ps[cl]'(by omega) = op := by
    rw [List.getElem?_eq_getElem (by omega)] at hop; exact Option.some.inj hop
  rw [hpi] at hq
  simp only [targetMajorAt, List.getElem?_eq_getElem hcl', pure_bind, exprGetD, List.getElem?_eq_getElem hcf]
  generalize g.cls[cl] = m at hrep ⊢
  generalize g.formerTys[cl] = fty at hfx ⊢
  obtain ⟨oa, ha3, hind, hlv, ⟨pd, hpd, hds⟩, -, hniE, -, -, -⟩ := hrep
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrQ _ (oms + 1 + cl) _ hq (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv]; exact cellA_mulIdx C oms cl (by omega)) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrNi (vv mjrQ) op _ hniE.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrQ _ (op + 3) _ ha3 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 3) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrInd (vv mjrQ) oa _ hind (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrLv _ (oa + 1) _ hlv (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oa) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrDs _ (oa + 2) _ hpd (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oa 2) ?_
  have hdl0 := hds.1
  simp only [List.length_map] at hdl0
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mjrDn (vv mjrDs) pd _ hdl0 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  have hdl61 : m.ds.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN0' hds; simp at this; omega
  refine specR_guardI mjrNi m.nIdx 56 (by decide) (by simp +decide [Env.get_cons]) (by have := hniE.2; omega)
    (fun hni => ?_)
  refine specR_guardI mjrDn m.ds.length 56 (by decide) (by simp +decide [Env.get_cons]) (by omega)
    (fun hdl => ?_)
  refine specR_callNIH (C := ctxH C C.H) mjrTy fInstPis ipwParams [vv mjrDs, .const 0, vv mjrDn, vv mjrFt] ipwBody
    [cellA C pd, BitVec.ofNat 64 0, BitVec.ofNat 64 m.ds.length, Enc.idxW fty] (by decide) rfl (by decide) hc.ipw
    ⟨by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], trivial⟩
    (PostSome (ctxH C C.H)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
    (fun o w s' st ⟨t, h1, h2, hsr⟩ => ⟨C.H, hp0, ⟨t, h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipwParams _ rfl hlk)
      (by have hip := ipw_spec (σ := σ) ra C hok hc.ipw hc.i1f hc.i1c m.ds pd C.H hds m.ds.length 0 s fty (by omega) (by omega); simp only [List.drop_zero] at hip; exact hip))
    (fun o w s1 H1 hp1 ⟨ty, ho, hw⟩ => ?_)
  subst ho hw
  have hp1' : C.H <+: H1 := hp1
  simp only
  refine specR_callNIH (C := ctxH C H1) mjrX fOpenFvars ofParams [vv mjrNi, vv mjrTy, vv mjrD]
    (ofBody C) [BitVec.ofNat 64 m.nIdx, Enc.idxW ty, BitVec.ofNat 64 d] (by decide) rfl
    (by decide) hc.ofc ⟨by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], trivial⟩
    (PostOF (ctxH C H1)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op m.nIdx ty d (by omega) (by omega) H1 hp1' s1))
    (fun o w s2 H2 hp2 ⟨hn, hsm⟩ => ?_)
  have hp2' : H1 <+: H2 := hp2
  rcases o with _ | ⟨ifs, e'⟩
  · have e0 := hn rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, oa, rfl, hob, -, hfb⟩ := hsm ifs e' rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol : ob < H2.length := (List.getElem?_eq_some_iff.mp hob).1
  have hHN' : H2.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H2) mjrIf (vv mjrX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfl : H2[oa]? = some (BitVec.ofNat 64 ifs.length) := by simpa using hfb.1
  refine UD.specR_heapLoadI' (C := ctxH C H2) mjrLi (vv mjrIf) oa _ hfl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hil0 : ifs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos ifs.length with h0 | hpos
    · omega
    · have h1 := hfb.2 (ifs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hin : ifs.length = m.nIdx
  swap
  · have hne2 : BitVec.ofNat 64 ifs.length ≠ BitVec.ofNat 64 m.nIdx := fun e => hin (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hin]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  refine ILP.callE_spec (C := ctxH C H2) mjrHd fInternConst [lEn, lEus] [vv mjrInd, vv mjrLv] constBody
    [Enc.idxW m.ind, Enc.idxW m.lvls] (by decide) rfl (by decide) hc.ic ⟨by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], trivial⟩
    (const_body_spec ra (ctxH C H2) (ctxOK_H hok H2) s2 _ _) (fun hd s3 => ?_)
  refine specR_callPure (C := ctxH C H2) mjrA1 fCat catParams [vv mjrDs, vv mjrIf, .const 0] catBody
    [cellA C pd, cellA C oa, BitVec.ofNat 64 0] (m.ds.map Enc.idxW ++ (ifs.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons, Env.get, mjrParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H2 <+: H' ∧ s' = s3 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (ifs.map Enc.idxW) oa (by simp; omega) _ 0 _ pd H2 s3 rfl (by omega)
        (blkAt_mono hds hpC2) hfb))
    (fun w H3 hp3 ⟨o3, hw3, hb3⟩ => ?_)
  subst hw3
  have hp3' : H2 <+: H3 := hp3
  have hb3' : BlkAt H3 o3 ((m.ds ++ ifs).map Enc.idxW) := by simpa using hb3
  have hl3 := hb3'.1
  simp only [List.length_map] at hl3
  refine UD.specR_heapLoadI' (C := ctxH C H3) mjrL1 (vv mjrA1) o3 _ hl3 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine ILP.callE_spec (C := ctxH C H3) mjrMj ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv mjrHd, vv mjrA1, .const 0, vv mjrL1] ExK.mkaBody
    [Enc.idxW hd, cellA C o3, BitVec.ofNat 64 0, BitVec.ofNat 64 (m.ds ++ ifs).length] (by decide) rfl (by decide) hc.mka
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
      trivial⟩
    (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H3) (ctxOK_H hok H3) hc.mka hc.app o3 (m.ds ++ ifs) hb3' (by simp; omega) 0 (by omega) hd s3; simp only [List.drop_zero] at h; exact h)
    (fun maj s4 => ?_)
  refine specR_alloc2I (ctxOK_H hok H3) mjrR (vv mjrIf) (vv mjrMj) (cellA C oa) (Enc.idxW maj) (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H4 ws4 hp4 hws4 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H4 ws4 (cellA C oa) (Enc.idxW maj) hws4
  have hp4' : H3 <+: _ := (hp4 : H3 <+: H4).trans (img2_prefix H4 ws4 (cellA C oa) (Enc.idxW maj) hws4)
  exact specR_returnI _ (cellA C H4.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, ifs, maj, H4.length, oa,
    hpC2.trans (hp3'.trans hp4'), rfl, rfl, k0, blkAt_mono hfb (hp3'.trans hp4'), k1, by omega,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `ClassGen.motiveTy` -/

def motDs := ofString "mot_ds"
def motDn := ofString "mot_dn"
def motFt := ofString "mot_ft"
def motNi := ofString "mot_ni"
def motD := ofString "mot_d"
def motInd := ofString "mot_ind"
def motLv := ofString "mot_lv"
def motEl := ofString "mot_el"
def motM := ofString "mot_m"
def motIf := ofString "mot_if"
def motMj := ofString "mot_mj"
def motSrt := ofString "mot_srt"
def motBd := ofString "mot_bd"
def motBs := ofString "mot_bs"
def motLb := ofString "mot_lb"
def motR := ofString "mot_r"
def motOms := ofString "mot_oms"
def motFts := ofString "mot_fts"
def motCl := ofString "mot_cl"
def motQ := ofString "mot_q"
def fMot := ofString "motiveTy"

def motParams : List MlS := [motOms, motFts, motCl, motD, motEl]
def motLocals : List MlS := [motM, motIf, motMj, motSrt, motBd, motBs, motLb, motR, motNi, motQ]

def motBody : ProgHOL 64 := prologue motLocals
  (.seq (.assign .local motQ (.load .one (vv motOms)))
  (.ite (.cmp .lower (vv motCl) (vv motQ))
  (.seq (.assign .local motQ (.load .one (.op .add [vv motOms, .op .add [.panop .mul [vv motCl, .const 8], .const 8]])))
  (.seq (.assign .local motNi (.load .one (vv motQ)))
  (guardP motNi 56
  (.seq (.call (some (some (.local, motM), none)) fMjr [vv motOms, vv motFts, vv motCl, vv motD])
  (.seq (.assign .local motIf (.load .one (vv motM)))
  (.seq (.assign .local motMj (.load .one (.op .add [vv motM, .const 8])))
  (.seq (.call (some (some (.local, motSrt), none)) fInternSort [vv motEl])
  (.seq (.call (some (some (.local, motBd), none)) fInternForallE [vv motMj, vv motSrt])
  (.seq (.call (some (some (.local, motBs), none)) fFvtDs [vv motIf])
  (.seq (.assign .local motLb (.load .one (vv motBs)))
  (.ite (.cmp .equal (vv motLb) (vv motNi))
  (.seq (.call (some (some (.local, motR), none)) fCtg [vv motD, .const 0, vv motBs, .const 0, vv motBd])
  (.return (vv motR)))
  hang)))))))))))
  hang))

structure MOTCodes (C : Ctx) : Prop where
  mjr : MJRCodes C
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  fa : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  ftd : C.code.lookup fFvtDs = some (ftdParams.map (fun p => (p, ShapeHOL.one)), ftdBody C, .one)
  ftf : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  ctg : CTGCodes C
  self : C.code.lookup fMot = some (motParams.map (fun p => (p, ShapeHOL.one)), motBody, .one)

section
variable {σ : Type}

theorem mot_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ motLocals → (ctxEnv C ++ motParams.zip vals).get x = none :=
  Knot.params_none C motLocals motParams vals (by decide) (by decide)

theorem mapM_classBinder_eq : ∀ l : List EIdx, l.mapM classBinder = fvarTypeDs l
  | [] => rfl
  | x :: l => by rw [List.mapM_cons, fvarTypeDs, mapM_classBinder_eq l]; rfl

set_option maxHeartbeats 16000000 in
/-- **`ClassGen.motiveTy c d`** (class `c` read off the class block). -/
theorem mot_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : MOTCodes C)
    (g : ClassGen) (cl oms fts : Nat) (hcl : cl < 2 ^ 63) (hT : TMBlkR C C.H oms g.cls)
    (hfts : BlkAt C.H fts (g.formerTys.map Enc.idxW)) (d : Nat) (hd : d < 2 ^ 61) (s : AState) :
    SpecR (σ := σ) (Pre C s (motParams.zip [cellA C oms, cellA C fts, BitVec.ofNat 64 cl, BitVec.ofNat 64 d,
        Enc.idxW g.elim])) motBody s (g.motiveTy cl d) (PostSomeH C) := by
  refine specR_prologue (postSomeH_locals _) (mot_none _ _) ?_
  unfold ClassGen.motiveTy
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN0 => ?_)
  have hHN0' : C.H.length ≤ C.HN := hHN0
  have hlay := hok.heapLay
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := id hT
  have hcl0 : C.H[oms]? = some (BitVec.ofNat 64 g.cls.length) := by simpa [hpsl] using hpsb.1
  refine UD.specR_heapLoadI' (C := ctxH C C.H) motQ (vv motOms) oms _ hcl0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv]; rfl) ?_
  have hclen : g.cls.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN0' hpsb; simp at this; omega
  have hlwc := nd_lt_iff cl g.cls.length (by omega) (by omega)
  by_cases hcl' : cl < g.cls.length
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, motParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, motParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwc.mpr hcl']) (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨op, hop, hrep⟩ := hpsr cl hcl'
  have hq := hpsb.2 cl (by simp; omega)
  simp only [List.getElem_map] at hq
  have hpi : ps[cl]'(by omega) = op := by
    rw [List.getElem?_eq_getElem (by omega)] at hop; exact Option.some.inj hop
  rw [hpi] at hq
  generalize g.cls[cl] = m at hrep
  obtain ⟨-, -, -, -, -, -, hniE, -, -, -⟩ := hrep
  refine UD.specR_heapLoadI' (C := ctxH C C.H) motQ _ (oms + 1 + cl) _ hq (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv]; exact cellA_mulIdx C oms cl (by omega)) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) motNi (vv motQ) op _ hniE.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine specR_guardI motNi m.nIdx 56 (by decide) (by simp [Env.get_cons]) (by have := hniE.2; omega)
    (fun hni => ?_)
  refine specR_callNIH (C := ctxH C C.H) motM fMjr mjrParams [vv motOms, vv motFts, vv motCl, vv motD]
    (mjrBody C) [cellA C oms, cellA C fts, BitVec.ofNat 64 cl, BitVec.ofNat 64 d] (by decide) rfl (by decide) hc.mjr.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], trivial⟩
    (PostMJ (ctxH C C.H)) (fun o w _ H' => ∃ ifs maj ob oi, o = some (ifs, maj) ∧ w = cellA C ob ∧
      H'[ob]? = some (cellA C oi) ∧ BlkAt H' oi (ifs.map Enc.idxW) ∧ H'[ob + 1]? = some (Enc.idxW maj) ∧
      ifs.length < 2 ^ 56)
    (fun o w s' st ⟨H', ifs, maj, ob, oi, hp', h1, h2, h3, h4, h5, h6, hsr⟩ => ⟨H', hp', ⟨ifs, maj, ob, oi, h1, h2, h3, h4,
      h5, h6⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mjrParams _ rfl hlk)
      (mjr_spec ra (ctxH C C.H) (ctxOK_H hok C.H) (by ctx_tr hc.mjr) g cl oms fts hcl hT hfts d hd s))
    (fun o w s1 H1 hp1 ⟨ifs, maj, ob, oi, ho, hw, hob, hib, hmj, hil⟩ => ?_)
  subst ho hw
  have hp1' : C.H <+: H1 := hp1
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H1) motIf (vv motM) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) motMj _ (ob + 1) _ hmj (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ob) ?_
  have hok1 := ctxOK_H hok H1
  refine ILP.callE_spec (C := ctxH C H1) motSrt fInternSort [lEu] [vv motEl] sortBody [Enc.idxW g.elim]
    (by decide) rfl (by decide) hc.srt ⟨by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], trivial⟩ (sort_body_spec ra (ctxH C H1) hok1 s1 _) (fun srt s2 => ?_)
  refine specR_internForallEI ra hok1 hc.fa motBd (vv motMj) (vv motSrt) maj srt (by decide)
    (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons]) (fun bd s3 => ?_)
  rw [mapM_classBinder_eq]
  refine specR_callNIH (C := ctxH C H1) motBs fFvtDs ftdParams [vv motIf] (ftdBody C) [cellA C oi] (by decide) rfl
    (by decide) hc.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H1)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
    (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
      (ftd_spec C hok hc.ftd hc.ftf hc.fvt ifs oi (by omega) H1 s3 hib))
    (fun bs w s4 H2 hp2 ⟨o2, hw2, hb2⟩ => ?_)
  subst hw2
  have hp2' : H1 <+: H2 := hp2
  have hbl := hb2.1
  simp only [List.length_map] at hbl
  refine UD.specR_heapLoadI' (C := ctxH C H2) motLb (vv motBs) o2 _ hbl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H2.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hbl0 : bs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos bs.length with h0 | hpos
    · omega
    · have h1 := hb2.2 (bs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hbn : bs.length = m.nIdx
  swap
  · have hne : BitVec.ofNat 64 bs.length ≠ BitVec.ofNat 64 m.nIdx := fun e => hbn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hbn]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  unfold closeTelescope
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  refine specR_callNIH (C := ctxH C H2) motR fCtg ctgParams [vv motD, .const 0, vv motBs, .const 0, vv motBd] ctgBody
    [BitVec.ofNat 64 d, BitVec.ofNat 64 0, cellA C o2, BitVec.ofNat 64 0, Enc.idxW bd] (by decide) rfl (by decide)
    hc.ctg.self ⟨by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostK (ctxH C H2)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctgParams _ rfl hlk)
      (by have h := ctg_spec (σ := σ) ra C hok hc.ctg d (by omega) bs o2 (by omega) bd bs.length 0 0 H2 s4 (by omega) (by omega) (by omega) hpC2 hb2; simp only [List.drop_zero] at h; exact h))
    (fun r w s5 H3 hp3 hw => ?_)
  subst hw
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H3, r, hpC2.trans hp3, rfl, rfl,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## A class constructor by name -/

def fccT := ofString "fcc_t"
def fccI := ofString "fcc_i"
def fccK := ofString "fcc_k"
def fccC := ofString "fcc_c"
def fccP := ofString "fcc_p"
def fccQ := ofString "fcc_q"
def fccX := ofString "fcc_x"
def fccR := ofString "fcc_r"
def fFcc := ofString "findClassCtor"

def fccParams : List MlS := [fccT, fccI, fccK, fccC]
def fccLocals : List MlS := [fccP, fccQ, fccX, fccR]

def fccBody : ProgHOL 64 := prologue fccLocals
  (.ite (.cmp .lower (vv fccI) (vv fccK))
    (.seq (.assign .local fccP (.load .one (.op .add [vv fccT, .op .add [.panop .mul [vv fccI, .const 8], .const 8]])))
    (.seq (.assign .local fccQ (.load .one (vv fccP)))
    (.seq (.assign .local fccX (.load .one (vv fccQ)))
    (.ite (.cmp .equal (vv fccX) (vv fccC)) (.return (vv fccP))
      (.seq (.call (some (some (.local, fccR), none)) fFcc [vv fccT, .op .add [vv fccI, .const 1], vv fccK, vv fccC])
        (.return (vv fccR)))))))
    hang)

section
variable {σ : Type}

theorem fcc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fccLocals → (ctxEnv C ++ fccParams.zip vals).get x = none :=
  Knot.params_none C fccLocals fccParams vals (by decide) (by decide)

/-- A found class constructor, as its record (the state kept). -/
def PostFC (C : Ctx) (s : AState) (r : Option ClassCtor) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ x o, r = some x ∧ w = cellA C o ∧ CCRep C C.H o x ∧ SR C s' st

/-- **`(ccs.drop i).find? (·.cv.name == cn)`** (none hangs). -/
theorem fcc_spec (C : Ctx) (hc : C.code.lookup fFcc = some (fccParams.map (fun p => (p, ShapeHOL.one)), fccBody, .one))
    (ccs : List ClassCtor) (ot : Nat) (htl : ccs.length < 2 ^ 58) (cn : NIdx) (H : List (BitVec 64))
    (htb : PRep C H ot (fun H o cc => CCRep C H o cc) ccs) :
    ∀ f i (s : AState), ccs.length - i = f → i ≤ ccs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (fccParams.zip [cellA C ot, BitVec.ofNat 64 i, BitVec.ofNat 64 ccs.length,
        Enc.idxW cn])) fccBody s (pure ((ccs.drop i).find? (·.cv.name == cn))) (PostFC (ctxH C H) s) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := htb
  have hpost : ∀ (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostFC (ctxH C H) s a w s' st → PostFC (ctxH C H) s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ ⟨h0, x, o, h1, h2, h3, h4⟩ => ⟨h0, x, o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = ccs.length := by omega
    subst hin
    refine specR_prologue (hpost s) (fcc_none _ _) ?_
    have hlw := nd_lt_iff ccs.length ccs.length (by omega) (by omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, fccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  | succ f ih =>
    intro i s hf hi
    have hin : i < ccs.length := by omega
    refine specR_prologue (hpost s) (fcc_none _ _) ?_
    have hlw := nd_lt_iff i ccs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, fccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : i < os.length := by omega
    have hpe := hosb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hcr := hosr i hin hio
    obtain ⟨⟨ocv, hocv, hcv⟩, -⟩ := id hcr
    refine UD.specR_heapLoadI' (C := ctxH C H) fccP _ (ot + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get, fccParams, ctxEnv]; exact cellA_mulIdx C ot i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) fccQ (vv fccP) _ _ hocv (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) fccX (vv fccQ) _ _ hcv.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin, List.find?_cons]
    by_cases he : ccs[i].cv.name = cn
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, fccParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [he, beq_self_eq_true]
      exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons]; rfl) (fun t ht => ⟨rfl, ccs[i], os[i], rfl, rfl, hcr,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hne : Enc.idxW ccs[i].cv.name ≠ Enc.idxW cn := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, fccParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    have hbe : (ccs[i].cv.name == cn) = false := beq_eq_false_iff_ne.mpr he
    simp only [hbe]
    refine specR_congr (m' := (pure ((ccs.drop (i + 1)).find? (·.cv.name == cn)) : AM (Option ClassCtor)) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H) fccR fFcc fccParams [vv fccT, .op .add [vv fccI, .const 1], vv fccK, vv fccC]
      fccBody [cellA C ot, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ccs.length, Enc.idxW cn] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, fccParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fccParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, fccParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fccParams, ctxEnv], trivial⟩
      (PostFC (ctxH C H) s) (fun r w s' H' => H' = H ∧ s' = s ∧ ∃ x o, r = some x ∧ w = cellA C o ∧ CCRep C H o x)
      (fun r w s' st ⟨h0, x, o, h1, h2, h3, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, x, o, h1, h2, h3⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fccParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun r w s3 H3 hp3 ⟨eH, es3, x, o, h1, h2, h3⟩ => ?_)
    subst H3 s3 h2
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨rfl, x, o, h1, rfl, h3,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `ClassGen.prefixBinders.slotsGo` (one class; motive first, then the minors) -/

def pslSl := ofString "psl_sl"
def pslS := ofString "psl_s"
def pslN := ofString "psl_n"
def pslNP := ofString "psl_np"
def pslCcs := ofString "psl_ccs"
def pslCk := ofString "psl_ck"
def pslDs := ofString "psl_ds"
def pslDn := ofString "psl_dn"
def pslFt := ofString "psl_ft"
def pslNi := ofString "psl_ni"
def pslInd := ofString "psl_ind"
def pslLv := ofString "psl_lv"
def pslEl := ofString "psl_el"
def pslNPc := ofString "psl_npc"
def pslP := ofString "psl_p"
def pslTg := ofString "psl_tg"
def pslD := ofString "psl_d"
def pslT := ofString "psl_t"
def pslCc := ofString "psl_cc"
def pslCn := ofString "psl_cn"
def pslX := ofString "psl_x"
def pslOms := ofString "psl_oms"
def fPsl := ofString "prefixSlots"

def pslFts := ofString "psl_fts"
def pslMc := ofString "psl_mc"
def pslQ := ofString "psl_q"

def pslParams : List MlS := [pslSl, pslS, pslN, pslNP, pslCcs, pslFts, pslEl, pslOms, pslMc]
def pslLocals : List MlS := gaaLocals ++ [pslP, pslTg, pslD, pslT, pslCc, pslCn, pslX, pslQ, pslCk]

def pslRec (ec : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, ExS.lY), none)) fPsl [vv pslSl, .op .add [vv pslS, .const 1], vv pslN, vv pslNP, vv pslCcs,
    vv pslFts, vv pslEl, vv pslOms, ec]

def pslBody (C : Ctx) : ProgHOL 64 := prologue pslLocals
  (.ite (.cmp .lower (vv pslS) (vv pslN))
  (.seq (.assign .local pslP (.load .one (.op .add [vv pslSl, .op .add [.panop .mul [vv pslS, .const 8], .const 8]])))
  (.seq (.assign .local pslTg (.load .one (vv pslP)))
  (.seq (.assign .local pslD (.op .add [vv pslNP, vv pslS]))
  (.ite (.cmp .equal (vv pslTg) (.const 0))
  (.seq (.call (some (some (.local, pslT), none)) fMot [vv pslOms, vv pslFts, vv pslMc, vv pslD, vv pslEl])
  (.seq (pslRec (.op .add [vv pslMc, .const 1])) (prependP C pslT)))
  (.ite (.cmp .equal (vv pslTg) (.const 1))
  (.seq (.assign .local pslCc (.load .one (.op .add [vv pslP, .const 8])))
  (.seq (.assign .local pslCn (.load .one (.op .add [vv pslP, .const 16])))
  (.seq (.assign .local pslQ (.load .one (vv pslCcs)))
  (.ite (.cmp .lower (vv pslCc) (vv pslQ))
  (.seq (.assign .local pslX (.load .one (.op .add [vv pslCcs, .op .add [.panop .mul [vv pslCc, .const 8], .const 8]])))
  (.seq (.assign .local pslCk (.load .one (vv pslX)))
  (.seq (.call (some (some (.local, pslX), none)) fFcc [vv pslX, .const 0, vv pslCk, vv pslCn])
  (.seq (.call (some (some (.local, pslT), none)) fMty [vv pslX, vv pslD, vv pslOms, vv pslSl, vv pslNP, vv pslCc])
  (.seq (pslRec (vv pslMc)) (prependP C pslT))))))
  hang))))
  hang)))))
  (alloc1 C lW (.const 0) (.return (vv lW))))

structure PSLCodes (C : Ctx) : Prop where
  mot : MOTCodes C
  mty : MTYCodes C
  fcc : C.code.lookup fFcc = some (fccParams.map (fun p => (p, ShapeHOL.one)), fccBody, .one)
  self : C.code.lookup fPsl = some (pslParams.map (fun p => (p, ShapeHOL.one)), pslBody C, .one)

/-- The number of motive slots among the first `i` (the class of the motive at slot `i`). -/
def motCnt (sls : List ClassSlot) (i : Nat) : Nat :=
  ((sls.take i).filter (fun s => match s with | .motive _ => true | .minor .. => false)).length

theorem motCnt_succ (sls : List ClassSlot) (i : Nat) (hi : i < sls.length) :
    motCnt sls (i + 1) = motCnt sls i + (match sls[i] with | .motive _ => 1 | .minor .. => 0) := by
  unfold motCnt
  rw [List.take_succ, List.filter_append, List.length_append, List.getElem?_eq_getElem hi]
  cases sls[i] <;> simp

theorem motCnt_le (sls : List ClassSlot) (i : Nat) : motCnt sls i ≤ i :=
  Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

theorem motCnt_zero (sls : List ClassSlot) : motCnt sls 0 = 0 := by simp [motCnt]

section
variable {σ : Type}

theorem psl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pslLocals → (ctxEnv C ++ pslParams.zip vals).get x = none :=
  Knot.params_none C pslLocals pslParams vals (by decide) (by decide)

set_option maxHeartbeats 32000000 in
/-- **`ClassGen.prefixBinders.slotsGo g s`** over the slots from `s` on, at any number of classes: a motive slot is
class `motCnt` (the motives before it), a minor premise slot's constructor is looked up in its class's block. -/
theorem psl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PSLCodes C)
    (g : ClassGen) (osl ocss fts oms : Nat) (hsll : g.slots.length < 2 ^ 56) (hsb : SlotBlk C C.H osl g.slots)
    (hcss : PRep C C.H ocss (fun H o xs => PRep C H o (fun H o cc => CCRep C H o cc) xs) g.ctors)
    (hcsl : ∀ xs ∈ g.ctors, xs.length < 2 ^ 58 ∧ ∀ x ∈ xs, x.nF < 2 ^ 56)
    (hfts : BlkAt C.H fts (g.formerTys.map Enc.idxW)) (hT : TMBlkR C C.H oms g.cls) (hnP : g.nP < 2 ^ 56)
    (hcb' : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63) :
    ∀ f i (H : List (BitVec 64)) (s : AState), g.slots.length - i = f → i ≤ g.slots.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (pslParams.zip [cellA C osl, BitVec.ofNat 64 i, BitVec.ofNat 64 g.slots.length,
        BitVec.ofNat 64 g.nP, cellA C ocss, cellA C fts, Enc.idxW g.elim, cellA C oms,
        BitVec.ofNat 64 (motCnt g.slots i)])) (pslBody C) s (ClassGen.prefixBinders.slotsGo g i (g.slots.drop i))
        (PostSL (ctxH C H)) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := id hsb
  obtain ⟨oss, hossl, hossb, hossr⟩ := id hcss
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = g.slots.length := by omega
    subst hin
    refine specR_prologue (postSL_locals _) (psl_none _ _) ?_
    have hlw := nd_lt_iff g.slots.length g.slots.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pslParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]; simp only [ClassGen.prefixBinders.slotsGo]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨[], _, H2.length, rfl,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < g.slots.length := by omega
    refine specR_prologue (postSL_locals _) (psl_none _ _) ?_
    have hlw := nd_lt_iff i g.slots.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pslParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin]; simp only [ClassGen.prefixBinders.slotsGo]
    have hpC : C.H <+: H := hp
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN0 => ?_)
    have hHN0' : H.length ≤ C.HN := hHN0
    have hlay := hok.heapLay
    obtain ⟨op, hop, hsr⟩ := hpsr i hin
    have hio : i < ps.length := by omega
    have hpe := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hpi : ps[i] = op := by simpa [List.getElem?_eq_getElem hio] using hop
    rw [hpi] at hpe
    refine UD.specR_heapLoadI' (C := ctxH C H) pslP _ (osl + 1 + i) _ (get_prefix hpe hpC) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv]; exact cellA_mulIdx C osl i (by omega)) ?_
    have hmcl := motCnt_le g.slots i
    have hrest : ∀ (ty : EIdx) (Hx : List (BitVec 64)) (sx : AState) (Γ : Env) (ec : ExpHOL 64), H <+: Hx →
        Γ.get pslT = some (Enc.idxW ty) → Γ.get pslSl = some (cellA C osl) → Γ.get pslS = some (BitVec.ofNat 64 i) →
        Γ.get pslN = some (BitVec.ofNat 64 g.slots.length) → Γ.get pslNP = some (BitVec.ofNat 64 g.nP) →
        Γ.get pslCcs = some (cellA C ocss) → Γ.get pslFts = some (cellA C fts) →
        Γ.get pslEl = some (Enc.idxW g.elim) → Γ.get pslOms = some (cellA C oms) →
        sev Γ ec = some (BitVec.ofNat 64 (motCnt g.slots (i + 1))) → Γ.get lCz = none →
        SpecR (σ := σ) (Inv (ctxH C Hx) sx Γ [] (ctxLocals ++ pslLocals)) (.seq (pslRec ec) (prependP C pslT)) sx
          (ClassGen.prefixBinders.slotsGo g (i + 1) (g.slots.drop (i + 1)) >>= fun r => match r with
            | none => pure none
            | some rest => pure (some (ty :: rest))) (PostSL (ctxH C H)) := by
      intro ty Hx sx Γ ec hpx gT gSl gS gN gNP gCcs gFts gEl gOms hec gCz
      unfold pslRec
      refine specR_callNIH (C := ctxH C Hx) ExS.lY fPsl pslParams [vv pslSl, .op .add [vv pslS, .const 1], vv pslN,
          vv pslNP, vv pslCcs, vv pslFts, vv pslEl, vv pslOms, ec] (pslBody C)
        [cellA C osl, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 g.slots.length, BitVec.ofNat 64 g.nP, cellA C ocss,
          cellA C fts, Enc.idxW g.elim, cellA C oms, BitVec.ofNat 64 (motCnt g.slots (i + 1))] (by decide) rfl
        (by decide) hc.self
        ⟨by simp [sev, gSl], by simp only [sev, sev_vv, gS]; simp; exact word_add1_eq i, by simp [sev, gN],
          by simp [sev, gNP], by simp [sev, gCcs], by simp [sev, gFts], by simp [sev, gEl], by simp [sev, gOms], hec,
          trivial⟩
        (PostSL (ctxH C Hx)) (fun o w _ H' => ∃ ds oy, o = some ds ∧ w = cellA C oy ∧ BlkAt H' oy (ds.map Enc.idxW))
        (fun o w s' st ⟨ds, H', oy, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, oy, h0, hw, hb⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pslParams _ rfl hlk)
          (ih (i + 1) Hx sx (by omega) (by omega) (hpC.trans hpx)))
        (fun o w s2 H2 hp2 ⟨ds, oy, ho, hw, hb⟩ => ?_)
      subst ho hw
      have hp2' : Hx <+: H2 := hp2
      simp only
      refine ExPre.prepend_spec C hok (H := H2) pslT (Enc.idxW ty) oy (ds.map Enc.idxW) (by decide)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons, gT]) hb (by decide)
        (by simp +decide [Env.get_cons, gCz]) (by decide) (fun H' o t hp' hb' hsr => ?_)
      exact ⟨ty :: ds, H', o, rfl, hpx.trans (hp2'.trans hp'), rfl, by simpa using hb', hsr⟩
    have hslm := List.getElem_mem hin
    have hmcs := motCnt_succ g.slots i hin
    generalize hsli : g.slots[i] = sl at hsr hslm hmcs ⊢
    cases sl with
    | motive k' =>
      have hmcs' : motCnt g.slots (i + 1) = motCnt g.slots i + 1 := by simp [hmcs]
      obtain ⟨htg, -, -, -⟩ := hsr
      refine UD.specR_heapLoadI' (C := ctxH C H) pslTg (vv pslP) op _ (get_prefix htg hpC) (by decide)
        (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_assignI pslD _ (BitVec.ofNat 64 (g.nP + i)) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      have e : ∀ (q : ClassSlot → Bool), (∀ x, q x = (match x with | .motive _ => true | .minor .. => false)) →
          (List.filter q (List.take i g.slots)).length = motCnt g.slots i := by
        intro q hq; unfold motCnt; congr 1; exact List.filter_congr (fun x _ => hq x)
      rw [e _ (fun x => by cases x <;> rfl)]
      refine specR_callNIH (C := ctxH C H) pslT fMot motParams
        [vv pslOms, vv pslFts, vv pslMc, vv pslD, vv pslEl] motBody
        [cellA C oms, cellA C fts, BitVec.ofNat 64 (motCnt g.slots i), BitVec.ofNat 64 (g.nP + i), Enc.idxW g.elim]
        (by decide) rfl (by decide) hc.mot.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv], trivial⟩
        (PostSomeH (ctxH C H)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
        (fun o w s' st ⟨H', t, hp', h1, h2, hsr⟩ => ⟨H', hp', ⟨t, h1, h2⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu motParams _ rfl hlk)
          (mot_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.mot) g (motCnt g.slots i) oms fts (by omega)
            (tmBlkR_mono hpC hT) (blkAt_mono hfts hpC) (g.nP + i) (by omega) s))
        (fun o w s1 H1 hp1 ⟨ty, ho, hw⟩ => ?_)
      subst ho hw
      simp only
      exact hrest ty H1 s1 _ _ hp1 (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv])
        (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, pslParams, ctxEnv]; rw [hmcs']; exact word_add1_eq _) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv])
    | minor c C' ihs =>
      have hmcs' : motCnt g.slots (i + 1) = motCnt g.slots i := by simp [hmcs]
      obtain ⟨htg, hcw, hcn, -⟩ := hsr
      have hc63 := hcb' _ hslm c C' ihs rfl
      refine UD.specR_heapLoadI' (C := ctxH C H) pslTg (vv pslP) op _ (get_prefix htg hpC) (by decide)
        (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_assignI pslD _ (BitVec.ofNat 64 (g.nP + i)) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) pslCc _ (op + 1) _ (get_prefix hcw hpC) (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) pslCn _ (op + 2) _ (get_prefix hcn hpC) (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 2) ?_
      have hcs0 : C.H[ocss]? = some (BitVec.ofNat 64 g.ctors.length) := by simpa [hossl] using hossb.1
      refine UD.specR_heapLoadI' (C := ctxH C H) pslQ (vv pslCcs) ocss _ (get_prefix hcs0 hpC) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv]; rfl) ?_
      have hctl : g.ctors.length < 2 ^ 61 := by
        have := blk_len_lt hok hHN0' (blkAt_mono hossb hpC); simp at this; omega
      have hlwc := nd_lt_iff c g.ctors.length (by omega) (by omega)
      by_cases hcc : c < g.ctors.length
      swap
      · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, pslParams, ctxEnv,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
          (fun h => absurd rfl h) (fun _ => specR_hangI)
      refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, pslParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwc.mpr hcc]) (fun _ => ?_) (fun h => absurd h (by decide))
      have hxo : c < oss.length := by omega
      have hxe := hossb.2 c (by simp; omega)
      simp only [List.getElem_map] at hxe
      refine UD.specR_heapLoadI' (C := ctxH C H) pslX _ (ocss + 1 + c) _ (get_prefix hxe hpC) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv]; exact cellA_mulIdx C ocss c (by omega)) ?_
      have hxr := hossr c hcc hxo
      obtain ⟨hxl58, hxnf⟩ := hcsl _ (List.getElem_mem hcc)
      obtain ⟨os2, hos2l, hos2b, -⟩ := id hxr
      have hck : C.H[oss[c]]? = some (BitVec.ofNat 64 g.ctors[c].length) := by simpa [hos2l] using hos2b.1
      refine UD.specR_heapLoadI' (C := ctxH C H) pslCk (vv pslX) oss[c] _ (get_prefix hck hpC) (by decide)
        (by simp [sev, Env.get_cons]; rfl) ?_
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcc, Option.getD_some]
      refine specR_callPure (C := ctxH C H) pslX fFcc fccParams [vv pslX, .const 0, vv pslCk, vv pslCn] fccBody
        [cellA C oss[c], BitVec.ofNat 64 0, BitVec.ofNat 64 g.ctors[c].length, Enc.idxW C']
        ((g.ctors[c].drop 0).find? (·.cv.name == C'))
        (by decide) rfl (by decide) hc.fcc ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
          by simp +decide [sev, Env.get_cons], trivial⟩
        (PostFC (ctxH C H) s) (fun r w s' H' => H' = H ∧ ∃ x o, r = some x ∧ w = cellA C o ∧ CCRep C H o x)
        (fun r w s' st ⟨_, x, o, h1, h2, h3, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, x, o, h1, h2, h3⟩, h4⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fccParams _ rfl hlk)
          (fcc_spec C hc.fcc g.ctors[c] oss[c] hxl58 C' H (pRep_mono hpC (fun _ _ => ccRep_mono hpC) hxr)
            g.ctors[c].length 0 s (by omega) (by omega)))
        (fun w H1 hp1 ⟨eH, x, ox, hfx, hw, hxr'⟩ => ?_)
      subst H1 hw
      simp only [List.drop_zero] at hfx
      rw [hfx]
      simp only
      have hxm : x ∈ g.ctors[c] := List.mem_of_find?_eq_some hfx
      have hxn := hxnf x hxm
      refine specR_callNIH (C := ctxH C H) pslT fMty mtyParams
        [vv pslX, vv pslD, vv pslOms, vv pslSl, vv pslNP, vv pslCc] (mtyBody C)
        [cellA C ox, BitVec.ofNat 64 (g.nP + i), cellA C oms, cellA C osl, BitVec.ofNat 64 g.nP,
          BitVec.ofNat 64 c] (by decide) rfl (by decide) hc.mty.self
        ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pslParams, ctxEnv],
          by simp +decide [sev, Env.get_cons], trivial⟩
        (PostSomeH (ctxH C H)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
        (fun o w s' st ⟨H', t, hp', h1, h2, hsr⟩ => ⟨H', hp', ⟨t, h1, h2⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mtyParams _ rfl hlk)
          (mty_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.mty) g c oms osl hc63 (tmBlkR_mono hpC hT)
            (slotBlk_mono hpC hsb) (by omega) x ox hxr' hxn (g.nP + i) (by omega) hnP s))
        (fun o w s1 H1 hp1 ⟨ty, ho, hw⟩ => ?_)
      subst ho hw
      simp only
      exact hrest ty H1 s1 _ _ hp1 (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv])
        (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, pslParams, ctxEnv]; rw [hmcs']) (by simp +decide [Env.get_cons, Env.get, pslParams, ctxEnv])

end

/-! ## `ClassGen.prefixBinders` -/

def pbPs := ofString "pb_ps"
def pbSl := ofString "pb_sl"
def pbN := ofString "pb_n"
def pbNP := ofString "pb_np"
def pbCcs := ofString "pb_ccs"
def pbCk := ofString "pb_ck"
def pbDs := ofString "pb_ds"
def pbDn := ofString "pb_dn"
def pbFt := ofString "pb_ft"
def pbNi := ofString "pb_ni"
def pbInd := ofString "pb_ind"
def pbLv := ofString "pb_lv"
def pbEl := ofString "pb_el"
def pbNPc := ofString "pb_npc"
def pbB := ofString "pb_b"
def pbS := ofString "pb_s"
def pbR := ofString "pb_r"
def pbL := ofString "pb_l"
def pbOms := ofString "pb_oms"
def pbFts := ofString "pb_fts"
def fPb := ofString "prefixBinders"

def pbParams : List MlS := [pbPs, pbSl, pbN, pbNP, pbCcs, pbFts, pbEl, pbOms]
def pbLocals : List MlS := [pbB, pbS, pbR, pbL]

def pbBody (C : Ctx) : ProgHOL 64 := prologue pbLocals
  (.seq (.call (some (some (.local, pbB), none)) fFvtDs [vv pbPs])
  (.seq (.call (some (some (.local, pbS), none)) fPsl [vv pbSl, .const 0, vv pbN, vv pbNP, vv pbCcs, vv pbFts, vv pbEl,
      vv pbOms, .const 0])
  (.seq (.assign .local pbL (.load .one (vv pbS)))
  (.ite (.cmp .equal (vv pbL) (vv pbN))
    (.seq (.call (some (some (.local, pbR), none)) fCat [vv pbB, vv pbS, .const 0])
    (.return (vv pbR)))
    hang))))

structure PBCodes (C : Ctx) : Prop where
  psl : PSLCodes C
  cat : CatCodes C
  self : C.code.lookup fPb = some (pbParams.map (fun p => (p, ShapeHOL.one)), pbBody C, .one)

section
variable {σ : Type}

theorem pb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pbLocals → (ctxEnv C ++ pbParams.zip vals).get x = none :=
  Knot.params_none C pbLocals pbParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`ClassGen.prefixBinders`**, at any number of classes. -/
theorem pb_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PBCodes C)
    (g : ClassGen) (opp osl ocss fts oms : Nat) (hppl : g.params.length < 2 ^ 56)
    (hpp : BlkAt C.H opp (g.params.map Enc.idxW)) (hsll : g.slots.length < 2 ^ 56) (hsb : SlotBlk C C.H osl g.slots)
    (hcss : PRep C C.H ocss (fun H o xs => PRep C H o (fun H o cc => CCRep C H o cc) xs) g.ctors)
    (hcsl : ∀ xs ∈ g.ctors, xs.length < 2 ^ 58 ∧ ∀ x ∈ xs, x.nF < 2 ^ 56)
    (hfts : BlkAt C.H fts (g.formerTys.map Enc.idxW)) (hT : TMBlkR C C.H oms g.cls) (hnP : g.nP < 2 ^ 56)
    (hcb' : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63) (s : AState) :
    SpecR (σ := σ) (Pre C s (pbParams.zip [cellA C opp, cellA C osl, BitVec.ofNat 64 g.slots.length,
        BitVec.ofNat 64 g.nP, cellA C ocss, cellA C fts, Enc.idxW g.elim, cellA C oms])) (pbBody C) s g.prefixBinders
      (PostSL C) := by
  refine specR_prologue (postSL_locals _) (pb_none _ _) ?_
  unfold ClassGen.prefixBinders
  rw [mapM_binder_eq]
  refine specR_callNIH (C := ctxH C C.H) pbB fFvtDs ftdParams [vv pbPs] (ftdBody C) [cellA C opp] (by decide) rfl
    (by decide) hc.psl.mty.ftd ⟨by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], trivial⟩
    (PostA (ctxH C C.H)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
    (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
      (ftd_spec C hok hc.psl.mty.ftd hc.psl.mty.ftf hc.psl.mty.fvt g.params opp (by omega) C.H s hpp))
    (fun pbs w s1 H1 hp1 ⟨o1, hw, hb1⟩ => ?_)
  subst hw
  have hp1' : C.H <+: H1 := hp1
  have hpsl := psl_spec (σ := σ) ra C hok hc.psl g osl ocss fts oms hsll hsb hcss hcsl hfts hT hnP hcb'
    g.slots.length 0 H1 s1 (by omega) (by omega) hp1'
  simp only [List.drop_zero] at hpsl
  refine specR_callNIH (C := ctxH C H1) pbS fPsl pslParams [vv pbSl, .const 0, vv pbN, vv pbNP, vv pbCcs, vv pbFts, vv pbEl,
      vv pbOms, .const 0] (pslBody C) [cellA C osl, BitVec.ofNat 64 0, BitVec.ofNat 64 g.slots.length,
      BitVec.ofNat 64 g.nP, cellA C ocss, cellA C fts, Enc.idxW g.elim, cellA C oms, BitVec.ofNat 64 (motCnt g.slots 0)]
    (by decide) rfl (by decide)
    hc.psl.self ⟨by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv], by simp [sev, motCnt_zero], trivial⟩
    (PostSL (ctxH C H1)) (fun o w _ H' => ∃ ds oy, o = some ds ∧ w = cellA C oy ∧ BlkAt H' oy (ds.map Enc.idxW))
    (fun o w s' st ⟨ds, H', oy, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, oy, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pslParams _ rfl hlk) hpsl)
    (fun o w s2 H2 hp2 ⟨sbs, o2, ho, hw, hb2⟩ => ?_)
  subst ho hw
  have hp2' : H1 <+: H2 := hp2
  simp only
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H2.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hsl2 := hb2.1
  simp only [List.length_map] at hsl2
  refine UD.specR_heapLoadI' (C := ctxH C H2) pbL (vv pbS) o2 _ hsl2 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hsbl0 : sbs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos sbs.length with h0 | hpos
    · omega
    · have h1 := hb2.2 (sbs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hsn : sbs.length = g.slots.length
  swap
  · have hne : BitVec.ofNat 64 sbs.length ≠ BitVec.ofNat 64 g.slots.length := fun e => hsn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, pbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsn]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  refine specR_callPure (C := ctxH C H2) pbR fCat catParams [vv pbB, vv pbS, .const 0] catBody
    [cellA C o1, cellA C o2, BitVec.ofNat 64 0] (pbs.map Enc.idxW ++ (sbs.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H2 <+: H' ∧ s' = s2 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (sbs.map Enc.idxW) o2 (by simp; omega) _ 0 _ o1 H2 s2 rfl (by omega)
        (blkAt_mono hb1 hp2') hb2))
    (fun w H3 hp3 ⟨o3, hw3, hb3⟩ => ?_)
  subst hw3
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨pbs ++ sbs, H3, o3, rfl,
    hp1'.trans (hp2'.trans hp3), rfl, by simpa using hb3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classGenRecTy` (one class) -/

def grtPre := ofString "grt_pre"
def grtPrl := ofString "grt_prl"
def grtDs := ofString "grt_ds"
def grtDn := ofString "grt_dn"
def grtFt := ofString "grt_ft"
def grtNi := ofString "grt_ni"
def grtInd := ofString "grt_ind"
def grtLv := ofString "grt_lv"
def grtNP := ofString "grt_np"
def grtM := ofString "grt_m"
def grtIf := ofString "grt_if"
def grtMj := ofString "grt_mj"
def grtLi := ofString "grt_li"
def grtT := ofString "grt_t"
def grtIb := ofString "grt_ib"
def grtLb := ofString "grt_lb"
def grtB1 := ofString "grt_b1"
def grtB2 := ofString "grt_b2"
def grtBs := ofString "grt_bs"
def grtZ := ofString "grt_z"
def grtSz := ofString "grt_sz"
def grtMv := ofString "grt_mv"
def grtA1 := ofString "grt_a1"
def grtA := ofString "grt_a"
def grtLa := ofString "grt_la"
def grtBd := ofString "grt_bd"
def grtLbs := ofString "grt_lbs"
def grtR := ofString "grt_r"
def grtOms := ofString "grt_oms"
def grtFts := ofString "grt_fts"
def grtOsl := ofString "grt_osl"
def grtCl := ofString "grt_cl"
def grtQ := ofString "grt_q"
def grtMs := ofString "grt_ms"
def fGrt := ofString "classGenRecTy"

def grtParams : List MlS := [grtPre, grtPrl, grtNP, grtOms, grtFts, grtOsl, grtCl]
def grtLocals : List MlS := [grtM, grtIf, grtMj, grtLi, grtT, grtIb, grtLb, grtB1, grtB2, grtBs, grtZ, grtSz, grtMv, grtA1, grtA, grtLa, grtBd, grtLbs, grtR, grtNi, grtQ, grtMs]

def grtBody (C : Ctx) : ProgHOL 64 := prologue grtLocals
  (.seq (.assign .local grtQ (.load .one (vv grtOms)))
  (.ite (.cmp .lower (vv grtCl) (vv grtQ))
  (.seq (.assign .local grtQ (.load .one (.op .add [vv grtOms, .op .add [.panop .mul [vv grtCl, .const 8], .const 8]])))
  (.seq (.assign .local grtNi (.load .one (vv grtQ)))
  (guardP grtNi 56
  (.seq (.assign .local grtQ (.load .one (vv grtOsl)))
  (.seq (.call (some (some (.local, grtMs), none)) fMsl [vv grtOsl, .const 0, vv grtQ, vv grtCl])
  (.seq (.call (some (some (.local, grtM), none)) fMjr [vv grtOms, vv grtFts, vv grtCl, vv grtPrl])
  (.seq (.assign .local grtIf (.load .one (vv grtM)))
  (.seq (.assign .local grtMj (.load .one (.op .add [vv grtM, .const 8])))
  (.seq (.assign .local grtLi (.load .one (vv grtIf)))
  (.seq (.call (some (some (.local, grtT), none)) fInternFVar [vv grtMj, .op .add [vv grtPrl, vv grtLi]])
  (.seq (.call (some (some (.local, grtIb), none)) fFvtDs [vv grtIf])
  (.seq (.assign .local grtLb (.load .one (vv grtIb)))
  (.ite (.cmp .equal (vv grtLb) (vv grtNi))
  (.seq (.call (some (some (.local, grtB1), none)) fCat [vv grtPre, vv grtIb, .const 0])
  (alloc2 C grtB2 (.const 1) (vv grtMj)
  (.seq (.call (some (some (.local, grtBs), none)) fCat [vv grtB1, vv grtB2, .const 0])
  (.seq (.assign .local grtZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, grtSz), none)) fInternSort [vv grtZ])
  (.seq (.call (some (some (.local, grtMv), none)) fInternFVar [vv grtSz, .op .add [vv grtNP, vv grtMs]])
  (alloc2 C grtA1 (.const 1) (vv grtT)
  (.seq (.call (some (some (.local, grtA), none)) fCat [vv grtIf, vv grtA1, .const 0])
  (.seq (.assign .local grtLa (.load .one (vv grtA)))
  (.seq (.call (some (some (.local, grtBd), none)) ExK.fMka [vv grtMv, vv grtA, .const 0, vv grtLa])
  (.seq (.call (some (some (.local, grtR), none)) fCtg [(.const 0), .const 0, vv grtBs, .const 0, vv grtBd])
  (.return (vv grtR)))))))))))))
  hang)))))))))))))
  hang))

structure GRTCodes (C : Ctx) : Prop where
  mot : MOTCodes C
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  cat : CatCodes C
  msl : C.code.lookup fMsl = some (mslParams.map (fun p => (p, ShapeHOL.one)), mslBody, .one)
  self : C.code.lookup fGrt = some (grtParams.map (fun p => (p, ShapeHOL.one)), grtBody C, .one)

section
variable {σ : Type}

theorem grt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ grtLocals → (ctxEnv C ++ grtParams.zip vals).get x = none :=
  Knot.params_none C grtLocals grtParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`classGenRecTy g c`**: class `c`'s major and motive (its record off the class block, its motive variable through
`motiveSlotOf`). -/
theorem grt_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : GRTCodes C)
    (g : ClassGen) (cl oms fts osl : Nat) (hcl : cl < 2 ^ 63) (hT : TMBlkR C C.H oms g.cls)
    (hfts : BlkAt C.H fts (g.formerTys.map Enc.idxW)) (hsb : SlotBlk C C.H osl g.slots) (hsll : g.slots.length < 2 ^ 56)
    (opre : Nat) (hprl : g.pre.length < 2 ^ 56) (hpre : BlkAt C.H opre (g.pre.map Enc.idxW)) (hnP : g.nP < 2 ^ 56)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (grtParams.zip [cellA C opre, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP,
        cellA C oms, cellA C fts, cellA C osl, BitVec.ofNat 64 cl])) (grtBody C) s (classGenRecTy g cl) (PostSomeH C) := by
  refine specR_prologue (postSomeH_locals _) (grt_none _ _) ?_
  unfold classGenRecTy
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN0 => ?_)
  have hHN0' : C.H.length ≤ C.HN := hHN0
  have hlay := hok.heapLay
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := id hT
  have hcl0 : C.H[oms]? = some (BitVec.ofNat 64 g.cls.length) := by simpa [hpsl] using hpsb.1
  refine UD.specR_heapLoadI' (C := ctxH C C.H) grtQ (vv grtOms) oms _ hcl0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv]; rfl) ?_
  have hclen : g.cls.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN0' hpsb; simp at this; omega
  have hlwc := nd_lt_iff cl g.cls.length (by omega) (by omega)
  by_cases hcl' : cl < g.cls.length
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, grtParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, grtParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwc.mpr hcl']) (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨op, hop, hrep⟩ := hpsr cl hcl'
  have hq := hpsb.2 cl (by simp; omega)
  simp only [List.getElem_map] at hq
  have hpi : ps[cl]'(by omega) = op := by
    rw [List.getElem?_eq_getElem (by omega)] at hop; exact Option.some.inj hop
  rw [hpi] at hq
  generalize g.cls[cl] = m at hrep
  obtain ⟨-, -, -, -, -, -, hniE, -, -, -⟩ := hrep
  refine UD.specR_heapLoadI' (C := ctxH C C.H) grtQ _ (oms + 1 + cl) _ hq (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv]; exact cellA_mulIdx C oms cl (by omega)) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) grtNi (vv grtQ) op _ hniE.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine specR_guardI grtNi m.nIdx 56 (by decide) (by simp [Env.get_cons]) (by have := hniE.2; omega)
    (fun hni => ?_)
  obtain ⟨sps, hspl, hspb, hspr⟩ := id hsb
  have hsl0' : C.H[osl]? = some (BitVec.ofNat 64 g.slots.length) := by simpa [hspl] using hspb.1
  refine UD.specR_heapLoadI' (C := ctxH C C.H) grtQ (vv grtOsl) osl _ hsl0' (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv]; rfl) ?_
  have hmsl := msl_spec (σ := σ) C hok hc.msl g.slots osl (by omega) C.H hsb
  refine specR_callPure (C := ctxH C C.H) grtMs fMsl mslParams [vv grtOsl, .const 0, vv grtQ, vv grtCl] mslBody
    [cellA C osl, BitVec.ofNat 64 0, BitVec.ofNat 64 g.slots.length, BitVec.ofNat 64 cl]
    ((((List.range' 0 (g.slots.length - 0)).filter (isMotSlot g.slots))[cl]?).getD 0) (by decide) rfl (by decide) hc.msl
    ⟨by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv], trivial⟩
    (PostMSL (ctxH C C.H) s) (fun r w s' H' => H' = C.H ∧ w = BitVec.ofNat 64 r)
    (fun r w s' st ⟨_, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mslParams _ rfl hlk)
      (hmsl g.slots.length 0 cl s (by omega) (by omega) (by omega)))
    (fun w H' _ ⟨eH, hw⟩ => ?_)
  subst H' hw
  have hms : (ClassRead.motiveSlot g.slots cl).getD 0 =
      (((List.range' 0 (g.slots.length - 0)).filter (isMotSlot g.slots))[cl]?).getD 0 := by rw [motiveSlot_eq]
  have hrle : (((List.range' 0 (g.slots.length - 0)).filter (isMotSlot g.slots))[cl]?).getD 0 ≤ g.slots.length := by
    rcases h : ((List.range' 0 (g.slots.length - 0)).filter (isMotSlot g.slots))[cl]? with _ | v
    · simp
    · simp only [Option.getD_some]
      have := List.mem_of_getElem? h
      simp only [List.mem_filter, List.mem_range'] at this
      omega
  generalize (((List.range' 0 (g.slots.length - 0)).filter (isMotSlot g.slots))[cl]?).getD 0 = r at hms hrle
  refine specR_callNIH (C := ctxH C C.H) grtM fMjr mjrParams [vv grtOms, vv grtFts, vv grtCl, vv grtPrl]
    (mjrBody C) [cellA C oms, cellA C fts, BitVec.ofNat 64 cl, BitVec.ofNat 64 g.pre.length] (by decide) rfl (by decide) hc.mot.mjr.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv], trivial⟩
    (PostMJ (ctxH C C.H)) (fun o w _ H' => ∃ ifs maj ob oi, o = some (ifs, maj) ∧ w = cellA C ob ∧
      H'[ob]? = some (cellA C oi) ∧ BlkAt H' oi (ifs.map Enc.idxW) ∧ H'[ob + 1]? = some (Enc.idxW maj) ∧
      ifs.length < 2 ^ 56)
    (fun o w s' st ⟨H', ifs, maj, ob, oi, hp', h1, h2, h3, h4, h5, h6, hsr⟩ => ⟨H', hp', ⟨ifs, maj, ob, oi, h1, h2, h3, h4,
      h5, h6⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mjrParams _ rfl hlk)
      (mjr_spec ra (ctxH C C.H) (ctxOK_H hok C.H) (by ctx_tr hc.mot.mjr) g cl oms fts hcl hT hfts g.pre.length (by omega) s))
    (fun o w s1 H1 hp1 ⟨ifs, maj, ob, oi, ho, hw, hob, hib, hmj, hil⟩ => ?_)
  subst ho hw
  have hp1' : C.H <+: H1 := hp1
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H1) grtIf (vv grtM) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) grtMj _ (ob + 1) _ hmj (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ob) ?_
  have hil1 := hib.1
  simp only [List.length_map] at hil1
  refine UD.specR_heapLoadI' (C := ctxH C H1) grtLi (vv grtIf) oi _ hil1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hok1 := ctxOK_H hok H1
  refine ILP.specR_internFVarI ra hok1 hc.fv grtT (vv grtMj) (.op .add [vv grtPrl, vv grtLi]) maj
    (g.pre.length + ifs.length) (by omega) (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) (fun t s2 => ?_)
  rw [mapM_binder_eq]
  refine specR_callNIH (C := ctxH C H1) grtIb fFvtDs ftdParams [vv grtIf] (ftdBody C) [cellA C oi] (by decide) rfl
    (by decide) hc.mot.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H1)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
    (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
      (ftd_spec C hok hc.mot.ftd hc.mot.ftf hc.mot.fvt ifs oi (by omega) H1 s2 hib))
    (fun ibs w s3 H2 hp2 ⟨o2, hw2, hb2⟩ => ?_)
  subst hw2
  have hp2' : H1 <+: H2 := hp2
  have hbl := hb2.1
  simp only [List.length_map] at hbl
  refine UD.specR_heapLoadI' (C := ctxH C H2) grtLb (vv grtIb) o2 _ hbl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H2.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hbl0 : ibs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos ibs.length with h0 | hpos
    · omega
    · have h1 := hb2.2 (ibs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hbn : ibs.length = m.nIdx
  swap
  · have hne : BitVec.ofNat 64 ibs.length ≠ BitVec.ofNat 64 m.nIdx := fun e => hbn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hbn]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  refine specR_callPure (C := ctxH C H2) grtB1 fCat catParams [vv grtPre, vv grtIb, .const 0] catBody
    [cellA C opre, cellA C o2, BitVec.ofNat 64 0] (g.pre.map Enc.idxW ++ (ibs.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H2 <+: H' ∧ s' = s3 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (ibs.map Enc.idxW) o2 (by simp; omega) _ 0 _ opre H2 s3 rfl (by omega)
        (blkAt_mono hpre hpC2) hb2))
    (fun w H3 hp3 ⟨o3, hw3, hb3⟩ => ?_)
  subst hw3
  have hp3' : H2 <+: H3 := hp3
  refine specR_alloc2I (ctxOK_H hok H3) grtB2 (.const 1) (vv grtMj) (BitVec.ofNat 64 1) (Enc.idxW maj)
    (by decide) (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H4 ws4 hp4 hws4 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H4 ws4 (BitVec.ofNat 64 1) (Enc.idxW maj) hws4
  have hp4' : H3 <+: _ := (hp4 : H3 <+: H4).trans (img2_prefix H4 ws4 (BitVec.ofNat 64 1) (Enc.idxW maj) hws4)
  have hb4 : BlkAt (((H4 ++ ws4).set H4.length (BitVec.ofNat 64 1)).set (H4.length + 1) (Enc.idxW maj)) H4.length
      [Enc.idxW maj] := ⟨by simpa using k0, fun i hi => by simp at hi; subst hi; simpa using k1⟩
  refine specR_callPure (C := ctxH C _) grtBs fCat catParams [vv grtB1, vv grtB2, .const 0] catBody
    [cellA C o3, cellA C H4.length, BitVec.ofNat 64 0]
    ((g.pre.map Enc.idxW ++ (ibs.map Enc.idxW).drop 0) ++ [Enc.idxW maj].drop 0) (by decide) rfl (by decide) hc.cat.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, rfl, trivial⟩
    (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s3 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat [Enc.idxW maj] H4.length (by simp) _ 0 _ o3 _ s3 rfl (by simp) (blkAt_mono hb3 hp4') hb4))
    (fun w H5 hp5 ⟨o5, hw5, hb5⟩ => ?_)
  subst hw5
  have hp5' : _ <+: H5 := hp5
  have hb5' : BlkAt H5 o5 ((g.pre ++ ibs ++ [maj]).map Enc.idxW) := by simpa using hb5
  simp only [ClassGen.motVar, hms, ClassGen.slotVar, zeroLevel, bind_assoc]
  have hok5 := ctxOK_H hok H5
  refine specR_pinXI (C := ctxH C H5) hok5 pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H5) hok5 hp) (pin_zeroLevel_cell hok5) grtZ (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H5) grtSz fInternSort [lEu] [vv grtZ] sortBody [Enc.idxW C.pins.zeroLevel]
    (by decide) rfl (by decide) hc.mot.srt ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
    (sort_body_spec ra (ctxH C H5) hok5 s3 _) (fun sz s4 => ?_)
  refine ILP.specR_internFVarI ra hok5 hc.fv grtMv (vv grtSz) (.op .add [vv grtNP, vv grtMs]) sz (g.nP + r) (by omega)
    (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [sev, Env.get_cons, Env.get, grtParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) (fun mv s5 => ?_)
  refine specR_alloc2I hok5 grtA1 (.const 1) (vv grtT) (BitVec.ofNat 64 1) (Enc.idxW t)
    (by decide) (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H6 ws6 hp6 hws6 => ?_)
  obtain ⟨j0, j1⟩ := img2_get H6 ws6 (BitVec.ofNat 64 1) (Enc.idxW t) hws6
  have hp6' : H5 <+: _ := (hp6 : H5 <+: H6).trans (img2_prefix H6 ws6 (BitVec.ofNat 64 1) (Enc.idxW t) hws6)
  have hb6 : BlkAt (((H6 ++ ws6).set H6.length (BitVec.ofNat 64 1)).set (H6.length + 1) (Enc.idxW t)) H6.length
      [Enc.idxW t] := ⟨by simpa using j0, fun i hi => by simp at hi; subst hi; simpa using j1⟩
  have hib6 : BlkAt _ oi (ifs.map Enc.idxW) := blkAt_mono hib (hp2'.trans (hp3'.trans (hp4'.trans (hp5'.trans hp6'))))
  refine specR_callPure (C := ctxH C _) grtA fCat catParams [vv grtIf, vv grtA1, .const 0] catBody
    [cellA C oi, cellA C H6.length, BitVec.ofNat 64 0] (ifs.map Enc.idxW ++ [Enc.idxW t].drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, rfl, trivial⟩
    (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s5 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat [Enc.idxW t] H6.length (by simp) _ 0 _ oi _ s5 rfl (by simp) hib6 hb6))
    (fun w H7 hp7 ⟨o7, hw7, hb7⟩ => ?_)
  subst hw7
  have hp7' : _ <+: H7 := hp7
  have hb7' : BlkAt H7 o7 ((ifs ++ [t]).map Enc.idxW) := by simpa using hb7
  have hl7 := hb7'.1
  simp only [List.length_map] at hl7
  have hpC7 : C.H <+: H7 := hpC2.trans (hp3'.trans (hp4'.trans (hp5'.trans (hp6'.trans hp7'))))
  refine UD.specR_heapLoadI' (C := ctxH C H7) grtLa (vv grtA) o7 _ hl7 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine ILP.callE_spec (C := ctxH C H7) grtBd ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv grtMv, vv grtA, .const 0, vv grtLa] ExK.mkaBody
    [Enc.idxW mv, cellA C o7, BitVec.ofNat 64 0, BitVec.ofNat 64 (ifs ++ [t]).length] (by decide) rfl (by decide)
    hc.mot.mjr.mka
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
      trivial⟩
    (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H7) (ctxOK_H hok H7) hc.mot.mjr.mka hc.mot.mjr.app o7 (ifs ++ [t]) hb7' (by simp; omega) 0 (by omega) mv s5; simp only [List.drop_zero] at h; exact h)
    (fun body s6 => ?_)
  unfold closeTelescope
  have hb5'' : BlkAt H7 o5 ((g.pre ++ ibs ++ [maj]).map Enc.idxW) := blkAt_mono hb5' (hp6'.trans hp7')
  refine specR_callNIH (C := ctxH C H7) grtR fCtg ctgParams [.const 0, .const 0, vv grtBs, .const 0, vv grtBd] ctgBody
    [BitVec.ofNat 64 0, BitVec.ofNat 64 0, cellA C o5, BitVec.ofNat 64 0, Enc.idxW body] (by decide) rfl (by decide)
    hc.mot.ctg.self ⟨rfl, rfl, by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostK (ctxH C H7)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctgParams _ rfl hlk)
      (by have h := ctg_spec (σ := σ) ra C hok hc.mot.ctg 0 (by omega) (g.pre ++ ibs ++ [maj]) o5 (by simp; omega) body (g.pre ++ ibs ++ [maj]).length 0 0 H7 s6 (by omega) (by omega) (by simp; omega) hpC7 hb5''; simp only [List.drop_zero] at h; exact h))
    (fun r w s7 H8 hp8 hw => ?_)
  subst hw
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun tt ht => ⟨H8, r, hpC7.trans hp8, rfl, rfl,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
