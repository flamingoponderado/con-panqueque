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
def fMjr := ofString "classMajor"

def mjrParams : List MlS := [mjrDs, mjrDn, mjrFt, mjrNi, mjrD, mjrInd, mjrLv]
def mjrLocals : List MlS := [mjrTy, mjrX, mjrIf, mjrLi, mjrHd, mjrA1, mjrL1, mjrMj, mjrR]

def mjrBody (C : Ctx) : ProgHOL 64 := prologue mjrLocals
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
  hang))))))

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
/-- **`ClassGen.major 0 d`** for the one class. -/
theorem mjr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : MJRCodes C)
    (g : ClassGen) (m : TargetMajor) (hcls : g.cls = [m]) (fty : EIdx) (hft : g.formerTys[0]? = some fty)
    (d : Nat) (hd : d + m.nIdx < 2 ^ 62) (hni : m.nIdx < 2 ^ 56) (pd : Nat) (hds : BlkAt C.H pd (m.ds.map Enc.idxW))
    (hdl : m.ds.length < 2 ^ 56) (s : AState) :
    SpecR (σ := σ) (Pre C s (mjrParams.zip [cellA C pd, BitVec.ofNat 64 m.ds.length, Enc.idxW fty,
        BitVec.ofNat 64 m.nIdx, BitVec.ofNat 64 d, Enc.idxW m.ind, Enc.idxW m.lvls])) (mjrBody C) s (g.major 0 d)
      (PostMJ C) := by
  refine specR_prologue (postMJ_locals _) (mjr_none _ _) ?_
  unfold ClassGen.major
  simp only [hcls, targetMajorAt, List.getElem?_cons_zero, pure_bind, exprGetD, hft]
  have hp0 : C.H <+: C.H := List.prefix_refl _
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
def fMot := ofString "motiveTy"

def motParams : List MlS := [motDs, motDn, motFt, motNi, motD, motInd, motLv, motEl]
def motLocals : List MlS := [motM, motIf, motMj, motSrt, motBd, motBs, motLb, motR]

def motBody : ProgHOL 64 := prologue motLocals
  (.seq (.call (some (some (.local, motM), none)) fMjr [vv motDs, vv motDn, vv motFt, vv motNi, vv motD, vv motInd, vv motLv])
  (.seq (.assign .local motIf (.load .one (vv motM)))
  (.seq (.assign .local motMj (.load .one (.op .add [vv motM, .const 8])))
  (.seq (.call (some (some (.local, motSrt), none)) fInternSort [vv motEl])
  (.seq (.call (some (some (.local, motBd), none)) fInternForallE [vv motMj, vv motSrt])
  (.seq (.call (some (some (.local, motBs), none)) fFvtDs [vv motIf])
  (.seq (.assign .local motLb (.load .one (vv motBs)))
  (.ite (.cmp .equal (vv motLb) (vv motNi))
  (.seq (.call (some (some (.local, motR), none)) fCtg [vv motD, .const 0, vv motBs, .const 0, vv motBd])
  (.return (vv motR)))
  hang))))))))

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
/-- **`ClassGen.motiveTy 0 d`** for the one class. -/
theorem mot_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : MOTCodes C)
    (g : ClassGen) (m : TargetMajor) (hcls : g.cls = [m]) (fty : EIdx) (hft : g.formerTys[0]? = some fty)
    (d : Nat) (hd : d + m.nIdx < 2 ^ 62) (hni : m.nIdx < 2 ^ 56) (pd : Nat) (hds : BlkAt C.H pd (m.ds.map Enc.idxW))
    (hdl : m.ds.length < 2 ^ 56) (s : AState) :
    SpecR (σ := σ) (Pre C s (motParams.zip [cellA C pd, BitVec.ofNat 64 m.ds.length, Enc.idxW fty,
        BitVec.ofNat 64 m.nIdx, BitVec.ofNat 64 d, Enc.idxW m.ind, Enc.idxW m.lvls, Enc.idxW g.elim])) motBody s
      (g.motiveTy 0 d) (PostSomeH C) := by
  refine specR_prologue (postSomeH_locals _) (mot_none _ _) ?_
  unfold ClassGen.motiveTy
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine specR_callNIH (C := ctxH C C.H) motM fMjr mjrParams [vv motDs, vv motDn, vv motFt, vv motNi, vv motD, vv motInd,
    vv motLv] (mjrBody C) [cellA C pd, BitVec.ofNat 64 m.ds.length, Enc.idxW fty, BitVec.ofNat 64 m.nIdx,
      BitVec.ofNat 64 d, Enc.idxW m.ind, Enc.idxW m.lvls] (by decide) rfl (by decide) hc.mjr.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, motParams, ctxEnv], trivial⟩
    (PostMJ (ctxH C C.H)) (fun o w _ H' => ∃ ifs maj ob oi, o = some (ifs, maj) ∧ w = cellA C ob ∧
      H'[ob]? = some (cellA C oi) ∧ BlkAt H' oi (ifs.map Enc.idxW) ∧ H'[ob + 1]? = some (Enc.idxW maj) ∧
      ifs.length < 2 ^ 56)
    (fun o w s' st ⟨H', ifs, maj, ob, oi, hp', h1, h2, h3, h4, h5, h6, hsr⟩ => ⟨H', hp', ⟨ifs, maj, ob, oi, h1, h2, h3, h4,
      h5, h6⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mjrParams _ rfl hlk)
      (mjr_spec ra (ctxH C C.H) (ctxOK_H hok C.H) (by ctx_tr hc.mjr) g m hcls fty hft d hd hni pd hds hdl s))
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

end ConPanqueque.T.Ind
