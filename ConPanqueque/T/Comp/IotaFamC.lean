import ConPanqueque.T.Core.IotaFamBody
import ConPanqueque.T.Comp.InferProjC
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `iotaFam`

The ι certificate's family check from its callees, every environment fact read off the state relation through
the recursor's and the constructor's `find?`.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

open ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq ConPanqueque.T.NEq
  ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub ConPanqueque.T.LLeq in
/-- The code `lvlsEq?` runs. -/
structure LsCodes (C : Ctx) : Prop where
  S : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one)
  N : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one)
  M : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one)
  Cb : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one)
  B : C.code.lookup fByC = some (LLeq.bcParams.map (fun p => (p, ShapeHOL.one)), LLeq.bcBody C, .one)
  I : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one)
  R : C.code.lookup fImax = some (leqParams.map (fun p => (p, ShapeHOL.one)), imBody C, .one)
  E : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one)
  Tr : C.code.lookup fRest = some (leqParams.map (fun p => (p, ShapeHOL.one)), restBody, .one)
  L : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), leqBody, .one)
  V : C.code.lookup fEqv = some ([(pLa, .one), (pLb, .one)], eqvBody, .one)
  G : C.code.lookup fLsGo = some (lsParams.map (fun p => (p, ShapeHOL.one)), lsGoBody, .one)

/-- The code `iotaFam` runs besides the knot entries. -/
structure FmAll (C : Ctx) : Prop where
  fm : FmCodes C
  rf : RfCodes C
  c3 : C3Codes C
  fz : FzCodes C
  fa : FaCodes C
  ik : IkCodes C
  ls : LsCodes C

section
variable {σ : Type}

theorem fm_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (hv : mode.verifiedChecks = true) (n : Nat) {C : Ctx} (hok : CtxOK C) (hc : FmAll C) (hn : n < 2 ^ 64)
    (hE : Ents (σ := σ) mode n C) (d : Nat)
    (s : AState) (c : NIdx) (us : LsIdx) (cv : IConstantVal) (mI rP : Nat) (isK : Bool) (rules : List IRecRule)
    (q : Nat) (hci : CIE C.EB C.EH q (.recInfo cv mI rP isK rules))
    (hfc : C.fe.find? c = some (.recInfo cv mI rP isK rules))
    (sargs : List EIdx) (oa : Nat) (hba : BlkAt C.H oa (sargs.map Enc.idxW)) (hle : mI + 1 ≤ sargs.length)
    (hsl : sargs.length < 2 ^ 58)
    (usj : LsIdx) (qj : Nat) (cvj : IConstantVal) (cnP nF : Nat) (ind : NIdx)
    (hcij : CIE C.EB C.EH qj (.ctorInfo cvj cnP nF ind)) {cj : NIdx}
    (hfj : C.fe.find? cj = some (.ctorInfo cvj cnP nF ind))
    (qr : Nat) (rl : IRecRule) (hrule : RuleE C.EB C.EH qr rl) (hrl : rl ∈ rules)
    (om : Nat) (margs : List EIdx) (hml : margs.length < 2 ^ 58)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hbm : BlkAt H om (margs.map Enc.idxW)) :
    SpecR (σ := σ) (Pre (ctxH C H) s (fmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW us,
      ecell C q, cellA C oa, BitVec.ofNat 64 (mI + 1), Enc.idxW usj, ecell C qj, ecell C qr, cellA C om])) (fmBody C) s
      (iotaFam mode (knot mode C n) C.fe d cv us mI rP isK (sargs.take (mI + 1)) usj cvj cnP ind rl margs)
      (Knot.PostB (ctxH C H)) := by
  obtain ⟨_, _, _, ⟨_, hrp⟩, _⟩ := id hci
  obtain ⟨_, _, ⟨_, hcnb⟩, _⟩ := id hcij
  refine fm_spec ra mode hv n C hok hc.fm d (fun H s1 hp e => hE.hI H s1 d e hp) (fun H s1 hp a b => hE.hD H s1 d a b hp)
    s c us cv mI rP isK rules q hci sargs oa hba hle hsl usj qj cvj cnP nF ind hcij qr rl hrule om margs hml
    (fun _ => True) trivial ?_ (fun _ _ _ _ _ => trivial) ?_ (fun _ _ _ _ _ _ => trivial) ?_
    (fun _ _ _ _ _ _ => trivial) ?_ (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) ?_ H hp hbm
  · -- recFireLevels
    intro H' s1 ok oj hp' _ hk hj t ht
    have h := ht.1
    obtain ⟨ks, hks⟩ := sr_lpDen h c _ hfc
    have hll := sr_lpLen h c _ hfc
    have hjl := sr_lpLen' h cj _ hfj
    have hrd := sr_recDen h hfc hrl
    simp only [IConstantInfo.toConstantVal] at hks hll hjl
    exact rf_spec ra C hok hc.rf s1 rl qr hrule cv.levelParams cvj.levelParams ok oj hk hj us ks hks h.twf
      h.cok.rn h.cok.rl h.cok.rls
      (fun _ => by obtain ⟨pns, hpns⟩ := sr_lpDen h cj _ hfj; exact ⟨pns, by simpa [IConstantInfo.toConstantVal] using hpns⟩)
      (fun lv hlv j hj => (hrd.1 lv hlv).1 _ (List.getElem_mem hj)) (fun lv hlv => (hrd.1 lv hlv).2)
      hll hjl H' hp' t ht
  · -- iotaCase3
    intro H' s1 L hp' _
    refine c3_spec mode n C hok hc.c3 s1 d isK ind L (fun cvT caps o hf hcT H2 hp2 => ?_) H' hp'
    intro t ht
    have h := ht.1
    obtain ⟨ks, hks⟩ := sr_lpDen h ind _ hf
    have hlen := sr_lpLen h ind _ hf
    have hden := sr_tyDen h ind _ hf
    simp only [IConstantInfo.toConstantVal] at hks hlen hden
    exact fza_spec ra mode n (ctxH C H2) (ctxOK_H hok H2) (by ctx_tr hc.fz) hn
      (fun H3 s3 hp3 d' e' => (hE.at H2 C.St).hW H3 s3 d' e' hp3) s1 d cvT caps o hcT L (sr_lwf h) (sr_stateOK h)
      ks hks h.cok.rn h.cok.rl h.cok.rls hden hlen (sr_capsLen h hf) t ht
  · -- lvlsEq?
    intro H' s1 L hp' _
    exact specR_mono (LLeq.lvlsEqQ_spec' C hok hc.ls.S hc.ls.N hc.ls.M hc.ls.Cb hc.ls.B hc.ls.I hc.ls.R hc.ls.E
      hc.ls.Tr hc.ls.L hc.ls.V hc.ls.G H' usj L s1) (fun _ h => h)
      (fun _ _ _ _ ⟨_, _, hw, hsr⟩ => ⟨H', List.prefix_refl _, hw, hsr⟩)
  · -- recFireArgs
    intro H' s1 ok oa' hp' _ hk hb t ht
    have h := ht.1
    obtain ⟨ks, hks⟩ := sr_lpDen h c _ hfc
    have hll := sr_lpLen h c _ hfc
    simp only [IConstantInfo.toConstantVal] at hks hll
    exact fa_spec' ra C hok hc.fa s1 rl qr hrule cv.levelParams ok hk hll us ks (sargs.take (mI + 1)) rP cnP hrp hcnb
      hks (sr_recDen h hfc hrl).2 H' hp' oa' hb (by simp; omega) t ht
  · -- constTyAt of the constructor
    intro H' s1 oj hp' _ hj
    have := ct_pre (σ := σ) ra (ctxOK_H hok H') (by ctx_tr hc.ik) s1 hfj oj hj usj
    simp only [IConstantInfo.toConstantVal] at this
    exact this

end

end ConPanqueque.T.Comp
