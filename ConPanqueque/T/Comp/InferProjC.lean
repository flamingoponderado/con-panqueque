import ConPanqueque.T.Core.InferProj
import ConPanqueque.T.Comp.InferLeaves
import ConPanqueque.T.Comp.Ents
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `inferProj`

The projection arm from its guard (`projGuardSort`, `projGuardRows`, `checkGuardRows`) and `typeAt`, every
state fact read off the state relation, `checkGuardRows` run above a floor raised where the guard level was read.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.T.ILP (fInstLPF ilpfBody CodesILP ilpBody)

section
variable {σ : Type}

theorem ct_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C) (hc : IkCodes C)
    (s : AState) {c : NIdx} {ci : IConstantInfo} (hf : C.fe.find? c = some ci) (ok : Nat)
    (hblk : EBlk C.EH ok (ci.toConstantVal.levelParams.map Enc.idxW)) (us : LsIdx) :
    SpecR (σ := σ) (Pre C s (CV.cvParams.zip [Enc.idxW ci.toConstantVal.name, ecell C ok,
      Enc.idxW ci.toConstantVal.type, Enc.idxW us])) (CT.ctBody C) s (constTyAt ci.toConstantVal us) (PostK C) :=
  fun t ht => by
    have h := ht.1
    obtain ⟨ks, hks⟩ := sr_lpDen h c ci hf
    exact CT.ct_spec ra C hok hc.ilp hc.ilpf s ci.toConstantVal ks us ok hblk (sr_lpLen h c ci hf) hks
      (sr_stateOK h) h.cok.rn h.cok.rl h.cok.rls (sr_tyDen h c ci hf) t ht

theorem gw_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C) (hgw : GwCodes C)
    (hik : IkCodes C) (tbl : IProjTable) (ot : Nat) (htb : TblE C.EB C.EH ot tbl) (i : Nat) (hi : i < 2 ^ 63)
    (us : LsIdx) (s : AState) :
    SpecR (σ := σ) (Pre C s (gwParams.zip [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us])) (gwBody C) s
      (projGuardRows C.fe (tbl.entry i) us) (PostRows C) :=
  gw_spec ra C hok hgw tbl ot htb i hi us (fun _ => True)
    (fun s1 _ oL _ hf hblk => ct_pre ra hok hik s1 hf oL hblk us) s trivial

theorem gs_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hfz : FzCodes C) (hzw : ZwCodes C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) {T : NIdx} {cvT : IConstantVal} {caps : IIndCaps}
    (hf : C.fe.find? T = some (.indInfo cvT caps)) (o : Nat) (hci : CIE C.EB C.EH o (.indInfo cvT caps))
    (us : LsIdx) :
    SpecR (σ := σ) (Pre C s (fzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C o, Enc.idxW us]))
      (gsBody C) s (projGuardSort (knot mode C n) cvT caps us) (PostGS C) := fun t ht => by
  have h := ht.1
  obtain ⟨ks, hks⟩ := sr_lpDen h T _ hf
  have hlen := sr_lpLen h T _ hf
  have hden := sr_tyDen h T _ hf
  simp only [IConstantInfo.toConstantVal] at hks hlen hden
  exact gs_spec ra mode n C hok hfz hzw hn (fun H s1 hp d e => hE.hW H s1 d e hp) s d cvT caps o hci us
    (sr_lwf h) (sr_stateOK h) ks hks h.cok.rn h.cok.rl h.cok.rls hden hlen (sr_capsLen h hf) (sr_zeroLevel h) t ht

theorem cg_pre (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx} (hok : CtxOK C) (hcg : CgCodes C)
    (hE : Ents (σ := σ) mode n C) (gl : ConLeche.Level) (gh : LIdx) (hfl : denoteL C.St.ls gh = some gl)
    (rows : Array (Nat × EIdx)) (o : Nat) (hb : BlkAt C.H o (rowsW rows.toList)) (hsz : rows.size < 2 ^ 58)
    (hall : ∀ p ∈ rows.toList, p.1 < 2 ^ 63) (s : AState) :
    SpecR (σ := σ) (Pre C s (cgParams.zip [BitVec.ofNat 64 n, Enc.idxW gh, cellA C o,
      BitVec.ofNat 64 rows.size, BitVec.ofNat 64 0])) cgBody s
      (checkGuardRows (knot mode C n) gl rows 0) (PostU C) := by
  have h := cg_spec mode n C hok hcg gl gh hfl hE.hIO hE.hW rows.toList o C.H (List.prefix_refl _) hb
    (by simpa using hsz) hall rows.toList.length 0 C.H s (List.prefix_refl _) (by omega) (by omega)
  rw [Array.length_toList, Array.toArray_toList] at h
  exact h

theorem gd_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hgd : GdCodes C) (hfz : FzCodes C) (hzw : ZwCodes C) (hgw : GwCodes C) (hik : IkCodes C)
    (hcg : CgCodes C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (tbl : IProjTable) (ot : Nat) (htb : TblE C.EB C.EH ot tbl) (i : Nat) (hi : i < 2 ^ 63) (us : LsIdx)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (gdParams.zip [BitVec.ofNat 64 n, ecell C ot, BitVec.ofNat 64 i, Enc.idxW us]))
      (gdBody C) s (checkProjGuard (knot mode C n) C.fe (tbl.entry i) us) (PostU C) :=
  gd_spec mode n C hok hgd tbl ot htb i us
    (fun s1 _ _ o hf hci => gs_pre ra mode n hok hfz hzw hn hE s1 0 hf o hci us)
    (fun H St s1 _ => gw_pre ra (ctxOK_St (ctxOK_H hok H) St) (by ctx_tr hgw) (by ctx_tr hik) tbl ot htb i hi us s1)
    (fun H St s1 gl gh rows o _ hfl hb hsz hall =>
      cg_pre mode n (ctxOK_St (ctxOK_H hok H) St) (by ctx_tr hcg) (hE.at H St) gl gh hfl rows o hb hsz hall s1) s

theorem ta_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C) (hta : TaCodes C)
    (H : List (BitVec 64)) (s : AState) (tbl : IProjTable) (ot : Nat) (i : Nat) (us : LsIdx) (targs : List EIdx)
    (oa : Nat) (pe : EIdx) (hp : C.H <+: H) (htb : TblE C.EB C.EH ot tbl) (hT : ∃ T, C.fe.findTable? T = some tbl)
    (hba : BlkAt H oa (targs.map Enc.idxW)) (hi : i < 2 ^ 63) :
    SpecR (σ := σ) (Pre (ctxH C H) s (taParams.zip [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us, cellA C oa,
      Enc.idxW pe])) (taBody C) s ((tbl.entry i).typeAt us targs pe) (PostK (ctxH C H)) := fun t ht => by
  have h := ht.1
  obtain ⟨T, hT⟩ := hT
  obtain ⟨ks, hks⟩ := sr_tblLp h hT
  exact ta_spec ra C hok hta tbl ot htb i hi us targs pe H oa hp hba s ks hks (sr_stateOK h) h.cok.rn h.cok.rl
    h.cok.rls (sr_tblBodies h hT) (sr_tblLen h hT) t ht

/-- The code the projection arm runs, all of it. -/
structure PjAll (C : Ctx) : Prop where
  pj : PjCodes C
  gd : GdCodes C
  fz : FzCodes C
  zw : ZwCodes C
  gw : GwCodes C
  ik : IkCodes C
  cg : CgCodes C
  ta : TaCodes C

theorem pj_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : PjAll C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) (hd : d < 2 ^ 63) (sn : NIdx) (i : Nat) (pe : EIdx) (hi : i < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s (iprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i,
      Enc.idxW pe])) (pjBody C) s (inferProj (knot mode C n) C.fe d sn i pe) (PostK C) :=
  pj_spec mode n C hok hc.pj (fun _ => True) hE.hI hE.hW (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun H s1 tbl ot i us _ _ htb _ hi =>
      gd_pre ra mode n (ctxOK_H hok H) (by ctx_tr hc.gd) (by ctx_tr hc.fz) (by ctx_tr hc.zw) (by ctx_tr hc.gw)
        (by ctx_tr hc.ik) (by ctx_tr hc.cg) hn (hE.at H C.St) tbl ot htb i hi us s1)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun H s1 tbl ot i us targs oa pe hp _ htb hT hba hi => ta_pre ra hok hc.ta H s1 tbl ot i us targs oa pe hp htb hT hba hi)
    s trivial d hd sn i pe hi

end

end ConPanqueque.T.Comp
