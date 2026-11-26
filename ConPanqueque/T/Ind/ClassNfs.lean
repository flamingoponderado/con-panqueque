import ConPanqueque.T.Ind.TargetMatch
import ConPanqueque.T.Ind.NestCtors

/-!
# `targetMajorNfs` (single-member blocks)

The table's entries, the tail first: each must be one of the class's constructors and match the class
(`targetClassMatch`); otherwise the port hangs.  So the answer is the whole table.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## A name among a constructor list's names -/

def cnmC := ofString "cnm_c"
def cnmI := ofString "cnm_i"
def cnmN := ofString "cnm_n"
def cnmM := ofString "cnm_m"
def cnmO := ofString "cnm_o"
def cnmX := ofString "cnm_x"
def cnmR := ofString "cnm_r"
def fCnm := ofString "ctorNameMem"

def cnmParams : List MlS := [cnmC, cnmI, cnmN, cnmM]
def cnmLocals : List MlS := [cnmO, cnmX, cnmR]

def cnmBody : ProgHOL 64 := prologue cnmLocals
  (.ite (.cmp .lower (vv cnmI) (vv cnmN))
    (.seq (.assign .local cnmO (.load .one (.op .add [vv cnmC, .op .add [.panop .mul [vv cnmI, .const 16], .const 8]])))
    (.seq (.assign .local cnmX (.load .one (vv cnmO)))
    (.ite (.cmp .equal (vv cnmX) (vv cnmM)) (.return (.const 1))
      (.seq (.call (some (some (.local, cnmR), none)) fCnm [vv cnmC, .op .add [vv cnmI, .const 1], vv cnmN, vv cnmM])
        (.return (vv cnmR))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem cnm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnmLocals → (ctxEnv C ++ cnmParams.zip vals).get x = none :=
  Knot.params_none C cnmLocals cnmParams vals (by decide) (by decide)

/-- **`(cs.drop i).any (·.1.name == m)`**. -/
theorem cnm_spec (C : Ctx) (hc : C.code.lookup fCnm = some (cnmParams.map (fun p => (p, ShapeHOL.one)), cnmBody, .one))
    (cs : List (IConstantVal × Nat)) (oq : Nat) (hcsl : cs.length < 2 ^ 58) (m : NIdx) (H : List (BitVec 64))
    (hcr : CtorsRep C H oq cs) :
    ∀ f i (s : AState), cs.length - i = f → i ≤ cs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cnmParams.zip [cellA C oq, BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length,
        Enc.idxW m])) cnmBody s (pure ((cs.drop i).any (·.1.name == m))) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = cs.length := by omega
    subst hin
    refine specR_prologue (postB_locals _) (cnm_none _ _) ?_
    have hlw := nd_lt_iff cs.length cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cnmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < cs.length := by omega
    refine specR_prologue (postB_locals _) (cnm_none _ _) ?_
    have hlw := nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cnmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, hoc, hcv, -⟩ := hcr.2 i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) cnmO _ (oq + 1 + 2 * i) _ hoc (by decide)
      (by simp +decide [sev, Env.get, cnmParams, ctxEnv]; exact cellA_pair1 C oq i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnmX (vv cnmO) oc _ hcv.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin, List.any_cons]
    by_cases he : cs[i].1.name = m
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cnmParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [he]; rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hne : Enc.idxW cs[i].1.name ≠ Enc.idxW m := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cnmParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    have hbe : (cs[i].1.name == m) = false := beq_eq_false_iff_ne.mpr he
    rw [hbe, Bool.false_or]
    refine specR_congr (m' := (pure ((cs.drop (i + 1)).any (·.1.name == m)) : AM Bool) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H) cnmR fCnm cnmParams [vv cnmC, .op .add [vv cnmI, .const 1], vv cnmN, vv cnmM]
      cnmBody [cellA C oq, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length, Enc.idxW m] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cnmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cnmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnmParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cnmParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun b w s3 H3 hp3 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `targetMajorNfs` -/

def tmnT := ofString "tmn_t"
def tmnI := ofString "tmn_i"
def tmnK := ofString "tmn_k"
def tmnCs := ofString "tmn_cs"
def tmnNc := ofString "tmn_nc"
def tmnU := ofString "tmn_u"
def tmnLp := ofString "tmn_lp"
def tmnFt := ofString "tmn_ft"
def tmnP := ofString "tmn_p"
def tmnPn := ofString "tmn_pn"
def tmnA := ofString "tmn_a"
def tmnN := ofString "tmn_n"
def tmnNm := ofString "tmn_nm"
def tmnR := ofString "tmn_r"
def tmnPe := ofString "tmn_pe"
def tmnCt := ofString "tmn_ct"
def tmnMb := ofString "tmn_mb"
def tmnLv := ofString "tmn_lv"
def tmnDb := ofString "tmn_db"
def tmnQ := ofString "tmn_q"
def fTmn := ofString "targetMajorNfs"

def tmnParams : List MlS := [tmnT, tmnI, tmnK, tmnCs, tmnNc, tmnU, tmnLp, tmnFt, tmnP, tmnPn, tmnA, tmnN, tmnNm]
def tmnLocals : List MlS := [tmnR, tmnPe, tmnCt, tmnMb, tmnLv, tmnDb, tmnQ]

def tmnBody : ProgHOL 64 := prologue tmnLocals
  (.ite (.cmp .lower (vv tmnI) (vv tmnK))
    (.seq (.call (some (some (.local, tmnR), none)) fTmn
        [vv tmnT, .op .add [vv tmnI, .const 1], vv tmnK, vv tmnCs, vv tmnNc, vv tmnU, vv tmnLp, vv tmnFt, vv tmnP,
          vv tmnPn, vv tmnA, vv tmnN, vv tmnNm])
    (.seq (.assign .local tmnPe (.load .one (.op .add [vv tmnT, .op .add [.panop .mul [vv tmnI, .const 8], .const 8]])))
    (.seq (.assign .local tmnCt (.load .one (vv tmnPe)))
    (.seq (.call (some (some (.local, tmnMb), none)) fCnm [vv tmnCs, .const 0, vv tmnNc, vv tmnCt])
    (.ite (.cmp .equal (vv tmnMb) (.const 0)) hang
    (.seq (.assign .local tmnLv (.load .one (.op .add [vv tmnPe, .const 8])))
    (.seq (.assign .local tmnDb (.load .one (.op .add [vv tmnPe, .const 16])))
    (.seq (.call (some (some (.local, tmnQ), none)) fTcc
        [vv tmnU, vv tmnLv, vv tmnLp, vv tmnFt, vv tmnP, vv tmnPn, vv tmnA, vv tmnDb, vv tmnN, vv tmnNm])
    (.ite (.cmp .equal (vv tmnQ) (.const 0)) hang (.return (.const 0)))))))))))
    (.return (.const 0)))

structure TMNCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  cnm : C.code.lookup fCnm = some (cnmParams.map (fun p => (p, ShapeHOL.one)), cnmBody, .one)
  tcc : TCCCodes mode C
  self : C.code.lookup fTmn = some (tmnParams.map (fun p => (p, ShapeHOL.one)), tmnBody, .one)

section
variable {σ : Type}

theorem tmn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tmnLocals → (ctxEnv C ++ tmnParams.zip vals).get x = none :=
  Knot.params_none C tmnLocals tmnParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`targetMajorNfs`** from entry `i` on: every entry kept (or a hang). -/
theorem tmn_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : TMNCodes mode C) (p : BlockShape) (ms0 : MemberShape) (hms : p.members = [ms0])
    (ty0 : EIdx) (pfvs ds : List EIdx) (us : LsIdx) (ctors : List (IConstantVal × Nat)) (tbl : List NestCtorNf)
    (olp pp pa oq ot : Nat) (hlpl : ms0.cvT.levelParams.length < 2 ^ 59) (hdl : ds.length < 2 ^ 58)
    (hpl : pfvs.length < 2 ^ 58) (hcsl : ctors.length < 2 ^ 58) (htl : tbl.length < 2 ^ 58)
    (hel : ∀ e ∈ tbl, e.ds.length < 2 ^ 58)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hlp : EBlk H0 olp (ms0.cvT.levelParams.map Enc.idxW))
    (hpf : BlkAt H0 pp (pfvs.map Enc.idxW)) (hA : BlkAt H0 pa (ds.map Enc.idxW)) (hcr : CtorsRep C H0 oq ctors)
    (htb : PRep C H0 ot (fun H o nf => NfRep C H o nf) tbl) :
    ∀ f i (H : List (BitVec 64)) (s : AState), tbl.length - i = f → i ≤ tbl.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (tmnParams.zip [cellA C ot, BitVec.ofNat 64 i, BitVec.ofNat 64 tbl.length,
        cellA C oq, BitVec.ofNat 64 ctors.length, Enc.idxW us, cellA C olp, Enc.idxW ty0, cellA C pp,
        BitVec.ofNat 64 pfvs.length, cellA C pa, BitVec.ofNat 64 ds.length, Enc.idxW ms0.cvT.name])) tmnBody s
        (targetMajorNfs mode C.fe p [ty0] pfvs us ds ctors (tbl.drop i))
        (fun r w s' st => r = tbl.drop i ∧ Decl.PostU (ctxH C H) () w s' st) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := htb
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = tbl.length := by omega
    subst hin
    refine specR_prologue (fun a w s' st L ⟨h1, H', hp', hsr⟩ => ⟨h1, H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩)
      (tmn_none _ _) ?_
    have hlw := nd_lt_iff tbl.length tbl.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨by simp, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < tbl.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (fun a w s' st L ⟨h1, H', hp', hsr⟩ => ⟨h1, H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩)
      (tmn_none _ _) ?_
    have hlw := nd_lt_iff i tbl.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin]
    unfold targetMajorNfs
    refine specR_callNIH (C := ctxH C H) tmnR fTmn tmnParams
      [vv tmnT, .op .add [vv tmnI, .const 1], vv tmnK, vv tmnCs, vv tmnNc, vv tmnU, vv tmnLp, vv tmnFt, vv tmnP,
        vv tmnPn, vv tmnA, vv tmnN, vv tmnNm] tmnBody
      [cellA C ot, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 tbl.length, cellA C oq, BitVec.ofNat 64 ctors.length,
        Enc.idxW us, cellA C olp, Enc.idxW ty0, cellA C pp, BitVec.ofNat 64 pfvs.length, cellA C pa,
        BitVec.ofNat 64 ds.length, Enc.idxW ms0.cvT.name] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], trivial⟩
      (fun r w s' st => r = tbl.drop (i + 1) ∧ Decl.PostU (ctxH C H) () w s' st) (fun r _ _ _ => r = tbl.drop (i + 1))
      (fun r w s' st ⟨h1, H', hp', hsr⟩ => ⟨H', hp', h1, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tmnParams _ rfl hlk)
        (ih (i + 1) H s (by omega) (by omega) hp))
      (fun r w s1 H1 hp1 hr => ?_)
    subst hr
    have hp1' : H <+: H1 := hp1
    have h01 : H0 <+: H1 := hp.trans hp1'
    have hio : i < os.length := by omega
    have hpe := hosb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    obtain ⟨hct, hlv, ⟨od, hod, hdb⟩, -⟩ := hosr i hin hio
    refine UD.specR_heapLoadI' (C := ctxH C H1) tmnPe _ (ot + 1 + i) _ (get_prefix hpe h01) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv]; exact cellA_mulIdx C ot i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) tmnCt (vv tmnPe) os[i] _ (get_prefix hct h01) (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    refine specR_callPure (C := ctxH C H1) tmnMb fCnm cnmParams [vv tmnCs, .const 0, vv tmnNc, vv tmnCt] cnmBody
      [cellA C oq, BitVec.ofNat 64 0, BitVec.ofNat 64 ctors.length, Enc.idxW tbl[i].ctor]
      ((ctors.drop 0).any (·.1.name == tbl[i].ctor)) (by decide) rfl (by decide) hc.cnm
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩ (PostB (ctxH C H1))
      (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cnmParams _ rfl hlk)
        (cnm_spec C hc.cnm ctors oq hcsl tbl[i].ctor H1 (ctorsRep_mono h01 hcr) ctors.length 0 s1 (by omega) (by omega)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    have h02 : H0 <+: H2 := h01.trans hp2'
    simp only [List.drop_zero] at *
    cases hany : ctors.any (·.1.name == tbl[i].ctor)
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hany, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hany, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [↓reduceIte]
    refine UD.specR_heapLoadI' (C := ctxH C H2) tmnLv _ (os[i] + 1) _ (get_prefix hlv h02) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C os[i]) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) tmnDb _ (os[i] + 2) _ (get_prefix hod h02) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C os[i] 2) ?_
    have hel' := hel tbl[i] (List.getElem_mem hin)
    refine specR_callNIH (C := ctxH C H2) tmnQ fTcc tccParams
      [vv tmnU, vv tmnLv, vv tmnLp, vv tmnFt, vv tmnP, vv tmnPn, vv tmnA, vv tmnDb, vv tmnN, vv tmnNm] (tccBody C)
      [Enc.idxW us, Enc.idxW tbl[i].lvls, cellA C olp, Enc.idxW ty0, cellA C pp, BitVec.ofNat 64 pfvs.length,
        cellA C pa, cellA C od, BitVec.ofNat 64 ds.length, Enc.idxW ms0.cvT.name] (by decide) rfl (by decide) hc.tcc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], trivial⟩
      (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tccParams _ rfl hlk)
        (tcc_spec mode ra C hok hs hc.tcc p ms0 hms ty0 pfvs ds tbl[i].ds us tbl[i].lvls olp pp pa od hlpl hdl hel' hpl
          H2 (hp0.trans h02) (eblk_mono hlp h02) (blkAt_mono hpf h02) (blkAt_mono hA h02) (blkAt_mono hdb h02)
          _))
      (fun b w s3 H3 hp3 hw => ?_)
    subst hw
    cases b
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, H3, hp1'.trans (hp2'.trans hp3), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
