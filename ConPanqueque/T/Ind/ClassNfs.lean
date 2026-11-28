import ConPanqueque.T.Ind.TargetMatch
import ConPanqueque.T.Ind.NestCtors

/-!
# `targetMajorNfs`

The table's entries, the tail first: an entry of another class's constructor is skipped; an entry of one of the
class's constructors must match the class (`targetClassMatch` at the block's formers), otherwise the port hangs.  So
the answer is the table filtered to the class's constructors.
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

/-- A class's entries (the table filtered to its constructors), filtered to one of its constructors, are the table's
entries of that constructor: the generator reads them off the whole table. -/
theorem nfs_filter_ctor (tbl : List NestCtorNf) (ctors : List (IConstantVal × Nat)) (c : IConstantVal × Nat)
    (hc : c ∈ ctors) :
    (tbl.filter (fun e => ctors.any (·.1.name == e.ctor))).filter (·.ctor == c.1.name) =
      tbl.filter (·.ctor == c.1.name) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases he : e.ctor = c.1.name
  · have : ctors.any (·.1.name == e.ctor) = true := List.any_eq_true.mpr ⟨c, hc, by simp [he]⟩
    simp only [this, Bool.and_true]
  · have : (e.ctor == c.1.name) = false := by simpa using he
    simp [this]

def tmnT := ofString "tmn_t"
def tmnI := ofString "tmn_i"
def tmnK := ofString "tmn_k"
def tmnCs := ofString "tmn_cs"
def tmnNc := ofString "tmn_nc"
def tmnU := ofString "tmn_u"
def tmnLp := ofString "tmn_lp"
def tmnMs := ofString "tmn_ms"
def tmnP := ofString "tmn_p"
def tmnPn := ofString "tmn_pn"
def tmnA := ofString "tmn_a"
def tmnN := ofString "tmn_n"
def tmnR := ofString "tmn_r"
def tmnPe := ofString "tmn_pe"
def tmnCt := ofString "tmn_ct"
def tmnMb := ofString "tmn_mb"
def tmnLv := ofString "tmn_lv"
def tmnDb := ofString "tmn_db"
def tmnQ := ofString "tmn_q"
def fTmn := ofString "targetMajorNfs"

def tmnParams : List MlS := [tmnT, tmnI, tmnK, tmnCs, tmnNc, tmnU, tmnLp, tmnMs, tmnP, tmnPn, tmnA, tmnN]
def tmnLocals : List MlS := [tmnR, tmnPe, tmnCt, tmnMb, tmnLv, tmnDb, tmnQ]

def tmnBody : ProgHOL 64 := prologue tmnLocals
  (.ite (.cmp .lower (vv tmnI) (vv tmnK))
    (.seq (.call (some (some (.local, tmnR), none)) fTmn
        [vv tmnT, .op .add [vv tmnI, .const 1], vv tmnK, vv tmnCs, vv tmnNc, vv tmnU, vv tmnLp, vv tmnMs, vv tmnP,
          vv tmnPn, vv tmnA, vv tmnN])
    (.seq (.assign .local tmnPe (.load .one (.op .add [vv tmnT, .op .add [.panop .mul [vv tmnI, .const 8], .const 8]])))
    (.seq (.assign .local tmnCt (.load .one (vv tmnPe)))
    (.seq (.call (some (some (.local, tmnMb), none)) fCnm [vv tmnCs, .const 0, vv tmnNc, vv tmnCt])
    (.ite (.cmp .equal (vv tmnMb) (.const 0)) (.return (.const 0))
    (.seq (.assign .local tmnLv (.load .one (.op .add [vv tmnPe, .const 8])))
    (.seq (.assign .local tmnDb (.load .one (.op .add [vv tmnPe, .const 16])))
    (.seq (.call (some (some (.local, tmnQ), none)) fTcc
        [vv tmnU, vv tmnLv, vv tmnLp, vv tmnMs, vv tmnP, vv tmnPn, vv tmnA, vv tmnDb, vv tmnN])
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
/-- **`targetMajorNfs`** from entry `i` at the block's formers `fts`: the entries of the class's constructors kept
(another class's skipped; a kept one that does not match hangs). -/
theorem tmn_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : TMNCodes mode C) (p : BlockShape) (fts : List EIdx)
    (hfts : fts = p.formers.map (·.type)) (pfvs ds : List EIdx) (us : LsIdx) (ctors : List (IConstantVal × Nat))
    (tbl : List NestCtorNf)
    (olp om pp pa oq ot : Nat) (hlpl : p.lps.length < 2 ^ 59) (hml : p.members.length < 2 ^ 58)
    (hdl : ds.length < 2 ^ 58)
    (hpl : pfvs.length < 2 ^ 58) (hcsl : ctors.length < 2 ^ 58) (htl : tbl.length < 2 ^ 58)
    (hel : ∀ e ∈ tbl, e.ds.length < 2 ^ 61)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hlp : EBlk H0 olp (p.lps.map Enc.idxW))
    (hM : PtrsRep C H0 om (MemberRep C H0) p.members)
    (hpf : BlkAt H0 pp (pfvs.map Enc.idxW)) (hA : BlkAt H0 pa (ds.map Enc.idxW)) (hcr : CtorsRep C H0 oq ctors)
    (htb : PRep C H0 ot (fun H o nf => NfRep C H o nf) tbl) :
    ∀ f i (H : List (BitVec 64)) (s : AState), tbl.length - i = f → i ≤ tbl.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (tmnParams.zip [cellA C ot, BitVec.ofNat 64 i, BitVec.ofNat 64 tbl.length,
        cellA C oq, BitVec.ofNat 64 ctors.length, Enc.idxW us, cellA C olp, cellA C om, cellA C pp,
        BitVec.ofNat 64 pfvs.length, cellA C pa, BitVec.ofNat 64 ds.length])) tmnBody s
        (targetMajorNfs mode C.fe p fts pfvs us ds ctors (tbl.drop i))
        (fun r w s' st => r = (tbl.drop i).filter (fun e => ctors.any (·.1.name == e.ctor)) ∧
          Decl.PostU (ctxH C H) () w s' st) := by
  subst hfts
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
      [vv tmnT, .op .add [vv tmnI, .const 1], vv tmnK, vv tmnCs, vv tmnNc, vv tmnU, vv tmnLp, vv tmnMs, vv tmnP,
        vv tmnPn, vv tmnA, vv tmnN] tmnBody
      [cellA C ot, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 tbl.length, cellA C oq, BitVec.ofNat 64 ctors.length,
        Enc.idxW us, cellA C olp, cellA C om, cellA C pp, BitVec.ofNat 64 pfvs.length, cellA C pa,
        BitVec.ofNat 64 ds.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], trivial⟩
      (fun r w s' st => r = (tbl.drop (i + 1)).filter (fun e => ctors.any (·.1.name == e.ctor)) ∧
        Decl.PostU (ctxH C H) () w s' st) (fun r _ _ _ => r = (tbl.drop (i + 1)).filter (fun e => ctors.any (·.1.name == e.ctor)))
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
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hany, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨by (try simp only [List.drop_eq_getElem_cons hin]); exact (List.filter_cons_of_neg (by simp only [hany]; decide)).symm, H2, hp1'.trans hp2',
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hany, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [↓reduceIte]
    refine UD.specR_heapLoadI' (C := ctxH C H2) tmnLv _ (os[i] + 1) _ (get_prefix hlv h02) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C os[i]) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) tmnDb _ (os[i] + 2) _ (get_prefix hod h02) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C os[i] 2) ?_
    have hel' := hel tbl[i] (List.getElem_mem hin)
    refine specR_callNIH (C := ctxH C H2) tmnQ fTcc tccParams
      [vv tmnU, vv tmnLv, vv tmnLp, vv tmnMs, vv tmnP, vv tmnPn, vv tmnA, vv tmnDb, vv tmnN] (tccBody C)
      [Enc.idxW us, Enc.idxW tbl[i].lvls, cellA C olp, cellA C om, cellA C pp, BitVec.ofNat 64 pfvs.length,
        cellA C pa, cellA C od, BitVec.ofNat 64 ds.length] (by decide) rfl (by decide) hc.tcc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, tmnParams, ctxEnv], trivial⟩
      (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tccParams _ rfl hlk)
        (tcc_spec mode ra C hok hs hc.tcc p _ rfl pfvs ds tbl[i].ds us tbl[i].lvls olp om pp pa od hlpl hdl hel' hpl hml
          H2 (hp0.trans h02) (eblk_mono hlp h02) (ptrsRep_mono h02 (fun _ _ h => memberRep_mono h02 h) hM)
          (blkAt_mono hpf h02) (blkAt_mono hA h02) (blkAt_mono hdb h02) _))
      (fun b w s3 H3 hp3 hw => ?_)
    subst hw
    cases b
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨by (try simp only [List.drop_eq_getElem_cons hin]); exact (List.filter_cons_of_pos (by simp only [hany])).symm, H3, hp1'.trans (hp2'.trans hp3),
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end


/-! ## `classesNfs` over the class block -/

theorem map_drop_getElem_cons {α β : Type} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
    List.map f (List.drop i l) = f l[i] :: List.map f (List.drop (i + 1) l) := by
  rw [List.drop_eq_getElem_cons h, List.map_cons]

def cnsMs := ofString "cns_ms"
def cnsI := ofString "cns_i"
def cnsK := ofString "cns_k"
def cnsT := ofString "cns_t"
def cnsNt := ofString "cns_nt"
def cnsLp := ofString "cns_lp"
def cnsOm := ofString "cns_om"
def cnsP := ofString "cns_p"
def cnsPn := ofString "cns_pn"
def cnsQ := ofString "cns_q"
def cnsOc := ofString "cns_oc"
def cnsNc := ofString "cns_nc"
def cnsOa := ofString "cns_oa"
def cnsLv := ofString "cns_lv"
def cnsOd := ofString "cns_od"
def cnsNd := ofString "cns_nd"
def cnsX := ofString "cns_x"
def fCns := ofString "classesNfs"

def cnsParams : List MlS := [cnsMs, cnsI, cnsK, cnsT, cnsNt, cnsLp, cnsOm, cnsP, cnsPn]
def cnsLocals : List MlS := [cnsQ, cnsOc, cnsNc, cnsOa, cnsLv, cnsOd, cnsNd, cnsX]

/-- Class `i` of the class block (`TMBlk`): its entries checked (`tmn`, its constructors, levels and parameters),
then the rest.  The entries are not copied: a class's entries are the table filtered to its constructors, and the
generator reads them off the whole table (`nfs_filter_ctor`). -/
def cnsBody : ProgHOL 64 := prologue cnsLocals
  (.ite (.cmp .lower (vv cnsI) (vv cnsK))
    (.seq (.assign .local cnsQ (.load .one (.op .add [vv cnsMs, .op .add [.panop .mul [vv cnsI, .const 8], .const 8]])))
    (.seq (.assign .local cnsOc (.load .one (.op .add [vv cnsQ, .const 8])))
    (.seq (.assign .local cnsNc (.load .one (vv cnsOc)))
    (.seq (.assign .local cnsOa (.load .one (.op .add [vv cnsQ, .const 24])))
    (.seq (.assign .local cnsLv (.load .one (.op .add [vv cnsOa, .const 8])))
    (.seq (.assign .local cnsOd (.load .one (.op .add [vv cnsOa, .const 16])))
    (.seq (.assign .local cnsNd (.load .one (vv cnsOd)))
    (.seq (.call (some (some (.local, cnsX), none)) fTmn
        [vv cnsT, .const 0, vv cnsNt, vv cnsOc, vv cnsNc, vv cnsLv, vv cnsLp, vv cnsOm, vv cnsP, vv cnsPn, vv cnsOd,
          vv cnsNd])
    (.seq (.call (some (some (.local, cnsX), none)) fCns
        [vv cnsMs, .op .add [vv cnsI, .const 1], vv cnsK, vv cnsT, vv cnsNt, vv cnsLp, vv cnsOm, vv cnsP, vv cnsPn])
      (.return (.const 0)))))))))))
    (.return (.const 0)))

structure CNSCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  tmn : TMNCodes mode C
  self : C.code.lookup fCns = some (cnsParams.map (fun p => (p, ShapeHOL.one)), cnsBody, .one)

section
variable {σ : Type}

theorem cns_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnsLocals → (ctxEnv C ++ cnsParams.zip vals).get x = none :=
  Knot.params_none C cnsLocals cnsParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`classesNfs`** from class `i` of the class block: every class with the table filtered to its constructors (a
kept entry that does not match its class hangs). -/
theorem cns_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CNSCodes mode C) (p : BlockShape) (fts : List EIdx)
    (hfts : fts = p.formers.map (·.type)) (pfvs : List EIdx) (ms : List TargetMajor) (tbl : List NestCtorNf)
    (oms olp om pp ot : Nat) (hlpl : p.lps.length < 2 ^ 59) (hml : p.members.length < 2 ^ 58)
    (hpl : pfvs.length < 2 ^ 58) (htl : tbl.length < 2 ^ 58) (hel : ∀ e ∈ tbl, e.ds.length < 2 ^ 61)
    (hmsl : ms.length < 2 ^ 58) (hmsb : ∀ m ∈ ms, m.ctors.length < 2 ^ 58 ∧ m.ds.length < 2 ^ 58)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hT : TMBlk C H0 oms pfvs ms)
    (hlp : EBlk H0 olp (p.lps.map Enc.idxW)) (hM : PtrsRep C H0 om (MemberRep C H0) p.members)
    (hpf : BlkAt H0 pp (pfvs.map Enc.idxW)) (htb : PRep C H0 ot (fun H o nf => NfRep C H o nf) tbl) :
    ∀ f i (H : List (BitVec 64)) (s : AState), ms.length - i = f → i ≤ ms.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cnsParams.zip [cellA C oms, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length,
        cellA C ot, BitVec.ofNat 64 tbl.length, cellA C olp, cellA C om, cellA C pp, BitVec.ofNat 64 pfvs.length]))
        cnsBody s (classesNfs mode C.fe p fts tbl (ms.drop i))
        (fun r w s' st => r = (ms.drop i).map (fun m => { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }) ∧
          Decl.PostU (ctxH C H) () w s' st) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hT
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = ms.length := by omega
    subst hin
    refine specR_prologue (fun a w s' st L ⟨h1, H', hp', hsr⟩ => ⟨h1, H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩)
      (cns_none _ _) ?_
    have hlw := nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨by simp, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < ms.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (fun a w s' st L ⟨h1, H', hp', hsr⟩ => ⟨h1, H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩)
      (cns_none _ _) ?_
    have hlw := nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hrep, hpfe, -⟩ := hpsr i hin
    have hq := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hq
    have hpi : ps[i]'(by omega) = op := by
      rw [List.getElem?_eq_getElem (by omega)] at hop; exact Option.some.inj hop
    rw [hpi] at hq
    obtain ⟨oa, ha3, -, hlv, ⟨od, hod, hdb⟩, -, -, ⟨oc, hoc, hcr⟩, -, -⟩ := hrep
    have hmb := hmsb ms[i] (List.getElem_mem hin)
    refine UD.specR_heapLoadI' (C := ctxH C H) cnsQ _ (oms + 1 + i) _ (get_prefix hq hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv]; exact cellA_mulIdx C oms i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnsOc _ (op + 1) _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnsNc (vv cnsOc) oc _ (get_prefix hcr.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnsOa _ (op + 3) _ (get_prefix ha3 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnsLv _ (oa + 1) _ (get_prefix hlv hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oa) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnsOd _ (oa + 2) _ (get_prefix hod hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oa 2) ?_
    have hdl := hdb.1
    simp only [List.length_map] at hdl
    refine UD.specR_heapLoadI' (C := ctxH C H) cnsNd (vv cnsOd) od _ (get_prefix hdl hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin]
    simp only [classesNfs, hpfe]
    refine specR_callNIH (C := ctxH C H) cnsX fTmn tmnParams
      [vv cnsT, .const 0, vv cnsNt, vv cnsOc, vv cnsNc, vv cnsLv, vv cnsLp, vv cnsOm, vv cnsP, vv cnsPn, vv cnsOd,
        vv cnsNd] tmnBody
      [cellA C ot, BitVec.ofNat 64 0, BitVec.ofNat 64 tbl.length, cellA C oc, BitVec.ofNat 64 ms[i].ctors.length,
        Enc.idxW ms[i].lvls, cellA C olp, cellA C om, cellA C pp, BitVec.ofNat 64 pfvs.length, cellA C od,
        BitVec.ofNat 64 ms[i].ds.length] (by decide) rfl (by decide) hc.tmn.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
      (fun r w s' st => r = (tbl.drop 0).filter (fun e => ms[i].ctors.any (·.1.name == e.ctor)) ∧
        Decl.PostU (ctxH C H) () w s' st)
      (fun r _ _ _ => r = tbl.filter (fun e => ms[i].ctors.any (·.1.name == e.ctor)))
      (fun r w s' st ⟨hr, H', hp', hsr⟩ => ⟨H', hp', by simpa using hr, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tmnParams _ rfl hlk)
        (tmn_spec mode ra C hok hs hc.tmn p fts hfts pfvs ms[i].ds ms[i].lvls ms[i].ctors tbl olp om pp od oc ot
          hlpl hml hmb.2 hpl hmb.1 htl hel H0 hp0 hlp hM hpf hdb hcr htb tbl.length 0 H s (by omega) (by omega) hp))
      (fun es w s1 H1 hp1 hes => ?_)
    subst hes
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) cnsX fCns cnsParams
      [vv cnsMs, .op .add [vv cnsI, .const 1], vv cnsK, vv cnsT, vv cnsNt, vv cnsLp, vv cnsOm, vv cnsP, vv cnsPn]
      cnsBody [cellA C oms, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length, cellA C ot, BitVec.ofNat 64 tbl.length,
        cellA C olp, cellA C om, cellA C pp, BitVec.ofNat 64 pfvs.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnsParams, ctxEnv], trivial⟩
      (fun r w s' st => r = (ms.drop (i + 1)).map (fun m => { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }) ∧
        Decl.PostU (ctxH C H1) () w s' st)
      (fun r _ _ _ => r = (ms.drop (i + 1)).map (fun m => { m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }))
      (fun r w s' st ⟨hr, H', hp', hsr⟩ => ⟨H', hp', hr, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cnsParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun rest w s2 H2 hp2 hr => ?_)
    subst hr
    exact specR_returnI _ 0 rfl (fun t ht => ⟨by simp only [List.map_cons, hpfe], H2, hp1'.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
