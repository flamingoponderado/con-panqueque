import ConPanqueque.T.Ind.OpenFvars
import ConPanqueque.T.Ind.IotaCtor
import ConPanqueque.T.Ind.CtorMember
import ConPanqueque.T.Ind.IotaPartsAt
import ConRon.Arena.Inductives.StructParts
import ConPanqueque.T.LvlLeqTop
import ConPanqueque.T.Decl.StepDefn

/-!
# A constructor's check (`checkSumCtor`)

`peBody`: a block's first `n` handles against another block of `n` handles (`as.take n == bs`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl ConPanqueque.T.WC

def peA := ofString "pe_a"
def peB := ofString "pe_b"
def peI := ofString "pe_i"
def peN := ofString "pe_n"
def peX := ofString "pe_x"
def peY := ofString "pe_y"
def peR := ofString "pe_r"
def fPrefEq := ofString "prefixEq"

def peParams : List MlS := [peA, peB, peI, peN]
def peLocals : List MlS := [peX, peY, peR]

def peBody : ProgHOL 64 := prologue peLocals
  (.ite (.cmp .lower (vv peI) (vv peN))
    (.seq (.assign .local peX (.load .one (.op .add [vv peA, .op .add [.panop .mul [vv peI, .const 8], .const 8]])))
    (.seq (.assign .local peY (.load .one (.op .add [vv peB, .op .add [.panop .mul [vv peI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv peX) (vv peY))
      (.seq (.call (some (some (.local, peR), none)) fPrefEq [vv peA, vv peB, .op .add [vv peI, .const 1], vv peN])
        (.return (vv peR)))
      (.return (.const 0)))))
    (.return (.const 1)))

section
variable {σ : Type}

theorem pe_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ peLocals → (ctxEnv C ++ peParams.zip vals).get x = none :=
  Knot.params_none C peLocals peParams vals (by decide) (by decide)

theorem take_drop_beq (as bs : List EIdx) (n i : Nat) (hi : i < n) (hn : n ≤ as.length) (hb : bs.length = n) :
    ((as.take n).drop i == bs.drop i) =
      ((as[i]'(by omega) == bs[i]'(by omega)) && ((as.take n).drop (i + 1) == bs.drop (i + 1))) := by
  have h1 : (as.take n).drop i = as[i]'(by omega) :: (as.take n).drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (show i < (as.take n).length by simp; omega)]; simp [List.getElem_take]
  have h2 : bs.drop i = bs[i]'(by omega) :: bs.drop (i + 1) := List.drop_eq_getElem_cons _
  rw [h1, h2, List.cons_beq_cons]

/-- **`prefixEq`** from position `i`. -/
theorem pe_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fPrefEq = some (peParams.map (fun p => (p, ShapeHOL.one)), peBody, .one))
    (as bs : List EIdx) (pa pb n : Nat) (hn : n ≤ as.length) (hb : bs.length = n) (H : List (BitVec 64))
    (hA : BlkAt H pa (as.map Enc.idxW)) (hB : BlkAt H pb (bs.map Enc.idxW)) :
    ∀ k i (s : AState), n - i = k → i ≤ n →
      SpecR (Pre (σ := σ) (ctxH C H) s (peParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i, BitVec.ofNat 64 n]))
        peBody s (pure ((as.take n).drop i == bs.drop i)) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i s hk hi
    refine specR_prologue (postB_locals _) (pe_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, peParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    have e1 : (as.take n).drop i = [] := List.drop_of_length_le (by simp; omega)
    have e2 : bs.drop i = [] := List.drop_of_length_le (by omega)
    rw [e1, e2]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i s hk hi
    have hin : i < n := by omega
    refine specR_prologue (postB_locals _) (pe_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i n (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, peParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have ha := hA.2 i (by simp; omega)
    have hbb := hB.2 i (by simp; omega)
    simp only [List.getElem_map] at ha hbb
    refine UD.specR_heapLoadI' (C := ctxH C H) peX _ (pa + 1 + i) _ ha (by decide)
      (by simp +decide [sev, Env.get, peParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) peY _ (pb + 1 + i) _ hbb (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, peParams, ctxEnv]; exact cellA_mulIdx C pb i (by omega)) ?_
    rw [take_drop_beq as bs n i hin hn hb]
    by_cases he : as[i]'(by omega) = bs[i]'(by omega)
    · rw [he]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, Bool.true_and]
      refine specR_congr (m' := (pure ((as.take n).drop (i + 1) == bs.drop (i + 1)) : AM Bool) >>= fun b => pure b)
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H) peR fPrefEq peParams [vv peA, vv peB, .op .add [vv peI, .const 1], vv peN]
        peBody [cellA C pa, cellA C pb, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 n] (by decide) rfl (by decide) hcode
        ⟨by simp +decide [sev, Env.get_cons, Env.get, peParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, peParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, peParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, peParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu peParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun b w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hw : Enc.idxW (as[i]'(by omega)) ≠ Enc.idxW (bs[i]'(by omega)) := fun h => he (ConPanqueque.V.Enc.idxW_inj h)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
        (fun h => absurd rfl h) (fun _ => ?_)
      have hf : (as[i]'(by omega) == bs[i]'(by omega)) = false := by simpa using he
      rw [hf, Bool.false_and]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `structCtorResidOk` -/

theorem structPsAt_go_eq (o nP : Nat) : ∀ m k, m = nP - k →
    structPsAt.go o nP m k = iotaBVars (o + nP) nP k := by
  intro m
  induction m with
  | zero => intro k hk; rw [structPsAt.go, iotaBVars, if_neg (by omega)]
  | succ m ih =>
    intro k hk
    rw [structPsAt.go, iotaBVars, if_pos (by omega), ih (k + 1) (by omega)]
    rfl

theorem structPsAt_eq (o nP : Nat) : structPsAt o nP = iotaBVars (o + nP) nP 0 :=
  structPsAt_go_eq o nP nP 0 (by omega)

def qzT := ofString "qz_t"
def qzL := ofString "qz_l"
def qzP := ofString "qz_p"
def qzO := ofString "qz_o"
def qzN := ofString "qz_n"
def qzB := ofString "qz_b"
def qzU := ofString "qz_u"
def qzH := ofString "qz_h"
def qzF := ofString "qz_f"
def qzA := ofString "qz_a"
def qzS := ofString "qz_s"
def qzK := ofString "qz_k"
def qzM := ofString "qz_m"
def qzR := ofString "qz_r"
def fResidOk := ofString "structCtorResidOk"

def qzParams : List MlS := [qzT, qzL, qzP, qzO, qzN, qzB]
def qzLocals : List MlS := [qzU, qzH, qzF, qzA, qzS, qzK, qzM, qzR]

def qzBody : ProgHOL 64 := prologue qzLocals
  (.seq (.call (some (some (.local, qzU), none)) fParamLevels [vv qzL])
  (.seq (.call (some (some (.local, qzH), none)) fInternConst [vv qzT, vv qzU])
  (.seq (.call (some (some (.local, qzF), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv qzB])
  (.seq (.call (some (some (.local, qzA), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv qzB])
  (.seq (.call (some (some (.local, qzS), none)) fIotaBVars [.op .add [vv qzO, vv qzP], vv qzP, .const 0])
  (.ite (.cmp .equal (vv qzF) (vv qzH))
    (.seq (.assign .local qzK (.load .one (vv qzA)))
    (.ite (.cmp .equal (vv qzK) (.op .add [vv qzP, vv qzN]))
      (.seq (.assign .local qzM (.load .one (vv qzS)))
      (.ite (.cmp .lower (vv qzK) (vv qzM))
        (.return (.const 0))
        (.seq (.call (some (some (.local, qzR), none)) fPrefEq [vv qzA, vv qzS, .const 0, vv qzM])
          (.return (vv qzR)))))
      (.return (.const 0))))
    (.return (.const 0))))))))

/-- The code `structCtorResidOk` runs. -/
structure QZCodes (C : Ctx) : Prop where
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  ilp1 : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ils : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  gf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  ib : C.code.lookup fIotaBVars = some (ibParams.map (fun p => (p, ShapeHOL.one)), ibBody C, .one)
  bv : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  pe : C.code.lookup fPrefEq = some (peParams.map (fun p => (p, ShapeHOL.one)), peBody, .one)

section
variable {σ : Type}

theorem qz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qzLocals → (ctxEnv C ++ qzParams.zip vals).get x = none :=
  Knot.params_none C qzLocals qzParams vals (by decide) (by decide)

set_option maxHeartbeats 4000000 in
/-- **`structCtorResidOk`**. -/
theorem qz_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : QZCodes C)
    (T : NIdx) (lps : List NIdx) (nP o nIdx : Nat) (cbody : EIdx) (ol : Nat)
    (hlp : lps.length < 2 ^ 59) (hr : o + nP < 2 ^ 62) (hni : nIdx < 2 ^ 62)
    (H : List (BitVec 64)) (hb : EBlk H ol (lps.map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (qzParams.zip [Enc.idxW T, cellA C ol, BitVec.ofNat 64 nP, BitVec.ofNat 64 o,
      BitVec.ofNat 64 nIdx, Enc.idxW cbody])) qzBody s (structCtorResidOk T lps nP o nIdx cbody) (PostB (ctxH C H)) := by
  unfold structCtorResidOk
  rw [structPsAt_eq]
  refine specR_prologue (postB_locals _) (qz_none _ _) ?_
  refine specR_callNIH (C := ctxH C H) qzU fParamLevels plParams [vv qzL] (plBody C) [cellA C ol] (by decide) rfl
    (by decide) hc.pl ⟨by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv], trivial⟩
    (PostLsH (ctxH C H)) (fun h w _ _ => w = Enc.idxW h) (fun h w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
      (pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.ils lps ol hlp H s hb))
    (fun us wu s1 H1 hp1 hwu => ?_)
  subst hwu
  have hok1 := ctxOK_H hok H1
  refine ILP.callE_spec (C := ctxH C H1) qzH fInternConst [lEn, lEus] [vv qzT, vv qzU] constBody
    [Enc.idxW T, Enc.idxW us] (by decide) rfl (by decide) hc.ic
    ⟨by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv], by simp [sev, Env.get_cons], trivial⟩
    (by exact const_body_spec ra (ctxH C H1) hok1 s1 _ _) (fun hd s2 => ?_)
  refine specR_callNIM qzF fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv qzB]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cbody] (by decide) rfl (by decide) hc.gf
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel cbody s2 = .ok (a, s') ∧ Post (ctxH C H1) s2 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H1) hc.gf coreWalkFuel cbody s2 CV.coreWalkFuel_lt t
        ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun fn w s' st ⟨_, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hs.symm
  subst hs'
  refine specR_callNIH (C := ctxH C H1) qzA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv qzB]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cbody] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv], trivial⟩
    (PostA (ctxH C H1)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
    (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H1) hok1 hc.gaa coreWalkFuel CV.coreWalkFuel_lt H1 cbody s2))
    (fun args w s3 H2 hp2 ⟨oa, hw, hba⟩ => ?_)
  subst hw
  refine specR_callNIH (C := ctxH C H2) qzS fIotaBVars ibParams [.op .add [vv qzO, vv qzP], vv qzP, .const 0] (ibBody C)
    [BitVec.ofNat 64 (o + nP), BitVec.ofNat 64 nP, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ib
    ⟨by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat, Nat.add_comm],
      by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv], rfl, trivial⟩
    (PostA (ctxH C H2)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
    (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibParams _ rfl hlk)
      (ib_spec ra (ctxH C H2) (ctxOK_H hok H2) hc.ib hc.bv (o + nP) nP (by omega) hr _ 0 H2 s3 rfl (by omega)))
    (fun ys wy s4 H3 hp3 ⟨oy, hwy, hby⟩ => ?_)
  subst hwy
  have hp13 : H <+: H3 := (hp1.trans hp2).trans hp3
  have hba3 : BlkAt H3 oa (args.map Enc.idxW) := blkAt_mono hba hp3
  have hok3 := ctxOK_H hok H3
  by_cases hfh : fn = hd
  swap
  · have hne : Enc.idxW fn ≠ Enc.idxW hd := fun e => hfh (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    have : (fn == hd) = false := by simpa using hfh
    rw [this, Bool.false_and, Bool.false_and]; exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  subst hfh
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [beq_self_eq_true, Bool.true_and]
  refine UD.specR_heapLoadI' (C := ctxH C H3) qzK (vv qzA) oa _ hba3.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t3 ht3 => ?_
  have hal := Big.blk_small0 hok3 ht3.sr hba3
  have hyl := Big.blk_small0 hok3 ht3.sr hby
  simp only [List.length_map] at hal hyl
  by_cases hK : args.length = nP + nIdx
  swap
  · have hne : BitVec.ofNat 64 args.length ≠ BitVec.ofNat 64 nP + BitVec.ofNat 64 nIdx := by
      rw [BitVec.ofNat_add_ofNat]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
    have : (args.length == nP + nIdx) = false := by simpa using hK
    rw [this, Bool.false_and]; exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, qzParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hK, BitVec.ofNat_add_ofNat]) (fun _ => ?_) (fun h => absurd h (by decide))
  rw [show (args.length == nP + nIdx) = true by simpa using hK, Bool.true_and]
  refine UD.specR_heapLoadI' (C := ctxH C H3) qzM (vv qzS) oy _ hby.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hlw := ConPanqueque.T.Decl.nd_lt_iff args.length ys.length (by omega) (by omega)
  by_cases hlt : args.length < ys.length
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hlt])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have : (args.take ys.length == ys) = false := by
      rw [List.take_of_length_le (by omega)]
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; rw [e] at hlt; omega
    rw [this]; exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_congr (m' := (pure ((args.take ys.length).drop 0 == ys.drop 0)) >>= fun b => pure b) (by simp) ?_
  refine specR_callNIH (C := ctxH C H3) qzR fPrefEq peParams [vv qzA, vv qzS, .const 0, vv qzM]
    peBody [cellA C oa, cellA C oy, BitVec.ofNat 64 0, BitVec.ofNat 64 ys.length] (by decide) rfl (by decide) hc.pe
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl,
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu peParams _ rfl hlk)
      (pe_spec (ctxH C H3) hok3 hc.pe args ys oa oy ys.length (by omega) rfl H3 hba3 hby _ 0 s4 rfl (by omega)))
    (fun b w s5 H4 hp4 hw => ?_)
  subst hw
  exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H4, hp13.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `fvarTypeDs`, into a block -/

theorem fvarTypeDs_cons (x : EIdx) (xs : List EIdx) : fvarTypeDs (x :: xs) =
    (do let t ← fvarTypeD x; let ts ← fvarTypeDs xs; pure (t :: ts)) := rfl

theorem fvarTypeDs_nil : fvarTypeDs [] = pure [] := rfl

def ftdL := ofString "ftd_l"
def ftdW := ofString "ftd_w"
def ftdI := ofString "ftd_i"
def ftdN := ofString "ftd_n"
def ftdX := ofString "ftd_x"
def ftdH := ofString "ftd_h"
def fFvt := ofString "fvarTypeD"
def fFtdFill := ofString "fvarTypeDsFill"

def ftfParams : List MlS := [ftdL, ftdW, ftdI, ftdN]
def ftfLocals : List MlS := [ftdX, ftdH]

def ftfBody : ProgHOL 64 := prologue ftfLocals
  (.ite (.cmp .lower (vv ftdI) (vv ftdN))
    (.seq (.assign .local ftdX (.load .one (.op .add [vv ftdL, .op .add [.panop .mul [vv ftdI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, ftdH), none)) fFvt [vv ftdX])
    (.seq (.store (.op .add [vv ftdW, .panop .mul [vv ftdI, .const 8]]) (vv ftdH))
    (.seq (.call (some (some (.local, ftdX), none)) fFtdFill [vv ftdL, vv ftdW, .op .add [vv ftdI, .const 1], vv ftdN])
      (.return (.const 0))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem ftf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ftfLocals → (ctxEnv C ++ ftfParams.zip vals).get x = none :=
  Knot.params_none C ftfLocals ftfParams vals (by decide) (by decide)

/-- The fill's post (as `PostPF`, at expression handles). -/
def PostFTF (C : Ctx) (H0 : List (BitVec 64)) (len ow i n : Nat) (us : List EIdx) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', H0 <+: H' ∧ H'.length = len ∧ SR (ctxH C H') s' st ∧ us.length = n - i ∧
    ∀ j (hj : j < us.length), H'[ow + i + j]? = some (Enc.idxW us[j])

theorem postFTF_locals (C : Ctx) (H0 : List (BitVec 64)) (len ow i n : Nat) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostFTF C H0 len ow i n a w s' st →
      PostFTF C H0 len ow i n a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hl, hs, h1, h2⟩ => ⟨H', hp, hl, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

/-- **`fvarTypeDs`**' fill from position `i`. -/
theorem ftf_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one))
    (hcF : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one))
    (xs : List EIdx) (ol ow : Nat) (hn : xs.length < 2 ^ 59) :
    ∀ f i (H0 H : List (BitVec 64)) (s : AState), BlkAt H0 ol (xs.map Enc.idxW) → H0 <+: H → H0.length ≤ ow + i →
      ow + xs.length ≤ H.length → xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ftfParams.zip [cellA C ol, cellA C ow, BitVec.ofNat 64 i,
        BitVec.ofNat 64 xs.length])) ftfBody s (fvarTypeDs (xs.drop i))
        (PostFTF C H0 H.length ow i xs.length) := by
  intro f
  induction f with
  | zero =>
    intro i H0 H s hb h0 hl0 hroom hf hi
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postFTF_locals _ _ _ _ _ _) (ftf_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ftfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, fvarTypeDs_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, h0, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, by simp,
      fun j hj => absurd hj (by simp)⟩)
  | succ f ih =>
    intro i H0 H s hb h0 hl0 hroom hf hi
    have hin : i < xs.length := by omega
    refine specR_prologue (postFTF_locals _ _ _ _ _ _) (ftf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ftfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, fvarTypeDs_cons]
    let Γ0 : Env := ctxEnv (ctxH C H) ++ ftfParams.zip [cellA C ol, cellA C ow, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length]
    have vL : Γ0.get ftdL = some (cellA C ol) := by simp +decide [Γ0, Env.get, ftfParams, ctxEnv]
    have vW : Γ0.get ftdW = some (cellA C ow) := by simp +decide [Γ0, Env.get, ftfParams, ctxEnv]
    have vI : Γ0.get ftdI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, ftfParams, ctxEnv]
    have vN : Γ0.get ftdN = some (BitVec.ofNat 64 xs.length) := by simp +decide [Γ0, Env.get, ftfParams, ctxEnv]
    have hx : (ctxH C H).H[ol + 1 + i]? = some (Enc.idxW xs[i]) := by
      show H[ol + 1 + i]? = _
      have := hb.2 i (by simp; omega); simp only [List.getElem_map] at this; exact get_prefix this h0
    refine UD.specR_heapLoadI' (C := ctxH C H) ftdX _ (ol + 1 + i) _ hx (by simp +decide [ctxLocals, ftfLocals])
      (by
        have e : sev Γ0 (.op .add [vv ftdL, .op .add [.panop .mul [vv ftdI, .const 8], .const 8]]) =
            some (cellA C (ol + 1 + i)) := by
          simp only [sev, sev_vv, vL, vI]; simp; exact cellA_mulIdx C ol i (by omega)
        exact e) ?_
    let Γ1 : Env := (ftdX, Enc.idxW xs[i]) :: Γ0
    have g1 : ∀ y v, y ≠ ftdX → Γ0.get y = some v → sev Γ1 (vv y) = some v := fun y v hy h => by
      simp only [sev, sev_vv, Γ1, Env.get_cons, hy, ite_false, h]
    refine ILP.callE_spec (C := ctxH C H) ftdH fFvt [pH] [vv ftdX] ExM.fvtBody [Enc.idxW xs[i]] (by decide) rfl
      (by simp +decide [ctxLocals, ftfLocals]) hcF ⟨by simp [Γ1, sev, Env.get_cons], trivial⟩
      (ExM.fvt_spec (ctxH C H) s xs[i]) (fun h s1 => ?_)
    let Γ2 : Env := (ftdH, Enc.idxW h) :: Γ1
    have g2 : ∀ y v, y ≠ ftdX → y ≠ ftdH → Γ0.get y = some v → sev Γ2 (vv y) = some v := fun y v hy hy' h => by
      have := g1 y v hy h
      simp only [sev, sev_vv, Γ2, Env.get_cons, hy', ite_false] at this ⊢; exact this
    have gW := g2 ftdW _ (by decide) (by decide) vW
    have gI := g2 ftdI _ (by decide) (by decide) vI
    refine specR_heapStoreI (ctxOK_H hok H) (.op .add [vv ftdW, .panop .mul [vv ftdI, .const 8]]) (vv ftdH) (ow + i)
      (by show _ < H.length; omega) (Enc.idxW h)
      (by
        have e : sev Γ2 (.op .add [vv ftdW, .panop .mul [vv ftdI, .const 8]]) = some (cellA C (ow + i)) := by
          simp only [sev] at gW gI ⊢; rw [gW, gI]; simp; exact cellA_mulOff C ow i (by omega)
        exact e)
      (by simp [Γ2, sev, Env.get_cons]) ?_
    let H2 := H.set (ow + i) (Enc.idxW h)
    have hl2 : H2.length = H.length := by simp [H2]
    have h02 : H0 <+: H2 := prefix_set h0 hl0 _
    let H0' := H2.take (ow + i + 1)
    have h00' : H0 <+: H0' := prefix_take_of h02 (by omega)
    have h0'2 : H0' <+: H2 := List.take_prefix _ _
    have hH0'l : H0'.length = ow + i + 1 := by simp only [H0', List.length_take, hl2]; omega
    have hcell : H0'[ow + i]? = some (Enc.idxW h) := by
      simp only [H0', H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by omega)
    have gL := g2 ftdL _ (by decide) (by decide) vL
    have gN := g2 ftdN _ (by decide) (by decide) vN
    refine specR_congr (m' := fvarTypeDs (xs.drop (i + 1)) >>= fun rest => pure (h :: rest)) rfl ?_
    refine specR_callNIG (C := ctxH (ctxH C H) H2) ftdX fFtdFill ftfParams
      [vv ftdL, vv ftdW, .op .add [vv ftdI, .const 1], vv ftdN] ftfBody
      [cellA C ol, cellA C ow, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl
      (by simp +decide [ctxLocals, ftfLocals]) hc
      ⟨gL, gW, by
        have e : sev Γ2 (.op .add [vv ftdI, .const 1]) = some (BitVec.ofNat 64 (i + 1)) := by
          simp only [sev] at gI ⊢; rw [gI]; simp; exact word_add1_eq i
        exact e, gN, trivial⟩
      (PostFTF C H0' H2.length ow (i + 1) xs.length) (fun us _ _ H' => H0' <+: H' ∧ H'.length = H2.length ∧
        us.length = xs.length - (i + 1) ∧ ∀ j (hj : j < us.length), H'[ow + (i + 1) + j]? = some (Enc.idxW us[j]))
      (fun us w s' st ⟨H', hp', hl', hs', h1, h2⟩ => ⟨H', ⟨hp', hl', h1, h2⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftfParams _ rfl hlk)
        (ih (i + 1) H0' H2 s1 (blkAt_mono hb h00') h0'2 (by omega) (by omega) (by omega) (by omega)))
      (fun us w s3 H4 ⟨h0'4, hl4, hus, hcells⟩ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, h00'.trans h0'4, by rw [hl4, hl2], sr_of_eq ht.sr rfl rfl rfl rfl,
      by simp; omega, fun j hj => by
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        exact get_prefix hcell h0'4
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [show ow + i + (j + 1) = ow + (i + 1) + j by omega]
        exact hcells j (by simpa using hj)⟩)

end

def ftdQ := ofString "ftd_q"
def ftdK := ofString "ftd_k"
def ftdY := ofString "ftd_y"
def ftdR := ofString "ftd_r"
def fFvtDs := ofString "fvarTypeDs"

def ftdParams : List MlS := [ftdQ]
def ftdLocals : List MlS := [ftdK, ftdY, ftdR]

def ftdBody (C : Ctx) : ProgHOL 64 := prologue ftdLocals
  (.seq (.assign .local ftdK (.load .one (vv ftdQ)))
  (allocP C ftdY (.op .add [.panop .mul [vv ftdK, .const 8], .const 8])
  (.seq (.store (vv ftdY) (vv ftdK))
  (.seq (.call (some (some (.local, ftdR), none)) fFtdFill [vv ftdQ, .op .add [vv ftdY, .const 8], .const 0, vv ftdK])
    (.return (vv ftdY))))))

section
variable {σ : Type}

theorem ftd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ftdLocals → (ctxEnv C ++ ftdParams.zip vals).get x = none :=
  Knot.params_none C ftdLocals ftdParams vals (by decide) (by decide)

/-- **`fvarTypeDs`**: the types of a block's free variables, as a fresh block. -/
theorem ftd_spec (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fFvtDs = some (ftdParams.map (fun p => (p, ShapeHOL.one)), ftdBody C, .one))
    (hc : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one))
    (hcF : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one))
    (xs : List EIdx) (ol : Nat) (hn : xs.length < 2 ^ 59) (H : List (BitVec 64)) (s : AState)
    (hb : BlkAt H ol (xs.map Enc.idxW)) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ftdParams.zip [cellA C ol])) (ftdBody C) s (fvarTypeDs xs)
      (PostA (ctxH C H)) := by
  refine specR_prologue (postA_locals _) (ftd_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  let Γ0 : Env := ctxEnv (ctxH C H) ++ ftdParams.zip [cellA C ol]
  have vQ : Γ0.get ftdQ = some (cellA C ol) := by simp +decide [Γ0, Env.get, ftdParams, ctxEnv]
  have hk0 : (ctxH C H).H[ol]? = some (BitVec.ofNat 64 xs.length) := by
    have := hb.1; simp only [List.length_map] at this; exact this
  refine UD.specR_heapLoadI' (C := ctxH C H) ftdK (vv ftdQ) ol _ hk0 (by simp +decide [ctxLocals, ftdLocals])
    (by simp only [sev, sev_vv, vQ]; rfl) ?_
  let Γ1 : Env := (ftdK, BitVec.ofNat 64 xs.length) :: Γ0
  refine specR_allocI (C := ctxH C H) ftdY _ (xs.length + 1) (by omega) (by simp +decide [ctxLocals, ftdLocals])
    (fun v => by
      have h1 : sev ((ftdY, v) :: Γ1) (vv ftdK) = some (BitVec.ofNat 64 xs.length) := by
        simp +decide [sev, Env.get_cons, Γ1]
      simp only [sev] at h1 ⊢; rw [h1]; simp; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H1 ws hp1 hws hroom1 => ?_)
  have hp1' : H <+: H1 := hp1
  have hroom1' : H1.length + (xs.length + 1) ≤ C.HN := hroom1
  let Γ2 : Env := (ftdY, cellA (ctxH C H) H1.length) :: Γ1
  have gQ : sev Γ2 (vv ftdQ) = some (cellA C ol) := by
    simp only [sev, sev_vv, Γ2, Γ1, Env.get_cons, show ftdQ ≠ ftdY by decide, show ftdQ ≠ ftdK by decide, ite_false, vQ]
  have gK : sev Γ2 (vv ftdK) = some (BitVec.ofNat 64 xs.length) := by
    simp only [sev, sev_vv, Γ2, Γ1, Env.get_cons, show ftdK ≠ ftdY by decide, ite_false, ite_true]
  have gY : sev Γ2 (vv ftdY) = some (cellA C H1.length) := by simp [sev, Γ2, Env.get_cons]; rfl
  have hl1 : (H1 ++ ws).length = H1.length + (xs.length + 1) := by simp [hws]
  refine specR_heapStoreI (ctxOK_H hok (H1 ++ ws)) (vv ftdY) (vv ftdK) H1.length
    (by show _ < (H1 ++ ws).length; omega) (BitVec.ofNat 64 xs.length) gY gK ?_
  let H2 := (H1 ++ ws).set H1.length (BitVec.ofNat 64 xs.length)
  have hl2 : H2.length = H1.length + (xs.length + 1) := by simp [H2, hws]
  have h12 : H1 <+: H2 := prefix_set (List.prefix_append _ _) (by simp) _
  let H0 := H2.take (H1.length + 1)
  have h00 : H1 <+: H0 := prefix_take_of h12 (by omega)
  have h02 : H0 <+: H2 := List.take_prefix _ _
  have hH0l : H0.length = H1.length + 1 := by simp only [H0, List.length_take, hl2]; omega
  have hhdr : H0[H1.length]? = some (BitVec.ofNat 64 xs.length) := by
    simp only [H0, H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by simp [hws])
  have gY1 : sev Γ2 (.op .add [vv ftdY, .const 8]) = some (cellA C (H1.length + 1)) := by
    simp only [sev] at gY ⊢; rw [gY]; simp; exact cellA_add8 C H1.length
  refine specR_congr (m' := fvarTypeDs xs >>= fun us => pure us) (by simp) ?_
  refine specR_callNIG (C := ctxH (ctxH C (H1 ++ ws)) H2) ftdR fFtdFill ftfParams
    [vv ftdQ, .op .add [vv ftdY, .const 8], .const 0, vv ftdK] ftfBody
    [cellA C ol, cellA C (H1.length + 1), BitVec.ofNat 64 0, BitVec.ofNat 64 xs.length] (by decide) rfl
    (by simp +decide [ctxLocals, ftdLocals]) hc ⟨gQ, gY1, rfl, gK, trivial⟩
    (PostFTF C H0 H2.length (H1.length + 1) 0 xs.length) (fun us _ _ H' => H0 <+: H' ∧
      us.length = xs.length - 0 ∧ ∀ j (hj : j < us.length), H'[H1.length + 1 + 0 + j]? = some (Enc.idxW us[j]))
    (fun us w s' st ⟨H', hp', _, hs', h1, h2⟩ => ⟨H', ⟨hp', h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftfParams _ rfl hlk) (by
      have := ftf_spec (σ := σ) C hok hc hcF xs ol (H1.length + 1) hn xs.length 0 H0 H2 s
        (blkAt_mono hb (hp1'.trans h00)) h02 (by omega) (by omega) (by omega) (by omega)
      rw [List.drop_zero] at this
      exact this))
    (fun us w s1 H3 ⟨h03, hus, hcells⟩ => ?_)
  simp only [Nat.sub_zero, Nat.add_zero] at hus hcells
  have gY' : sev ((ftdR, w) :: Γ2) (vv ftdY) = some (cellA C H1.length) := by
    simp only [sev, sev_vv, Env.get_cons, show ftdY ≠ ftdR by decide, ite_false] at gY ⊢; exact gY
  exact specR_returnI (vv ftdY) _ gY' (fun t ht => ⟨H3, H1.length, hp1'.trans (h00.trans h03), rfl,
    ⟨by rw [List.length_map, hus]; exact get_prefix hhdr h03,
     fun j hj => by simp only [List.length_map] at hj; simp only [List.getElem_map]; exact hcells j hj⟩,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `checkStructDomsAt` -/

def sdA := ofString "sd_a"
def sdDm := ofString "sd_d"
def sdO := ofString "sd_o"
def sdJ := ofString "sd_j"
def sdJ1 := ofString "sd_j1"
def sdLa := ofString "sd_la"
def sdLd := ofString "sd_ld"
def sdX := ofString "sd_x"
def sdY := ofString "sd_y"
def sdT := ofString "sd_t"
def sdR := ofString "sd_r"
def fSdoms := ofString "checkStructDomsAt"

def sdParams : List MlS := [sdA, sdDm, sdO, sdJ]
def sdLocals : List MlS := [sdJ1, sdLa, sdLd, sdX, sdY, sdT, sdR]

def sdBody : ProgHOL 64 := prologue sdLocals
  (.ite (.cmp .equal (vv sdJ) (.const 0)) (.return (.const 0))
  (.seq (.assign .local sdJ1 (.op .sub [vv sdJ, .const 1]))
  (.seq (.assign .local sdLa (.load .one (vv sdA)))
  (.ite (.cmp .lower (vv sdJ1) (vv sdLa))
    (.seq (.assign .local sdLd (.load .one (vv sdDm)))
    (.ite (.cmp .lower (vv sdJ1) (vv sdLd))
      (.seq (.assign .local sdX (.load .one (.op .add [vv sdA, .op .add [.panop .mul [vv sdJ1, .const 8], .const 8]])))
      (.seq (.assign .local sdY (.load .one (.op .add [vv sdDm, .op .add [.panop .mul [vv sdJ1, .const 8], .const 8]])))
      (.seq (.call (some (some (.local, sdT), none)) fFvt [vv sdX])
      (.seq (.call (some (some (.local, sdR), none)) fD
          [.const (BitVec.ofNat 64 checkFuel), .op .add [vv sdO, vv sdJ1], vv sdT, vv sdY])
      (.ite (.cmp .equal (vv sdR) (.const 0)) Decl.rejectP
        (.seq (.call (some (some (.local, sdR), none)) fSdoms [vv sdA, vv sdDm, vv sdO, vv sdJ1])
          (.return (.const 0))))))))
      Decl.rejectP))
    Decl.rejectP))))

section
variable {σ : Type}

theorem sd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ sdLocals → (ctxEnv C ++ sdParams.zip vals).get x = none :=
  Knot.params_none C sdLocals sdParams vals (by decide) (by decide)

theorem word_sub1_eq (j : Nat) : BitVec.ofNat 64 (j + 1) - 1#64 = BitVec.ofNat 64 j := by
  rw [← word_add1_eq, BitVec.add_sub_cancel]

/-- **`checkStructDomsAt`** from count `j` down. -/
theorem sd_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C)
    (hc : C.code.lookup fSdoms = some (sdParams.map (fun p => (p, ShapeHOL.one)), sdBody, .one))
    (hcF : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one))
    (fvs doms : List EIdx) (pa pd off : Nat) :
    ∀ j (H : List (BitVec 64)) (s : AState), off + j < 2 ^ 62 → C.H <+: H →
      BlkAt H pa (fvs.map Enc.idxW) → BlkAt H pd (doms.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (sdParams.zip [cellA C pa, cellA C pd, BitVec.ofNat 64 off, BitVec.ofNat 64 j]))
        sdBody s (checkStructDomsAt mode C.fe off fvs doms j) (Decl.PostU (ctxH C H)) := by
  intro j
  induction j with
  | zero =>
    intro H s _ _ _ _
    refine specR_prologue (Decl.postU_locals _) (sd_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, sdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ j ih =>
    intro H s hoj hpH hA hD
    refine specR_prologue (Decl.postU_locals _) (sd_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hne : BitVec.ofNat 64 (j + 1) ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, sdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI sdJ1 _ (BitVec.ofNat 64 j) (by decide)
      (by simp +decide [sev, Env.get, sdParams, ctxEnv]; exact word_sub1_eq j) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) sdLa (vv sdA) pa _ hA.1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv]; rfl) ?_
    have hal := blkAt_len_le hA
    have hdl := blkAt_len_le hD
    simp only [List.length_map] at hal hdl
    unfold checkStructDomsAt
    by_cases hja : j < fvs.length
    swap
    · have hlw := ConPanqueque.T.Decl.nd_lt_iff j fvs.length (by omega) (by omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_rejectI
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j fvs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hja])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := ctxH C H) sdLd (vv sdDm) pd _ hD.1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv]; rfl) ?_
    by_cases hjd : j < doms.length
    swap
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_rejectI
    have hlw2 := ConPanqueque.T.Decl.nd_lt_iff j doms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr hjd])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hxa := hA.2 j (by simp; omega)
    have hyd := hD.2 j (by simp; omega)
    simp only [List.getElem_map] at hxa hyd
    refine UD.specR_heapLoadI' (C := ctxH C H) sdX _ (pa + 1 + j) _ hxa (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv]; exact cellA_mulIdx C pa j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) sdY _ (pd + 1 + j) _ hyd (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv]; exact cellA_mulIdx C pd j (by omega)) ?_
    rw [List.getElem?_eq_getElem hja, List.getElem?_eq_getElem hjd]
    simp only [unwrapOr, pure_bind, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) sdT fFvt [pH] [vv sdX] ExM.fvtBody [Enc.idxW fvs[j]] (by decide) rfl
      (by decide) hcF ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (ExM.fvt_spec (ctxH C H) s fvs[j]) (fun ta s1 => ?_)
    have hokH := ctxOK_H hok H
    have hkH := kcodes_H hk H
    refine specR_callCB (C := ctxH C H) sdR fD dParams
      [.const (BitVec.ofNat 64 checkFuel), .op .add [vv sdO, vv sdJ1], vv sdT, vv sdY]
      (dE (ctxH C H)) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 (off + j), Enc.idxW ta, Enc.idxW doms[j]] (by decide) rfl
      (by decide) hkH.ed
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat],
        by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
      (Comp.defeqTop ra mode hokH hkH (allCodes_H hac H) hs s1 (off + j) (by omega) ta doms[j]) (fun b s2 H2 hp2 _ => ?_)
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    refine specR_congr (m' := checkStructDomsAt mode C.fe off fvs doms j >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIH (C := ctxH C H2) sdR fSdoms sdParams [vv sdA, vv sdDm, vv sdO, vv sdJ1]
      sdBody [cellA C pa, cellA C pd, BitVec.ofNat 64 off, BitVec.ofNat 64 j] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, sdParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (Decl.PostU (ctxH C H2)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sdParams _ rfl hlk)
        (ih H2 s2 (by omega) (hpH.trans hp2) (blkAt_mono hA hp2) (blkAt_mono hD hp2)))
      (fun _ w s3 H3 hp3 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp2.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `fieldDomsResolve`, `idxArgsResolve` (a `false` hangs: the twin fails right after) -/

def fdrA := ofString "fdr_a"
def fdrI := ofString "fdr_i"
def fdrN := ofString "fdr_n"
def fdrX := ofString "fdr_x"
def fdrT := ofString "fdr_t"
def fdrB := ofString "fdr_b"
def fdrR := ofString "fdr_r"
def fFieldDoms := ofString "fieldDomsResolve"
def fIdxArgs := ofString "idxArgsResolve"

def fdrParams : List MlS := [fdrA, fdrI, fdrN]
def fdrLocals : List MlS := [fdrX, fdrT, fdrB, fdrR]

/-- `fieldDomsResolve` (`ty = true`: through each variable's type) or `idxArgsResolve`. -/
def fdrBody (ty : Bool) : ProgHOL 64 := prologue fdrLocals
  (.ite (.cmp .lower (vv fdrI) (vv fdrN))
    (.seq (.assign .local fdrX (.load .one (.op .add [vv fdrA, .op .add [.panop .mul [vv fdrI, .const 8], .const 8]])))
    (.seq (if ty then .call (some (some (.local, fdrT), none)) fFvt [vv fdrX] else .assign .local fdrT (vv fdrX))
    (.seq (.call (some (some (.local, fdrB), none)) fCrff [vv fdrT])
    (.ite (.cmp .equal (vv fdrB) (.const 0)) Decl.rejectP
      (.seq (.call (some (some (.local, fdrR), none)) (if ty then fFieldDoms else fIdxArgs)
          [vv fdrA, .op .add [vv fdrI, .const 1], vv fdrN])
        (.return (vv fdrR)))))))
    (.return (.const 1)))

section
variable {σ : Type}

theorem fdr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fdrLocals → (ctxEnv C ++ fdrParams.zip vals).get x = none :=
  Knot.params_none C fdrLocals fdrParams vals (by decide) (by decide)

theorem fieldDomsResolve_cons (fe : IFEnv) (x : EIdx) (xs : List EIdx) : fieldDomsResolve fe (x :: xs) =
    (do let t ← fvarTypeD x; let b ← constsResolveFFast fe t
        if b = true then fieldDomsResolve fe xs else pure false) := rfl

theorem idxArgsResolve_cons (fe : IFEnv) (x : EIdx) (xs : List EIdx) : idxArgsResolve fe (x :: xs) =
    (do let b ← constsResolveFFast fe x
        if b = true then idxArgsResolve fe xs else pure false) := rfl

/-- **`fieldDomsResolve`** from position `i`. -/
theorem fdrT_spec (C : Ctx) (hok : CtxOK C) (hcr : CrfCodes C)
    (hc : C.code.lookup fFieldDoms = some (fdrParams.map (fun p => (p, ShapeHOL.one)), fdrBody true, .one))
    (hcF : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one))
    (hcc : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one))
    (xs : List EIdx) (pa : Nat) :
    ∀ f i (H : List (BitVec 64)) (s : AState), xs.length - i = f → i ≤ xs.length →
      BlkAt H pa (xs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (fdrParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length]))
        (fdrBody true) s (fieldDomsResolve C.fe (xs.drop i)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hA
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postB_locals _) (fdr_none _ _) ?_
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, fdrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hA
    have hin : i < xs.length := by omega
    refine specR_prologue (postB_locals _) (fdr_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, fdrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, fieldDomsResolve_cons]
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) fdrX _ (pa + 1 + i) _ hx (by decide)
      (by simp +decide [sev, Env.get, fdrParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine ILP.callE_spec (C := ctxH C H) fdrT fFvt [pH] [vv fdrX] ExM.fvtBody [Enc.idxW xs[i]] (by decide) rfl
      (by decide) hcF ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (ExM.fvt_spec (ctxH C H) s xs[i]) (fun ta s1 => ?_)
    refine specR_callNIH (C := ctxH C H) fdrB fCrff [crffE] [vv fdrT] crffBody [Enc.idxW ta] (by decide) rfl
      (by decide) hcc ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
        (crff_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hcr) s1 ta))
      (fun b w s2 H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    refine specR_congr (m' := fieldDomsResolve C.fe (xs.drop (i + 1)) >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H2) fdrR fFieldDoms fdrParams [vv fdrA, .op .add [vv fdrI, .const 1], vv fdrN]
      (fdrBody true) [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, fdrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fdrParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, fdrParams, ctxEnv], trivial⟩
      (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fdrParams _ rfl hlk)
        (ih (i + 1) H2 s2 (by omega) (by omega) (blkAt_mono hA hp2)))
      (fun r w s3 H3 hp3 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H3, hp2.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- **`idxArgsResolve`** from position `i`. -/
theorem fdrI_spec (C : Ctx) (hok : CtxOK C) (hcr : CrfCodes C)
    (hc : C.code.lookup fIdxArgs = some (fdrParams.map (fun p => (p, ShapeHOL.one)), fdrBody false, .one))
    (hcc : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one))
    (xs : List EIdx) (pa : Nat) :
    ∀ f i (H : List (BitVec 64)) (s : AState), xs.length - i = f → i ≤ xs.length →
      BlkAt H pa (xs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (fdrParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length]))
        (fdrBody false) s (idxArgsResolve C.fe (xs.drop i)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hA
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postB_locals _) (fdr_none _ _) ?_
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, fdrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hA
    have hin : i < xs.length := by omega
    refine specR_prologue (postB_locals _) (fdr_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, fdrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, idxArgsResolve_cons]
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) fdrX _ (pa + 1 + i) _ hx (by decide)
      (by simp +decide [sev, Env.get, fdrParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine specR_assignI fdrT (vv fdrX) (Enc.idxW xs[i]) (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_callNIH (C := ctxH C H) fdrB fCrff [crffE] [vv fdrT] crffBody [Enc.idxW xs[i]] (by decide) rfl
      (by decide) hcc ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
        (crff_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hcr) s xs[i]))
      (fun b w s2 H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    refine specR_congr (m' := idxArgsResolve C.fe (xs.drop (i + 1)) >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H2) fdrR fIdxArgs fdrParams [vv fdrA, .op .add [vv fdrI, .const 1], vv fdrN]
      (fdrBody false) [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, fdrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fdrParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, fdrParams, ctxEnv], trivial⟩
      (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fdrParams _ rfl hlk)
        (ih (i + 1) H2 s2 (by omega) (by omega) (blkAt_mono hA hp2)))
      (fun r w s3 H3 hp3 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H3, hp2.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `List.contains` over a block of handles -/

def bkcA := ofString "bkc_a"
def bkcX := ofString "bkc_x"
def bkcI := ofString "bkc_i"
def bkcN := ofString "bkc_n"
def bkcY := ofString "bkc_y"
def bkcR := ofString "bkc_r"
def fBlkContains := ofString "blkContains"

def bkcParams : List MlS := [bkcA, bkcX, bkcI, bkcN]
def bkcLocals : List MlS := [bkcY, bkcR]

def bkcBody : ProgHOL 64 := prologue bkcLocals
  (.ite (.cmp .lower (vv bkcI) (vv bkcN))
    (.seq (.assign .local bkcY (.load .one (.op .add [vv bkcA, .op .add [.panop .mul [vv bkcI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv bkcY) (vv bkcX)) (.return (.const 1))
      (.seq (.call (some (some (.local, bkcR), none)) fBlkContains [vv bkcA, vv bkcX, .op .add [vv bkcI, .const 1], vv bkcN])
        (.return (vv bkcR)))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem bkc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bkcLocals → (ctxEnv C ++ bkcParams.zip vals).get x = none :=
  Knot.params_none C bkcLocals bkcParams vals (by decide) (by decide)

/-- **`blkContains`** from position `i`. -/
theorem cnt_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fBlkContains = some (bkcParams.map (fun p => (p, ShapeHOL.one)), bkcBody, .one))
    (xs : List EIdx) (x : EIdx) (pa : Nat) (H : List (BitVec 64)) (hA : BlkAt H pa (xs.map Enc.idxW)) :
    ∀ f i (s : AState), xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (bkcParams.zip [cellA C pa, Enc.idxW x, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length]))
        bkcBody s (pure ((xs.drop i).contains x)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postB_locals _) (bkc_none _ _) ?_
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, bkcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < xs.length := by omega
    refine specR_prologue (postB_locals _) (bkc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, bkcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, List.contains_cons]
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) bkcY _ (pa + 1 + i) _ hx (by decide)
      (by simp +decide [sev, Env.get, bkcParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    by_cases he : xs[i] = x
    · subst he
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, bkcParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, Bool.true_or]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hw : Enc.idxW xs[i] ≠ Enc.idxW x := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, bkcParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    have hf' : (x == xs[i]) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he e.symm
    rw [hf', Bool.false_or]
    refine specR_congr (m' := (pure ((xs.drop (i + 1)).contains x) : AM Bool) >>= fun b => pure b) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) bkcR fBlkContains bkcParams [vv bkcA, vv bkcX, .op .add [vv bkcI, .const 1], vv bkcN]
      bkcBody [cellA C pa, Enc.idxW x, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, bkcParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bkcParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bkcParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, bkcParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bkcParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `checkStructFieldSortsI` -/

def fsA := ofString "fs_a"
def fsX := ofString "fs_x"
def fsS := ofString "fs_s"
def fsP := ofString "fs_p"
def fsIp := ofString "fs_ip"
def fsLg := ofString "fs_lg"
def fsJ := ofString "fs_j"
def fsJ1 := ofString "fs_j1"
def fsLa := ofString "fs_la"
def fsV := ofString "fs_v"
def fsT := ofString "fs_t"
def fsTy := ofString "fs_ty"
def fsU := ofString "fs_u"
def fsO := ofString "fs_o"
def fsZ := ofString "fs_z"
def fsN := ofString "fs_n"
def fsR := ofString "fs_r"
def fFieldSorts := ofString "checkStructFieldSortsI"

def fsParams : List MlS := [fsA, fsX, fsS, fsP, fsIp, fsLg, fsJ]
def fsLocals : List MlS := [fsJ1, fsLa, fsV, fsT, fsTy, fsU, fsO, fsZ, fsN, fsR]

def fsRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, fsR), none)) fFieldSorts [vv fsA, vv fsX, vv fsS, vv fsP, vv fsIp, vv fsLg, vv fsJ1])
    (.return (.const 0))

def fsBody (C : Ctx) : ProgHOL 64 := prologue fsLocals
  (.ite (.cmp .equal (vv fsJ) (.const 0)) (.return (.const 0))
  (.seq (.assign .local fsJ1 (.op .sub [vv fsJ, .const 1]))
  (.seq (.assign .local fsLa (.load .one (vv fsA)))
  (.ite (.cmp .lower (vv fsJ1) (vv fsLa))
    (.seq (.assign .local fsV (.load .one (.op .add [vv fsA, .op .add [.panop .mul [vv fsJ1, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, fsT), none)) fFvt [vv fsV])
    (.seq (.call (some (some (.local, fsTy), none)) fI
        [.const (BitVec.ofNat 64 checkFuel), .op .add [vv fsP, vv fsJ1], vv fsT])
    (.seq (.call (some (some (.local, fsU), none)) fEns
        [.const (BitVec.ofNat 64 checkFuel), .op .add [vv fsP, vv fsJ1], vv fsTy])
    (.ite (.cmp .equal (vv fsIp) (.const 0))
      (.seq (.call (some (some (.local, fsO), none)) LLeq.fLeqTop [vv fsU, vv fsS])
        (.ite (.cmp .equal (vv fsO) (.const 2)) fsRec Decl.rejectP))
      (.ite (vv fsLg)
        (.seq (.assign .local fsZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
        (.seq (.call (some (some (.local, fsO), none)) LLeq.fEqv [vv fsU, vv fsZ])
        (.ite (.cmp .equal (vv fsO) (.const 2)) fsRec
          (.seq (.assign .local fsN (.load .one (vv fsX)))
          (.seq (.call (some (some (.local, fsR), none)) fBlkContains [vv fsX, vv fsV, .const 0, vv fsN])
          (.ite (.cmp .equal (vv fsR) (.const 0)) Decl.rejectP fsRec))))))
        fsRec))))))
    Decl.rejectP))))

/-- The code `checkStructFieldSortsI` runs. -/
structure FSCodes (C : Ctx) : Prop where
  self : C.code.lookup fFieldSorts = some (fsParams.map (fun p => (p, ShapeHOL.one)), fsBody C, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  ens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one)
  eqv : C.code.lookup LLeq.fEqv = some ([LEq.pLa, LEq.pLb].map (fun p => (p, ShapeHOL.one)), LLeq.eqvBody, .one)
  lqt : C.code.lookup LLeq.fLeqTop = some ([LEq.pLa, LEq.pLb].map (fun p => (p, ShapeHOL.one)), LLeq.leqTopBody, .one)
  bkc : C.code.lookup fBlkContains = some (bkcParams.map (fun p => (p, ShapeHOL.one)), bkcBody, .one)
  lS : C.code.lookup LSub.fSubst = some (LSub.substParams.map (fun p => (p, ShapeHOL.one)), LSub.substBody C, .one)
  lN : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  lM : C.code.lookup LSimp.fSimp = some ([(LEq.pLa, .one)], LSimp.simpBody C, .one)
  lC : C.code.lookup LComb.fComb = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LComb.combBody C, .one)
  lB : C.code.lookup LLeq.fByC = some (LLeq.bcParams.map (fun p => (p, ShapeHOL.one)), LLeq.bcBody C, .one)
  lI : C.code.lookup LLeq.fITag = some ([(LEq.pLa, .one)], LLeq.itagBody, .one)
  lR : C.code.lookup LLeq.fImax = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), LLeq.imBody C, .one)
  lE : C.code.lookup LEq.fLvlEq = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LEq.lvlEqBody, .one)
  lT : C.code.lookup LLeq.fRest = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), LLeq.restBody, .one)
  lL : C.code.lookup LLeq.fLeq = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), LLeq.leqBody, .one)

section
variable {σ : Type}

theorem fs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fsLocals → (ctxEnv C ++ fsParams.zip vals).get x = none :=
  Knot.params_none C fsLocals fsParams vals (by decide) (by decide)

/-- `ensureSortCore` at any depth. -/
theorem ens_topD (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) {C : Ctx} (hok : CtxOK C)
    (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hs : C.side = false) (s : AState) (d : Nat)
    (hd : d < 2 ^ 63) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW e])) ensBody s
      (ensureSortCore mode C.fe checkFuel d e) (PostLH C) := by
  rw [ensureSortCore_eq mode hs]
  exact ens_spec (d := d) mode checkFuel C hk.ew s e
    ((Comp.knot_closed (σ := σ) ra mode checkFuel Comp.checkFuel_le C hok hk s hac).2.1 d e hd)

end

section
variable {σ : Type}

set_option maxHeartbeats 8000000 in
/-- **`checkStructFieldSortsI`** from count `j` down (the level equivalence's spec a hypothesis). -/
theorem fs_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : FSCodes C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (isProp large : Bool) (sr : LIdx) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls sr = some lsr)
    (nP : Nat) (fvs idxArgs : List EIdx) (pa px : Nat) :
    ∀ j (H : List (BitVec 64)) (s : AState), nP + j < 2 ^ 62 → C.H <+: H →
      BlkAt H pa (fvs.map Enc.idxW) → BlkAt H px (idxArgs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (fsParams.zip [cellA C pa, cellA C px, Enc.idxW sr, BitVec.ofNat 64 nP,
          boolW isProp, boolW large, BitVec.ofNat 64 j]))
        (fsBody C) s (checkStructFieldSortsI mode C.fe isProp large sr nP fvs idxArgs j) (Decl.PostU (ctxH C H)) := by
  intro j
  induction j with
  | zero =>
    intro H s _ _ _ _
    refine specR_prologue (Decl.postU_locals _) (fs_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, fsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ j ih =>
    intro H s hoj hpH hA hX
    -- the recursive call, from any later heap and any environment holding the parameters
    have hrec : ∀ (Γ : Env) (H' : List (BitVec 64)) (s' : AState), H <+: H' →
        Γ.get fsA = some (cellA C pa) → Γ.get fsX = some (cellA C px) → Γ.get fsS = some (Enc.idxW sr) →
        Γ.get fsP = some (BitVec.ofNat 64 nP) → Γ.get fsIp = some (boolW isProp) →
        Γ.get fsLg = some (boolW large) → Γ.get fsJ1 = some (BitVec.ofNat 64 j) →
        SpecR (σ := σ) (Inv (ctxH C H') s' Γ [] (ctxLocals ++ fsLocals)) fsRec s'
          (checkStructFieldSortsI mode C.fe isProp large sr nP fvs idxArgs j) (Decl.PostU (ctxH C H)) := by
      intro Γ H' s' hp gA gX gS gP gI gL gJ
      refine specR_congr (m' := checkStructFieldSortsI mode C.fe isProp large sr nP fvs idxArgs j >>= fun _ => pure ())
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H') fsR fFieldSorts fsParams [vv fsA, vv fsX, vv fsS, vv fsP, vv fsIp, vv fsLg, vv fsJ1]
        (fsBody C) [cellA C pa, cellA C px, Enc.idxW sr, BitVec.ofNat 64 nP, boolW isProp, boolW large, BitVec.ofNat 64 j]
        (by decide) rfl (by decide) hc.self ⟨gA, gX, gS, gP, gI, gL, gJ, trivial⟩
        (Decl.PostU (ctxH C H')) (fun _ _ _ _ => True) (fun a w s' st ⟨H'', hp', hsr⟩ => ⟨H'', hp', trivial, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fsParams _ rfl hlk)
          (ih H' s' (by omega) (hpH.trans hp) (blkAt_mono hA hp) (blkAt_mono hX hp)))
        (fun _ w s3 H3 hp3 _ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_prologue (Decl.postU_locals _) (fs_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hne : BitVec.ofNat 64 (j + 1) ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, fsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI fsJ1 _ (BitVec.ofNat 64 j) (by decide)
      (by simp +decide [sev, Env.get, fsParams, ctxEnv]; exact word_sub1_eq j) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) fsLa (vv fsA) pa _ hA.1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv]; rfl) ?_
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    rw [checkStructFieldSortsI]
    by_cases hja : j < fvs.length
    swap
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_rejectI
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j fvs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hja])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hxa := hA.2 j (by simp; omega)
    simp only [List.getElem_map] at hxa
    refine UD.specR_heapLoadI' (C := ctxH C H) fsV _ (pa + 1 + j) _ hxa (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv]; exact cellA_mulIdx C pa j (by omega)) ?_
    rw [List.getElem?_eq_getElem hja]
    simp only [unwrapOr, pure_bind, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) fsT fFvt [pH] [vv fsV] ExM.fvtBody [Enc.idxW fvs[j]] (by decide) rfl
      (by decide) hc.fvt ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (ExM.fvt_spec (ctxH C H) s fvs[j]) (fun ta s1 => ?_)
    have hokH := ctxOK_H hok H
    have hkH := kcodes_H hk H
    refine Big.specR_callKC (C := ctxH C H) fsTy fI kParams
      [.const (BitVec.ofNat 64 checkFuel), .op .add [vv fsP, vv fsJ1], vv fsT]
      (inferE (ctxH C H) fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 (nP + j), Enc.idxW ta] (by decide) rfl
      (by decide) hkH.ei
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat],
        by simp +decide [sev, Env.get_cons], trivial⟩
      (Comp.inferTop ra mode hokH hkH (allCodes_H hac H) hs s1 (nP + j) (by omega) ta) (fun ty s2 H2 hp2 _ => ?_)
    have hok2 := ctxOK_H hok H2
    refine specR_callNIH (C := ctxH C H2) fsU fEns kParams
      [.const (BitVec.ofNat 64 checkFuel), .op .add [vv fsP, vv fsJ1], vv fsTy]
      ensBody [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 (nP + j), Enc.idxW ty] (by decide) rfl (by decide) hc.ens
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat],
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostLH (ctxH C H2)) (fun u w s' H' => w = Enc.idxW u ∧ ∃ h, s'.store.view h = some (.sort u))
      (fun u w s' st' ⟨H', hp', hw, hsr, hv⟩ => ⟨H', hp', ⟨hw, hv⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk)
        (ens_topD ra mode hok2 (kcodes_H hk H2) (allCodes_H hac H2) hs s2 (nP + j) (by omega) ty))
      (fun u w s3 H3 hp3 ⟨hw, hh, hvu⟩ => ?_)
    subst hw
    have hp3H : H <+: H3 := hp2.trans hp3
    have hok3 := ctxOK_H hok H3
    have hX3 : BlkAt H3 px (idxArgs.map Enc.idxW) := blkAt_mono hX hp3H
    refine specR_atEntry fun t3 ht3 => ?_
    obtain ⟨lu, hlu⟩ := sr_sortDen ht3.sr hh u hvu
    have hco3 := ht3.sr.cok
    have hsrD : denoteL s3.store.ls sr = some lsr := denoteL_ext hSd ht3.sr.floor
    cases isProp
    · -- the field's universe at most the result's
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv, boolW,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      rw [if_pos (by rfl)]
      refine specR_congr (m' := (readLevelM u >>= fun a => readLevelM sr >>= fun b => pure (a.leq b)) >>= fun o =>
          liftFueled "level comparison" o >>= fun b =>
            if b = true then checkStructFieldSortsI mode C.fe false large sr nP fvs idxArgs j
            else (do fail (CheckError.invalid "direct sum: field universe too large")
                     checkStructFieldSortsI mode C.fe false large sr nP fvs idxArgs j)) (by simp only [bind_assoc, pure_bind]) ?_
      obtain ⟨s4, hrun, e1, e2, e3, e4, hco4⟩ := readLvl2_run (fun a b => ConLeche.Level.leq a b) u sr s3 lu lsr hlu hsrD hco3
      refine specR_runBind hrun ?_
      refine specR_mono (P := Inv (ctxH (ctxH C H2) H3) s4 _ [] _) ?_
        (fun t ht => ⟨LLeq.sr_congrS ht.sr e1 e2 e3 e4 hco4, ht.env, ht.mem, ht.decl⟩) (fun _ _ _ _ h => h)
      refine specR_congr (m' := (pure (ConLeche.Level.leq lu lsr) : AM (Option Bool)) >>= fun o =>
          liftFueled "level comparison" o >>= fun b =>
            if b = true then checkStructFieldSortsI mode C.fe false large sr nP fvs idxArgs j
            else (do fail (CheckError.invalid "direct sum: field universe too large")
                     checkStructFieldSortsI mode C.fe false large sr nP fvs idxArgs j)) (by simp) ?_
      refine specR_callNIH (C := ctxH C H3) fsO LLeq.fLeqTop [LEq.pLa, LEq.pLb] [vv fsU, vv fsS] LLeq.leqTopBody
        [Enc.idxW u, Enc.idxW sr] (by decide) rfl (by decide) hc.lqt
        ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv], trivial⟩
        (LLeq.PostOB (ctxH C H3)) (fun o w s' H' => H' = H3 ∧ w = LLeq.obW o)
        (fun o w s' st ⟨hw, hsr⟩ => ⟨H3, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
          (LLeq.leqTop_spec C hok hc.lS hc.lN hc.lM hc.lC hc.lB hc.lI hc.lR hc.lE hc.lT hc.lL H3 lu lsr _ _ s4
            (lrep_arena _ _ _ u _ lu (by rw [e1]; exact hlu)) (lrep_arena _ _ _ sr _ lsr (by rw [e1]; exact hsrD))))
        (fun o w s5 H5 hp5 ⟨eH5, hw⟩ => ?_)
      subst hw; subst H5
      rcases o with _ | ⟨_ | _⟩
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => specR_rejectI)
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => specR_rejectI)
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [liftFueled, pure_bind, ↓reduceIte]
        exact hrec _ H3 s5 hp3H (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv, boolW,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (by decide)]
      cases large
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv, boolW])
          (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg (by decide)]
        exact hrec _ H3 s3 hp3H (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv, boolW])
          (fun _ => ?_) (fun h => absurd h (by decide))
        rw [if_pos rfl]
        simp only [zeroLevel]
        refine specR_pinXI (C := ctxH C H3) hok3 pinZeroLevel 1 C.pins.zeroLevel _
          (fun s hp => pinZeroLevel_run (C := ctxH C H3) hok3 hp) (pin_zeroLevel_cell hok3) fsZ (by decide) ?_
        have hz := sr_zeroLevel ht3.sr
        refine specR_callNIH (C := ctxH C H3) fsO LLeq.fEqv [LEq.pLa, LEq.pLb] [vv fsU, vv fsZ] LLeq.eqvBody
          [Enc.idxW u, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hc.eqv
          ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
          (LLeq.PostOB (ctxH C H3)) (fun o w s' H' => H' = H3 ∧ w = LLeq.obW o)
          (fun o w s' st ⟨hw, hsr⟩ => ⟨H3, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
          (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
            (heqS H3 u C.pins.zeroLevel s3 lu .zero hlu hz hco3))
          (fun o w s4 H4 hp4 ⟨eH4, hw⟩ => ?_)
        subst hw; subst H4
        by_cases ho : o = some true
        · subst ho
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun h => absurd h (by decide))
          rw [if_pos (by simp)]
          exact hrec _ H3 s4 hp3H (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
        have hob : LLeq.obW o ≠ 2#64 := by
          rcases o with _ | ⟨_ | _⟩
          · decide
          · decide
          · exact absurd rfl ho
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hob)
          (fun h => absurd rfl h) (fun _ => ?_)
        have hoF : (o == some true) = false := by simpa using ho
        simp only [hoF, Bool.false_or]
        refine UD.specR_heapLoadI' (C := ctxH C H3) fsN (vv fsX) px _ hX3.1 (by decide)
          (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv]; rfl) ?_
        refine specR_congr (m' := (pure ((idxArgs.drop 0).contains fvs[j]) : AM Bool) >>= fun b =>
            if b = true then checkStructFieldSortsI mode C.fe true true sr nP fvs idxArgs j
            else (do fail (CheckError.invalid "direct sum: large eliminator with a non-propositional field outside the indices")
                     checkStructFieldSortsI mode C.fe true true sr nP fvs idxArgs j)) (by simp) ?_
        refine specR_callNIH (C := ctxH C H3) fsR fBlkContains bkcParams [vv fsX, vv fsV, .const 0, vv fsN] bkcBody
          [cellA C px, Enc.idxW fvs[j], BitVec.ofNat 64 0, BitVec.ofNat 64 idxArgs.length] (by decide) rfl (by decide) hc.bkc
          ⟨by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl,
            by simp +decide [sev, Env.get_cons], trivial⟩
          (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu bkcParams _ rfl hlk)
            (cnt_spec C hok hc.bkc idxArgs fvs[j] px H3 hX3 _ 0 s4 rfl (by omega)))
          (fun b w s5 H5 hp5 hw => ?_)
        subst hw
        refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b)
          (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
        exact hrec _ H5 s5 (hp3H.trans hp5) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])

end

end ConPanqueque.T.Ind
