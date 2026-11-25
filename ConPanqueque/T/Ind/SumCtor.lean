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
def fsQ := ofString "fs_q"
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

def fsParams : List MlS := [fsA, fsX, fsQ, fsS, fsP, fsIp, fsLg, fsJ]
def fsLocals : List MlS := [fsJ1, fsLa, fsV, fsT, fsTy, fsU, fsO, fsZ, fsN, fsR]

def fsRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, fsR), none)) fFieldSorts [vv fsA, vv fsX, vv fsQ, vv fsS, vv fsP, vv fsIp, vv fsLg, vv fsJ1])
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
          (.seq (.call (some (some (.local, fsR), none)) fBlkContains [vv fsX, vv fsV, vv fsQ, vv fsN])
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
    (nP : Nat) (fvs xs : List EIdx) (q : Nat) (hq : q ≤ xs.length) (pa px : Nat) :
    ∀ j (H : List (BitVec 64)) (s : AState), nP + j < 2 ^ 62 → C.H <+: H →
      BlkAt H pa (fvs.map Enc.idxW) → BlkAt H px (xs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (fsParams.zip [cellA C pa, cellA C px, BitVec.ofNat 64 q, Enc.idxW sr, BitVec.ofNat 64 nP,
          boolW isProp, boolW large, BitVec.ofNat 64 j]))
        (fsBody C) s (checkStructFieldSortsI mode C.fe isProp large sr nP fvs (xs.drop q) j) (Decl.PostU (ctxH C H)) := by
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
        Γ.get fsA = some (cellA C pa) → Γ.get fsX = some (cellA C px) → Γ.get fsQ = some (BitVec.ofNat 64 q) →
        Γ.get fsS = some (Enc.idxW sr) →
        Γ.get fsP = some (BitVec.ofNat 64 nP) → Γ.get fsIp = some (boolW isProp) →
        Γ.get fsLg = some (boolW large) → Γ.get fsJ1 = some (BitVec.ofNat 64 j) →
        SpecR (σ := σ) (Inv (ctxH C H') s' Γ [] (ctxLocals ++ fsLocals)) fsRec s'
          (checkStructFieldSortsI mode C.fe isProp large sr nP fvs (xs.drop q) j) (Decl.PostU (ctxH C H)) := by
      intro Γ H' s' hp gA gX gQ gS gP gI gL gJ
      refine specR_congr (m' := checkStructFieldSortsI mode C.fe isProp large sr nP fvs (xs.drop q) j >>= fun _ => pure ())
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H') fsR fFieldSorts fsParams [vv fsA, vv fsX, vv fsQ, vv fsS, vv fsP, vv fsIp, vv fsLg, vv fsJ1]
        (fsBody C) [cellA C pa, cellA C px, BitVec.ofNat 64 q, Enc.idxW sr, BitVec.ofNat 64 nP, boolW isProp, boolW large, BitVec.ofNat 64 j]
        (by decide) rfl (by decide) hc.self ⟨gA, gX, gQ, gS, gP, gI, gL, gJ, trivial⟩
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
    have hX3 : BlkAt H3 px (xs.map Enc.idxW) := blkAt_mono hX hp3H
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
            if b = true then checkStructFieldSortsI mode C.fe false large sr nP fvs (xs.drop q) j
            else (do fail (CheckError.invalid "direct sum: field universe too large")
                     checkStructFieldSortsI mode C.fe false large sr nP fvs (xs.drop q) j)) (by simp only [bind_assoc, pure_bind]) ?_
      obtain ⟨s4, hrun, e1, e2, e3, e4, hco4⟩ := readLvl2_run (fun a b => ConLeche.Level.leq a b) u sr s3 lu lsr hlu hsrD hco3
      refine specR_runBind hrun ?_
      refine specR_mono (P := Inv (ctxH (ctxH C H2) H3) s4 _ [] _) ?_
        (fun t ht => ⟨LLeq.sr_congrS ht.sr e1 e2 e3 e4 hco4, ht.env, ht.mem, ht.decl⟩) (fun _ _ _ _ h => h)
      refine specR_congr (m' := (pure (ConLeche.Level.leq lu lsr) : AM (Option Bool)) >>= fun o =>
          liftFueled "level comparison" o >>= fun b =>
            if b = true then checkStructFieldSortsI mode C.fe false large sr nP fvs (xs.drop q) j
            else (do fail (CheckError.invalid "direct sum: field universe too large")
                     checkStructFieldSortsI mode C.fe false large sr nP fvs (xs.drop q) j)) (by simp) ?_
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
          (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv, boolW,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (by decide)]
      cases large
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv, boolW])
          (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg (by decide)]
        exact hrec _ H3 s3 hp3H (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
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
          exact hrec _ H3 s4 hp3H (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])
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
        refine specR_congr (m' := (pure ((xs.drop q).contains fvs[j]) : AM Bool) >>= fun b =>
            if b = true then checkStructFieldSortsI mode C.fe true true sr nP fvs (xs.drop q) j
            else (do fail (CheckError.invalid "direct sum: large eliminator with a non-propositional field outside the indices")
                     checkStructFieldSortsI mode C.fe true true sr nP fvs (xs.drop q) j)) (by simp) ?_
        refine specR_callNIH (C := ctxH C H3) fsR fBlkContains bkcParams [vv fsX, vv fsV, vv fsQ, vv fsN] bkcBody
          [cellA C px, Enc.idxW fvs[j], BitVec.ofNat 64 q, BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc.bkc
          ⟨by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv], by simp +decide [sev, Env.get_cons],
            by simp +decide [sev, Env.get_cons, Env.get, fsParams, ctxEnv],
            by simp +decide [sev, Env.get_cons], trivial⟩
          (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu bkcParams _ rfl hlk)
            (cnt_spec C hok hc.bkc xs fvs[j] px H3 hX3 _ q s4 rfl hq))
          (fun b w s5 H5 hp5 hw => ?_)
        subst hw
        refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b)
          (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
        exact hrec _ H5 s5 (hp3H.trans hp5) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, fsParams, ctxEnv])

end

/-! ## `checkSumCtor` -/

def scC := ofString "sc_c"
def scF := ofString "sc_f"
def scTa := ofString "sc_ta"
def scL := ofString "sc_l"
def scP := ofString "sc_p"
def scNI := ofString "sc_ni"
def scS := ofString "sc_s"
def scIp := ofString "sc_ip"
def scLg := ofString "sc_lg"
def scX := ofString "sc_x"
def scTy := ofString "sc_ty"
def scSt := ofString "sc_st"
def scSc := ofString "sc_sc"
def scB := ofString "sc_b"
def scTn := ofString "sc_tn"
def scR := ofString "sc_r"
def scQ1 := ofString "sc_q1"
def scCq := ofString "sc_cq"
def scCr := ofString "sc_cr"
def scTt := ofString "sc_tt"
def scQ2 := ofString "sc_q2"
def scTq := ofString "sc_tq"
def scDm := ofString "sc_dm"
def scQ3 := ofString "sc_q3"
def scXq := ofString "sc_xq"
def scXr := ofString "sc_xr"
def scU := ofString "sc_u"
def scH := ofString "sc_h"
def scFn := ofString "sc_fn"
def scA := ofString "sc_a"
def scK := ofString "sc_k"
def scLc := ofString "sc_lc"
def scN := ofString "sc_n"
def fSumCtor := ofString "checkSumCtor"

def scParams : List MlS := [scC, scF, scTa, scL, scP, scNI, scS, scIp, scLg]
def scLocals : List MlS := [scX, scTy, scSt, scSc, scB, scTn, scR, scQ1, scCq, scCr, scTt, scQ2, scTq, scDm, scQ3, scXq,
  scXr, scU, scH, scFn, scA, scK, scLc, scN]

/-- After the opened residual's checks: the pre-block resolutions and the field sorts. -/
def scTail : ProgHOL 64 :=
  .seq (.assign .local scN (.load .one (vv scXq)))
  (.seq (.call (some (some (.local, scR), none)) fFieldDoms [vv scXq, .const 0, vv scN])
  (.ite (.cmp .equal (vv scR) (.const 0)) Decl.rejectP
  (.seq (.call (some (some (.local, scR), none)) fIdxArgs [vv scA, vv scP, vv scK])
  (.ite (.cmp .equal (vv scR) (.const 0)) Decl.rejectP
  (.seq (.call (some (some (.local, scR), none)) fFieldSorts
      [vv scXq, vv scA, vv scP, vv scS, vv scP, vv scIp, vv scLg, vv scF])
    (.return (.const 0)))))))

/-- The opened residual: the family at the opened parameters, then `nIdx` indices. -/
def scResid : ProgHOL 64 :=
  .seq (.call (some (some (.local, scU), none)) fParamLevels [vv scL])
  (.seq (.call (some (some (.local, scH), none)) fInternConst [vv scTn, vv scU])
  (.seq (.call (some (some (.local, scFn), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv scXr])
  (.seq (.call (some (some (.local, scA), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv scXr])
  (.ite (.cmp .equal (vv scFn) (vv scH))
    (.seq (.assign .local scK (.load .one (vv scA)))
    (.ite (.cmp .equal (vv scK) (.op .add [vv scP, vv scNI]))
      (.seq (.assign .local scLc (.load .one (vv scCq)))
      (.ite (.cmp .equal (vv scLc) (vv scP))
        (.seq (.call (some (some (.local, scR), none)) fPrefEq [vv scA, vv scCq, .const 0, vv scP])
        (.ite (.cmp .equal (vv scR) (.const 0)) Decl.rejectP scTail))
        Decl.rejectP))
      Decl.rejectP))
    Decl.rejectP))))

/-- The opened frames: parameter domains against the former's, then the fields. -/
def scFrames : ProgHOL 64 :=
  .seq (.call (some (some (.local, scQ1), none)) fOpenFvars [vv scP, vv scTy, .const 0])
  (.ite (.cmp .equal (vv scQ1) (.const 0)) hang
  (.seq (.assign .local scCq (.load .one (vv scQ1)))
  (.seq (.assign .local scCr (.load .one (.op .add [vv scQ1, .const 8])))
  (.seq (.assign .local scTt (.load .one (.op .add [vv scTa, .const 16])))
  (.seq (.call (some (some (.local, scQ2), none)) fOpenFvars [vv scP, vv scTt, .const 0])
  (.ite (.cmp .equal (vv scQ2) (.const 0)) hang
  (.seq (.assign .local scTq (.load .one (vv scQ2)))
  (.seq (.call (some (some (.local, scDm), none)) fFvtDs [vv scTq])
  (.seq (.call (some (some (.local, scX), none)) fSdoms [vv scCq, vv scDm, .const 0, vv scP])
  (.seq (.call (some (some (.local, scQ3), none)) fOpenFvars [vv scF, vv scCr, vv scP])
  (.ite (.cmp .equal (vv scQ3) (.const 0)) hang
  (.seq (.assign .local scXq (.load .one (vv scQ3)))
  (.seq (.assign .local scXr (.load .one (.op .add [vv scQ3, .const 8])))
    scResid)))))))))))))

def scBody (C : Ctx) : ProgHOL 64 := prologue scLocals
  (.seq (.call (some (some (.local, scX), none)) fCcv [vv scC, .const 0, .const 0, .const 0])
  (.seq (.assign .local scTy (.load .one (.op .add [vv scC, .const 16])))
  (.seq (.call (some (some (.local, scSt), none)) fStripPis [.op .add [vv scP, vv scF], vv scTy])
  (.ite (.cmp .equal (vv scSt) (.const 0)) hang
  (.seq (.assign .local scSc (.load .one (vv scSt)))
  (.seq (.assign .local scB (.load .one (.op .add [vv scSt, .shift .lsl (vv scSc) (.const 3)])))
  (.seq (.assign .local scTn (.load .one (vv scTa)))
  (.seq (.call (some (some (.local, scR), none)) fResidOk [vv scTn, vv scL, vv scP, vv scF, vv scNI, vv scB])
  (.ite (.cmp .equal (vv scR) (.const 0)) Decl.rejectP scFrames)))))))))

/-- The code `checkSumCtor` runs. -/
structure SCCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  cc : CcvCodes mode C
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  qz : QZCodes C
  rok : C.code.lookup fResidOk = some (qzParams.map (fun p => (p, ShapeHOL.one)), qzBody, .one)
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  ftd : C.code.lookup fFvtDs = some (ftdParams.map (fun p => (p, ShapeHOL.one)), ftdBody C, .one)
  ftf : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one)
  sd : C.code.lookup fSdoms = some (sdParams.map (fun p => (p, ShapeHOL.one)), sdBody, .one)
  fdT : C.code.lookup fFieldDoms = some (fdrParams.map (fun p => (p, ShapeHOL.one)), fdrBody true, .one)
  fdI : C.code.lookup fIdxArgs = some (fdrParams.map (fun p => (p, ShapeHOL.one)), fdrBody false, .one)
  fs : FSCodes C

section
variable {σ : Type}

theorem sc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ scLocals → (ctxEnv C ++ scParams.zip vals).get x = none :=
  Knot.params_none C scLocals scParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`checkSumCtor`**: one constructor of a single-family block (the level equivalence's spec a hypothesis). -/
theorem sc_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : SCCodes mode C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls resSort = some lsr)
    (isProp large : Bool) (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal)
    (hb : nP + nF < 2 ^ 56) (hni : nIdx < 2 ^ 56) (hlp : lps.length < 2 ^ 59)
    (H : List (BitVec 64)) (hp : C.H <+: H) (oc ot ol : Nat) (hcv : CVRep C H oc cvC) (hta : CVRep C H ot cvTa)
    (hbl : EBlk H ol (lps.map Enc.idxW))
    (hlen : cvC.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = cvC.levelParams.length)
    (hks : ∀ j (hj : j < cvC.levelParams.length), denoteN C.St.ns cvC.levelParams[j] = some (ks[j]'(by omega)))
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (scParams.zip [cellA C oc, BitVec.ofNat 64 nF, cellA C ot, cellA C ol,
        BitVec.ofNat 64 nP, BitVec.ofNat 64 nIdx, Enc.idxW resSort, boolW isProp, boolW large]))
      (scBody C) s (checkSumCtor mode C.fe C.fe cvTa.name lps nP nIdx resSort isProp large cvC nF cvTa)
      (Decl.PostU (ctxH C H)) := by
  refine specR_prologue (Decl.postU_locals _) (sc_none _ _) ?_
  obtain ⟨hn0, ⟨wl, hwl, olc, hwlo, hebl⟩, hty⟩ := hcv
  have hblc : BlkAt H olc (cvC.levelParams.map Enc.idxW) := hebl
  obtain ⟨htn, -, htt⟩ := hta
  unfold checkSumCtor
  -- the constant check
  refine specR_callNIH (C := ctxH C H) scX fCcv ccvParams [vv scC, .const 0, .const 0, .const 0] (ccvBody C)
    [cellA C oc, boolW false, boolW false, boolW false] (by decide) rfl (by decide) hc.cc.ccv
    ⟨by simp +decide [sev, Env.get, scParams, ctxEnv], rfl, rfl, rfl, trivial⟩
    (Decl.PostU (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccvParams _ rfl hlk)
      (ccv_full mode (ctxH C H) (ctxOK_H hok H) hc.cc.g hc.cc.pr hc.cc.pim ra hs (by ctx_tr hc.cc.k) (by ctx_tr hc.cc.ac)
        hc.cc.cl (by ctx_tr hc.cc.lso) hc.cc.ndh hc.cc.ndg hc.cc.lbb (by ctx_tr hc.cc.cB) hc.cc.bvb hc.cc.hf
        (by ctx_tr hc.cc.cF) hc.cc.fvb hc.cc.atl (by ctx_tr hc.cc.al) hc.cc.crff (by ctx_tr hc.cc.crf) hc.cc.ens C.fe rfl
        cvC false false false oc olc hn0 (by show H[oc + 1]? = _; rw [hwl, hwlo]; rfl) hty hblc hlen ks hkl hks s))
    (fun _ w s1 H1 hp1 _ => ?_)
  have hp1' : H <+: H1 := hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) scTy _ (oc + 2) _ (get_prefix hty hp1') (by decide)
    (by simp +decide [sev, Env.get, scParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  simp only [bind_assoc]
  refine ro_strip C hok hc.sp (nP + nF) (by omega) cvC.type H1 s1 scSt (.op .add [vv scP, vv scF]) (vv scTy) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat])
    (by simp +decide [sev, Env.get_cons]) (fun o w s2 H2 hp2 hr2 hn2 hs2 => ?_)
  have hp2' : H1 <+: H2 := hp2
  rcases o with _ | ⟨tys, b⟩
  · rw [hn2 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, rfl, hba⟩ := hs2 tys b rfl
  obtain ⟨ha0, haL, -⟩ := strip_last hba
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hba
  have hHN' : H2.length ≤ C.HN := hHN
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H2) scSc (vv scSt) ob _ ha0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) scB _ (ob + 1 + tys.length) _ haL (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C ob + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  have hpH2 : H <+: H2 := hp1'.trans hp2'
  refine UD.specR_heapLoadI' (C := ctxH C H2) scTn (vv scTa) ot _ (get_prefix htn hpH2) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv]; rfl) ?_
  simp only [unwrapOr, pure_bind]
  refine specR_callNIH (C := ctxH C H2) scR fResidOk qzParams [vv scTn, vv scL, vv scP, vv scF, vv scNI, vv scB] qzBody
    [Enc.idxW cvTa.name, cellA C ol, BitVec.ofNat 64 nP, BitVec.ofNat 64 nF, BitVec.ofNat 64 nIdx, Enc.idxW b]
    (by decide) rfl (by decide) hc.rok
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu qzParams _ rfl hlk)
      (qz_spec ra C hok hc.qz cvTa.name lps nP nF nIdx b ol hlp (by omega) (by omega) H2 (eblk_mono hbl hpH2) s2))
    (fun rb w s3 H3 hp3 hw => ?_)
  subst hw
  have hpH3 : H <+: H3 := hpH2.trans hp3
  refine specR_failIteF (c := rb) _ (boolW (!rb)) (by simp +decide [sev, Env.get_cons]; exact eqz_b rb)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  unfold scFrames
  -- the constructor's parameter frame
  refine specR_callNIH (C := ctxH C H3) scQ1 fOpenFvars ofParams [vv scP, vv scTy, .const 0] (ofBody C)
    [BitVec.ofNat 64 nP, Enc.idxW cvC.type, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ofc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostOF (ctxH C H3)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op nP cvC.type 0 (by omega) (by omega) H3 (hp.trans hpH3) s3))
    (fun o1 w s4 H4 hp4 ⟨hn4, hs4⟩ => ?_)
  have hpH4 : H <+: H4 := hpH3.trans hp4
  rcases o1 with _ | ⟨cfv, cres⟩
  · rw [hn4 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨q1, oc1, rfl, hq1a, hq1b, hcfv⟩ := hs4 cfv cres rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN4 => ?_)
  have hq1l : q1 < H4.length := by
    have := (List.getElem?_eq_some_iff.mp hq1a).1; exact this
  have hHN4' : H4.length ≤ C.HN := hHN4
  have hne1 : cellA C q1 ≠ 0 := cellA_ne0 C hok q1 (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H4) scCq (vv scQ1) q1 _ hq1a (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H4) scCr _ (q1 + 1) _ hq1b (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q1) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H4) scTt _ (ot + 2) _ (get_prefix htt hpH4) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv]; exact cellA_add_ofNat C ot 2) ?_
  simp only [pure_bind]
  -- the former's parameter frame
  refine specR_callNIH (C := ctxH C H4) scQ2 fOpenFvars ofParams [vv scP, vv scTt, .const 0] (ofBody C)
    [BitVec.ofNat 64 nP, Enc.idxW cvTa.type, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ofc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostOF (ctxH C H4)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op nP cvTa.type 0 (by omega) (by omega) H4 (hp.trans hpH4) s4))
    (fun o2 w s5 H5 hp5 ⟨hn5, hs5⟩ => ?_)
  have hpH5 : H <+: H5 := hpH4.trans hp5
  rcases o2 with _ | ⟨tfv, tres⟩
  · rw [hn5 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨q2, oc2, rfl, hq2a, -, htfv⟩ := hs5 tfv tres rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN5 => ?_)
  have hq2l : q2 < H5.length := (List.getElem?_eq_some_iff.mp hq2a).1
  have hHN5' : H5.length ≤ C.HN := hHN5
  have hne2 : cellA C q2 ≠ 0 := cellA_ne0 C hok q2 (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H5) scTq (vv scQ2) q2 _ hq2a (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  simp only [pure_bind]
  refine specR_atEntry fun t5 ht5 => ?_
  have htl := Big.blk_small0 (ctxOK_H hok H5) ht5.sr htfv
  simp only [List.length_map] at htl
  -- the former's domains
  refine specR_callNIH (C := ctxH C H5) scDm fFvtDs ftdParams [vv scTq] (ftdBody C) [cellA C oc2] (by decide) rfl
    (by decide) hc.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H5)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
    (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
      (ftd_spec C hok hc.ftd hc.ftf hc.fs.fvt tfv oc2 (by omega) H5 s5 htfv))
    (fun tdoms w s6 H6 hp6 ⟨od, hwd, hbd⟩ => ?_)
  subst hwd
  have hpH6 : H <+: H6 := hpH5.trans hp6
  have hcfv6 : BlkAt H6 oc1 (cfv.map Enc.idxW) := blkAt_mono hcfv (hp5.trans hp6)
  refine specR_callNIH (C := ctxH C H6) scX fSdoms sdParams [vv scCq, vv scDm, .const 0, vv scP] sdBody
    [cellA C oc1, cellA C od, BitVec.ofNat 64 0, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc.sd
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], trivial⟩
    (Decl.PostU (ctxH C H6)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sdParams _ rfl hlk)
      (sd_spec mode ra C hok hs hc.cc.k hc.cc.ac hc.sd hc.fs.fvt cfv tdoms oc1 od 0 nP H6 s6 (by omega)
        (hp.trans hpH6) hcfv6 hbd))
    (fun _ w s7 H7 hp7 _ => ?_)
  have hpH7 : H <+: H7 := hpH6.trans hp7
  -- the field frame
  refine specR_callNIH (C := ctxH C H7) scQ3 fOpenFvars ofParams [vv scF, vv scCr, vv scP] (ofBody C)
    [BitVec.ofNat 64 nF, Enc.idxW cres, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc.ofc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], trivial⟩
    (PostOF (ctxH C H7)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op nF cres nP (by omega) (by omega) H7 (hp.trans hpH7) s7))
    (fun o3 w s8 H8 hp8 ⟨hn8, hs8⟩ => ?_)
  have hpH8 : H <+: H8 := hpH7.trans hp8
  rcases o3 with _ | ⟨xfv, xres⟩
  · rw [hn8 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨q3, oc3, rfl, hq3a, hq3b, hxfv⟩ := hs8 xfv xres rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN8 => ?_)
  have hq3l : q3 < H8.length := (List.getElem?_eq_some_iff.mp hq3a).1
  have hHN8' : H8.length ≤ C.HN := hHN8
  have hne3 : cellA C q3 ≠ 0 := cellA_ne0 C hok q3 (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne3)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H8) scXq (vv scQ3) q3 _ hq3a (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H8) scXr _ (q3 + 1) _ hq3b (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q3) ?_
  simp only [pure_bind]
  unfold scResid
  -- the opened residual
  have hok8 := ctxOK_H hok H8
  refine specR_callNIH (C := ctxH C H8) scU fParamLevels plParams [vv scL] (plBody C) [cellA C ol] (by decide) rfl
    (by decide) hc.qz.pl ⟨by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], trivial⟩
    (PostLsH (ctxH C H8)) (fun h w _ _ => w = Enc.idxW h) (fun h w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
      (pl_spec ra C hok hc.qz.pl hc.qz.pf hc.qz.ilp1 hc.qz.ils lps ol hlp H8 s8 (eblk_mono hbl hpH8)))
    (fun us wu s9 H9 hp9 hwu => ?_)
  subst hwu
  have hok9 := ctxOK_H hok H9
  have hpH9 : H <+: H9 := hpH8.trans hp9
  refine ILP.callE_spec (C := ctxH C H9) scH fInternConst [lEn, lEus] [vv scTn, vv scU] constBody
    [Enc.idxW cvTa.name, Enc.idxW us] (by decide) rfl (by decide) hc.qz.ic
    ⟨by simp +decide [sev, Env.get_cons], by simp [sev, Env.get_cons], trivial⟩
    (by exact const_body_spec ra (ctxH C H9) hok9 s9 _ _) (fun hd s10 => ?_)
  refine specR_callNIM scFn fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv scXr]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW xres] (by decide) rfl (by decide) hc.qz.gf
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel xres s10 = .ok (a, s') ∧ Post (ctxH C H9) s10 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H9) hc.qz.gf coreWalkFuel xres s10 CV.coreWalkFuel_lt t
        ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun fn w s' st ⟨_, hw, hsA, _⟩ => ?_)
  subst hw
  have hs' : s10 = s' := hsA.symm
  subst hs'
  refine specR_callNIH (C := ctxH C H9) scA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv scXr]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW xres] (by decide) rfl (by decide) hc.qz.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H9)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
    (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H9) hok9 hc.qz.gaa coreWalkFuel CV.coreWalkFuel_lt H9 xres s10))
    (fun xargs w s11 H10 hp10 ⟨oa, hw, hba⟩ => ?_)
  subst hw
  have hpH10 : H <+: H10 := hpH9.trans hp10
  have hok10 := ctxOK_H hok H10
  have hcfv10 : BlkAt H10 oc1 (cfv.map Enc.idxW) := blkAt_mono hcfv6 ((hp7.trans hp8).trans (hp9.trans hp10))
  have hxfv10 : BlkAt H10 oc3 (xfv.map Enc.idxW) := blkAt_mono hxfv (hp9.trans hp10)
  refine specR_atEntry fun t10 ht10 => ?_
  have hal := Big.blk_small0 hok10 ht10.sr hba
  have hcl := Big.blk_small0 hok10 ht10.sr hcfv10
  have hxl := Big.blk_small0 hok10 ht10.sr hxfv10
  simp only [List.length_map] at hal hcl hxl
  by_cases hfh : fn = hd
  swap
  · have hne : Enc.idxW fn ≠ Enc.idxW hd := fun e => hfh (Enc.idxW_inj e)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => specR_rejectI)
  subst hfh
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := ctxH C H10) scK (vv scA) oa _ hba.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  by_cases hK : xargs.length = nP + nIdx
  swap
  · have hne : BitVec.ofNat 64 xargs.length ≠ BitVec.ofNat 64 nP + BitVec.ofNat 64 nIdx := by
      rw [BitVec.ofNat_add_ofNat]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => specR_rejectI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hK, BitVec.ofNat_add_ofNat]) (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := ctxH C H10) scLc (vv scCq) oc1 _ hcfv10.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  by_cases hL : cfv.length = nP
  swap
  · have hne : BitVec.ofNat 64 cfv.length ≠ BitVec.ofNat 64 nP := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => specR_rejectI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hL]) (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_pureBind ((xargs.take nP).drop 0 == cfv.drop 0) ?_
  refine specR_callCB (C := ctxH C H10) scR fPrefEq peParams [vv scA, vv scCq, .const 0, vv scP] peBody
    [cellA C oa, cellA C oc1, BitVec.ofNat 64 0, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc.qz.pe
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], trivial⟩
    (callee_of_pre rfl (pe_spec (ctxH C H10) hok10 hc.qz.pe xargs cfv oa oc1 nP (by omega) hL H10 hba hcfv10 _ 0 s11 rfl
      (by omega))) (fun rb2 s12 H11 hp11 hrun => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hrb, hs12⟩ := hrun
  subst hs12
  have hpH11 : H <+: H11 := hpH10.trans hp11
  by_cases hb2 : rb2 = true
  swap
  · have hb2' : rb2 = false := by simpa using hb2
    subst hb2'
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_rejectI) (fun h => absurd h (by decide))
  subst hb2
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  have htk : (List.take nP xargs == cfv) = true := by
    simpa only [List.drop_zero] using hrb
  rw [if_pos (by simp only [beq_self_eq_true, htk, hK, Bool.true_and, beq_self_eq_true])]
  unfold scTail
  have hxfv11 : BlkAt H11 oc3 (xfv.map Enc.idxW) := blkAt_mono hxfv10 hp11
  have hba11 : BlkAt H11 oa (xargs.map Enc.idxW) := blkAt_mono hba hp11
  refine UD.specR_heapLoadI' (C := ctxH C H11) scN (vv scXq) oc3 _ hxfv11.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  have hT := fdrT_spec (σ := σ) C hok hc.cc.crf hc.fdT hc.fs.fvt hc.cc.crff xfv oc3 _ 0 H11 s11 rfl (by omega) hxfv11
  rw [List.drop_zero] at hT
  refine specR_callNIH (C := ctxH C H11) scR fFieldDoms fdrParams [vv scXq, .const 0, vv scN] (fdrBody true)
    [cellA C oc3, BitVec.ofNat 64 0, BitVec.ofNat 64 xfv.length] (by decide) rfl (by decide) hc.fdT
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H11)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fdrParams _ rfl hlk) hT)
    (fun b w s13 H12 hp12 hw => ?_)
  subst hw
  refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  have hba12 : BlkAt H12 oa (xargs.map Enc.idxW) := blkAt_mono hba11 hp12
  refine specR_callNIH (C := ctxH C H12) scR fIdxArgs fdrParams [vv scA, vv scP, vv scK] (fdrBody false)
    [cellA C oa, BitVec.ofNat 64 nP, BitVec.ofNat 64 xargs.length] (by decide) rfl (by decide) hc.fdI
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H12)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fdrParams _ rfl hlk)
      (fdrI_spec C hok hc.cc.crf hc.fdI hc.cc.crff xargs oa _ nP H12 s13 rfl (by omega) hba12))
    (fun b2 w s14 H13 hp13 hw => ?_)
  subst hw
  refine specR_failIteF (c := b2) _ (boolW (!b2)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b2)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  have hpH13 : H <+: H13 := (hpH11.trans hp12).trans hp13
  refine specR_congr (m' := checkStructFieldSortsI mode C.fe isProp large resSort nP xfv (List.drop nP xargs) nF >>=
    fun _ => pure ()) (by simp) ?_
  refine specR_callNIH (C := ctxH C H13) scR fFieldSorts fsParams
    [vv scXq, vv scA, vv scP, vv scS, vv scP, vv scIp, vv scLg, vv scF] (fsBody C)
    [cellA C oc3, cellA C oa, BitVec.ofNat 64 nP, Enc.idxW resSort, BitVec.ofNat 64 nP, boolW isProp, boolW large,
      BitVec.ofNat 64 nF] (by decide) rfl (by decide) hc.fs.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scParams, ctxEnv],
      trivial⟩
    (Decl.PostU (ctxH C H13)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fsParams _ rfl hlk)
      (fs_spec mode ra C hok hs hc.cc.k hc.cc.ac hc.fs heqS isProp large resSort lsr hSd nP xfv xargs nP (by omega)
        oc3 oa nF H13 s14 (by omega) (hp.trans hpH13) (blkAt_mono hxfv11 (hp12.trans hp13)) (blkAt_mono hba12 hp13)))
    (fun _ w s15 H14 hp14 _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H14, hpH13.trans hp14, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `checkSumCtors` -/

def scsC := ofString "scs_c"
def scsI := ofString "scs_i"
def scsN := ofString "scs_n"
def scsTa := ofString "scs_ta"
def scsL := ofString "scs_l"
def scsP := ofString "scs_p"
def scsNI := ofString "scs_ni"
def scsS := ofString "scs_s"
def scsIp := ofString "scs_ip"
def scsLg := ofString "scs_lg"
def scsO := ofString "scs_o"
def scsF := ofString "scs_f"
def scsR := ofString "scs_r"
def fSumCtors := ofString "checkSumCtors"

def scsParams : List MlS := [scsC, scsI, scsN, scsTa, scsL, scsP, scsNI, scsS, scsIp, scsLg]
def scsLocals : List MlS := [scsO, scsF, scsR]

def scsBody : ProgHOL 64 := prologue scsLocals
  (.ite (.cmp .lower (vv scsI) (vv scsN))
    (.seq (.assign .local scsO (.load .one (.op .add [vv scsC, .op .add [.panop .mul [vv scsI, .const 16], .const 8]])))
    (.seq (.assign .local scsF (.load .one (.op .add [vv scsC, .op .add [.panop .mul [vv scsI, .const 16], .const 16]])))
    (.seq (.call (some (some (.local, scsR), none)) fSumCtor
        [vv scsO, vv scsF, vv scsTa, vv scsL, vv scsP, vv scsNI, vv scsS, vv scsIp, vv scsLg])
    (.seq (.call (some (some (.local, scsR), none)) fSumCtors
        [vv scsC, .op .add [vv scsI, .const 1], vv scsN, vv scsTa, vv scsL, vv scsP, vv scsNI, vv scsS, vv scsIp, vv scsLg])
      (.return (.const 0))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem scs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ scsLocals → (ctxEnv C ++ scsParams.zip vals).get x = none :=
  Knot.params_none C scsLocals scsParams vals (by decide) (by decide)

theorem cellA_pair1 (C : Ctx) (o i : Nat) (hi : i < 2 ^ 59) :
    cellA C o + (BitVec.ofNat 64 i * 16#64 + 8#64) = cellA C (o + 1 + 2 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem cellA_pair2 (C : Ctx) (o i : Nat) (hi : i < 2 ^ 59) :
    cellA C o + (BitVec.ofNat 64 i * 16#64 + 16#64) = cellA C (o + 2 + 2 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

/-- The per-constructor side conditions `checkSumCtor` needs. -/
def SumCtorOK (C : Ctx) (nP : Nat) (c : IConstantVal × Nat) : Prop :=
  nP + c.2 < 2 ^ 56 ∧ c.1.levelParams.length < 2 ^ 62 ∧ ∃ ks : List ConLeche.Name,
    ks.length = c.1.levelParams.length ∧ ∀ j (hj : j < c.1.levelParams.length), denoteN C.St.ns c.1.levelParams[j] = ks[j]?

theorem checkSumCtors_drop (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (resSort : LIdx) (isProp large : Bool) (cvTa : IConstantVal) (cs : List (IConstantVal × Nat)) (i : Nat)
    (hi : i < cs.length) :
    checkSumCtors mode fe₀ fe T lps nP nIdx resSort isProp large cvTa (cs.drop i) =
      (do checkSumCtor mode fe₀ fe T lps nP nIdx resSort isProp large cs[i].1 cs[i].2 cvTa
          checkSumCtors mode fe₀ fe T lps nP nIdx resSort isProp large cvTa (cs.drop (i + 1))) := by
  rw [List.drop_eq_getElem_cons hi]; rfl

set_option maxHeartbeats 4000000 in
/-- **`checkSumCtors`** from position `i`. -/
theorem scs_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : SCCodes mode C)
    (hcs : C.code.lookup fSumCtor = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody C, .one))
    (hcl : C.code.lookup fSumCtors = some (scsParams.map (fun p => (p, ShapeHOL.one)), scsBody, .one))
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls resSort = some lsr)
    (isProp large : Bool) (cvTa : IConstantVal) (cs : List (IConstantVal × Nat))
    (hni : nIdx < 2 ^ 56) (hlp : lps.length < 2 ^ 59) (hcsl : cs.length < 2 ^ 58)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (oq ot ol : Nat) (hcr : CtorsRep C H0 oq cs) (hta : CVRep C H0 ot cvTa)
    (hbl : EBlk H0 ol (lps.map Enc.idxW)) (hct : ∀ i (hi : i < cs.length), SumCtorOK C nP cs[i]) :
    ∀ f i (H : List (BitVec 64)) (s : AState), cs.length - i = f → i ≤ cs.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (scsParams.zip [cellA C oq, BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length,
          cellA C ot, cellA C ol, BitVec.ofNat 64 nP, BitVec.ofNat 64 nIdx, Enc.idxW resSort, boolW isProp, boolW large]))
        scsBody s (checkSumCtors mode C.fe C.fe cvTa.name lps nP nIdx resSort isProp large cvTa (cs.drop i))
        (Decl.PostU (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hpH
    have hin : i = cs.length := by omega
    subst hin
    refine specR_prologue (Decl.postU_locals _) (scs_none _ _) ?_
    have hlw := nd_lt_iff cs.length cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, scsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hpH
    have hin : i < cs.length := by omega
    refine specR_prologue (Decl.postU_locals _) (scs_none _ _) ?_
    have hlw := nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, scsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, hoc, hcv, hnf⟩ := hcr.2 i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) scsO _ (oq + 1 + 2 * i) _ (get_prefix hoc hpH) (by decide)
      (by simp +decide [sev, Env.get, scsParams, ctxEnv]; exact cellA_pair1 C oq i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) scsF _ (oq + 2 + 2 * i) _ (get_prefix hnf.1 hpH) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv]; exact cellA_pair2 C oq i (by omega)) ?_
    rw [checkSumCtors_drop _ _ _ _ _ _ _ _ _ _ _ _ _ hin]
    obtain ⟨hb1, hlen1, ks, hkl, hks⟩ := hct i hin
    refine specR_callNIH (C := ctxH C H) scsR fSumCtor scParams
      [vv scsO, vv scsF, vv scsTa, vv scsL, vv scsP, vv scsNI, vv scsS, vv scsIp, vv scsLg] (scBody C)
      [cellA C oc, BitVec.ofNat 64 cs[i].2, cellA C ot, cellA C ol, BitVec.ofNat 64 nP, BitVec.ofNat 64 nIdx,
        Enc.idxW resSort, boolW isProp, boolW large] (by decide) rfl (by decide) hcs
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu scParams _ rfl hlk)
        (sc_spec mode ra C hok hs hc heqS lps nP nIdx resSort lsr hSd isProp large cs[i].1 cs[i].2 cvTa hb1 hni hlp
          H (hp0.trans hpH) oc ot ol (cve_mono hpH hcv) (cve_mono hpH hta) (eblk_mono hbl hpH) hlen1 ks hkl
          (fun j hj => by rw [hks j hj, List.getElem?_eq_getElem (by omega)]) s))
      (fun _ w s1 H1 hp1 _ => ?_)
    refine specR_congr (m' := checkSumCtors mode C.fe C.fe cvTa.name lps nP nIdx resSort isProp large cvTa (cs.drop (i + 1))
      >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) scsR fSumCtors scsParams
      [vv scsC, .op .add [vv scsI, .const 1], vv scsN, vv scsTa, vv scsL, vv scsP, vv scsNI, vv scsS, vv scsIp, vv scsLg]
      scsBody [cellA C oq, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length, cellA C ot, cellA C ol, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 nIdx, Enc.idxW resSort, boolW isProp, boolW large] (by decide) rfl (by decide) hcl
      ⟨by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, scsParams, ctxEnv],
        trivial⟩
      (Decl.PostU (ctxH C H1)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu scsParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hpH.trans hp1)))
      (fun _ w s2 H2 hp2 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp1.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
end

end ConPanqueque.T.Ind
