import ConPanqueque.T.Ind.OpenFvars
import ConPanqueque.T.Ind.IotaCtor
import ConPanqueque.T.Ind.CtorMember
import ConPanqueque.T.Ind.IotaPartsAt
import ConRon.Arena.Inductives.StructParts

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

end ConPanqueque.T.Ind
