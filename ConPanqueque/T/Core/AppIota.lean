import ConPanqueque.T.Core.Beta
import ConRon.Bridge.ExprOps.Subst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfAppIota`: ι at the spine accumulated so far

At a stored recursor head with its own number of levels, applied to exactly `mI + 1` arguments: `iotaRecAt` on
them (the same function `whnfStuck` calls, its argument block taken whole).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def qA := ofString "wqa"
def qN := ofString "wqn"
def qR := ofString "wqr"
def fWai := ofString "whnfAppIota"

@[simp] theorem wq_qA_ne_qN : qA ≠ qN := by decide
@[simp] theorem wq_qA_ne_qR : qA ≠ qR := by decide
@[simp] theorem wq_qA_ne_lFl : qA ≠ lFl := by decide
@[simp] theorem wq_lFl_ne_qA : lFl ≠ qA := by decide
@[simp] theorem wq_qA_ne_lDh : qA ≠ lDh := by decide
@[simp] theorem wq_lDh_ne_qA : lDh ≠ qA := by decide
@[simp] theorem wq_qA_ne_lDt : qA ≠ lDt := by decide
@[simp] theorem wq_lDt_ne_qA : lDt ≠ qA := by decide
@[simp] theorem wq_qA_ne_lDg : qA ≠ lDg := by decide
@[simp] theorem wq_lDg_ne_qA : lDg ≠ qA := by decide
@[simp] theorem wq_qA_ne_lDi : qA ≠ lDi := by decide
@[simp] theorem wq_lDi_ne_qA : lDi ≠ qA := by decide
@[simp] theorem wq_qA_ne_lRp : qA ≠ lRp := by decide
@[simp] theorem wq_lRp_ne_qA : lRp ≠ qA := by decide
@[simp] theorem wq_qA_ne_lRn : qA ≠ lRn := by decide
@[simp] theorem wq_lRn_ne_qA : lRn ≠ qA := by decide
@[simp] theorem wq_qA_ne_kFu : qA ≠ kFu := by decide
@[simp] theorem wq_kFu_ne_qA : kFu ≠ qA := by decide
@[simp] theorem wq_qA_ne_kD : qA ≠ kD := by decide
@[simp] theorem wq_kD_ne_qA : kD ≠ qA := by decide
@[simp] theorem wq_qA_ne_sH : qA ≠ sH := by decide
@[simp] theorem wq_sH_ne_qA : sH ≠ qA := by decide
@[simp] theorem wq_qA_ne_lFle : qA ≠ lFle := by decide
@[simp] theorem wq_lFle_ne_qA : lFle ≠ qA := by decide
@[simp] theorem wq_qA_ne_lFls : qA ≠ lFls := by decide
@[simp] theorem wq_lFls_ne_qA : lFls ≠ qA := by decide
@[simp] theorem wq_qA_ne_lDir : qA ≠ lDir := by decide
@[simp] theorem wq_lDir_ne_qA : lDir ≠ qA := by decide
@[simp] theorem wq_qA_ne_lKb : qA ≠ lKb := by decide
@[simp] theorem wq_lKb_ne_qA : lKb ≠ qA := by decide
@[simp] theorem wq_qA_ne_tC : qA ≠ tC := by decide
@[simp] theorem wq_tC_ne_qA : tC ≠ qA := by decide
@[simp] theorem wq_qA_ne_tU : qA ≠ tU := by decide
@[simp] theorem wq_tU_ne_qA : tU ≠ qA := by decide
@[simp] theorem wq_qA_ne_tW : qA ≠ tW := by decide
@[simp] theorem wq_tW_ne_qA : tW ≠ qA := by decide
@[simp] theorem wq_qA_ne_tQ : qA ≠ tQ := by decide
@[simp] theorem wq_tQ_ne_qA : tQ ≠ qA := by decide
@[simp] theorem wq_qA_ne_tT : qA ≠ tT := by decide
@[simp] theorem wq_tT_ne_qA : tT ≠ qA := by decide
@[simp] theorem wq_qA_ne_tLp : qA ≠ tLp := by decide
@[simp] theorem wq_tLp_ne_qA : tLp ≠ qA := by decide
@[simp] theorem wq_qA_ne_tLl : qA ≠ tLl := by decide
@[simp] theorem wq_tLl_ne_qA : tLl ≠ qA := by decide
@[simp] theorem wq_qA_ne_tM : qA ≠ tM := by decide
@[simp] theorem wq_tM_ne_qA : tM ≠ qA := by decide
@[simp] theorem wq_qA_ne_tO : qA ≠ tO := by decide
@[simp] theorem wq_tO_ne_qA : tO ≠ qA := by decide
@[simp] theorem wq_qN_ne_qA : qN ≠ qA := by decide
@[simp] theorem wq_qN_ne_qR : qN ≠ qR := by decide
@[simp] theorem wq_qN_ne_lFl : qN ≠ lFl := by decide
@[simp] theorem wq_lFl_ne_qN : lFl ≠ qN := by decide
@[simp] theorem wq_qN_ne_lDh : qN ≠ lDh := by decide
@[simp] theorem wq_lDh_ne_qN : lDh ≠ qN := by decide
@[simp] theorem wq_qN_ne_lDt : qN ≠ lDt := by decide
@[simp] theorem wq_lDt_ne_qN : lDt ≠ qN := by decide
@[simp] theorem wq_qN_ne_lDg : qN ≠ lDg := by decide
@[simp] theorem wq_lDg_ne_qN : lDg ≠ qN := by decide
@[simp] theorem wq_qN_ne_lDi : qN ≠ lDi := by decide
@[simp] theorem wq_lDi_ne_qN : lDi ≠ qN := by decide
@[simp] theorem wq_qN_ne_lRp : qN ≠ lRp := by decide
@[simp] theorem wq_lRp_ne_qN : lRp ≠ qN := by decide
@[simp] theorem wq_qN_ne_lRn : qN ≠ lRn := by decide
@[simp] theorem wq_lRn_ne_qN : lRn ≠ qN := by decide
@[simp] theorem wq_qN_ne_kFu : qN ≠ kFu := by decide
@[simp] theorem wq_kFu_ne_qN : kFu ≠ qN := by decide
@[simp] theorem wq_qN_ne_kD : qN ≠ kD := by decide
@[simp] theorem wq_kD_ne_qN : kD ≠ qN := by decide
@[simp] theorem wq_qN_ne_sH : qN ≠ sH := by decide
@[simp] theorem wq_sH_ne_qN : sH ≠ qN := by decide
@[simp] theorem wq_qN_ne_lFle : qN ≠ lFle := by decide
@[simp] theorem wq_lFle_ne_qN : lFle ≠ qN := by decide
@[simp] theorem wq_qN_ne_lFls : qN ≠ lFls := by decide
@[simp] theorem wq_lFls_ne_qN : lFls ≠ qN := by decide
@[simp] theorem wq_qN_ne_lDir : qN ≠ lDir := by decide
@[simp] theorem wq_lDir_ne_qN : lDir ≠ qN := by decide
@[simp] theorem wq_qN_ne_lKb : qN ≠ lKb := by decide
@[simp] theorem wq_lKb_ne_qN : lKb ≠ qN := by decide
@[simp] theorem wq_qN_ne_tC : qN ≠ tC := by decide
@[simp] theorem wq_tC_ne_qN : tC ≠ qN := by decide
@[simp] theorem wq_qN_ne_tU : qN ≠ tU := by decide
@[simp] theorem wq_tU_ne_qN : tU ≠ qN := by decide
@[simp] theorem wq_qN_ne_tW : qN ≠ tW := by decide
@[simp] theorem wq_tW_ne_qN : tW ≠ qN := by decide
@[simp] theorem wq_qN_ne_tQ : qN ≠ tQ := by decide
@[simp] theorem wq_tQ_ne_qN : tQ ≠ qN := by decide
@[simp] theorem wq_qN_ne_tT : qN ≠ tT := by decide
@[simp] theorem wq_tT_ne_qN : tT ≠ qN := by decide
@[simp] theorem wq_qN_ne_tLp : qN ≠ tLp := by decide
@[simp] theorem wq_tLp_ne_qN : tLp ≠ qN := by decide
@[simp] theorem wq_qN_ne_tLl : qN ≠ tLl := by decide
@[simp] theorem wq_tLl_ne_qN : tLl ≠ qN := by decide
@[simp] theorem wq_qN_ne_tM : qN ≠ tM := by decide
@[simp] theorem wq_tM_ne_qN : tM ≠ qN := by decide
@[simp] theorem wq_qN_ne_tO : qN ≠ tO := by decide
@[simp] theorem wq_tO_ne_qN : tO ≠ qN := by decide
@[simp] theorem wq_qR_ne_qA : qR ≠ qA := by decide
@[simp] theorem wq_qR_ne_qN : qR ≠ qN := by decide
@[simp] theorem wq_qR_ne_lFl : qR ≠ lFl := by decide
@[simp] theorem wq_lFl_ne_qR : lFl ≠ qR := by decide
@[simp] theorem wq_qR_ne_lDh : qR ≠ lDh := by decide
@[simp] theorem wq_lDh_ne_qR : lDh ≠ qR := by decide
@[simp] theorem wq_qR_ne_lDt : qR ≠ lDt := by decide
@[simp] theorem wq_lDt_ne_qR : lDt ≠ qR := by decide
@[simp] theorem wq_qR_ne_lDg : qR ≠ lDg := by decide
@[simp] theorem wq_lDg_ne_qR : lDg ≠ qR := by decide
@[simp] theorem wq_qR_ne_lDi : qR ≠ lDi := by decide
@[simp] theorem wq_lDi_ne_qR : lDi ≠ qR := by decide
@[simp] theorem wq_qR_ne_lRp : qR ≠ lRp := by decide
@[simp] theorem wq_lRp_ne_qR : lRp ≠ qR := by decide
@[simp] theorem wq_qR_ne_lRn : qR ≠ lRn := by decide
@[simp] theorem wq_lRn_ne_qR : lRn ≠ qR := by decide
@[simp] theorem wq_qR_ne_kFu : qR ≠ kFu := by decide
@[simp] theorem wq_kFu_ne_qR : kFu ≠ qR := by decide
@[simp] theorem wq_qR_ne_kD : qR ≠ kD := by decide
@[simp] theorem wq_kD_ne_qR : kD ≠ qR := by decide
@[simp] theorem wq_qR_ne_sH : qR ≠ sH := by decide
@[simp] theorem wq_sH_ne_qR : sH ≠ qR := by decide
@[simp] theorem wq_qR_ne_lFle : qR ≠ lFle := by decide
@[simp] theorem wq_lFle_ne_qR : lFle ≠ qR := by decide
@[simp] theorem wq_qR_ne_lFls : qR ≠ lFls := by decide
@[simp] theorem wq_lFls_ne_qR : lFls ≠ qR := by decide
@[simp] theorem wq_qR_ne_lDir : qR ≠ lDir := by decide
@[simp] theorem wq_lDir_ne_qR : lDir ≠ qR := by decide
@[simp] theorem wq_qR_ne_lKb : qR ≠ lKb := by decide
@[simp] theorem wq_lKb_ne_qR : lKb ≠ qR := by decide
@[simp] theorem wq_qR_ne_tC : qR ≠ tC := by decide
@[simp] theorem wq_tC_ne_qR : tC ≠ qR := by decide
@[simp] theorem wq_qR_ne_tU : qR ≠ tU := by decide
@[simp] theorem wq_tU_ne_qR : tU ≠ qR := by decide
@[simp] theorem wq_qR_ne_tW : qR ≠ tW := by decide
@[simp] theorem wq_tW_ne_qR : tW ≠ qR := by decide
@[simp] theorem wq_qR_ne_tQ : qR ≠ tQ := by decide
@[simp] theorem wq_tQ_ne_qR : tQ ≠ qR := by decide
@[simp] theorem wq_qR_ne_tT : qR ≠ tT := by decide
@[simp] theorem wq_tT_ne_qR : tT ≠ qR := by decide
@[simp] theorem wq_qR_ne_tLp : qR ≠ tLp := by decide
@[simp] theorem wq_tLp_ne_qR : tLp ≠ qR := by decide
@[simp] theorem wq_qR_ne_tLl : qR ≠ tLl := by decide
@[simp] theorem wq_tLl_ne_qR : tLl ≠ qR := by decide
@[simp] theorem wq_qR_ne_tM : qR ≠ tM := by decide
@[simp] theorem wq_tM_ne_qR : tM ≠ qR := by decide
@[simp] theorem wq_qR_ne_tO : qR ≠ tO := by decide
@[simp] theorem wq_tO_ne_qR : tO ≠ qR := by decide

def waiParams : List MlS := [kFu, kD, sH, qA, qN]
def waiLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, tC, tU, tW, tQ, tT, tLp, tLl, tM, tO]

def waiNone : ProgHOL 64 := .return (.const 0)

def waiCore (C : Ctx) : ProgHOL 64 :=
  .ite (tagIsE sH 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv sH)) (.seq eViewP
    (.seq (.assign .local tC (.load .one (vv lRp))) (.seq (.assign .local tU (.load .one (.op .add [vv lRp, .const 8])))
    (envFindP C tW (vv tC)
    (.ite (.cmp .equal (vv tW) (.const 0)) waiNone
    (.seq (.assign .local tQ (.op .sub [vv tW, .const 1])) (.seq (.assign .local tT (.load .one (vv tQ)))
    (.ite (.cmp .notEqual (vv tT) (.const 5)) waiNone
    (.seq (.assign .local tM (.load .one (.op .add [vv tQ, .const 32])))
    (.ite (.cmp .notEqual (vv qN) (.op .add [vv tM, .const 1])) waiNone
    (.seq (.assign .local tLp (.load .one (.op .add [vv tQ, .const 16])))
    (.seq (.assign .local tLl (.load .one (vv tLp)))
    (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv tU)) (.seq lsViewP
    (.ite (.cmp .notEqual (vv lRn) (vv tLl)) waiNone
    (.seq (.call (some (some (.local, tO), none)) fIota [vv kFu, vv kD, vv tC, vv tU, vv tQ, vv qA, vv qN])
      (.return (vv tO)))))))))))))))))))))
    waiNone

def waiBody (C : Ctx) : ProgHOL 64 := prologue waiLocals (waiCore C)

theorem takeEidx_self (xs : Array EIdx) : takeEidx xs xs.size = xs := by
  apply Array.ext'
  rw [ConRon.Bridge.ExprOps.takeEidx_toList, ← Array.length_toList, List.take_length]


section
variable {σ : Type}

theorem wai_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ waiLocals → (ctxEnv C ++ waiParams.zip vals).get x = none :=
  Knot.params_none C waiLocals waiParams vals (by decide) (by decide)

theorem wai_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (Bio : ProgHOL 64)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcio : C.code.lookup fIota = some (ioParams.map (fun p => (p, ShapeHOL.one)), Bio, .one))
    (s : AState) (d : Nat) (hd : EIdx) (va : Array EIdx) (o : Nat) (hblk : BlkAt C.H o (va.toList.map Enc.idxW))
    (hsz : va.size < 2 ^ 63)
    (hIota : ∀ (sargs : List EIdx) c us q cv mI rP isK rules,
      BlkAt C.H o (sargs.map Enc.idxW) → C.fe.find? c = some (.recInfo cv mI rP isK rules) →
      CIE C.EB C.EH q (.recInfo cv mI rP isK rules) → mI + 1 ≤ sargs.length →
      SpecR (σ := σ) (Pre C s (ioParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW us,
        ecell C q, cellA C o, BitVec.ofNat 64 (mI + 1)])) Bio s
        (iotaRecAt mode (knot mode C n) C.fe d c us cv mI rP isK rules (takeEidx sargs.toArray (mI + 1)))
        (UD.PostO C)) :
    SpecR (σ := σ) (Pre C s (waiParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW hd, cellA C o,
      BitVec.ofNat 64 va.size])) (waiBody C) s (whnfAppIota mode (knot mode C n) C.fe d hd va va.size) (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (wai_none C _) ?_
  unfold waiCore whnfAppIota
  have hnone : ∀ {s' : AState} {Γ : Env} {M : Mem} {D : List MlS},
      SpecR (σ := σ) (Inv C s' Γ M D) waiNone s' (pure none) (UD.PostO C) :=
    fun {s' Γ M D} => specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV sH hd 3 (by decide) (by decide) (by simp +decide [Env.get, waiParams, ctxEnv])
    (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hd.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    exact hnone
  rw [ite_eq_left (show (hd.tag == ETag.const) = true by simp [htg, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv sH) (Enc.idxW hd) (by decide) (by simp +decide [Env.get, waiParams, ctxEnv]) ?_
  refine specR_viewP hd (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  have hvc : s.store.viewConst hd = some (c, us) := viewConst_of_view (by rw [htg]; rfl) hv
  refine specR_runBind (by rw [viewConst_run, hvc]) ?_
  refine specR_loadI' tC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_loadI' tU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
  refine specR_dropM ?_
  refine specR_envFindI hok hcodeG hcodeP tW (vv tC) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv]) ?_
  have hrel := find_rel hok c
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel
    rw [hrel]; simp only [hfind]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hnone
  intro ⟨q, hm, hci⟩
  rw [hm]; simp only [hfind]
  refine specR_atEntry fun t ht => ?_
  have hoE : q < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI tQ _ (ecell C q) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C q) ?_
  refine specR_envLoadI tT (vv tQ) q _ (by decide) (by simp) (UD.cie_tag hci) ?_
  cases ci with
  | recInfo cv mI rP isK rules =>
    refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    have hci' := hci
    obtain ⟨⟨_, ⟨w, hw, o', hw', hblk'⟩, _⟩, _, hmi, _⟩ := hci
    subst hw'
    refine specR_envLoadI tM (.op .add [vv tQ, .const 32]) (q + 4) _ (by decide)
      (by simp [sev, vv]; exact UD.ecell_add32 C q) hmi.1 ?_
    have hmi63 := hmi.2
    have hadd : BitVec.ofNat 64 mI + 1#64 = BitVec.ofNat 64 (mI + 1) := word_add1_eq mI
    have heqw : BitVec.ofNat 64 va.size = BitVec.ofNat 64 (mI + 1) ↔ va.size = mI + 1 :=
      UD.ofNat_eq_iff_small _ _ (by omega) (by omega)
    dsimp only
    by_cases hn : va.size = mI + 1
    · rw [ite_eq_right (by simpa using hn)]
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, waiParams, ctxEnv, hadd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, heqw.mpr hn])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_envLoadI tLp (.op .add [vv tQ, .const 16]) (q + 2) _ (by decide)
        (by simp [sev, vv]; exact UD.ecell_add16 C q) (by simpa using hw) ?_
      have hl0 : C.EH[o']? = some (BitVec.ofNat 64 cv.levelParams.length) := by
        have := hblk'.1; simpa [IConstantInfo.toConstantVal] using this
      refine specR_envLoadI tLl (vv tLp) o' _ (by decide) (by simp; rfl) hl0 ?_
      refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, waiParams, ctxEnv]) ?_
      refine specR_assignI lDh (vv tU) (Enc.idxW us) (by decide) (by simp) ?_
      refine specR_lsviewPI us (by simp) (by simp) (by simp +decide [Env.get, waiParams, ctxEnv]) (by decide)
        (fun vl Pl hvl _ hvll => ?_)
      refine specR_runBind (viewLsLen_run us s vl hvl) ?_
      dsimp only
      have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
      have hlp : cv.levelParams.length < 2 ^ 61 := by
        have h1 := blkAt_len (show BlkAt C.EH o' (cv.levelParams.map Enc.idxW) from hblk')
        have h2 := ht.sr.env.1.len; have h3 := hok.envLay
        simp only [List.length_map] at h1; omega
      by_cases hl : vl.length = cv.levelParams.length
      · rw [ite_eq_right (by simpa using hl)]
        refine specR_ifI _ 0 (by simp [sev, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
          (fun _ => ?_)
        refine specR_dropM ?_
        have hta : takeEidx va.toList.toArray (mI + 1) = va := by rw [← hn]; simpa using takeEidx_self va
        refine specR_congr (m' := iotaRecAt mode (knot mode C n) C.fe d c us cv mI rP isK rules
          (takeEidx va.toList.toArray (mI + 1)) >>= fun r => pure r) (by rw [hta]; simp) ?_
        refine specR_callNIH tO fIota ioParams [vv kFu, vv kD, vv tC, vv tU, vv tQ, vv qA, vv qN] Bio
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW us, ecell C q, cellA C o,
            BitVec.ofNat 64 (mI + 1)] (by decide) rfl (by decide) hcio
          ⟨by simp +decide [Env.get, waiParams, ctxEnv], by simp +decide [Env.get, waiParams, ctxEnv], by simp,
            by simp, by simp, by simp +decide [Env.get, waiParams, ctxEnv],
            by simp +decide [Env.get, waiParams, ctxEnv]; rw [hn], trivial⟩
          (UD.PostO C) (fun r w _ _ => w = optW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ioParams _ rfl hlk)
            (hIota va.toList c us q cv mI rP isK rules (by simpa using hblk) hfind hci' (by simp; omega)))
          (fun r w s3 H3 hp3 hw => ?_)
        subst hw
        exact specR_returnI _ (optW r) (by simp) (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · rw [ite_eq_left (by simpa using hl)]
        have hne : BitVec.ofNat 64 vl.length ≠ BitVec.ofNat 64 cv.levelParams.length := fun x =>
          hl ((UD.ofNat_eq_iff_small _ _ (by omega) (by omega)).mp x)
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        exact hnone
    · rw [ite_eq_left (by simpa using hn)]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, waiParams, ctxEnv, hadd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        (not_congr heqw).mpr hn]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact hnone
  | _ =>
    refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hnone

end

end ConPanqueque.T.WC
