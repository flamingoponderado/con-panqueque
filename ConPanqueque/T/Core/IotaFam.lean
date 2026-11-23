import ConPanqueque.T.Core.IotaPins
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The ι fire certificate (`iotaFam`) and its read-only gate `iotaNoCert`

`iotaNoCert`: a K recursor, or a constructor family (the `indInfo` at `induct`) recording a never-zero sort with
as many level parameters as the rule's comparand levels (`recFireLevelCount`). A pure function of the
environment; the port reads the stored records.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConPanqueque.T.CV (prefix_fillI blk_of_fillI mul8_eq)

def ncK := ofString "nck"
def ncI := ofString "nci"
def ncR := ofString "ncr"
def ncJs := ofString "ncjs"
def ncW := ofString "ncw"
def ncQ := ofString "ncq"
def ncT := ofString "nct"
def ncZ := ofString "ncz"
def ncLp := ofString "nclp"
def ncLl := ofString "ncll"
def ncF := ofString "ncf"
def ncN := ofString "ncn"
def ncV := ofString "ncv"
def fNc := ofString "iotaNoCert"

@[simp] theorem nc_ncK_ne_ncI : ncK ≠ ncI := by decide
@[simp] theorem nc_ncK_ne_ncR : ncK ≠ ncR := by decide
@[simp] theorem nc_ncK_ne_ncJs : ncK ≠ ncJs := by decide
@[simp] theorem nc_ncK_ne_ncW : ncK ≠ ncW := by decide
@[simp] theorem nc_ncK_ne_ncQ : ncK ≠ ncQ := by decide
@[simp] theorem nc_ncK_ne_ncT : ncK ≠ ncT := by decide
@[simp] theorem nc_ncK_ne_ncZ : ncK ≠ ncZ := by decide
@[simp] theorem nc_ncK_ne_ncLp : ncK ≠ ncLp := by decide
@[simp] theorem nc_ncK_ne_ncLl : ncK ≠ ncLl := by decide
@[simp] theorem nc_ncK_ne_ncF : ncK ≠ ncF := by decide
@[simp] theorem nc_ncK_ne_ncN : ncK ≠ ncN := by decide
@[simp] theorem nc_ncK_ne_ncV : ncK ≠ ncV := by decide
@[simp] theorem nc_ncK_ne_lKb : ncK ≠ lKb := by decide
@[simp] theorem nc_ncI_ne_ncK : ncI ≠ ncK := by decide
@[simp] theorem nc_ncI_ne_ncR : ncI ≠ ncR := by decide
@[simp] theorem nc_ncI_ne_ncJs : ncI ≠ ncJs := by decide
@[simp] theorem nc_ncI_ne_ncW : ncI ≠ ncW := by decide
@[simp] theorem nc_ncI_ne_ncQ : ncI ≠ ncQ := by decide
@[simp] theorem nc_ncI_ne_ncT : ncI ≠ ncT := by decide
@[simp] theorem nc_ncI_ne_ncZ : ncI ≠ ncZ := by decide
@[simp] theorem nc_ncI_ne_ncLp : ncI ≠ ncLp := by decide
@[simp] theorem nc_ncI_ne_ncLl : ncI ≠ ncLl := by decide
@[simp] theorem nc_ncI_ne_ncF : ncI ≠ ncF := by decide
@[simp] theorem nc_ncI_ne_ncN : ncI ≠ ncN := by decide
@[simp] theorem nc_ncI_ne_ncV : ncI ≠ ncV := by decide
@[simp] theorem nc_ncI_ne_lKb : ncI ≠ lKb := by decide
@[simp] theorem nc_ncR_ne_ncK : ncR ≠ ncK := by decide
@[simp] theorem nc_ncR_ne_ncI : ncR ≠ ncI := by decide
@[simp] theorem nc_ncR_ne_ncJs : ncR ≠ ncJs := by decide
@[simp] theorem nc_ncR_ne_ncW : ncR ≠ ncW := by decide
@[simp] theorem nc_ncR_ne_ncQ : ncR ≠ ncQ := by decide
@[simp] theorem nc_ncR_ne_ncT : ncR ≠ ncT := by decide
@[simp] theorem nc_ncR_ne_ncZ : ncR ≠ ncZ := by decide
@[simp] theorem nc_ncR_ne_ncLp : ncR ≠ ncLp := by decide
@[simp] theorem nc_ncR_ne_ncLl : ncR ≠ ncLl := by decide
@[simp] theorem nc_ncR_ne_ncF : ncR ≠ ncF := by decide
@[simp] theorem nc_ncR_ne_ncN : ncR ≠ ncN := by decide
@[simp] theorem nc_ncR_ne_ncV : ncR ≠ ncV := by decide
@[simp] theorem nc_ncR_ne_lKb : ncR ≠ lKb := by decide
@[simp] theorem nc_ncJs_ne_ncK : ncJs ≠ ncK := by decide
@[simp] theorem nc_ncJs_ne_ncI : ncJs ≠ ncI := by decide
@[simp] theorem nc_ncJs_ne_ncR : ncJs ≠ ncR := by decide
@[simp] theorem nc_ncJs_ne_ncW : ncJs ≠ ncW := by decide
@[simp] theorem nc_ncJs_ne_ncQ : ncJs ≠ ncQ := by decide
@[simp] theorem nc_ncJs_ne_ncT : ncJs ≠ ncT := by decide
@[simp] theorem nc_ncJs_ne_ncZ : ncJs ≠ ncZ := by decide
@[simp] theorem nc_ncJs_ne_ncLp : ncJs ≠ ncLp := by decide
@[simp] theorem nc_ncJs_ne_ncLl : ncJs ≠ ncLl := by decide
@[simp] theorem nc_ncJs_ne_ncF : ncJs ≠ ncF := by decide
@[simp] theorem nc_ncJs_ne_ncN : ncJs ≠ ncN := by decide
@[simp] theorem nc_ncJs_ne_ncV : ncJs ≠ ncV := by decide
@[simp] theorem nc_ncJs_ne_lKb : ncJs ≠ lKb := by decide
@[simp] theorem nc_ncW_ne_ncK : ncW ≠ ncK := by decide
@[simp] theorem nc_ncW_ne_ncI : ncW ≠ ncI := by decide
@[simp] theorem nc_ncW_ne_ncR : ncW ≠ ncR := by decide
@[simp] theorem nc_ncW_ne_ncJs : ncW ≠ ncJs := by decide
@[simp] theorem nc_ncW_ne_ncQ : ncW ≠ ncQ := by decide
@[simp] theorem nc_ncW_ne_ncT : ncW ≠ ncT := by decide
@[simp] theorem nc_ncW_ne_ncZ : ncW ≠ ncZ := by decide
@[simp] theorem nc_ncW_ne_ncLp : ncW ≠ ncLp := by decide
@[simp] theorem nc_ncW_ne_ncLl : ncW ≠ ncLl := by decide
@[simp] theorem nc_ncW_ne_ncF : ncW ≠ ncF := by decide
@[simp] theorem nc_ncW_ne_ncN : ncW ≠ ncN := by decide
@[simp] theorem nc_ncW_ne_ncV : ncW ≠ ncV := by decide
@[simp] theorem nc_ncW_ne_lKb : ncW ≠ lKb := by decide
@[simp] theorem nc_ncQ_ne_ncK : ncQ ≠ ncK := by decide
@[simp] theorem nc_ncQ_ne_ncI : ncQ ≠ ncI := by decide
@[simp] theorem nc_ncQ_ne_ncR : ncQ ≠ ncR := by decide
@[simp] theorem nc_ncQ_ne_ncJs : ncQ ≠ ncJs := by decide
@[simp] theorem nc_ncQ_ne_ncW : ncQ ≠ ncW := by decide
@[simp] theorem nc_ncQ_ne_ncT : ncQ ≠ ncT := by decide
@[simp] theorem nc_ncQ_ne_ncZ : ncQ ≠ ncZ := by decide
@[simp] theorem nc_ncQ_ne_ncLp : ncQ ≠ ncLp := by decide
@[simp] theorem nc_ncQ_ne_ncLl : ncQ ≠ ncLl := by decide
@[simp] theorem nc_ncQ_ne_ncF : ncQ ≠ ncF := by decide
@[simp] theorem nc_ncQ_ne_ncN : ncQ ≠ ncN := by decide
@[simp] theorem nc_ncQ_ne_ncV : ncQ ≠ ncV := by decide
@[simp] theorem nc_ncQ_ne_lKb : ncQ ≠ lKb := by decide
@[simp] theorem nc_ncT_ne_ncK : ncT ≠ ncK := by decide
@[simp] theorem nc_ncT_ne_ncI : ncT ≠ ncI := by decide
@[simp] theorem nc_ncT_ne_ncR : ncT ≠ ncR := by decide
@[simp] theorem nc_ncT_ne_ncJs : ncT ≠ ncJs := by decide
@[simp] theorem nc_ncT_ne_ncW : ncT ≠ ncW := by decide
@[simp] theorem nc_ncT_ne_ncQ : ncT ≠ ncQ := by decide
@[simp] theorem nc_ncT_ne_ncZ : ncT ≠ ncZ := by decide
@[simp] theorem nc_ncT_ne_ncLp : ncT ≠ ncLp := by decide
@[simp] theorem nc_ncT_ne_ncLl : ncT ≠ ncLl := by decide
@[simp] theorem nc_ncT_ne_ncF : ncT ≠ ncF := by decide
@[simp] theorem nc_ncT_ne_ncN : ncT ≠ ncN := by decide
@[simp] theorem nc_ncT_ne_ncV : ncT ≠ ncV := by decide
@[simp] theorem nc_ncT_ne_lKb : ncT ≠ lKb := by decide
@[simp] theorem nc_ncZ_ne_ncK : ncZ ≠ ncK := by decide
@[simp] theorem nc_ncZ_ne_ncI : ncZ ≠ ncI := by decide
@[simp] theorem nc_ncZ_ne_ncR : ncZ ≠ ncR := by decide
@[simp] theorem nc_ncZ_ne_ncJs : ncZ ≠ ncJs := by decide
@[simp] theorem nc_ncZ_ne_ncW : ncZ ≠ ncW := by decide
@[simp] theorem nc_ncZ_ne_ncQ : ncZ ≠ ncQ := by decide
@[simp] theorem nc_ncZ_ne_ncT : ncZ ≠ ncT := by decide
@[simp] theorem nc_ncZ_ne_ncLp : ncZ ≠ ncLp := by decide
@[simp] theorem nc_ncZ_ne_ncLl : ncZ ≠ ncLl := by decide
@[simp] theorem nc_ncZ_ne_ncF : ncZ ≠ ncF := by decide
@[simp] theorem nc_ncZ_ne_ncN : ncZ ≠ ncN := by decide
@[simp] theorem nc_ncZ_ne_ncV : ncZ ≠ ncV := by decide
@[simp] theorem nc_ncZ_ne_lKb : ncZ ≠ lKb := by decide
@[simp] theorem nc_ncLp_ne_ncK : ncLp ≠ ncK := by decide
@[simp] theorem nc_ncLp_ne_ncI : ncLp ≠ ncI := by decide
@[simp] theorem nc_ncLp_ne_ncR : ncLp ≠ ncR := by decide
@[simp] theorem nc_ncLp_ne_ncJs : ncLp ≠ ncJs := by decide
@[simp] theorem nc_ncLp_ne_ncW : ncLp ≠ ncW := by decide
@[simp] theorem nc_ncLp_ne_ncQ : ncLp ≠ ncQ := by decide
@[simp] theorem nc_ncLp_ne_ncT : ncLp ≠ ncT := by decide
@[simp] theorem nc_ncLp_ne_ncZ : ncLp ≠ ncZ := by decide
@[simp] theorem nc_ncLp_ne_ncLl : ncLp ≠ ncLl := by decide
@[simp] theorem nc_ncLp_ne_ncF : ncLp ≠ ncF := by decide
@[simp] theorem nc_ncLp_ne_ncN : ncLp ≠ ncN := by decide
@[simp] theorem nc_ncLp_ne_ncV : ncLp ≠ ncV := by decide
@[simp] theorem nc_ncLp_ne_lKb : ncLp ≠ lKb := by decide
@[simp] theorem nc_ncLl_ne_ncK : ncLl ≠ ncK := by decide
@[simp] theorem nc_ncLl_ne_ncI : ncLl ≠ ncI := by decide
@[simp] theorem nc_ncLl_ne_ncR : ncLl ≠ ncR := by decide
@[simp] theorem nc_ncLl_ne_ncJs : ncLl ≠ ncJs := by decide
@[simp] theorem nc_ncLl_ne_ncW : ncLl ≠ ncW := by decide
@[simp] theorem nc_ncLl_ne_ncQ : ncLl ≠ ncQ := by decide
@[simp] theorem nc_ncLl_ne_ncT : ncLl ≠ ncT := by decide
@[simp] theorem nc_ncLl_ne_ncZ : ncLl ≠ ncZ := by decide
@[simp] theorem nc_ncLl_ne_ncLp : ncLl ≠ ncLp := by decide
@[simp] theorem nc_ncLl_ne_ncF : ncLl ≠ ncF := by decide
@[simp] theorem nc_ncLl_ne_ncN : ncLl ≠ ncN := by decide
@[simp] theorem nc_ncLl_ne_ncV : ncLl ≠ ncV := by decide
@[simp] theorem nc_ncLl_ne_lKb : ncLl ≠ lKb := by decide
@[simp] theorem nc_ncF_ne_ncK : ncF ≠ ncK := by decide
@[simp] theorem nc_ncF_ne_ncI : ncF ≠ ncI := by decide
@[simp] theorem nc_ncF_ne_ncR : ncF ≠ ncR := by decide
@[simp] theorem nc_ncF_ne_ncJs : ncF ≠ ncJs := by decide
@[simp] theorem nc_ncF_ne_ncW : ncF ≠ ncW := by decide
@[simp] theorem nc_ncF_ne_ncQ : ncF ≠ ncQ := by decide
@[simp] theorem nc_ncF_ne_ncT : ncF ≠ ncT := by decide
@[simp] theorem nc_ncF_ne_ncZ : ncF ≠ ncZ := by decide
@[simp] theorem nc_ncF_ne_ncLp : ncF ≠ ncLp := by decide
@[simp] theorem nc_ncF_ne_ncLl : ncF ≠ ncLl := by decide
@[simp] theorem nc_ncF_ne_ncN : ncF ≠ ncN := by decide
@[simp] theorem nc_ncF_ne_ncV : ncF ≠ ncV := by decide
@[simp] theorem nc_ncF_ne_lKb : ncF ≠ lKb := by decide
@[simp] theorem nc_ncN_ne_ncK : ncN ≠ ncK := by decide
@[simp] theorem nc_ncN_ne_ncI : ncN ≠ ncI := by decide
@[simp] theorem nc_ncN_ne_ncR : ncN ≠ ncR := by decide
@[simp] theorem nc_ncN_ne_ncJs : ncN ≠ ncJs := by decide
@[simp] theorem nc_ncN_ne_ncW : ncN ≠ ncW := by decide
@[simp] theorem nc_ncN_ne_ncQ : ncN ≠ ncQ := by decide
@[simp] theorem nc_ncN_ne_ncT : ncN ≠ ncT := by decide
@[simp] theorem nc_ncN_ne_ncZ : ncN ≠ ncZ := by decide
@[simp] theorem nc_ncN_ne_ncLp : ncN ≠ ncLp := by decide
@[simp] theorem nc_ncN_ne_ncLl : ncN ≠ ncLl := by decide
@[simp] theorem nc_ncN_ne_ncF : ncN ≠ ncF := by decide
@[simp] theorem nc_ncN_ne_ncV : ncN ≠ ncV := by decide
@[simp] theorem nc_ncN_ne_lKb : ncN ≠ lKb := by decide
@[simp] theorem nc_ncV_ne_ncK : ncV ≠ ncK := by decide
@[simp] theorem nc_ncV_ne_ncI : ncV ≠ ncI := by decide
@[simp] theorem nc_ncV_ne_ncR : ncV ≠ ncR := by decide
@[simp] theorem nc_ncV_ne_ncJs : ncV ≠ ncJs := by decide
@[simp] theorem nc_ncV_ne_ncW : ncV ≠ ncW := by decide
@[simp] theorem nc_ncV_ne_ncQ : ncV ≠ ncQ := by decide
@[simp] theorem nc_ncV_ne_ncT : ncV ≠ ncT := by decide
@[simp] theorem nc_ncV_ne_ncZ : ncV ≠ ncZ := by decide
@[simp] theorem nc_ncV_ne_ncLp : ncV ≠ ncLp := by decide
@[simp] theorem nc_ncV_ne_ncLl : ncV ≠ ncLl := by decide
@[simp] theorem nc_ncV_ne_ncF : ncV ≠ ncF := by decide
@[simp] theorem nc_ncV_ne_ncN : ncV ≠ ncN := by decide
@[simp] theorem nc_ncV_ne_lKb : ncV ≠ lKb := by decide
@[simp] theorem nc_lKb_ne_ncK : lKb ≠ ncK := by decide
@[simp] theorem nc_lKb_ne_ncI : lKb ≠ ncI := by decide
@[simp] theorem nc_lKb_ne_ncR : lKb ≠ ncR := by decide
@[simp] theorem nc_lKb_ne_ncJs : lKb ≠ ncJs := by decide
@[simp] theorem nc_lKb_ne_ncW : lKb ≠ ncW := by decide
@[simp] theorem nc_lKb_ne_ncQ : lKb ≠ ncQ := by decide
@[simp] theorem nc_lKb_ne_ncT : lKb ≠ ncT := by decide
@[simp] theorem nc_lKb_ne_ncZ : lKb ≠ ncZ := by decide
@[simp] theorem nc_lKb_ne_ncLp : lKb ≠ ncLp := by decide
@[simp] theorem nc_lKb_ne_ncLl : lKb ≠ ncLl := by decide
@[simp] theorem nc_lKb_ne_ncF : lKb ≠ ncF := by decide
@[simp] theorem nc_lKb_ne_ncN : lKb ≠ ncN := by decide
@[simp] theorem nc_lKb_ne_ncV : lKb ≠ ncV := by decide

def ncParams : List MlS := [ncK, ncI, ncR, ncJs]
def ncLocals : List MlS := [ncW, ncQ, ncT, ncZ, ncLp, ncLl, ncF, ncN, ncV]

def ncCore (C : Ctx) : ProgHOL 64 :=
  .ite (vv ncK) (.return (.const 1))
  (envFindP C ncW (vv ncI)
  (.ite (.cmp .equal (vv ncW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ncQ (.op .sub [vv ncW, .const 1])) (.seq (.assign .local ncT (.load .one (vv ncQ)))
  (.ite (.cmp .notEqual (vv ncT) (.const 3)) (.return (.const 0))
  (.seq (.assign .local ncZ (.load .one (.op .add [vv ncQ, .const 72])))
  (.ite (.cmp .equal (vv ncZ) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ncLp (.load .one (.op .add [vv ncQ, .const 16])))
  (.seq (.assign .local ncLl (.load .one (vv ncLp)))
  (.seq (.assign .local ncF (.load .one (.op .add [vv ncR, .const 16])))
  (.ite (.cmp .equal (vv ncF) (.const 0))
    (.seq (.assign .local ncN (.load .one (vv ncJs))) (.return (.cmp .equal (vv ncLl) (vv ncN))))
    (.seq (.assign .local ncV (.load .one (.op .add [vv ncR, .const 24])))
    (.seq (.assign .local ncN (.load .one (vv ncV))) (.return (.cmp .equal (vv ncLl) (vv ncN))))))))))))))))

def ncBody (C : Ctx) : ProgHOL 64 := prologue ncLocals (ncCore C)

structure NcCodes (C : Ctx) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)

section
variable {σ : Type}

theorem nc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ncLocals → (ctxEnv C ++ ncParams.zip vals).get x = none :=
  Knot.params_none C ncLocals ncParams vals (by decide) (by decide)

theorem eblk_small {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (hsr : SR C s t) {o : Nat}
    {xs : List (BitVec 64)} (hb : EBlk C.EH o xs) : xs.length < 2 ^ 61 := by
  have h1 := blkAt_len (show BlkAt C.EH o xs from hb)
  have h2 := hsr.env.1.len; have h3 := hok.envLay
  omega

theorem sev_cmpEqN (Γ : Env) (x y : MlS) (a b : Nat) (hx : Γ.get x = some (BitVec.ofNat 64 a))
    (hy : Γ.get y = some (BitVec.ofNat 64 b)) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    sev Γ (.cmp .equal (vv x) (vv y)) = some (boolW (a == b)) := by
  simp only [sev, vv, hx, hy, Option.bind_some, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : a = b
  · subst h; simp [boolW]
  · have hne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h ((UD.ofNat_eq_iff_small _ _ ha hb).mp e)
    simp [hne, h, boolW]

theorem nc_spec (C : Ctx) (hok : CtxOK C) (hc : NcCodes C) (s : AState) (isK : Bool) (induct : NIdx)
    (rl : IRecRule) (qr : Nat) (hrule : RuleE C.EB C.EH qr rl) (cvjLps : List NIdx) (oj : Nat)
    (hjs : EBlk C.EH oj (cvjLps.map Enc.idxW)) (H : List (BitVec 64)) (hp : C.H <+: H) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ncParams.zip [boolW isK, Enc.idxW induct, ecell C qr, ecell C oj])) (ncBody C) s
      (pure (iotaNoCert C.fe isK induct (recFireLevelCount rl cvjLps))) (PostBS (ctxH C H) s) := by
  have hok1 := ctxOK_H hok H
  refine specR_prologue (postBS_locals _ _) (nc_none _ _) ?_
  unfold ncCore
  cases isK
  swap
  · refine specR_ifI _ (boolW true) (by simp +decide [sev, Env.get, ncParams, ctxEnv]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, by simp [iotaNoCert, boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ (boolW false) (by simp +decide [sev, Env.get, ncParams, ctxEnv])
    (fun h => absurd h (by decide)) (fun _ => ?_)
  refine specR_envFindI (C := ctxH C H) hok1 hc.mg hc.mp ncW (vv ncI) induct (by decide)
    (by simp +decide [Env.get, ncParams, ctxEnv]) (by simp +decide [Env.get, ncParams, ctxEnv] <;> rfl) ?_
  have hrel : (match C.fe.find? induct with
      | none => (ctxH C H).envM[induct]? = none
      | some ci => ∃ o, (ctxH C H).envM[induct]? = some (ecell (ctxH C H) o) ∧
          CIE (ctxH C H).EB (ctxH C H).EH o ci) := find_rel hok1 induct
  revert hrel
  unfold iotaNoCert
  rcases hfind : C.fe.find? induct with _ | ci
  · intro hrel; simp only at hrel
    rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < (ctxH C H).EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok1 hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI ncQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  refine specR_envLoadI ncT (vv ncQ) o _ (by decide) (by simp; rfl) (UD.cie_tag hci) ?_
  cases ci
  case indInfo cvT caps =>
    dsimp only
    refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    obtain ⟨⟨_, ⟨w, hw, o', hw', hblk⟩, _⟩, _, -, -, -, -, -, hnz⟩ := hci
    subst hw'
    refine specR_envLoadI ncZ (.op .add [vv ncQ, .const 72]) (o + 9) _ (by decide)
      (by simp [sev, vv]; exact fz_ecell72 C o) hnz ?_
    cases hz : caps.neverZero
    · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_envLoadI ncLp (.op .add [vv ncQ, .const 16]) (o + 2) _ (by decide)
      (by simp [sev, vv]; exact UD.ecell_add16 C o) (by simpa using hw) ?_
    have hl0 : (ctxH C H).EH[o']? = some (BitVec.ofNat 64 cvT.levelParams.length) := by
      have := hblk.1; simpa [IConstantInfo.toConstantVal] using this
    have hlp : cvT.levelParams.length < 2 ^ 61 := by
      have := eblk_small hok1 ht.sr (show EBlk (ctxH C H).EH o' (cvT.levelParams.map Enc.idxW) from hblk)
      simpa using this
    refine specR_envLoadI ncLl (vv ncLp) o' _ (by decide) (by simp; rfl) hl0 ?_
    have hjl : cvjLps.length < 2 ^ 61 := by
      have := eblk_small hok1 ht.sr (show EBlk (ctxH C H).EH oj (cvjLps.map Enc.idxW) from hjs); simpa using this
    rcases hf : rl.fire with _ | ⟨lv, pins⟩ | lv
    · have hft : C.EH[qr + 2]? = some 0 := by have := hrule.2.2.1; rw [hf] at this; exact this
      refine specR_envLoadI ncF (.op .add [vv ncR, .const 16]) (qr + 2) _ (by decide)
        (by simp +decide [sev, Env.get, ncParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine specR_envLoadI ncN (vv ncJs) oj _ (by decide) (by simp +decide [Env.get, ncParams, ctxEnv]; rfl)
        (by simpa using hjs.1 : C.EH[oj]? = _) ?_
      refine specR_returnI _ (boolW (cvT.levelParams.length == cvjLps.length))
        (sev_cmpEqN _ ncLl ncN _ _ (by simp +decide [Env.get]) (by simp +decide [Env.get]) (by omega) (by omega))
        (fun t ht => ⟨rfl, by simp [recFireLevelCount, hf], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hfe := hrule.2.2.1; rw [hf] at hfe
      obtain ⟨hft, ⟨w3, hw3, olv, hw3', hblv⟩, -⟩ := hfe
      subst hw3'
      have hvl : lv.length < 2 ^ 61 := by
        have := eblk_small hok1 ht.sr (show EBlk (ctxH C H).EH olv (lv.map Enc.idxW) from hblv); simpa using this
      refine specR_envLoadI ncF (.op .add [vv ncR, .const 16]) (qr + 2) _ (by decide)
        (by simp +decide [sev, Env.get, ncParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      refine specR_envLoadI ncV (.op .add [vv ncR, .const 24]) (qr + 3) _ (by decide)
        (by simp +decide [sev, Env.get, ncParams, ctxEnv]; exact ecell_add24 C qr) (by simpa using hw3 : C.EH[qr + 3]? = _) ?_
      refine specR_envLoadI ncN (vv ncV) olv _ (by decide) (by simp +decide [Env.get]; rfl)
        (by simpa using hblv.1 : C.EH[olv]? = _) ?_
      refine specR_returnI _ (boolW (cvT.levelParams.length == lv.length))
        (sev_cmpEqN _ ncLl ncN _ _ (by simp +decide [Env.get]) (by simp +decide [Env.get]) (by omega) (by omega))
        (fun t ht => ⟨rfl, by simp [recFireLevelCount, hf], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hfe := hrule.2.2.1; rw [hf] at hfe
      obtain ⟨hft, w3, hw3, olv, hw3', hblv⟩ := hfe
      subst hw3'
      have hvl : lv.length < 2 ^ 61 := by
        have := eblk_small hok1 ht.sr (show EBlk (ctxH C H).EH olv (lv.map Enc.idxW) from hblv); simpa using this
      refine specR_envLoadI ncF (.op .add [vv ncR, .const 16]) (qr + 2) _ (by decide)
        (by simp +decide [sev, Env.get, ncParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      refine specR_envLoadI ncV (.op .add [vv ncR, .const 24]) (qr + 3) _ (by decide)
        (by simp +decide [sev, Env.get, ncParams, ctxEnv]; exact ecell_add24 C qr) (by simpa using hw3 : C.EH[qr + 3]? = _) ?_
      refine specR_envLoadI ncN (vv ncV) olv _ (by decide) (by simp +decide [Env.get]; rfl)
        (by simpa using hblv.1 : C.EH[olv]? = _) ?_
      refine specR_returnI _ (boolW (cvT.levelParams.length == lv.length))
        (sev_cmpEqN _ ncLl ncN _ _ (by simp +decide [Env.get]) (by simp +decide [Env.get]) (by omega) (by omega))
        (fun t ht => ⟨rfl, by simp [recFireLevelCount, hf], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  all_goals
    dsimp only
    refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-! ## A fresh block holding a block's first `k` cells -/

def takeCopyP (C : Ctx) (x src cnt : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lCn (vv cnt))
  (allocP C x (.shift .lsl (.op .add [vv lCn, .const 1]) (.const 3))
  (.seq (.store (vv x) (vv lCn))
  (.seq (.assign .local lSrc (.op .add [vv src, .const 8]))
  (.seq (.assign .local lDst (.op .add [vv x, .const 8]))
  (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop rest))))))

theorem blk_of_fillI_hdr (B xs : List (BitVec 64)) (o : Nat) (h0 : B[o]? = some (BitVec.ofNat 64 xs.length))
    (hdst : o + 1 + xs.length ≤ B.length) : BlkAt (fillI B xs (o + 1) xs.length) o xs := by
  constructor
  · rw [fillI_get?, if_neg (by omega)]; exact h0
  · intro i hi
    rw [fillI_get?, if_pos ⟨by omega, by omega, by omega⟩]
    simp [show o + 1 + i - (o + 1) = i by omega, List.getD_eq_getElem?_getD, hi]

theorem specR_takeCopyI {α : Type} {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x src cnt : MlS) (oa k : Nat) (xs : List (BitVec 64))
    (hD : x ∈ D ∧ lCn ∈ D ∧ lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hsrc : Γ.get src = some (cellA C oa)) (hcnt : Γ.get cnt = some (BitVec.ofNat 64 k)) (hk : k ≤ xs.length)
    (hxl : xs.length < 2 ^ 58) (hb : BlkAt H oa xs) (hz : Γ.get lCz = none)
    (hne : x ≠ lCn ∧ x ≠ lSrc ∧ x ≠ lDst ∧ x ≠ lCi ∧ x ≠ lCz) (hsn : src ≠ lCn ∧ src ≠ x)
    (hcont : ∀ (H' : List (BitVec 64)) o, H <+: H' → H.length ≤ o → BlkAt H' o (xs.take k) →
      SpecR (Inv (ctxH C H') s ((lCi, BitVec.ofNat 64 k) :: (lDst, cellA C (o + 1 + k)) ::
        (lSrc, cellA C (oa + 1 + k)) :: (x, cellA C o) :: (lCn, BitVec.ofNat 64 k) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (takeCopyP C x src cnt rest) s m R := by
  have hlen := blkAt_len hb
  refine specR_assignI lCn (vv cnt) (BitVec.ofNat 64 k) hD.2.1 (by simpa using hcnt) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) x _ (k + 1) (by omega) hD.1 (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get, hne.1.symm]
    rw [shl_ofNat _ _ (by omega), show (8#64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat, show 2 ^ 3 * k + 8 = 8 * (k + 1) by ring]
  have hp2' : H <+: H2 := hp2
  have hH12 := hp2'.length_le
  have hq0 : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) (vv lCn) H2.length hq0 (BitVec.ofNat 64 k)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, hne.1.symm]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 k))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 k) = B
  have hBlen : B.length = H2.length + (k + 1) := by rw [← hB]; simp [hws]
  refine specR_assignI lSrc _ (cellA C (oa + 1)) hD.2.2.1
    (by simp +decide [sev, Env.get, hsn.1, hsn.2, hsrc]; exact cellA_add8 C oa) ?_
  refine specR_assignI lDst _ (cellA C (H2.length + 1)) hD.2.2.2.1
    (by simp +decide [sev, Env.get, hne.2.1]; exact cellA_add8 C _) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) hD.2.2.2.2.1 rfl ?_
  have hsrcB : ∀ j (hj : j < (xs.take k).length), B[oa + 1 + j]? = some (xs.take k)[j] := by
    intro j hj
    simp only [List.length_take] at hj
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega), List.getElem_take]
    exact (blkAt_mono hb hp2').2 j (by omega)
  have htk : (xs.take k).length = k := by simp; omega
  refine specR_copyI (C := C) hok B (xs.take k) (oa + 1) (H2.length + 1)
    ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1, hD.2.2.2.2.2⟩ hsrcB (by rw [htk]; omega) (by rw [htk]; omega)
    (by rw [htk]; omega) (by rw [htk]; simp +decide [Env.get, hne.1.symm]) (by decide)
    (by simp +decide [Env.get, hne.2.2.2.2.symm]; exact hz) ?_
  rw [htk]
  refine hcont _ H2.length ?_ hH12 ?_
  · refine hp2'.trans (prefix_of_get? (by rw [fillI_length, hBlen]; omega) (fun j hj => ?_))
    rw [fillI_get?, if_neg (by omega), ← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  · have := blk_of_fillI_hdr B (xs.take k) H2.length
      (by rw [htk, ← hB, List.getElem?_set_self (by simp; omega)]) (by rw [htk, hBlen]; omega)
    rw [htk] at this; exact this

end


def faR := ofString "far"
def faKs := ofString "faks"
def faU := ofString "fau"
def faA := ofString "faa"
def faRp := ofString "farp"
def faCn := ofString "facn"
def faT := ofString "fat"
def faKl := ofString "fakl"
def faKb := ofString "fakb"
def faL := ofString "fal"
def faM := ofString "fam"
def faM2 := ofString "fam2"
def faTk := ofString "fatk"
def faAc := ofString "faac"
def faPs := ofString "faps"
def faPn := ofString "fapn"
def faX := ofString "fax"
def faB := ofString "fab"
def fFa := ofString "recFireArgs"

@[simp] theorem fa_faR_ne_faKs : faR ≠ faKs := by decide
@[simp] theorem fa_faR_ne_faU : faR ≠ faU := by decide
@[simp] theorem fa_faR_ne_faA : faR ≠ faA := by decide
@[simp] theorem fa_faR_ne_faRp : faR ≠ faRp := by decide
@[simp] theorem fa_faR_ne_faCn : faR ≠ faCn := by decide
@[simp] theorem fa_faR_ne_faT : faR ≠ faT := by decide
@[simp] theorem fa_faR_ne_faKl : faR ≠ faKl := by decide
@[simp] theorem fa_faR_ne_faKb : faR ≠ faKb := by decide
@[simp] theorem fa_faR_ne_faL : faR ≠ faL := by decide
@[simp] theorem fa_faR_ne_faM : faR ≠ faM := by decide
@[simp] theorem fa_faR_ne_faM2 : faR ≠ faM2 := by decide
@[simp] theorem fa_faR_ne_faTk : faR ≠ faTk := by decide
@[simp] theorem fa_faR_ne_faAc : faR ≠ faAc := by decide
@[simp] theorem fa_faR_ne_faPs : faR ≠ faPs := by decide
@[simp] theorem fa_faR_ne_faPn : faR ≠ faPn := by decide
@[simp] theorem fa_faR_ne_faX : faR ≠ faX := by decide
@[simp] theorem fa_faR_ne_faB : faR ≠ faB := by decide
@[simp] theorem fa_faR_ne_lKb : faR ≠ lKb := by decide
@[simp] theorem fa_faR_ne_lCn : faR ≠ lCn := by decide
@[simp] theorem fa_faR_ne_lSrc : faR ≠ lSrc := by decide
@[simp] theorem fa_faR_ne_lDst : faR ≠ lDst := by decide
@[simp] theorem fa_faR_ne_lCi : faR ≠ lCi := by decide
@[simp] theorem fa_faR_ne_lCz : faR ≠ lCz := by decide
@[simp] theorem fa_faKs_ne_faR : faKs ≠ faR := by decide
@[simp] theorem fa_faKs_ne_faU : faKs ≠ faU := by decide
@[simp] theorem fa_faKs_ne_faA : faKs ≠ faA := by decide
@[simp] theorem fa_faKs_ne_faRp : faKs ≠ faRp := by decide
@[simp] theorem fa_faKs_ne_faCn : faKs ≠ faCn := by decide
@[simp] theorem fa_faKs_ne_faT : faKs ≠ faT := by decide
@[simp] theorem fa_faKs_ne_faKl : faKs ≠ faKl := by decide
@[simp] theorem fa_faKs_ne_faKb : faKs ≠ faKb := by decide
@[simp] theorem fa_faKs_ne_faL : faKs ≠ faL := by decide
@[simp] theorem fa_faKs_ne_faM : faKs ≠ faM := by decide
@[simp] theorem fa_faKs_ne_faM2 : faKs ≠ faM2 := by decide
@[simp] theorem fa_faKs_ne_faTk : faKs ≠ faTk := by decide
@[simp] theorem fa_faKs_ne_faAc : faKs ≠ faAc := by decide
@[simp] theorem fa_faKs_ne_faPs : faKs ≠ faPs := by decide
@[simp] theorem fa_faKs_ne_faPn : faKs ≠ faPn := by decide
@[simp] theorem fa_faKs_ne_faX : faKs ≠ faX := by decide
@[simp] theorem fa_faKs_ne_faB : faKs ≠ faB := by decide
@[simp] theorem fa_faKs_ne_lKb : faKs ≠ lKb := by decide
@[simp] theorem fa_faKs_ne_lCn : faKs ≠ lCn := by decide
@[simp] theorem fa_faKs_ne_lSrc : faKs ≠ lSrc := by decide
@[simp] theorem fa_faKs_ne_lDst : faKs ≠ lDst := by decide
@[simp] theorem fa_faKs_ne_lCi : faKs ≠ lCi := by decide
@[simp] theorem fa_faKs_ne_lCz : faKs ≠ lCz := by decide
@[simp] theorem fa_faU_ne_faR : faU ≠ faR := by decide
@[simp] theorem fa_faU_ne_faKs : faU ≠ faKs := by decide
@[simp] theorem fa_faU_ne_faA : faU ≠ faA := by decide
@[simp] theorem fa_faU_ne_faRp : faU ≠ faRp := by decide
@[simp] theorem fa_faU_ne_faCn : faU ≠ faCn := by decide
@[simp] theorem fa_faU_ne_faT : faU ≠ faT := by decide
@[simp] theorem fa_faU_ne_faKl : faU ≠ faKl := by decide
@[simp] theorem fa_faU_ne_faKb : faU ≠ faKb := by decide
@[simp] theorem fa_faU_ne_faL : faU ≠ faL := by decide
@[simp] theorem fa_faU_ne_faM : faU ≠ faM := by decide
@[simp] theorem fa_faU_ne_faM2 : faU ≠ faM2 := by decide
@[simp] theorem fa_faU_ne_faTk : faU ≠ faTk := by decide
@[simp] theorem fa_faU_ne_faAc : faU ≠ faAc := by decide
@[simp] theorem fa_faU_ne_faPs : faU ≠ faPs := by decide
@[simp] theorem fa_faU_ne_faPn : faU ≠ faPn := by decide
@[simp] theorem fa_faU_ne_faX : faU ≠ faX := by decide
@[simp] theorem fa_faU_ne_faB : faU ≠ faB := by decide
@[simp] theorem fa_faU_ne_lKb : faU ≠ lKb := by decide
@[simp] theorem fa_faU_ne_lCn : faU ≠ lCn := by decide
@[simp] theorem fa_faU_ne_lSrc : faU ≠ lSrc := by decide
@[simp] theorem fa_faU_ne_lDst : faU ≠ lDst := by decide
@[simp] theorem fa_faU_ne_lCi : faU ≠ lCi := by decide
@[simp] theorem fa_faU_ne_lCz : faU ≠ lCz := by decide
@[simp] theorem fa_faA_ne_faR : faA ≠ faR := by decide
@[simp] theorem fa_faA_ne_faKs : faA ≠ faKs := by decide
@[simp] theorem fa_faA_ne_faU : faA ≠ faU := by decide
@[simp] theorem fa_faA_ne_faRp : faA ≠ faRp := by decide
@[simp] theorem fa_faA_ne_faCn : faA ≠ faCn := by decide
@[simp] theorem fa_faA_ne_faT : faA ≠ faT := by decide
@[simp] theorem fa_faA_ne_faKl : faA ≠ faKl := by decide
@[simp] theorem fa_faA_ne_faKb : faA ≠ faKb := by decide
@[simp] theorem fa_faA_ne_faL : faA ≠ faL := by decide
@[simp] theorem fa_faA_ne_faM : faA ≠ faM := by decide
@[simp] theorem fa_faA_ne_faM2 : faA ≠ faM2 := by decide
@[simp] theorem fa_faA_ne_faTk : faA ≠ faTk := by decide
@[simp] theorem fa_faA_ne_faAc : faA ≠ faAc := by decide
@[simp] theorem fa_faA_ne_faPs : faA ≠ faPs := by decide
@[simp] theorem fa_faA_ne_faPn : faA ≠ faPn := by decide
@[simp] theorem fa_faA_ne_faX : faA ≠ faX := by decide
@[simp] theorem fa_faA_ne_faB : faA ≠ faB := by decide
@[simp] theorem fa_faA_ne_lKb : faA ≠ lKb := by decide
@[simp] theorem fa_faA_ne_lCn : faA ≠ lCn := by decide
@[simp] theorem fa_faA_ne_lSrc : faA ≠ lSrc := by decide
@[simp] theorem fa_faA_ne_lDst : faA ≠ lDst := by decide
@[simp] theorem fa_faA_ne_lCi : faA ≠ lCi := by decide
@[simp] theorem fa_faA_ne_lCz : faA ≠ lCz := by decide
@[simp] theorem fa_faRp_ne_faR : faRp ≠ faR := by decide
@[simp] theorem fa_faRp_ne_faKs : faRp ≠ faKs := by decide
@[simp] theorem fa_faRp_ne_faU : faRp ≠ faU := by decide
@[simp] theorem fa_faRp_ne_faA : faRp ≠ faA := by decide
@[simp] theorem fa_faRp_ne_faCn : faRp ≠ faCn := by decide
@[simp] theorem fa_faRp_ne_faT : faRp ≠ faT := by decide
@[simp] theorem fa_faRp_ne_faKl : faRp ≠ faKl := by decide
@[simp] theorem fa_faRp_ne_faKb : faRp ≠ faKb := by decide
@[simp] theorem fa_faRp_ne_faL : faRp ≠ faL := by decide
@[simp] theorem fa_faRp_ne_faM : faRp ≠ faM := by decide
@[simp] theorem fa_faRp_ne_faM2 : faRp ≠ faM2 := by decide
@[simp] theorem fa_faRp_ne_faTk : faRp ≠ faTk := by decide
@[simp] theorem fa_faRp_ne_faAc : faRp ≠ faAc := by decide
@[simp] theorem fa_faRp_ne_faPs : faRp ≠ faPs := by decide
@[simp] theorem fa_faRp_ne_faPn : faRp ≠ faPn := by decide
@[simp] theorem fa_faRp_ne_faX : faRp ≠ faX := by decide
@[simp] theorem fa_faRp_ne_faB : faRp ≠ faB := by decide
@[simp] theorem fa_faRp_ne_lKb : faRp ≠ lKb := by decide
@[simp] theorem fa_faRp_ne_lCn : faRp ≠ lCn := by decide
@[simp] theorem fa_faRp_ne_lSrc : faRp ≠ lSrc := by decide
@[simp] theorem fa_faRp_ne_lDst : faRp ≠ lDst := by decide
@[simp] theorem fa_faRp_ne_lCi : faRp ≠ lCi := by decide
@[simp] theorem fa_faRp_ne_lCz : faRp ≠ lCz := by decide
@[simp] theorem fa_faCn_ne_faR : faCn ≠ faR := by decide
@[simp] theorem fa_faCn_ne_faKs : faCn ≠ faKs := by decide
@[simp] theorem fa_faCn_ne_faU : faCn ≠ faU := by decide
@[simp] theorem fa_faCn_ne_faA : faCn ≠ faA := by decide
@[simp] theorem fa_faCn_ne_faRp : faCn ≠ faRp := by decide
@[simp] theorem fa_faCn_ne_faT : faCn ≠ faT := by decide
@[simp] theorem fa_faCn_ne_faKl : faCn ≠ faKl := by decide
@[simp] theorem fa_faCn_ne_faKb : faCn ≠ faKb := by decide
@[simp] theorem fa_faCn_ne_faL : faCn ≠ faL := by decide
@[simp] theorem fa_faCn_ne_faM : faCn ≠ faM := by decide
@[simp] theorem fa_faCn_ne_faM2 : faCn ≠ faM2 := by decide
@[simp] theorem fa_faCn_ne_faTk : faCn ≠ faTk := by decide
@[simp] theorem fa_faCn_ne_faAc : faCn ≠ faAc := by decide
@[simp] theorem fa_faCn_ne_faPs : faCn ≠ faPs := by decide
@[simp] theorem fa_faCn_ne_faPn : faCn ≠ faPn := by decide
@[simp] theorem fa_faCn_ne_faX : faCn ≠ faX := by decide
@[simp] theorem fa_faCn_ne_faB : faCn ≠ faB := by decide
@[simp] theorem fa_faCn_ne_lKb : faCn ≠ lKb := by decide
@[simp] theorem fa_faCn_ne_lCn : faCn ≠ lCn := by decide
@[simp] theorem fa_faCn_ne_lSrc : faCn ≠ lSrc := by decide
@[simp] theorem fa_faCn_ne_lDst : faCn ≠ lDst := by decide
@[simp] theorem fa_faCn_ne_lCi : faCn ≠ lCi := by decide
@[simp] theorem fa_faCn_ne_lCz : faCn ≠ lCz := by decide
@[simp] theorem fa_faT_ne_faR : faT ≠ faR := by decide
@[simp] theorem fa_faT_ne_faKs : faT ≠ faKs := by decide
@[simp] theorem fa_faT_ne_faU : faT ≠ faU := by decide
@[simp] theorem fa_faT_ne_faA : faT ≠ faA := by decide
@[simp] theorem fa_faT_ne_faRp : faT ≠ faRp := by decide
@[simp] theorem fa_faT_ne_faCn : faT ≠ faCn := by decide
@[simp] theorem fa_faT_ne_faKl : faT ≠ faKl := by decide
@[simp] theorem fa_faT_ne_faKb : faT ≠ faKb := by decide
@[simp] theorem fa_faT_ne_faL : faT ≠ faL := by decide
@[simp] theorem fa_faT_ne_faM : faT ≠ faM := by decide
@[simp] theorem fa_faT_ne_faM2 : faT ≠ faM2 := by decide
@[simp] theorem fa_faT_ne_faTk : faT ≠ faTk := by decide
@[simp] theorem fa_faT_ne_faAc : faT ≠ faAc := by decide
@[simp] theorem fa_faT_ne_faPs : faT ≠ faPs := by decide
@[simp] theorem fa_faT_ne_faPn : faT ≠ faPn := by decide
@[simp] theorem fa_faT_ne_faX : faT ≠ faX := by decide
@[simp] theorem fa_faT_ne_faB : faT ≠ faB := by decide
@[simp] theorem fa_faT_ne_lKb : faT ≠ lKb := by decide
@[simp] theorem fa_faT_ne_lCn : faT ≠ lCn := by decide
@[simp] theorem fa_faT_ne_lSrc : faT ≠ lSrc := by decide
@[simp] theorem fa_faT_ne_lDst : faT ≠ lDst := by decide
@[simp] theorem fa_faT_ne_lCi : faT ≠ lCi := by decide
@[simp] theorem fa_faT_ne_lCz : faT ≠ lCz := by decide
@[simp] theorem fa_faKl_ne_faR : faKl ≠ faR := by decide
@[simp] theorem fa_faKl_ne_faKs : faKl ≠ faKs := by decide
@[simp] theorem fa_faKl_ne_faU : faKl ≠ faU := by decide
@[simp] theorem fa_faKl_ne_faA : faKl ≠ faA := by decide
@[simp] theorem fa_faKl_ne_faRp : faKl ≠ faRp := by decide
@[simp] theorem fa_faKl_ne_faCn : faKl ≠ faCn := by decide
@[simp] theorem fa_faKl_ne_faT : faKl ≠ faT := by decide
@[simp] theorem fa_faKl_ne_faKb : faKl ≠ faKb := by decide
@[simp] theorem fa_faKl_ne_faL : faKl ≠ faL := by decide
@[simp] theorem fa_faKl_ne_faM : faKl ≠ faM := by decide
@[simp] theorem fa_faKl_ne_faM2 : faKl ≠ faM2 := by decide
@[simp] theorem fa_faKl_ne_faTk : faKl ≠ faTk := by decide
@[simp] theorem fa_faKl_ne_faAc : faKl ≠ faAc := by decide
@[simp] theorem fa_faKl_ne_faPs : faKl ≠ faPs := by decide
@[simp] theorem fa_faKl_ne_faPn : faKl ≠ faPn := by decide
@[simp] theorem fa_faKl_ne_faX : faKl ≠ faX := by decide
@[simp] theorem fa_faKl_ne_faB : faKl ≠ faB := by decide
@[simp] theorem fa_faKl_ne_lKb : faKl ≠ lKb := by decide
@[simp] theorem fa_faKl_ne_lCn : faKl ≠ lCn := by decide
@[simp] theorem fa_faKl_ne_lSrc : faKl ≠ lSrc := by decide
@[simp] theorem fa_faKl_ne_lDst : faKl ≠ lDst := by decide
@[simp] theorem fa_faKl_ne_lCi : faKl ≠ lCi := by decide
@[simp] theorem fa_faKl_ne_lCz : faKl ≠ lCz := by decide
@[simp] theorem fa_faKb_ne_faR : faKb ≠ faR := by decide
@[simp] theorem fa_faKb_ne_faKs : faKb ≠ faKs := by decide
@[simp] theorem fa_faKb_ne_faU : faKb ≠ faU := by decide
@[simp] theorem fa_faKb_ne_faA : faKb ≠ faA := by decide
@[simp] theorem fa_faKb_ne_faRp : faKb ≠ faRp := by decide
@[simp] theorem fa_faKb_ne_faCn : faKb ≠ faCn := by decide
@[simp] theorem fa_faKb_ne_faT : faKb ≠ faT := by decide
@[simp] theorem fa_faKb_ne_faKl : faKb ≠ faKl := by decide
@[simp] theorem fa_faKb_ne_faL : faKb ≠ faL := by decide
@[simp] theorem fa_faKb_ne_faM : faKb ≠ faM := by decide
@[simp] theorem fa_faKb_ne_faM2 : faKb ≠ faM2 := by decide
@[simp] theorem fa_faKb_ne_faTk : faKb ≠ faTk := by decide
@[simp] theorem fa_faKb_ne_faAc : faKb ≠ faAc := by decide
@[simp] theorem fa_faKb_ne_faPs : faKb ≠ faPs := by decide
@[simp] theorem fa_faKb_ne_faPn : faKb ≠ faPn := by decide
@[simp] theorem fa_faKb_ne_faX : faKb ≠ faX := by decide
@[simp] theorem fa_faKb_ne_faB : faKb ≠ faB := by decide
@[simp] theorem fa_faKb_ne_lKb : faKb ≠ lKb := by decide
@[simp] theorem fa_faKb_ne_lCn : faKb ≠ lCn := by decide
@[simp] theorem fa_faKb_ne_lSrc : faKb ≠ lSrc := by decide
@[simp] theorem fa_faKb_ne_lDst : faKb ≠ lDst := by decide
@[simp] theorem fa_faKb_ne_lCi : faKb ≠ lCi := by decide
@[simp] theorem fa_faKb_ne_lCz : faKb ≠ lCz := by decide
@[simp] theorem fa_faL_ne_faR : faL ≠ faR := by decide
@[simp] theorem fa_faL_ne_faKs : faL ≠ faKs := by decide
@[simp] theorem fa_faL_ne_faU : faL ≠ faU := by decide
@[simp] theorem fa_faL_ne_faA : faL ≠ faA := by decide
@[simp] theorem fa_faL_ne_faRp : faL ≠ faRp := by decide
@[simp] theorem fa_faL_ne_faCn : faL ≠ faCn := by decide
@[simp] theorem fa_faL_ne_faT : faL ≠ faT := by decide
@[simp] theorem fa_faL_ne_faKl : faL ≠ faKl := by decide
@[simp] theorem fa_faL_ne_faKb : faL ≠ faKb := by decide
@[simp] theorem fa_faL_ne_faM : faL ≠ faM := by decide
@[simp] theorem fa_faL_ne_faM2 : faL ≠ faM2 := by decide
@[simp] theorem fa_faL_ne_faTk : faL ≠ faTk := by decide
@[simp] theorem fa_faL_ne_faAc : faL ≠ faAc := by decide
@[simp] theorem fa_faL_ne_faPs : faL ≠ faPs := by decide
@[simp] theorem fa_faL_ne_faPn : faL ≠ faPn := by decide
@[simp] theorem fa_faL_ne_faX : faL ≠ faX := by decide
@[simp] theorem fa_faL_ne_faB : faL ≠ faB := by decide
@[simp] theorem fa_faL_ne_lKb : faL ≠ lKb := by decide
@[simp] theorem fa_faL_ne_lCn : faL ≠ lCn := by decide
@[simp] theorem fa_faL_ne_lSrc : faL ≠ lSrc := by decide
@[simp] theorem fa_faL_ne_lDst : faL ≠ lDst := by decide
@[simp] theorem fa_faL_ne_lCi : faL ≠ lCi := by decide
@[simp] theorem fa_faL_ne_lCz : faL ≠ lCz := by decide
@[simp] theorem fa_faM_ne_faR : faM ≠ faR := by decide
@[simp] theorem fa_faM_ne_faKs : faM ≠ faKs := by decide
@[simp] theorem fa_faM_ne_faU : faM ≠ faU := by decide
@[simp] theorem fa_faM_ne_faA : faM ≠ faA := by decide
@[simp] theorem fa_faM_ne_faRp : faM ≠ faRp := by decide
@[simp] theorem fa_faM_ne_faCn : faM ≠ faCn := by decide
@[simp] theorem fa_faM_ne_faT : faM ≠ faT := by decide
@[simp] theorem fa_faM_ne_faKl : faM ≠ faKl := by decide
@[simp] theorem fa_faM_ne_faKb : faM ≠ faKb := by decide
@[simp] theorem fa_faM_ne_faL : faM ≠ faL := by decide
@[simp] theorem fa_faM_ne_faM2 : faM ≠ faM2 := by decide
@[simp] theorem fa_faM_ne_faTk : faM ≠ faTk := by decide
@[simp] theorem fa_faM_ne_faAc : faM ≠ faAc := by decide
@[simp] theorem fa_faM_ne_faPs : faM ≠ faPs := by decide
@[simp] theorem fa_faM_ne_faPn : faM ≠ faPn := by decide
@[simp] theorem fa_faM_ne_faX : faM ≠ faX := by decide
@[simp] theorem fa_faM_ne_faB : faM ≠ faB := by decide
@[simp] theorem fa_faM_ne_lKb : faM ≠ lKb := by decide
@[simp] theorem fa_faM_ne_lCn : faM ≠ lCn := by decide
@[simp] theorem fa_faM_ne_lSrc : faM ≠ lSrc := by decide
@[simp] theorem fa_faM_ne_lDst : faM ≠ lDst := by decide
@[simp] theorem fa_faM_ne_lCi : faM ≠ lCi := by decide
@[simp] theorem fa_faM_ne_lCz : faM ≠ lCz := by decide
@[simp] theorem fa_faM2_ne_faR : faM2 ≠ faR := by decide
@[simp] theorem fa_faM2_ne_faKs : faM2 ≠ faKs := by decide
@[simp] theorem fa_faM2_ne_faU : faM2 ≠ faU := by decide
@[simp] theorem fa_faM2_ne_faA : faM2 ≠ faA := by decide
@[simp] theorem fa_faM2_ne_faRp : faM2 ≠ faRp := by decide
@[simp] theorem fa_faM2_ne_faCn : faM2 ≠ faCn := by decide
@[simp] theorem fa_faM2_ne_faT : faM2 ≠ faT := by decide
@[simp] theorem fa_faM2_ne_faKl : faM2 ≠ faKl := by decide
@[simp] theorem fa_faM2_ne_faKb : faM2 ≠ faKb := by decide
@[simp] theorem fa_faM2_ne_faL : faM2 ≠ faL := by decide
@[simp] theorem fa_faM2_ne_faM : faM2 ≠ faM := by decide
@[simp] theorem fa_faM2_ne_faTk : faM2 ≠ faTk := by decide
@[simp] theorem fa_faM2_ne_faAc : faM2 ≠ faAc := by decide
@[simp] theorem fa_faM2_ne_faPs : faM2 ≠ faPs := by decide
@[simp] theorem fa_faM2_ne_faPn : faM2 ≠ faPn := by decide
@[simp] theorem fa_faM2_ne_faX : faM2 ≠ faX := by decide
@[simp] theorem fa_faM2_ne_faB : faM2 ≠ faB := by decide
@[simp] theorem fa_faM2_ne_lKb : faM2 ≠ lKb := by decide
@[simp] theorem fa_faM2_ne_lCn : faM2 ≠ lCn := by decide
@[simp] theorem fa_faM2_ne_lSrc : faM2 ≠ lSrc := by decide
@[simp] theorem fa_faM2_ne_lDst : faM2 ≠ lDst := by decide
@[simp] theorem fa_faM2_ne_lCi : faM2 ≠ lCi := by decide
@[simp] theorem fa_faM2_ne_lCz : faM2 ≠ lCz := by decide
@[simp] theorem fa_faTk_ne_faR : faTk ≠ faR := by decide
@[simp] theorem fa_faTk_ne_faKs : faTk ≠ faKs := by decide
@[simp] theorem fa_faTk_ne_faU : faTk ≠ faU := by decide
@[simp] theorem fa_faTk_ne_faA : faTk ≠ faA := by decide
@[simp] theorem fa_faTk_ne_faRp : faTk ≠ faRp := by decide
@[simp] theorem fa_faTk_ne_faCn : faTk ≠ faCn := by decide
@[simp] theorem fa_faTk_ne_faT : faTk ≠ faT := by decide
@[simp] theorem fa_faTk_ne_faKl : faTk ≠ faKl := by decide
@[simp] theorem fa_faTk_ne_faKb : faTk ≠ faKb := by decide
@[simp] theorem fa_faTk_ne_faL : faTk ≠ faL := by decide
@[simp] theorem fa_faTk_ne_faM : faTk ≠ faM := by decide
@[simp] theorem fa_faTk_ne_faM2 : faTk ≠ faM2 := by decide
@[simp] theorem fa_faTk_ne_faAc : faTk ≠ faAc := by decide
@[simp] theorem fa_faTk_ne_faPs : faTk ≠ faPs := by decide
@[simp] theorem fa_faTk_ne_faPn : faTk ≠ faPn := by decide
@[simp] theorem fa_faTk_ne_faX : faTk ≠ faX := by decide
@[simp] theorem fa_faTk_ne_faB : faTk ≠ faB := by decide
@[simp] theorem fa_faTk_ne_lKb : faTk ≠ lKb := by decide
@[simp] theorem fa_faTk_ne_lCn : faTk ≠ lCn := by decide
@[simp] theorem fa_faTk_ne_lSrc : faTk ≠ lSrc := by decide
@[simp] theorem fa_faTk_ne_lDst : faTk ≠ lDst := by decide
@[simp] theorem fa_faTk_ne_lCi : faTk ≠ lCi := by decide
@[simp] theorem fa_faTk_ne_lCz : faTk ≠ lCz := by decide
@[simp] theorem fa_faAc_ne_faR : faAc ≠ faR := by decide
@[simp] theorem fa_faAc_ne_faKs : faAc ≠ faKs := by decide
@[simp] theorem fa_faAc_ne_faU : faAc ≠ faU := by decide
@[simp] theorem fa_faAc_ne_faA : faAc ≠ faA := by decide
@[simp] theorem fa_faAc_ne_faRp : faAc ≠ faRp := by decide
@[simp] theorem fa_faAc_ne_faCn : faAc ≠ faCn := by decide
@[simp] theorem fa_faAc_ne_faT : faAc ≠ faT := by decide
@[simp] theorem fa_faAc_ne_faKl : faAc ≠ faKl := by decide
@[simp] theorem fa_faAc_ne_faKb : faAc ≠ faKb := by decide
@[simp] theorem fa_faAc_ne_faL : faAc ≠ faL := by decide
@[simp] theorem fa_faAc_ne_faM : faAc ≠ faM := by decide
@[simp] theorem fa_faAc_ne_faM2 : faAc ≠ faM2 := by decide
@[simp] theorem fa_faAc_ne_faTk : faAc ≠ faTk := by decide
@[simp] theorem fa_faAc_ne_faPs : faAc ≠ faPs := by decide
@[simp] theorem fa_faAc_ne_faPn : faAc ≠ faPn := by decide
@[simp] theorem fa_faAc_ne_faX : faAc ≠ faX := by decide
@[simp] theorem fa_faAc_ne_faB : faAc ≠ faB := by decide
@[simp] theorem fa_faAc_ne_lKb : faAc ≠ lKb := by decide
@[simp] theorem fa_faAc_ne_lCn : faAc ≠ lCn := by decide
@[simp] theorem fa_faAc_ne_lSrc : faAc ≠ lSrc := by decide
@[simp] theorem fa_faAc_ne_lDst : faAc ≠ lDst := by decide
@[simp] theorem fa_faAc_ne_lCi : faAc ≠ lCi := by decide
@[simp] theorem fa_faAc_ne_lCz : faAc ≠ lCz := by decide
@[simp] theorem fa_faPs_ne_faR : faPs ≠ faR := by decide
@[simp] theorem fa_faPs_ne_faKs : faPs ≠ faKs := by decide
@[simp] theorem fa_faPs_ne_faU : faPs ≠ faU := by decide
@[simp] theorem fa_faPs_ne_faA : faPs ≠ faA := by decide
@[simp] theorem fa_faPs_ne_faRp : faPs ≠ faRp := by decide
@[simp] theorem fa_faPs_ne_faCn : faPs ≠ faCn := by decide
@[simp] theorem fa_faPs_ne_faT : faPs ≠ faT := by decide
@[simp] theorem fa_faPs_ne_faKl : faPs ≠ faKl := by decide
@[simp] theorem fa_faPs_ne_faKb : faPs ≠ faKb := by decide
@[simp] theorem fa_faPs_ne_faL : faPs ≠ faL := by decide
@[simp] theorem fa_faPs_ne_faM : faPs ≠ faM := by decide
@[simp] theorem fa_faPs_ne_faM2 : faPs ≠ faM2 := by decide
@[simp] theorem fa_faPs_ne_faTk : faPs ≠ faTk := by decide
@[simp] theorem fa_faPs_ne_faAc : faPs ≠ faAc := by decide
@[simp] theorem fa_faPs_ne_faPn : faPs ≠ faPn := by decide
@[simp] theorem fa_faPs_ne_faX : faPs ≠ faX := by decide
@[simp] theorem fa_faPs_ne_faB : faPs ≠ faB := by decide
@[simp] theorem fa_faPs_ne_lKb : faPs ≠ lKb := by decide
@[simp] theorem fa_faPs_ne_lCn : faPs ≠ lCn := by decide
@[simp] theorem fa_faPs_ne_lSrc : faPs ≠ lSrc := by decide
@[simp] theorem fa_faPs_ne_lDst : faPs ≠ lDst := by decide
@[simp] theorem fa_faPs_ne_lCi : faPs ≠ lCi := by decide
@[simp] theorem fa_faPs_ne_lCz : faPs ≠ lCz := by decide
@[simp] theorem fa_faPn_ne_faR : faPn ≠ faR := by decide
@[simp] theorem fa_faPn_ne_faKs : faPn ≠ faKs := by decide
@[simp] theorem fa_faPn_ne_faU : faPn ≠ faU := by decide
@[simp] theorem fa_faPn_ne_faA : faPn ≠ faA := by decide
@[simp] theorem fa_faPn_ne_faRp : faPn ≠ faRp := by decide
@[simp] theorem fa_faPn_ne_faCn : faPn ≠ faCn := by decide
@[simp] theorem fa_faPn_ne_faT : faPn ≠ faT := by decide
@[simp] theorem fa_faPn_ne_faKl : faPn ≠ faKl := by decide
@[simp] theorem fa_faPn_ne_faKb : faPn ≠ faKb := by decide
@[simp] theorem fa_faPn_ne_faL : faPn ≠ faL := by decide
@[simp] theorem fa_faPn_ne_faM : faPn ≠ faM := by decide
@[simp] theorem fa_faPn_ne_faM2 : faPn ≠ faM2 := by decide
@[simp] theorem fa_faPn_ne_faTk : faPn ≠ faTk := by decide
@[simp] theorem fa_faPn_ne_faAc : faPn ≠ faAc := by decide
@[simp] theorem fa_faPn_ne_faPs : faPn ≠ faPs := by decide
@[simp] theorem fa_faPn_ne_faX : faPn ≠ faX := by decide
@[simp] theorem fa_faPn_ne_faB : faPn ≠ faB := by decide
@[simp] theorem fa_faPn_ne_lKb : faPn ≠ lKb := by decide
@[simp] theorem fa_faPn_ne_lCn : faPn ≠ lCn := by decide
@[simp] theorem fa_faPn_ne_lSrc : faPn ≠ lSrc := by decide
@[simp] theorem fa_faPn_ne_lDst : faPn ≠ lDst := by decide
@[simp] theorem fa_faPn_ne_lCi : faPn ≠ lCi := by decide
@[simp] theorem fa_faPn_ne_lCz : faPn ≠ lCz := by decide
@[simp] theorem fa_faX_ne_faR : faX ≠ faR := by decide
@[simp] theorem fa_faX_ne_faKs : faX ≠ faKs := by decide
@[simp] theorem fa_faX_ne_faU : faX ≠ faU := by decide
@[simp] theorem fa_faX_ne_faA : faX ≠ faA := by decide
@[simp] theorem fa_faX_ne_faRp : faX ≠ faRp := by decide
@[simp] theorem fa_faX_ne_faCn : faX ≠ faCn := by decide
@[simp] theorem fa_faX_ne_faT : faX ≠ faT := by decide
@[simp] theorem fa_faX_ne_faKl : faX ≠ faKl := by decide
@[simp] theorem fa_faX_ne_faKb : faX ≠ faKb := by decide
@[simp] theorem fa_faX_ne_faL : faX ≠ faL := by decide
@[simp] theorem fa_faX_ne_faM : faX ≠ faM := by decide
@[simp] theorem fa_faX_ne_faM2 : faX ≠ faM2 := by decide
@[simp] theorem fa_faX_ne_faTk : faX ≠ faTk := by decide
@[simp] theorem fa_faX_ne_faAc : faX ≠ faAc := by decide
@[simp] theorem fa_faX_ne_faPs : faX ≠ faPs := by decide
@[simp] theorem fa_faX_ne_faPn : faX ≠ faPn := by decide
@[simp] theorem fa_faX_ne_faB : faX ≠ faB := by decide
@[simp] theorem fa_faX_ne_lKb : faX ≠ lKb := by decide
@[simp] theorem fa_faX_ne_lCn : faX ≠ lCn := by decide
@[simp] theorem fa_faX_ne_lSrc : faX ≠ lSrc := by decide
@[simp] theorem fa_faX_ne_lDst : faX ≠ lDst := by decide
@[simp] theorem fa_faX_ne_lCi : faX ≠ lCi := by decide
@[simp] theorem fa_faX_ne_lCz : faX ≠ lCz := by decide
@[simp] theorem fa_faB_ne_faR : faB ≠ faR := by decide
@[simp] theorem fa_faB_ne_faKs : faB ≠ faKs := by decide
@[simp] theorem fa_faB_ne_faU : faB ≠ faU := by decide
@[simp] theorem fa_faB_ne_faA : faB ≠ faA := by decide
@[simp] theorem fa_faB_ne_faRp : faB ≠ faRp := by decide
@[simp] theorem fa_faB_ne_faCn : faB ≠ faCn := by decide
@[simp] theorem fa_faB_ne_faT : faB ≠ faT := by decide
@[simp] theorem fa_faB_ne_faKl : faB ≠ faKl := by decide
@[simp] theorem fa_faB_ne_faKb : faB ≠ faKb := by decide
@[simp] theorem fa_faB_ne_faL : faB ≠ faL := by decide
@[simp] theorem fa_faB_ne_faM : faB ≠ faM := by decide
@[simp] theorem fa_faB_ne_faM2 : faB ≠ faM2 := by decide
@[simp] theorem fa_faB_ne_faTk : faB ≠ faTk := by decide
@[simp] theorem fa_faB_ne_faAc : faB ≠ faAc := by decide
@[simp] theorem fa_faB_ne_faPs : faB ≠ faPs := by decide
@[simp] theorem fa_faB_ne_faPn : faB ≠ faPn := by decide
@[simp] theorem fa_faB_ne_faX : faB ≠ faX := by decide
@[simp] theorem fa_faB_ne_lKb : faB ≠ lKb := by decide
@[simp] theorem fa_faB_ne_lCn : faB ≠ lCn := by decide
@[simp] theorem fa_faB_ne_lSrc : faB ≠ lSrc := by decide
@[simp] theorem fa_faB_ne_lDst : faB ≠ lDst := by decide
@[simp] theorem fa_faB_ne_lCi : faB ≠ lCi := by decide
@[simp] theorem fa_faB_ne_lCz : faB ≠ lCz := by decide
@[simp] theorem fa_lKb_ne_faR : lKb ≠ faR := by decide
@[simp] theorem fa_lKb_ne_faKs : lKb ≠ faKs := by decide
@[simp] theorem fa_lKb_ne_faU : lKb ≠ faU := by decide
@[simp] theorem fa_lKb_ne_faA : lKb ≠ faA := by decide
@[simp] theorem fa_lKb_ne_faRp : lKb ≠ faRp := by decide
@[simp] theorem fa_lKb_ne_faCn : lKb ≠ faCn := by decide
@[simp] theorem fa_lKb_ne_faT : lKb ≠ faT := by decide
@[simp] theorem fa_lKb_ne_faKl : lKb ≠ faKl := by decide
@[simp] theorem fa_lKb_ne_faKb : lKb ≠ faKb := by decide
@[simp] theorem fa_lKb_ne_faL : lKb ≠ faL := by decide
@[simp] theorem fa_lKb_ne_faM : lKb ≠ faM := by decide
@[simp] theorem fa_lKb_ne_faM2 : lKb ≠ faM2 := by decide
@[simp] theorem fa_lKb_ne_faTk : lKb ≠ faTk := by decide
@[simp] theorem fa_lKb_ne_faAc : lKb ≠ faAc := by decide
@[simp] theorem fa_lKb_ne_faPs : lKb ≠ faPs := by decide
@[simp] theorem fa_lKb_ne_faPn : lKb ≠ faPn := by decide
@[simp] theorem fa_lKb_ne_faX : lKb ≠ faX := by decide
@[simp] theorem fa_lKb_ne_faB : lKb ≠ faB := by decide
@[simp] theorem fa_lCn_ne_faR : lCn ≠ faR := by decide
@[simp] theorem fa_lCn_ne_faKs : lCn ≠ faKs := by decide
@[simp] theorem fa_lCn_ne_faU : lCn ≠ faU := by decide
@[simp] theorem fa_lCn_ne_faA : lCn ≠ faA := by decide
@[simp] theorem fa_lCn_ne_faRp : lCn ≠ faRp := by decide
@[simp] theorem fa_lCn_ne_faCn : lCn ≠ faCn := by decide
@[simp] theorem fa_lCn_ne_faT : lCn ≠ faT := by decide
@[simp] theorem fa_lCn_ne_faKl : lCn ≠ faKl := by decide
@[simp] theorem fa_lCn_ne_faKb : lCn ≠ faKb := by decide
@[simp] theorem fa_lCn_ne_faL : lCn ≠ faL := by decide
@[simp] theorem fa_lCn_ne_faM : lCn ≠ faM := by decide
@[simp] theorem fa_lCn_ne_faM2 : lCn ≠ faM2 := by decide
@[simp] theorem fa_lCn_ne_faTk : lCn ≠ faTk := by decide
@[simp] theorem fa_lCn_ne_faAc : lCn ≠ faAc := by decide
@[simp] theorem fa_lCn_ne_faPs : lCn ≠ faPs := by decide
@[simp] theorem fa_lCn_ne_faPn : lCn ≠ faPn := by decide
@[simp] theorem fa_lCn_ne_faX : lCn ≠ faX := by decide
@[simp] theorem fa_lCn_ne_faB : lCn ≠ faB := by decide
@[simp] theorem fa_lSrc_ne_faR : lSrc ≠ faR := by decide
@[simp] theorem fa_lSrc_ne_faKs : lSrc ≠ faKs := by decide
@[simp] theorem fa_lSrc_ne_faU : lSrc ≠ faU := by decide
@[simp] theorem fa_lSrc_ne_faA : lSrc ≠ faA := by decide
@[simp] theorem fa_lSrc_ne_faRp : lSrc ≠ faRp := by decide
@[simp] theorem fa_lSrc_ne_faCn : lSrc ≠ faCn := by decide
@[simp] theorem fa_lSrc_ne_faT : lSrc ≠ faT := by decide
@[simp] theorem fa_lSrc_ne_faKl : lSrc ≠ faKl := by decide
@[simp] theorem fa_lSrc_ne_faKb : lSrc ≠ faKb := by decide
@[simp] theorem fa_lSrc_ne_faL : lSrc ≠ faL := by decide
@[simp] theorem fa_lSrc_ne_faM : lSrc ≠ faM := by decide
@[simp] theorem fa_lSrc_ne_faM2 : lSrc ≠ faM2 := by decide
@[simp] theorem fa_lSrc_ne_faTk : lSrc ≠ faTk := by decide
@[simp] theorem fa_lSrc_ne_faAc : lSrc ≠ faAc := by decide
@[simp] theorem fa_lSrc_ne_faPs : lSrc ≠ faPs := by decide
@[simp] theorem fa_lSrc_ne_faPn : lSrc ≠ faPn := by decide
@[simp] theorem fa_lSrc_ne_faX : lSrc ≠ faX := by decide
@[simp] theorem fa_lSrc_ne_faB : lSrc ≠ faB := by decide
@[simp] theorem fa_lDst_ne_faR : lDst ≠ faR := by decide
@[simp] theorem fa_lDst_ne_faKs : lDst ≠ faKs := by decide
@[simp] theorem fa_lDst_ne_faU : lDst ≠ faU := by decide
@[simp] theorem fa_lDst_ne_faA : lDst ≠ faA := by decide
@[simp] theorem fa_lDst_ne_faRp : lDst ≠ faRp := by decide
@[simp] theorem fa_lDst_ne_faCn : lDst ≠ faCn := by decide
@[simp] theorem fa_lDst_ne_faT : lDst ≠ faT := by decide
@[simp] theorem fa_lDst_ne_faKl : lDst ≠ faKl := by decide
@[simp] theorem fa_lDst_ne_faKb : lDst ≠ faKb := by decide
@[simp] theorem fa_lDst_ne_faL : lDst ≠ faL := by decide
@[simp] theorem fa_lDst_ne_faM : lDst ≠ faM := by decide
@[simp] theorem fa_lDst_ne_faM2 : lDst ≠ faM2 := by decide
@[simp] theorem fa_lDst_ne_faTk : lDst ≠ faTk := by decide
@[simp] theorem fa_lDst_ne_faAc : lDst ≠ faAc := by decide
@[simp] theorem fa_lDst_ne_faPs : lDst ≠ faPs := by decide
@[simp] theorem fa_lDst_ne_faPn : lDst ≠ faPn := by decide
@[simp] theorem fa_lDst_ne_faX : lDst ≠ faX := by decide
@[simp] theorem fa_lDst_ne_faB : lDst ≠ faB := by decide
@[simp] theorem fa_lCi_ne_faR : lCi ≠ faR := by decide
@[simp] theorem fa_lCi_ne_faKs : lCi ≠ faKs := by decide
@[simp] theorem fa_lCi_ne_faU : lCi ≠ faU := by decide
@[simp] theorem fa_lCi_ne_faA : lCi ≠ faA := by decide
@[simp] theorem fa_lCi_ne_faRp : lCi ≠ faRp := by decide
@[simp] theorem fa_lCi_ne_faCn : lCi ≠ faCn := by decide
@[simp] theorem fa_lCi_ne_faT : lCi ≠ faT := by decide
@[simp] theorem fa_lCi_ne_faKl : lCi ≠ faKl := by decide
@[simp] theorem fa_lCi_ne_faKb : lCi ≠ faKb := by decide
@[simp] theorem fa_lCi_ne_faL : lCi ≠ faL := by decide
@[simp] theorem fa_lCi_ne_faM : lCi ≠ faM := by decide
@[simp] theorem fa_lCi_ne_faM2 : lCi ≠ faM2 := by decide
@[simp] theorem fa_lCi_ne_faTk : lCi ≠ faTk := by decide
@[simp] theorem fa_lCi_ne_faAc : lCi ≠ faAc := by decide
@[simp] theorem fa_lCi_ne_faPs : lCi ≠ faPs := by decide
@[simp] theorem fa_lCi_ne_faPn : lCi ≠ faPn := by decide
@[simp] theorem fa_lCi_ne_faX : lCi ≠ faX := by decide
@[simp] theorem fa_lCi_ne_faB : lCi ≠ faB := by decide
@[simp] theorem fa_lCz_ne_faR : lCz ≠ faR := by decide
@[simp] theorem fa_lCz_ne_faKs : lCz ≠ faKs := by decide
@[simp] theorem fa_lCz_ne_faU : lCz ≠ faU := by decide
@[simp] theorem fa_lCz_ne_faA : lCz ≠ faA := by decide
@[simp] theorem fa_lCz_ne_faRp : lCz ≠ faRp := by decide
@[simp] theorem fa_lCz_ne_faCn : lCz ≠ faCn := by decide
@[simp] theorem fa_lCz_ne_faT : lCz ≠ faT := by decide
@[simp] theorem fa_lCz_ne_faKl : lCz ≠ faKl := by decide
@[simp] theorem fa_lCz_ne_faKb : lCz ≠ faKb := by decide
@[simp] theorem fa_lCz_ne_faL : lCz ≠ faL := by decide
@[simp] theorem fa_lCz_ne_faM : lCz ≠ faM := by decide
@[simp] theorem fa_lCz_ne_faM2 : lCz ≠ faM2 := by decide
@[simp] theorem fa_lCz_ne_faTk : lCz ≠ faTk := by decide
@[simp] theorem fa_lCz_ne_faAc : lCz ≠ faAc := by decide
@[simp] theorem fa_lCz_ne_faPs : lCz ≠ faPs := by decide
@[simp] theorem fa_lCz_ne_faPn : lCz ≠ faPn := by decide
@[simp] theorem fa_lCz_ne_faX : lCz ≠ faX := by decide
@[simp] theorem fa_lCz_ne_faB : lCz ≠ faB := by decide

def faParams : List MlS := [faR, faKs, faU, faA, faRp, faCn]
def faLocals : List MlS := [faT, faKl, faKb, faL, faM, faM2, faTk, faAc, faPs, faPn, faX, faB, lCn, lSrc, lDst, lCi, lCz]

def faCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local faT (.load .one (.op .add [vv faR, .const 16])))
  (.seq (.assign .local faL (.load .one (vv faA)))
  (.ite (.cmp .equal (vv faT) (.const 1))
    (.seq (.assign .local faKl (.load .one (vv faKs)))
    (.seq (.assign .local lCn (.op .add [vv faKl, .const 1]))
    (allocP C faKb (.panop .mul [vv lCn, .const 8])
    (.seq (.assign .local lSrc (vv faKs)) (.seq (.assign .local lDst (vv faKb)) (.seq (.assign .local lCi (.const 0))
    (.seq copyLoop
    (.seq (.assign .local faM2 (.cmp .lower (vv faRp) (vv faL)))
    (.seq (.assign .local faM (.op .add [vv faL, .op .and [.op .sub [vv faRp, vv faL], .op .sub [.const 0, vv faM2]]]))
    (takeCopyP C faTk faA faM
    (allocP C faAc (.const 8) (.seq (.store (vv faAc) (.const 0))
    (.seq (.assign .local faPs (.load .one (.op .add [vv faR, .const 32])))
    (.seq (.assign .local faPn (.load .one (vv faPs)))
    (.seq (.call (some (some (.local, faX), none)) fIp
        [.op .add [vv faPs, .const 8], vv faPn, vv faKb, vv faU, vv faTk, vv faRp, vv faAc])
      (.return (vv faX)))))))))))))))))
    (.seq (.assign .local faM2 (.cmp .lower (vv faCn) (vv faL)))
    (.seq (.assign .local faM (.op .add [vv faL, .op .and [.op .sub [vv faCn, vv faL], .op .sub [.const 0, vv faM2]]]))
    (takeCopyP C faB faA faM (.return (vv faB)))))))

def faBody (C : Ctx) : ProgHOL 64 := prologue faLocals (faCore C)

section
variable {σ : Type}

structure FaCodes (C : Ctx) : Prop where
  ip : IpCodes C
  self : C.code.lookup fFa = some (faParams.map (fun p => (p, ShapeHOL.one)), faBody C, .one)

theorem fa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ faLocals → (ctxEnv C ++ faParams.zip vals).get x = none :=
  Knot.params_none C faLocals faParams vals (by decide) (by decide)

theorem take_min (xs : List EIdx) (k : Nat) : xs.take (if k < xs.length then k else xs.length) = xs.take k := by
  split
  · rfl
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem fa_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : FaCodes C) (s : AState)
    (rl : IRecRule) (qr : Nat) (hrule : RuleE C.EB C.EH qr rl) (lps : List NIdx) (ok : Nat)
    (hks0 : EBlk C.EH ok (lps.map Enc.idxW)) (hll : lps.length + 1 < 2 ^ 60) (us : LsIdx)
    (ks : List ConLeche.Name) (vs : List ConLeche.Level) (args : List EIdx) (rP cnP : Nat)
    (hrP : rP < 2 ^ 63) (hcn : cnP < 2 ^ 63) (Q : AState → Prop)
    (hQ : ∀ s, Q s → StateOK s ∧ ReadNCacheOK s.caches.readNC s.store ∧ ReadLCacheOK s.caches.readLC s.store ∧
      ReadLsCacheOK s.caches.readLsC s.store ∧ Frontend.denoteNList s.store.ns lps = some ks ∧
      denoteLs s.store.lss us = some vs ∧
      ∀ lv pins, rl.fire = .nested lv pins → ∀ p, p ∈ pins → (denoteE s.store p).isSome = true)
    (hQi : ∀ s p q s', Q s → instLPFast coreWalkFuel lps us p s = .ok (q, s') → Q s')
    (hQs : ∀ s q r s', Q s → instSpine coreWalkFuel (args.take rP) (rP - 1) q s = .ok (r, s') → Q s')
    (hq : Q s) (H : List (BitVec 64)) (hp : C.H <+: H) (oa : Nat) (hba : BlkAt H oa (args.map Enc.idxW))
    (hal : args.length < 2 ^ 58) :
    SpecR (σ := σ) (Pre (ctxH C H) s (faParams.zip [ecell C qr, ecell C ok, Enc.idxW us, cellA C oa,
      BitVec.ofNat 64 rP, BitVec.ofNat 64 cnP])) (faBody C) s (recFireArgs rl cnP lps us args rP)
      (PostA (ctxH C H)) := by
  refine specR_prologue (postA_locals _) (fa_none _ _) ?_
  unfold faCore recFireArgs
  have hl0 : C.EH[ok]? = some (BitVec.ofNat 64 lps.length) := by simpa using hks0.1
  obtain ⟨hlo, hlv0⟩ := blkAt_get0 hba
  have hw0 : (ctxH C H).H[oa]? = some (BitVec.ofNat 64 args.length) := by
    show H[oa]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp
  rcases hf : rl.fire with _ | ⟨lv, pins⟩ | lv
  · have hft : C.EH[qr + 2]? = some 0 := by have := hrule.2.2.1; rw [hf] at this; exact this
    refine specR_envLoadI faT (.op .add [vv faR, .const 16]) (qr + 2) _ (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) faL (vv faA) oa _ hw0 (by decide)
      (by simp +decide [Env.get, faParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI faM2 _ (if BitVec.ofNat 64 cnP < BitVec.ofNat 64 args.length then 1#64 else 0#64) (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
    refine specR_assignI faM _ (BitVec.ofNat 64 (if cnP < args.length then cnP else args.length)) (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv]; simpa using min_word cnP args.length (by omega) (by omega)) ?_
    refine specR_takeCopyI (C := C) hok faB faA faM oa (if cnP < args.length then cnP else args.length) (args.map Enc.idxW)
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ (by simp +decide [Env.get, faParams, ctxEnv])
      (by simp +decide [Env.get]) (by simp; split <;> omega) (by simp; omega) hba (by simp +decide [Env.get, faParams, ctxEnv])
      ⟨by decide, by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide⟩ (fun H' o hp' hL hb' => ?_)
    rw [← List.map_take, take_min] at hb'
    exact specR_returnI _ (cellA C o) (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨H', o, hp', rfl, hb', sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hfe := hrule.2.2.1; rw [hf] at hfe
    obtain ⟨hft, -, w4, hw4, ops, hw4', hbp⟩ := hfe
    subst hw4'
    refine specR_envLoadI faT (.op .add [vv faR, .const 16]) (qr + 2) _ (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) faL (vv faA) oa _ hw0 (by decide)
      (by simp +decide [Env.get, faParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_atEntry fun t ht => ?_
    have hpl : pins.length < 2 ^ 61 := by
      have := eblk_small (ctxOK_H hok H) ht.sr (show EBlk (ctxH C H).EH ops (pins.map Enc.idxW) from hbp)
      simpa using this
    refine specR_envLoadI faKl (vv faKs) ok _ (by decide) (by simp +decide [Env.get, faParams, ctxEnv]; rfl) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (lps.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI (C := ctxH C H) faKb (.panop .mul [vv lCn, .const 8]) (lps.length + 1) (by omega) (by decide)
      (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _) (fun H1 ws hpa hwl2 hcap => ?_)
    refine specR_assignI lSrc (vv faKs) (ecell C ok) (by decide) (by simp +decide [sev, Env.get, faParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDst (vv faKb) (cellA C H1.length) (by decide) (by simp +decide [sev, Env.get] <;> rfl) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = lps.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) ok H1.length
      (by decide) (fun j hj => ?_) (by simp [hwl2]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, faParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hks0.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show ok + (j + 1) = ok + 1 + j by omega]; simpa using this
    generalize hF : fillI (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H1.length
      (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = F
    have hblkK : BlkAt F H1.length (lps.map Enc.idxW) := by
      rw [← hF]; exact blk_of_fillI _ _ H1.length _ (by simp) (by simp [hwl2])
    have hpF : H <+: F := by
      rw [← hF]; exact prefix_fillI _ _ _ H hpa.length_le (hpa.trans (List.prefix_append _ _)) _
    refine specR_assignI faM2 _ (if BitVec.ofNat 64 rP < BitVec.ofNat 64 args.length then 1#64 else 0#64) (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
    refine specR_assignI faM _ (BitVec.ofNat 64 (if rP < args.length then rP else args.length)) (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv]; simpa using min_word rP args.length (by omega) (by omega)) ?_
    refine specR_takeCopyI (C := C) hok faTk faA faM oa (if rP < args.length then rP else args.length)
      (args.map Enc.idxW) ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      (by simp +decide [Env.get, faParams, ctxEnv]) (by simp +decide [Env.get]) (by simp; split <;> omega)
      (by simp; omega) (blkAt_mono hba hpF) (by simp +decide [Env.get, faParams, ctxEnv])
      ⟨by decide, by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide⟩ (fun H2 o2 hp2 hL2 hb2 => ?_)
    rw [← List.map_take, take_min] at hb2
    refine specR_allocI (C := ctxH C H2) faAc (.const 8) 1 (by decide) (by decide) (fun _ => rfl)
      (fun H3 ws3 hp3 hws3 _ => ?_)
    have hj3 : H3.length < (ctxH (ctxH C H2) (H3 ++ ws3)).H.length := by
      show H3.length < (H3 ++ ws3).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv faAc) (.const 0) H3.length hj3 0 (by simp <;> rfl) rfl ?_
    change SpecR (Inv (ctxH C ((H3 ++ ws3).set H3.length 0)) _ _ _ _) _ _ _ _
    generalize hG : (H3 ++ ws3).set H3.length 0 = G
    have hpG : H2 <+: G := by
      rw [← hG]; exact prefix_set_ge (hp3.trans (List.prefix_append _ _)) _ hp3.length_le _
    have hbA : BlkAt G H3.length (([] : List EIdx).map Enc.idxW) :=
      ⟨by rw [← hG, List.getElem?_set_self (by simp; omega)]; rfl, fun i hi => absurd hi (by simp)⟩
    have hHG : H <+: G := hpF.trans (hp2.trans hpG)
    refine specR_envLoadI (C := ctxH C G) faPs (.op .add [vv faR, .const 32]) (qr + 4) _ (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv]; exact UD.ecell_add32 C qr)
      (by simpa using hw4 : C.EH[qr + 4]? = _) ?_
    refine specR_envLoadI (C := ctxH C G) faPn (vv faPs) ops _ (by decide) (by simp +decide [Env.get]; rfl)
      (by simpa using hbp.1 : C.EH[ops]? = _) ?_
    refine specR_congr (m' := instSpinePins lps us args rP pins >>= fun xs => pure (([] : List EIdx) ++ xs)) (by simp) ?_
    refine specR_bindPure ?_
    refine specR_callNIH (C := ctxH C G) faX fIp ipParams
      [.op .add [vv faPs, .const 8], vv faPn, vv faKb, vv faU, vv faTk, vv faRp, vv faAc] ipBody
      [ecell C (ops + 1), BitVec.ofNat 64 pins.length, cellA C H1.length, Enc.idxW us, cellA C o2,
        BitVec.ofNat 64 rP, cellA C H3.length] (by decide) rfl (by decide) hc.ip.self
      ⟨by simp +decide [sev, Env.get]; exact ecell_add8 C ops, by simp +decide [Env.get],
        by simp +decide [Env.get] <;> rfl, by simp +decide [Env.get, faParams, ctxEnv],
        by simp +decide [Env.get] <;> rfl, by simp +decide [Env.get, faParams, ctxEnv],
        by simp +decide [Env.get] <;> rfl, trivial⟩
      (PostA (ctxH C G)) (fun a w _ H4 => ∃ o4, w = cellA C o4 ∧ BlkAt H4 o4 (a.map Enc.idxW))
      (fun a w s' st ⟨H4, o4, hp4, hw, hb4, hsr⟩ => ⟨H4, hp4, ⟨o4, hw, hb4⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipParams _ rfl hlk)
        (ip_spec ra C hok hc.ip lps ks us vs args rP hrP H1.length o2 pins Q
          (fun s h => let ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hQ s h; ⟨a1, a2, a3, a4, a5, a6, a7 lv pins hf⟩) hQi hQs
          pins (ops + 1) G [] H3.length s (hp.trans hHG) (fun p hp => hp)
          (fun j hj => by have h' := hbp.2 j (by simpa using hj); simpa using h')
          hbA (blkAt_mono hblkK (hp2.trans hpG)) (blkAt_mono hb2 hpG) hq (by omega)))
      (fun r w s4 H4 hp4 ⟨o4, hw, hb4⟩ => ?_)
    subst hw
    exact specR_returnI _ (cellA C o4) (by simp)
      (fun t ht => ⟨H4, o4, hHG.trans hp4, rfl, by simpa using hb4, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hfe := hrule.2.2.1; rw [hf] at hfe
    obtain ⟨hft, -⟩ := hfe
    refine specR_envLoadI faT (.op .add [vv faR, .const 16]) (qr + 2) _ (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) faL (vv faA) oa _ hw0 (by decide)
      (by simp +decide [Env.get, faParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI faM2 _ (if BitVec.ofNat 64 cnP < BitVec.ofNat 64 args.length then 1#64 else 0#64) (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
    refine specR_assignI faM _ (BitVec.ofNat 64 (if cnP < args.length then cnP else args.length)) (by decide)
      (by simp +decide [sev, Env.get, faParams, ctxEnv]; simpa using min_word cnP args.length (by omega) (by omega)) ?_
    refine specR_takeCopyI (C := C) hok faB faA faM oa (if cnP < args.length then cnP else args.length) (args.map Enc.idxW)
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ (by simp +decide [Env.get, faParams, ctxEnv])
      (by simp +decide [Env.get]) (by simp; split <;> omega) (by simp; omega) hba (by simp +decide [Env.get, faParams, ctxEnv])
      ⟨by decide, by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide⟩ (fun H' o hp' hL hb' => ?_)
    rw [← List.map_take, take_min] at hb'
    exact specR_returnI _ (cellA C o) (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨H', o, hp', rfl, hb', sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
