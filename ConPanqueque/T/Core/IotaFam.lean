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

end

end ConPanqueque.T.WC
