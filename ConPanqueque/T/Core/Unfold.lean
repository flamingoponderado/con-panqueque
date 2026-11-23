import ConPanqueque.T.Core.ConstVal
import ConPanqueque.T.Ex.AppArgs
import ConPanqueque.T.Ex.MkApp
import ConPanqueque.T.LsView
import ConPanqueque.T.PinRead
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `unfoldDefinition`

The tail after the definition is found (`unfoldD`): check the level count, instantiate the value through
`constValAt`, and apply it to the spine's arguments.
-/

namespace ConPanqueque.T.UD

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.T.Knot (PostK postK_locals params_none specR_of_pre)
open ConPanqueque.T.ILP (fInstLPF ilpfBody CodesILP ilpBody)
open ConPanqueque.T.CV (cvBody cvParams cv_spec)
open ConRon.Bridge

def uE := ofString "ue"
def uN := ofString "un"
def uUs := ofString "uus"
def uP := ofString "up"
def uLp := ofString "ulp"
def uV := ofString "uv"
def uLl := ofString "ull"
def uCv := ofString "ucv"
def uArgs := ofString "uargs"
def uLen := ofString "ulen"
def uR := ofString "ur"
def fCV := ofString "constValAt"
def uH := ofString "uh"
def uW := ofString "uw"
def uT := ofString "ut"
def fUD := ofString "unfoldD"
def fUnfold := ofString "unfoldDefinition"

def udParams : List MlS := [uE, uN, uUs, uP]
def udLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, uLp, uV, uLl, uCv, uArgs, uLen, uR]

def udCore : ProgHOL 64 :=
  .seq (.assign .local uLp (.load .one (.op .add [vv uP, .const 16])))
  (.seq (.assign .local uV (.load .one (.op .add [vv uP, .const 32])))
  (.seq (.assign .local uLl (.load .one (vv uLp)))
  (.seq (.assign .local lFl (vv lFls))
  (.seq (.assign .local lDh (vv uUs))
  (.seq lsViewP
  (.ite (.cmp .notEqual (vv lRn) (vv uLl)) (.return (.const 0))
  (.seq (.call (some (some (.local, uCv), none)) fCV [vv uN, vv uLp, vv uV, vv uUs])
  (.seq (.call (some (some (.local, uArgs), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv uE])
  (.seq (.assign .local uLen (.load .one (vv uArgs)))
  (.seq (.call (some (some (.local, uR), none)) ExK.fMka [vv uCv, vv uArgs, .const 0, vv uLen])
  (.return (.op .add [vv uR, .const 1]))))))))))))

def udBody : ProgHOL 64 := prologue udLocals udCore

/-- The twin's tail of `unfoldDefinition`, once the definition is found. -/
def unfoldD (e : EIdx) (n : NIdx) (us : LsIdx) (cv : IConstantVal) (value : EIdx) : AM (Option EIdx) := do
  let usl ← viewLs us
  if usl.length = cv.levelParams.length then do
    let v ← constValAt n cv.levelParams value us
    let args ← getAppArgs coreWalkFuel e
    let r ← mkAppN v args
    pure (some r)
  else pure none

section
variable {σ : Type}

/-- The post of a Core helper returning an optional handle (`0` for `none`, `h + 1` for `some h`). -/
def PostO (C : Ctx) (a : Option EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = optW a ∧ SR (ctxH C H') s' st

theorem postO_locals (C : Ctx) : ∀ (a : Option EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostO C a w s' st → PostO C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem ud_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ udLocals → (ctxEnv C ++ udParams.zip vals).get x = none :=
  params_none C udLocals udParams vals (by decide) (by decide)

theorem viewLs_run (h : LsIdx) (s : AState) (v : LsNodeView) (hv : s.store.lss.view h = some v) :
    viewLs h s = .ok (v, s) := by
  simp [viewLs, hv, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
    Except.pure]

theorem ecell_add16 (C : Ctx) (o : Nat) : ecell C o + 16 = ecell C (o + 2) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 (8 * 2) from rfl, ecell_add]

theorem ecell_add32 (C : Ctx) (o : Nat) : ecell C o + 32 = ecell C (o + 4) := by
  rw [show (32 : BitVec 64) = BitVec.ofNat 64 (8 * 4) from rfl, ecell_add]

theorem specR_heapLoadI' {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (j : Nat) (w : BitVec 64)
    (hw : C.H[j]? = some w) (hx : x ∈ D) (he : sev Γ e = some (cellA C j))
    (h : SpecR (Inv C s ((x, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one e)) rest) s m R := by
  obtain ⟨hj, hjw⟩ := List.getElem?_eq_some_iff.mp hw
  exact specR_heapLoadI x e j hj hx he (hjw ▸ h)

theorem ofNat_eq_iff_small (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; rw [h]

theorem ud_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesILP C (ilpBody C))
    (hcf : C.code.lookup fInstLPF = some (ILP.ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one))
    (hccv : C.code.lookup fCV = some (cvParams.map (fun p => (p, ShapeHOL.one)), cvBody C, .one))
    (hcg : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one))
    (hcm : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
      ExK.mkaBody, .one))
    (s : AState) (e : EIdx) (n : NIdx) (us : LsIdx) (cv : IConstantVal) (value : EIdx)
    (hint : ConLeche.ReducibilityHint) (o : Nat) (hci : CIE C.EB C.EH o (.defnInfo cv value hint))
    (ks : List ConLeche.Name) (vsL : List ConLeche.Level)
    (hks : Frontend.denoteNList s.store.ns cv.levelParams = some ks) (hus : denoteLs s.store.lss us = some vsL)
    (hst : StateOK s) (hcn : ReadNCacheOK s.caches.readNC s.store) (hcl : ReadLCacheOK s.caches.readLC s.store)
    (hcls : ReadLsCacheOK s.caches.readLsC s.store) (hden : (denoteE s.store value).isSome = true)
    (hlen : cv.levelParams.length + 1 < 2 ^ 60) :
    SpecR (σ := σ) (Pre C s (udParams.zip [Enc.idxW e, Enc.idxW n, Enc.idxW us, ecell C o])) udBody s
      (unfoldD e n us cv value) (PostO C) := by
  obtain ⟨⟨_, ⟨w, hw, o', hw', hblk⟩, _⟩, _, hval, _⟩ := hci
  subst hw'
  refine specR_prologue (postO_locals C) (ud_none C _) ?_
  unfold udCore
  refine specR_envLoadI uLp (.op .add [vv uP, .const 16]) (o + 2) _ (by decide)
    (by simp +decide [sev, Env.get, udParams, ctxEnv]; exact ecell_add16 C o) (by simpa using hw) ?_
  refine specR_envLoadI uV (.op .add [vv uP, .const 32]) (o + 4) _ (by decide)
    (by simp +decide [sev, Env.get, udParams, ctxEnv]; exact ecell_add32 C o) hval ?_
  have hl0 : C.EH[o']? = some (BitVec.ofNat 64 cv.levelParams.length) := by
    have := hblk.1; simpa [IConstantInfo.toConstantVal] using this
  refine specR_envLoadI uLl (vv uLp) o' _ (by decide) (by simp +decide [Env.get]; rfl) hl0 ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, udParams, ctxEnv]) ?_
  refine specR_assignI lDh (vv uUs) (Enc.idxW us) (by decide) (by simp +decide [Env.get, udParams, ctxEnv]) ?_
  refine specR_lsviewPI us (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, udParams, ctxEnv])
    (by decide) (fun v P hv _ hvl => ?_)
  refine specR_congr (m' := if v.length = cv.levelParams.length then
      (constValAt n cv.levelParams value us >>= fun v1 => getAppArgs coreWalkFuel e >>= fun args =>
        mkAppN v1 args >>= fun r => pure (some r)) else pure none)
    (by unfold unfoldD; simp only [bind, StateT.bind]; rw [viewLs_run us s v hv]; rfl) ?_
  have hvl' : v.length < 2 ^ 61 := by simpa using hvl
  by_cases hl : v.length = cv.levelParams.length
  · rw [if_pos hl]
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callNIH uCv fCV cvParams [vv uN, vv uLp, vv uV, vv uUs] (cvBody C)
      [Enc.idxW n, ecell C o', Enc.idxW value, Enc.idxW us] (by decide) rfl (by decide) hccv
      ⟨by simp +decide [sev, Env.get, udParams, ctxEnv], by simp +decide [sev, Env.get]; rfl,
        by simp +decide [sev, Env.get], by simp +decide [sev, Env.get, udParams, ctxEnv], trivial⟩
      (PostK C) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => specR_of_pre u (pre_of_lookups hu cvParams _ rfl hlk)
        (cv_spec ra C hok hc hcf s n cv.levelParams ks value us vsL o' hblk hlen hks hus hst hcn hcl hcls hden))
      (fun v1 w s1 H1 hp1 hw => ?_)
    subst hw
    refine specR_callNIH uArgs ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv uE] (ExG.gaaBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcg
      ⟨rfl, by simp +decide [sev, Env.get, udParams, ctxEnv], trivial⟩
      (PostA (ctxH C H1)) (fun a w _ H2 => ∃ o2, w = cellA C o2 ∧ BlkAt H2 o2 (a.map Enc.idxW))
      (fun a w s' st ⟨H2, o2, hp, hw, hb, hsr⟩ => ⟨H2, hp, ⟨o2, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec C hok hcg coreWalkFuel CV.coreWalkFuel_lt H1 e s1))
      (fun args w s2 H2 hp2 ⟨o2, hw, hb⟩ => ?_)
    subst hw
    obtain ⟨hlo, hlv⟩ := blkAt_get0 hb
    have hw0 : (ctxH C H2).H[o2]? = some (BitVec.ofNat 64 args.length) := by
      show H2[o2]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp
    refine specR_heapLoadI' (C := ctxH C H2) uLen (vv uArgs) o2 _ hw0 (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_atEntry fun t ht => ?_
    obtain ⟨H3, hp3, ha3⟩ := ht.sr.heap
    have hlen3 := ha3.len
    have hbl := blkAt_len hb
    have hp3l := hp3.length_le
    have hcap := hok.heapCap
    have hn : args.length < 2 ^ 59 := by
      rw [List.length_map] at hbl; simp only [ctxH] at hlen3 hp3l; omega
    refine specR_congr (m' := mkAppN v1 (args.drop 0) >>= fun r => pure (some r)) (by simp) ?_
    refine ILP.callE_spec (C := ctxH C H2) uR ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
      [vv uCv, vv uArgs, .const 0, vv uLen] ExK.mkaBody
      [Enc.idxW v1, cellA C o2, BitVec.ofNat 64 0, BitVec.ofNat 64 args.length] (by decide) rfl (by decide) hcm
      ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], rfl, by simp +decide [sev, Env.get], trivial⟩
      (ExK.mkAppN_spec ra (ctxH C H2) (ctxOK_H hok H2) hcm hc.internApp o2 args hb hn 0 (by omega) v1 s2)
      (fun r s3 => ?_)
    refine specR_returnI _ (Enc.idxW r + 1) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
    exact ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · rw [if_neg hl]
    have hne : BitVec.ofNat 64 v.length ≠ BitVec.ofNat 64 cv.levelParams.length := fun x =>
      hl ((ofNat_eq_iff_small _ _ (by omega) (by omega)).mp x)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_returnI _ 0 rfl (fun t ht => ?_)
    exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

/-! ## The head: `getAppFn`, the `const` view, the lookup -/

def ufLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, uH, uN, uUs, uW, uP, uT, uR]

def ufCore (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, uH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv uE])
  (.ite (tagIsE uH 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv uH)) (.seq eViewP
    (.seq (.assign .local uN (.load .one (vv lRp))) (.seq (.assign .local uUs (.load .one (.op .add [vv lRp, .const 8])))
    (envFindP C uW (vv uN)
    (.ite (.cmp .equal (vv uW) (.const 0)) (.return (.const 0))
    (.seq (.assign .local uP (.op .sub [vv uW, .const 1])) (.seq (.assign .local uT (.load .one (vv uP)))
    (.ite (.cmp .notEqual (vv uT) (.const 1)) (.return (.const 0))
    (.seq (.call (some (some (.local, uR), none)) fUD [vv uE, vv uN, vv uUs, vv uP]) (.return (vv uR)))))))))))))
    (.return (.const 0)))

def ufBody (C : Ctx) : ProgHOL 64 := prologue ufLocals (ufCore C)

theorem uf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ufLocals → (ctxEnv C ++ [uE].zip vals).get x = none :=
  params_none C ufLocals [uE] vals (by decide) (by decide)

theorem unfoldDefinition_eq (fe : IFEnv) (e : EIdx) :
    unfoldDefinition fe e = (getAppFn coreWalkFuel e >>= fun hh =>
      if hh.tag == ETag.const then
        (view hh >>= fun v => match v with
          | .const n us =>
            match fe.find? n with
            | some (.defnInfo cv value _) => unfoldD e n us cv value
            | _ => pure none
          | _ => pure none)
      else pure none) := by
  rfl

def ciTag : IConstantInfo → Nat
  | .axiomInfo _ => 0 | .defnInfo .. => 1 | .thmInfo _ => 2 | .indInfo .. => 3 | .ctorInfo .. => 4 | .recInfo .. => 5

theorem cie_tag {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) :
    H[o]? = some (BitVec.ofNat 64 (ciTag ci)) := by
  obtain ⟨_, h2⟩ := h
  cases ci <;> simp only at h2 <;> first | exact h2 | exact h2.1

theorem tagN_const {v : ENodeView} (h : v.tagN = 3) : ∃ n us, v = .const n us := by
  cases v <;> simp [ENodeView.tagN] at h ⊢

theorem uf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesILP C (ilpBody C))
    (hcf : C.code.lookup fInstLPF = some (ILP.ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one))
    (hccv : C.code.lookup fCV = some (cvParams.map (fun p => (p, ShapeHOL.one)), cvBody C, .one))
    (hcg : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one))
    (hcm : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
      ExK.mkaBody, .one))
    (hcud : C.code.lookup fUD = some (udParams.map (fun p => (p, ShapeHOL.one)), udBody, .one))
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (s : AState) (e : EIdx)
    (hst : StateOK s) (hcn : ReadNCacheOK s.caches.readNC s.store) (hcl : ReadLCacheOK s.caches.readLC s.store)
    (hcls : ReadLsCacheOK s.caches.readLsC s.store)
    (hpre : ∀ hh n us cv value hint, getAppFn coreWalkFuel e s = .ok (hh, s) → s.store.view hh = some (.const n us) →
      C.fe.find? n = some (.defnInfo cv value hint) → ∃ ks vsL,
        Frontend.denoteNList s.store.ns cv.levelParams = some ks ∧ denoteLs s.store.lss us = some vsL ∧
        (denoteE s.store value).isSome = true ∧ cv.levelParams.length + 1 < 2 ^ 60) :
    SpecR (σ := σ) (Pre C s ([uE].zip [Enc.idxW e])) (ufBody C) s (unfoldDefinition C.fe e) (PostO C) := by
  refine specR_prologue (postO_locals C) (uf_none C _) ?_
  rw [unfoldDefinition_eq]
  unfold ufCore
  refine specR_callNIM uH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv uE] getAppFnBody
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [sev, Env.get, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel e s = .ok (a, s') ∧ Post C s a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hh w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV uH hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · have hb : (hh.tag == ETag.const) = true := by simp [htg, ETag.const]
    rw [if_pos hb]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv uH) (Enc.idxW hh) (by decide) (by simp +decide [Env.get]) ?_
    refine ILP.specR_viewIv hh (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
    obtain ⟨n, us, rfl⟩ := tagN_const h3
    simp only
    refine specR_loadI' uN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp [sev]) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW n) [Enc.idxW us] []) ?_
    refine specR_loadI' uUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW n) (Enc.idxW us) [] []) ?_
    refine specR_envFindI hok hc.memoGet hc.memoProbe uW (vv uN) n (by decide) (by simp +decide [Env.get])
      (by simp +decide [Env.get, ctxEnv]) ?_
    have hrel := find_rel hok n
    revert hrel
    rcases hfind : C.fe.find? n with _ | ci
    · intro hrel; simp only at hrel
      rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_returnI _ 0 rfl (fun t ht => ?_)
      exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
    · intro ⟨o, hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      have hne := ecell_succ_ne hok hoE
      refine specR_ifI _ 0 (by simp [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_assignI uP _ (ecell C o) (by decide) (by simp [sev, Env.get, optWG]; exact ecell_succ_sub C o) ?_
      refine specR_envLoadI uT (vv uP) o _ (by decide) (by simp +decide [Env.get]) (cie_tag hci) ?_
      cases ci with
      | defnInfo cv value hint =>
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only
        obtain ⟨ks, vsL, hks, hus, hden, hlen⟩ := hpre hh n us cv value hint hrun hv hfind
        refine specR_congr (m' := unfoldD e n us cv value >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH uR fUD udParams [vv uE, vv uN, vv uUs, vv uP] udBody
          [Enc.idxW e, Enc.idxW n, Enc.idxW us, ecell C o] (by decide) rfl (by decide) hcud
          ⟨by simp +decide [sev, Env.get, ctxEnv], by simp +decide [sev, Env.get], by simp +decide [sev, Env.get],
            by simp +decide [sev, Env.get], trivial⟩
          (PostO C) (fun a w _ _ => w = optW a) (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
          (fun u hu _ hlk => specR_of_pre u (pre_of_lookups hu udParams _ rfl hlk)
            (ud_spec ra C hok hc hcf hccv hcg hcm s e n us cv value hint o hci ks vsL hks hus hst hcn hcl hcls hden
              hlen))
          (fun r w s' H' hp hw => ?_)
        subst hw
        refine specR_returnI _ (optW r) (by simp +decide [Env.get]) (fun t ht => ?_)
        exact ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
      | _ =>
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_returnI _ 0 rfl (fun t ht => ?_)
        exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · have hb : ¬ (hh.tag == ETag.const) = true := by simpa [ETag.const] using htg
    rw [if_neg hb]
    refine specR_returnI _ 0 rfl (fun t ht => ?_)
    exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.UD
