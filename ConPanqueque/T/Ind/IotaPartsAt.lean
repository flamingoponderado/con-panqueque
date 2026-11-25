import ConPanqueque.T.Ind.IotaBody
import ConRon.Bridge.Inductives.IotaRead

/-!
# A rule's parts, read through its constructor (`iotaPartsAt`)

The run facts the reading needs: `ctorLevelsAt` and `iotaParamsAt` only grow the store, and the levels
`ctorLevelsAt` answers denote, so `instLPFast`'s denotation hypotheses carry over.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge ConRon.Bridge.Inductives

namespace ConPanqueque.T.Ind

theorem iotaBVars_pstep (rP n : Nat) : ∀ (m i : Nat), n - i = m → ∀ {s s' : AState}
    {r : List EIdx}, StateOK s → iotaBVars rP n i s = .ok (r, s') → PStep s s' := by
  intro m
  induction m with
  | zero =>
    intro i hm s s' r hok hrun
    rw [iotaBVars, ite_eq_right (by omega)] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact PStep.refl hok
  | succ m ih =>
    intro i hm s s' r hok hrun
    rw [iotaBVars, ite_eq_left (by omega)] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, -⟩ := internBVarE_run hok k1
    obtain ⟨bs, s₂, k2, z2⟩ := AM.bind_ok z1
    have p2 := ih (i + 1) (by omega) p1.ok k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    exact p1.trans p2

theorem iotaParamsAt_pstep {s s' : AState} {rl : IRecRule} {rP cnP : Nat} {r : List EIdx} (hok : StateOK s)
    (hrun : iotaParamsAt rl rP cnP s = .ok (r, s')) : PStep s s' := by
  simp only [iotaParamsAt] at hrun
  cases hfr : rl.fire with
  | nested lvls pins =>
    rw [hfr] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact PStep.refl hok
  | plain => rw [hfr] at hrun; exact iotaBVars_pstep rP _ _ 0 rfl hok hrun
  | levels lvls => rw [hfr] at hrun; exact iotaBVars_pstep rP _ _ 0 rfl hok hrun

theorem ctorLevelsAt_ext {s s' : AState} {rl : IRecRule} {lps : List NIdx}
    {lpsP : List ConLeche.Name} {r : LsIdx} (hok : StateOK s)
    (hfl : ∀ lv, ((∃ pins, rl.fire = .nested lv pins) ∨ rl.fire = .levels lv) →
      ∃ ls, denoteLList s.store.ls lv = some ls)
    (hlps : Frontend.denoteNList s.store.ns lps = some lpsP)
    (hrun : ctorLevelsAt rl lps s = .ok (r, s')) :
    Ext s.store s'.store ∧ ∃ vs, denoteLs s'.store.lss r = some vs := by
  simp only [ctorLevelsAt] at hrun
  cases hfr : rl.fire with
  | plain =>
    rw [hfr] at hrun
    obtain ⟨p, hr⟩ := paramLevels_run hok hlps hrun
    exact ⟨p.ext, _, hr⟩
  | nested lvls pins =>
    rw [hfr] at hrun
    obtain ⟨ls, h1⟩ := hfl lvls (Or.inl ⟨pins, hfr⟩)
    obtain ⟨p, hr⟩ := internLsNode_run hok h1 hrun
    exact ⟨p.ext, _, hr⟩
  | levels lvls =>
    rw [hfr] at hrun
    obtain ⟨ls, h1⟩ := hfl lvls (Or.inr hfr)
    obtain ⟨p, hr⟩ := internLsNode_run hok h1 hrun
    exact ⟨p.ext, _, hr⟩


open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.Decl
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.ExSP
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)

def apQ := ofString "ap_q"
def apCl := ofString "ap_cl"
def apTy := ofString "ap_ty"
def apCn := ofString "ap_cn"
def apMI := ofString "ap_mi"
def apRP := ofString "ap_rp"
def apLn := ofString "ap_ln"
def apL := ofString "ap_l"
def apP := ofString "ap_p"
def apPn := ofString "ap_pn"
def apT := ofString "ap_t"
def apS := ofString "ap_s"
def apSc := ofString "ap_sc"
def apCb := ofString "ap_cb"
def apI1 := ofString "ap_i1"
def apPd := ofString "ap_pd"
def apNF := ofString "ap_nf"
def apR := ofString "ap_r"
def fIotaPartsAt := ofString "iotaPartsAt"

def apParams : List MlS := [apQ, apCl, apTy, apCn, apMI, apRP]
def apLocals : List MlS := [apLn, apL, apP, apPn, apT, apS, apSc, apCb, apI1, apPd, apNF, apR, lCn, lSrc, lDst, lCi, lCz]

/-- `x`'s word below `2 ^ k`, else hang. -/
def guardP (x : MlS) (k : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv x) (.const (BitVec.ofNat 64 k))) hang rest

def apBody (C : Ctx) : ProgHOL 64 := prologue apLocals
  (guardP apCn 58 (guardP apMI 58 (guardP apRP 58
  (.seq (.assign .local apLn (.load .one (vv apCl)))
  (guardP apLn 59
  (.seq (.call (some (some (.local, apL), none)) fCtorLevels [vv apQ, vv apCl])
  (.seq (.call (some (some (.local, apP), none)) fIotaParams [vv apQ, vv apRP, vv apCn])
  (.seq (.assign .local apPn (.load .one (vv apP)))
  (guardP apPn 59
  (.seq (.call (some (some (.local, apT), none)) fInstLPF
    [.const (BitVec.ofNat 64 coreWalkFuel), vv apTy, vv apCl, vv apL])
  (.seq (.call (some (some (.local, apS), none)) fStripPis [vv apCn, vv apT])
  (.ite (.cmp .equal (vv apS) (.const 0)) (.return (.const 0))
  (.seq (.assign .local apSc (.load .one (vv apS)))
  (.seq (.assign .local apCb (.load .one (.op .add [vv apS, .shift .lsl (vv apSc) (.const 3)])))
  (.seq (.assign .local apI1 (.op .sub [vv apSc, .const 1]))
  (sliceCopyP C apPd apS (.const 0) apI1
  (.seq (.assign .local apNF (.load .one (.op .add [vv apQ, .const 8])))
  (guardP apNF 58
  (.seq (.call (some (some (.local, apR), none)) fIotaPartsBody
    [vv apCn, vv apMI, vv apRP, vv apNF, vv apL, vv apP, vv apPd, vv apCb])
  (.return (vv apR)))))))))))))))))))))

section
variable {σ : Type}

theorem specR_guardI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (n k : Nat) (hk : k < 64)
    (hx : Γ.get x = some (BitVec.ofNat 64 n)) (hn : n < 2 ^ 64)
    (h : n < 2 ^ k → SpecR (Inv C s Γ M D) rest s m R) : SpecR (Inv C s Γ M D) (guardP x k rest) s m R := by
  unfold guardP
  refine specR_ifI _ (BitVec.ofNat 64 n >>> k) (by
      have hk' : (BitVec.ofNat 64 k).toNat = k := by simp; omega
      simp only [sev, sev_vv, hx, Option.map_some, hk', if_pos hk]) (fun _ => specR_hangI) (fun h0 => h ?_)
  have := congrArg BitVec.toNat h0
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
  rcases Nat.lt_or_ge n (2 ^ k) with h1 | h1
  · exact h1
  · have := Nat.div_pos h1 (Nat.two_pow_pos k); omega

theorem ap_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ apLocals → (ctxEnv C ++ apParams.zip vals).get x = none :=
  Knot.params_none C apLocals apParams vals (by decide) (by decide)

/-- The code `iotaPartsAt` runs. -/
structure APCodes (C : Ctx) : Prop where
  cl : C.code.lookup fCtorLevels = some (clParams.map (fun p => (p, ShapeHOL.one)), clBody C, .one)
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  ilp1 : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ils : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  pa : C.code.lookup fIotaParams = some (paParams.map (fun p => (p, ShapeHOL.one)), paBody, .one)
  ts : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one)
  ib : C.code.lookup fIotaBVars = some (ibParams.map (fun p => (p, ShapeHOL.one)), ibBody C, .one)
  bv : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  ilp : CodesILP C (ilpBody C)
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  ab : C.code.lookup fIotaPartsBody = some (abParams.map (fun p => (p, ShapeHOL.one)), abBody C, .one)
  abc : ABCodes C

set_option maxHeartbeats 8000000 in
/-- **`iotaPartsAt`**: a rule's parts read through its constructor `cvj`. -/
theorem ap_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : APCodes C)
    (cvj : IConstantVal) (cnP mI rP : Nat) (rl : IRecRule) (oq ol : Nat)
    (hcn : cnP < 2 ^ 64) (hm : mI < 2 ^ 64) (hr : rP < 2 ^ 64)
    (H : List (BitVec 64)) (hq : RuleE C.HB H oq rl) (hbl : EBlk H ol (cvj.levelParams.map Enc.idxW)) (s : AState)
    {lpsP : List ConLeche.Name} {tyP : ConLeche.Expr}
    (hlp0 : Frontend.denoteNList s.store.ns cvj.levelParams = some lpsP) (hty0 : denoteE s.store cvj.type = some tyP)
    (hfl : ∀ lv, ((∃ pins, rl.fire = .nested lv pins) ∨ rl.fire = .levels lv) →
      ∃ ls, denoteLList s.store.ls lv = some ls) :
    SpecR (σ := σ) (Pre (ctxH C H) s (apParams.zip [cellA C oq, cellA C ol, Enc.idxW cvj.type, BitVec.ofNat 64 cnP,
      BitVec.ofNat 64 mI, BitVec.ofNat 64 rP])) (apBody C) s (iotaPartsAt cvj cnP mI rP rl) (PostAB (ctxH C H)) := by
  refine specR_prologue (postAB_locals _) (ap_none _ _) ?_
  unfold iotaPartsAt
  let Γ0 : Env := ctxEnv (ctxH C H) ++ apParams.zip [cellA C oq, cellA C ol, Enc.idxW cvj.type, BitVec.ofNat 64 cnP,
      BitVec.ofNat 64 mI, BitVec.ofNat 64 rP]
  have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ apLocals → z ∉ apLocals →
      Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
    have hne : z ≠ x := fun e => hz (e ▸ hx)
    simp only [Env.get_cons, hne, ite_false]
  have pk : ∀ (Γ : Env), (∀ z, z ∉ apLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ apParams → ∀ v,
      Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
    have hyl : y ∉ apLocals := by
      simp only [apParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp only [sev, sev_vv, hΓ y hyl, h]
  have vQ : Γ0.get apQ = some (cellA C oq) := by simp +decide [Γ0, Env.get, apParams, ctxEnv]
  have vCl : Γ0.get apCl = some (cellA C ol) := by simp +decide [Γ0, Env.get, apParams, ctxEnv]
  have vTy : Γ0.get apTy = some (Enc.idxW cvj.type) := by simp +decide [Γ0, Env.get, apParams, ctxEnv]
  have vCn : Γ0.get apCn = some (BitVec.ofNat 64 cnP) := by simp +decide [Γ0, Env.get, apParams, ctxEnv]
  have vMI : Γ0.get apMI = some (BitVec.ofNat 64 mI) := by simp +decide [Γ0, Env.get, apParams, ctxEnv]
  have vRP : Γ0.get apRP = some (BitVec.ofNat 64 rP) := by simp +decide [Γ0, Env.get, apParams, ctxEnv]
  have vZ : Γ0.get lCz = none := ap_none (ctxH C H) _ lCz (by decide)
  have retNone : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env), H <+: H1 →
      SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ apLocals)) (.return (.const 0)) s1 (pure none)
        (PostAB (ctxH C H)) := fun H1 s1 Γ hp1 =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun _ _ e => by simp at e⟩)
  refine specR_guardI apCn cnP 58 (by decide) vCn hcn (fun hcn' => ?_)
  refine specR_guardI apMI mI 58 (by decide) vMI hm (fun hm' => ?_)
  refine specR_guardI apRP rP 58 (by decide) vRP hr (fun hr' => ?_)
  have hbll := blkAt_len hbl
  simp only [List.length_map] at hbll
  have hc0 : (ctxH C H).H[ol]? = some (BitVec.ofNat 64 cvj.levelParams.length) := by
    show H[ol]? = _; rw [hbl.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) apLn (vv apCl) ol _ hc0 (by simp +decide [ctxLocals, apLocals])
    (pk Γ0 (fun _ _ => rfl) apCl (by decide) _ vCl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  refine specR_guardI apLn cvj.levelParams.length 59 (by decide) (by simp [Env.get_cons]) (by omega)
    (fun hlpl => ?_)
  let Γ1 : Env := (apLn, BitVec.ofNat 64 cvj.levelParams.length) :: Γ0
  have hΓ1 : ∀ z, z ∉ apLocals → Γ1.get z = Γ0.get z := fun z hz => cnl (by decide) hz
  refine specR_fact (fun t ht => sr_stateOK ht.sr) (fun hst0 => ?_)
  -- the constructor's levels
  refine specR_callNIH (C := ctxH C H) apL fCtorLevels clParams [vv apQ, vv apCl] (clBody C)
    [cellA C oq, cellA C ol] (by decide) rfl (by simp +decide [ctxLocals, apLocals]) hc.cl
    ⟨pk Γ1 hΓ1 apQ (by decide) _ vQ, pk Γ1 hΓ1 apCl (by decide) _ vCl, trivial⟩
    (fun a w s' st => ctorLevelsAt rl cvj.levelParams s = .ok (a, s') ∧ PostLsH (ctxH C H) a w s' st)
    (fun a w s' H' => ctorLevelsAt rl cvj.levelParams s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr1, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr1, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact cl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.ils rl cvj.levelParams (by omega) oq ol H hq hbl s _
        (pre_of_lookups hu clParams _ rfl hlk)))
    (fun lv wl s1 H1 hp1 ⟨hrun1, hwl⟩ => ?_)
  subst hwl
  obtain ⟨ext1, vsL, hvs⟩ := ctorLevelsAt_ext hst0 hfl hlp0 hrun1
  have hp1' : H <+: H1 := hp1
  let Γ2 : Env := (apL, Enc.idxW lv) :: Γ1
  have hΓ2 : ∀ z, z ∉ apLocals → Γ2.get z = Γ0.get z := fun z hz => by
    simp only [Γ2]; rw [cnl (by decide) hz]; exact hΓ1 z hz
  refine specR_fact (fun t ht => sr_stateOK ht.sr) (fun hst1 => ?_)
  -- the rule's parameters
  refine specR_callNIH (C := ctxH C H1) apP fIotaParams paParams [vv apQ, vv apRP, vv apCn] paBody
    [cellA C oq, BitVec.ofNat 64 rP, BitVec.ofNat 64 cnP] (by decide) rfl (by simp +decide [ctxLocals, apLocals]) hc.pa
    ⟨pk Γ2 hΓ2 apQ (by decide) _ vQ, pk Γ2 hΓ2 apRP (by decide) _ vRP, pk Γ2 hΓ2 apCn (by decide) _ vCn, trivial⟩
    (fun a w s' st => iotaParamsAt rl rP cnP s1 = .ok (a, s') ∧ PostA (ctxH C H1) a w s' st)
    (fun a w s' H' => iotaParamsAt rl rP cnP s1 = .ok (a, s') ∧ ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW))
    (fun a w s' st ⟨hr2, H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨hr2, o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact pa_spec ra C hok hc.pa hc.ts hc.ib hc.bv rl oq rP cnP (by omega) (by omega) H1 (ruleE_mono hp1' hq) s1 _
        (pre_of_lookups hu paParams _ rfl hlk)))
    (fun params wp s2 H2 hp2 ⟨hrun2, op, hwp, hpsb⟩ => ?_)
  subst hwp
  have hp2' : H1 <+: H2 := hp2
  have ext2 := (iotaParamsAt_pstep hst1 hrun2).ext
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN2 => ?_)
  have hHN2' : H2.length ≤ C.HN := hHN2
  have hpsl := blkAt_len hpsb
  simp only [List.length_map] at hpsl
  have hP0 : (ctxH C H2).H[op]? = some (BitVec.ofNat 64 params.length) := by show H2[op]? = _; rw [hpsb.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H2) apPn (vv apP) op _ hP0 (by simp +decide [ctxLocals, apLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_guardI apPn params.length 59 (by decide) (by simp [Env.get_cons]) (by omega) (fun hpl => ?_)
  let Γ3 : Env := (apPn, BitVec.ofNat 64 params.length) :: (apP, cellA C op) :: Γ2
  have hΓ3 : ∀ z, z ∉ apLocals → Γ3.get z = Γ0.get z := fun z hz => by
    simp only [Γ3]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ2 z hz
  -- the type at the rule's levels
  have ext12 := ext1.trans ext2
  obtain ⟨ks, hks⟩ : ∃ ks, Frontend.denoteNList s2.store.ns cvj.levelParams = some ks :=
    ⟨_, denoteNList_ext ext12.lss.1.1 _ _ hlp0⟩
  have hus2 := denoteLs_ext hvs ext2
  have hden2 : (denoteE s2.store cvj.type).isSome = true := by rw [denote_ext hty0 ext12]; rfl
  have hp12 : H <+: H2 := hp1'.trans hp2'
  refine specR_callNIH (C := ctxH C H2) apT fInstLPF ilpParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv apTy, vv apCl, vv apL] (ilpfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cvj.type, cellA C ol, Enc.idxW lv] (by decide) rfl
    (by simp +decide [ctxLocals, apLocals]) hc.ilpf
    ⟨rfl, pk Γ3 hΓ3 apTy (by decide) _ vTy, pk Γ3 hΓ3 apCl (by decide) _ vCl,
      by simp +decide [Γ3, Γ2, sev, Env.get_cons], trivial⟩
    (PostILP (ctxH C H2)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H'', hp, hw, hsr⟩ => ⟨H'', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
      (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt ol cvj.levelParams ks lv vsL H2 s2 cvj.type hks hus2
        (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls hden2 (blkAt_mono hbl hp12)))
    (fun ty wt s3 H3 hp3 hwt => ?_)
  subst hwt
  have hp3' : H2 <+: H3 := hp3
  let Γ4 : Env := (apT, Enc.idxW ty) :: Γ3
  have hΓ4 : ∀ z, z ∉ apLocals → Γ4.get z = Γ0.get z := fun z hz => by
    simp only [Γ4]; rw [cnl (by decide) hz]; exact hΓ3 z hz
  -- the parameters' binders
  refine ro_strip C hok hc.sp cnP (by omega) ty H3 s3 apS (vv apCn) (vv apT)
    (by simp +decide [ctxLocals, apLocals]) (pk Γ4 hΓ4 apCn (by decide) _ vCn) (by simp [Γ4, sev, Env.get_cons])
    (fun o wa s4 H4 hp4 hr4 hn4 hs4 => ?_)
  have hp4' : H3 <+: H4 := hp4
  have hp14 : H <+: H4 := (hp12.trans hp3').trans hp4'
  rcases o with _ | ⟨pd, cb⟩
  · have e0 := hn4 rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact retNone H4 s4 _ hp14
  obtain ⟨oa, rfl, hba⟩ := hs4 pd cb rfl
  have hpdl := stripPis_length _ _ _ _ _ _ hr4
  obtain ⟨ha0, haL, -⟩ := strip_last hba
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN4 => ?_)
  have hol := blkAt_lt hba
  have hHN4' : H4.length ≤ C.HN := hHN4
  have hne : cellA C oa ≠ 0 := cellA_ne0 C hok oa (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H4) apSc (vv apS) oa _ ha0 (by simp +decide [ctxLocals, apLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H4) apCb _ (oa + 1 + pd.length) _ haL (by simp +decide [ctxLocals, apLocals])
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C oa + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  refine specR_assignI apI1 _ (BitVec.ofNat 64 pd.length) (by simp +decide [ctxLocals, apLocals])
    (by
      have e : sev ((apCb, Enc.idxW cb) :: (apSc, BitVec.ofNat 64 (pd.length + 1)) :: (apS, cellA C oa) :: Γ4)
          (vv apSc) = some (BitVec.ofNat 64 (pd.length + 1)) := by simp +decide [sev, Env.get_cons]
      rw [sev_sub2 _ _ _ _ _ e rfl]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) ?_
  let Γ5 : Env := (apI1, BitVec.ofNat 64 pd.length) :: (apCb, Enc.idxW cb) ::
    (apSc, BitVec.ofNat 64 (pd.length + 1)) :: (apS, cellA C oa) :: Γ4
  have hΓ5 : ∀ z, z ∉ apLocals → Γ5.get z = Γ0.get z := fun z hz => by
    simp only [Γ5]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]
    exact hΓ4 z hz
  have hz5 : Γ5.get lCz = none := by
    simp +decide only [Γ5, Γ4, Γ3, Γ2, Γ1, Env.get_cons, ite_false]; exact vZ
  refine specR_sliceCopyI hok apPd apS (.const 0) apI1 oa 0 pd.length (pd.map Enc.idxW ++ [Enc.idxW cb])
    (by simp +decide [ctxLocals, apLocals])
    (by simp +decide [Γ5, Env.get_cons]) (fun _ _ => rfl) (by simp)
    (by simp [Γ5, Env.get_cons]) hba hz5 (by decide) (by decide) (fun H5 o5 hp5 hl5 hb5 => ?_)
  have hfd : ((pd.map Enc.idxW ++ [Enc.idxW cb]).drop 0).take pd.length = pd.map Enc.idxW := by simp
  rw [hfd] at hb5
  have hp5' : H4 <+: H5 := hp5
  have hp15 : H <+: H5 := hp14.trans hp5'
  let Γ6 : Env := (lCi, BitVec.ofNat 64 pd.length) :: (lDst, cellA C (o5 + 1 + pd.length)) ::
    (lSrc, cellA C (oa + 1 + 0 + pd.length)) :: (apPd, cellA C o5) :: (lCn, BitVec.ofNat 64 pd.length) :: Γ5
  have hΓ6 : ∀ z, z ∉ apLocals → z ≠ lCi → z ≠ lDst → z ≠ lSrc → z ≠ lCn → Γ6.get z = Γ0.get z :=
    fun z hz h1 h2 h3 h4 => by
      simp only [Γ6]
      rw [Env.get_cons, if_neg h1, Env.get_cons, if_neg h2, Env.get_cons, if_neg h3, cnl (by decide) hz,
        Env.get_cons, if_neg h4]
      exact hΓ5 z hz
  -- the rule's field count
  obtain ⟨hnf0, hnfb⟩ := (ruleE_mono hp15 hq).2.1
  have hq1 : (ctxH C H5).H[oq + 1]? = some (BitVec.ofNat 64 rl.nfields) := hnf0
  refine UD.specR_heapLoadI' (C := ctxH C H5) apNF _ (oq + 1) _ hq1 (by simp +decide [ctxLocals, apLocals])
    (by
      have e := pk Γ6 (fun z hz => hΓ6 z hz (by rintro rfl; exact hz (by decide)) (by rintro rfl; exact hz (by decide))
        (by rintro rfl; exact hz (by decide)) (by rintro rfl; exact hz (by decide))) apQ (by decide) _ vQ
      simp only [sev] at e ⊢
      rw [e]; simp; exact cellA_add8 C oq) ?_
  refine specR_guardI apNF rl.nfields 58 (by decide) (by simp [Env.get_cons]) (by omega) (fun hnf => ?_)
  let Γ7 : Env := (apNF, BitVec.ofNat 64 rl.nfields) :: Γ6
  have pk7 : ∀ y, y ∈ apParams → ∀ v, Γ0.get y = some v → sev Γ7 (vv y) = some v := fun y hy v h => by
    have hyl : y ∉ apLocals := by
      simp only [apParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have e := pk Γ6 (fun z hz => hΓ6 z hz (by rintro rfl; exact hz (by decide)) (by rintro rfl; exact hz (by decide))
      (by rintro rfl; exact hz (by decide)) (by rintro rfl; exact hz (by decide))) y hy v h
    simp only [sev, sev_vv, Γ7] at e ⊢
    rw [cnl (by decide) hyl]; exact e
  -- the parts past the parameters
  refine specR_congr (m' := iotaPartsAtBody cnP mI rP rl lv params pd cb >>= fun r => pure r) (by rw [bind_pure]) ?_
  refine specR_callNIH (C := ctxH C H5) apR fIotaPartsBody abParams
    [vv apCn, vv apMI, vv apRP, vv apNF, vv apL, vv apP, vv apPd, vv apCb] (abBody C)
    [BitVec.ofNat 64 cnP, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, BitVec.ofNat 64 rl.nfields, Enc.idxW lv,
      cellA C op, cellA C o5, Enc.idxW cb] (by decide) rfl (by simp +decide [ctxLocals, apLocals]) hc.ab
    ⟨pk7 apCn (by decide) _ vCn, pk7 apMI (by decide) _ vMI, pk7 apRP (by decide) _ vRP,
      by simp [Γ7, sev, Env.get_cons],
      by simp +decide [Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons],
      by simp +decide [Γ7, Γ6, Γ5, Γ4, Γ3, sev, Env.get_cons],
      by simp +decide [Γ7, Γ6, sev, Env.get_cons],
      by simp +decide [Γ7, Γ6, Γ5, sev, Env.get_cons], trivial⟩
    (PostAB (ctxH C H5))
    (fun o w _ H' => (o = none → w = 0) ∧ ∀ ip pd', o = some (ip, pd') → ∃ ob, w = cellA C ob ∧ PartsRep C H' ob ip ∧
      ∃ o4, H'[ob + 4]? = some (cellA C o4) ∧ BlkAt H' o4 (pd'.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu abParams _ rfl hlk)
      (ab_spec ra C hok hc.abc cnP mI rP rl lv params pd cb op o5 hcn' hm' hr' hnf hpl H5
        (blkAt_mono hpsb ((hp3'.trans hp4').trans hp5')) hb5 s4))
    (fun o w s5 H6 hp6 ⟨h1, h2⟩ => ?_)
  have hp6' : H5 <+: H6 := hp6
  exact specR_returnI (vv apR) w (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H6, hp15.trans hp6', sr_of_eq ht.sr rfl rfl rfl rfl, h1, h2⟩)

end

end ConPanqueque.T.Ind
