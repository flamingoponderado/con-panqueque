import ConPanqueque.T.Ind.PinRec
import ConPanqueque.T.Ind.ParamLevels
import ConPanqueque.T.InstLPFast
import ConPanqueque.T.Decl.NameNodup
import ConPanqueque.T.Quot.ArmSpec
import ConPanqueque.T.Quot.RecSpec
import ConPanqueque.T.Ind.KindsFlat
import ConPanqueque.T.Ind.IndParams
import ConPanqueque.T.Ind.CloseTele
import ConPanqueque.T.Ind.IndNames
import ConPanqueque.T.Core.Unfold
import ConPanqueque.T.Core.IotaBody

/-!
# A block's records against its pin, up to level-parameter names (`pinCopiesOk`)

`pcpBody(c, p)`: the twin's `pinCopyOk` of the stream record at `c` (the environment's layout, `CIE`) and the
pinned record at `p` (`PinRec`): as many level parameters, distinct (else hang); the pin at the record's names
(`IConstantInfo.atLps`: `paramLevels`, `instLPFast` of the type and of each rule's right-hand side); then
`pinAgrees`, word by word (a mismatch hangs). `prlBody` is the rules' loop, `pcsBody` the block's.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec ilpParams)
open ConPanqueque.T.Quot (specR_guardNe specR_guardZ specR_guardNZ specR_readNamesI)

def pnC := ofString "pr_c"
def pnP := ofString "pr_p"
def pnL := ofString "pr_l"
def pnU := ofString "pr_u"
def pnJ := ofString "pr_j"
def pnN := ofString "pr_n"
def pnCq := ofString "pr_cq"
def pnPq := ofString "pr_pq"
def pnA := ofString "pr_a"
def pnB := ofString "pr_b"
def pnH := ofString "pr_h"
def pnX := ofString "pr_x"
def fPrl := ofString "pinRulesOk"

def prlParams : List MlS := [pnC, pnP, pnL, pnU, pnJ, pnN]
def prlLocals : List MlS := [pnCq, pnPq, pnA, pnB, pnH, pnX]

/-- `if x ≠ y then hang` on two loaded words. -/
def cmpW (a b : MlS) (ea eb : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local a (.load .one ea)) (.seq (.assign .local b (.load .one eb))
    (.ite (.cmp .notEqual (vv a) (vv b)) hang rest))

/-- The pin's rules from `j` at the record's names, against the record's rules (a mismatch hangs). -/
def prlBody : ProgHOL 64 := prologue prlLocals
  (.ite (.cmp .lower (vv pnJ) (vv pnN))
    (.seq (.assign .local pnPq (.load .one (.op .add [vv pnP, .op .add [.panop .mul [vv pnJ, .const 8], .const 8]])))
    (.seq (.assign .local pnCq (.load .one (.op .add [vv pnC, .op .add [.panop .mul [vv pnJ, .const 8], .const 8]])))
    (.seq (.assign .local pnA (.load .one (.op .add [vv pnPq, .const 16])))
    (.ite (.cmp .notEqual (vv pnA) (.const 0)) hang
    (.seq (.assign .local pnA (.load .one (.op .add [vv pnPq, .const 40])))
    (.seq (.call (some (some (.local, pnH), none)) fInstLPF
        [.const (BitVec.ofNat 64 coreWalkFuel), vv pnA, vv pnL, vv pnU])
    (cmpW pnA pnB (vv pnCq) (vv pnPq)
    (cmpW pnA pnB (.op .add [vv pnCq, .const 8]) (.op .add [vv pnPq, .const 8])
    (.seq (.assign .local pnA (.load .one (.op .add [vv pnCq, .const 16])))
    (.ite (.cmp .notEqual (vv pnA) (.const 0)) hang
    (.seq (.assign .local pnA (.load .one (.op .add [vv pnCq, .const 40])))
    (.ite (.cmp .notEqual (vv pnA) (vv pnH)) hang
    (.seq (.call (some (some (.local, pnX), none)) fPrl
        [vv pnC, vv pnP, vv pnL, vv pnU, .op .add [vv pnJ, .const 1], vv pnN])
      (.return (.const 1)))))))))))))))
    (.return (.const 1)))

/-- A rule block `[n, cellA q₀, …]` at `o`. -/
def PinRulesAt (C : Ctx) (H : List (BitVec 64)) (o : Nat) (rs : List IRecRule) : Prop :=
  H[o]? = some (BitVec.ofNat 64 rs.length) ∧
    ∀ i (hi : i < rs.length), ∃ q, H[o + 1 + i]? = some (cellA C q) ∧ RuleE C.HB H q rs[i]

theorem pinRulesAt_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {rs : List IRecRule}
    (h : PinRulesAt C H o rs) : PinRulesAt C H' o rs :=
  ⟨get_prefix h.1 hp, fun i hi => let ⟨q, h1, h2⟩ := h.2 i hi; ⟨q, get_prefix h1 hp, ruleE_mono hp h2⟩⟩

theorem pinRulesAt_of {C : Ctx} {H : List (BitVec 64)} {w : BitVec 64} {rs : List IRecRule}
    (h : RulesE C.HB H w rs) : ∃ o, w = cellA C o ∧ PinRulesAt C H o rs := by
  obtain ⟨o, hw, hl, hr⟩ := h
  exact ⟨o, hw, hl, fun i hi => let ⟨q, h1, h2⟩ := hr i hi; ⟨q, h1, h2⟩⟩

/-- The post of a procedure that hangs unless its verdict holds. -/
def PostPin {α : Type} {σ : Type} (C : Ctx) (P : α → Prop) (a : α) (_ : BitVec 64) (s' : AState) (st : PState σ) :
    Prop :=
  P a ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postPin_locals {α σ : Type} (C : Ctx) (P : α → Prop) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostPin C P a w s' st → PostPin C P a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, H', h1, h2⟩ => ⟨h0, H', h1, sr_of_eq h2 rfl rfl rfl rfl⟩


def pyC := ofString "py_c"
def pyP := ofString "py_p"
def pyCl := ofString "py_cl"
def pyCn := ofString "py_cn"
def pyPl := ofString "py_pl"
def pyPn := ofString "py_pn"
def pyX := ofString "py_x"
def pyUs := ofString "py_us"
def pyTy := ofString "py_ty"
def pyA := ofString "py_a"
def pyB := ofString "py_b"
def pyT := ofString "py_t"
def pyCr := ofString "py_cr"
def pyPr := ofString "py_pr"
def fPcp := ofString "pinCopyOk"

def pcpParams : List MlS := [pyC, pyP]
def pcpLocals : List MlS := [pyCl, pyCn, pyPl, pyPn, pyX, pyUs, pyTy, pyA, pyB, pyT, pyCr, pyPr]

/-- **`pinCopyOk`** of the record at `c` and the pinned record at `p` (hang unless it holds). -/
def pcpBody : ProgHOL 64 := prologue pcpLocals
  (.seq (.assign .local pyCl (.load .one (.op .add [vv pyC, .const 16])))
  (.seq (.assign .local pyCn (.load .one (vv pyCl)))
  (.seq (.assign .local pyPl (.load .one (.op .add [vv pyP, .const 16])))
  (.seq (.assign .local pyPn (.load .one (vv pyPl)))
  (.ite (.cmp .notEqual (vv pyCn) (vv pyPn)) hang
  (.seq (.call (some (some (.local, pyX), none)) fNdg [vv pyCl, .const 0, vv pyCn])
  (.ite (.cmp .equal (vv pyX) (.const 0)) hang
  (.seq (.assign .local pyT (.load .one (vv pyP)))
  (.ite (.cmp .lower (vv pyT) (.const 3)) hang
  (.ite (.cmp .lower (.const 5) (vv pyT)) hang
  (.seq (.call (some (some (.local, pyUs), none)) fParamLevels [vv pyCl])
  (.seq (.assign .local pyA (.load .one (.op .add [vv pyP, .const 24])))
  (.seq (.call (some (some (.local, pyTy), none)) fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv pyA, vv pyPl, vv pyUs])
  (cmpW pyA pyB (vv pyC) (vv pyP)
  (cmpW pyA pyB (.op .add [vv pyC, .const 8]) (.op .add [vv pyP, .const 8])
  (.seq (.assign .local pyA (.load .one (.op .add [vv pyC, .const 24])))
  (.ite (.cmp .notEqual (vv pyA) (vv pyTy)) hang
  (.ite (.cmp .equal (vv pyT) (.const 3)) (.return (.const 1))
  (cmpW pyA pyB (.op .add [vv pyC, .const 32]) (.op .add [vv pyP, .const 32])
  (cmpW pyA pyB (.op .add [vv pyC, .const 40]) (.op .add [vv pyP, .const 40])
  (cmpW pyA pyB (.op .add [vv pyC, .const 48]) (.op .add [vv pyP, .const 48])
  (.ite (.cmp .equal (vv pyT) (.const 4)) (.return (.const 1))
  (.seq (.call (some (some (.local, pyUs), none)) fParamLevels [vv pyCl])
  (.seq (.assign .local pyCr (.load .one (.op .add [vv pyC, .const 56])))
  (.seq (.assign .local pyPr (.load .one (.op .add [vv pyP, .const 56])))
  (cmpW pyA pyB (vv pyCr) (vv pyPr)
  (.seq (.call (some (some (.local, pyX), none)) fPrl [vv pyCr, vv pyPr, vv pyPl, vv pyUs, .const 0, vv pyB])
    (.return (.const 1)))))))))))))))))))))))))))))

/-- A stored constant's kind word. -/
def ciTag : IConstantInfo → Nat
  | .axiomInfo _ => 0
  | .defnInfo _ _ _ => 1
  | .thmInfo _ => 2
  | .indInfo _ _ => 3
  | .ctorInfo _ _ _ _ => 4
  | .recInfo _ _ _ _ _ => 5

theorem cie_tag {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) :
    H[o]? = some (BitVec.ofNat 64 (ciTag ci)) := by
  cases ci with
  | axiomInfo _ => exact h.2
  | defnInfo _ _ _ => exact h.2.1
  | thmInfo _ => exact h.2
  | indInfo _ _ => exact h.2.1
  | ctorInfo _ _ _ _ => exact h.2.1
  | recInfo _ _ _ _ _ => exact h.2.1

theorem pinRec_tag {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : PinRec EB H o ci) :
    H[o]? = some (BitVec.ofNat 64 (ciTag ci)) := by
  cases ci with
  | indInfo _ _ => exact h.2
  | ctorInfo _ _ _ _ => exact h.2.1
  | recInfo _ _ _ _ _ => exact h.2.1
  | axiomInfo _ => exact h.2.elim
  | defnInfo _ _ _ => exact h.2.elim
  | thmInfo _ => exact h.2.elim

/-- What `atLps` does after the constant value, by the pin's kind. -/
def atLpsK (pin : IConstantInfo) (ps : List NIdx) (cv2 : IConstantVal) : AM IConstantInfo :=
  match pin with
  | .indInfo _ caps => pure (.indInfo cv2 caps)
  | .ctorInfo _ nP nF T => pure (.ctorInfo cv2 nP nF T)
  | .recInfo cv mI rP isK rules => do
    let us ← paramLevels ps
    let lpsT ← readNamesM cv.levelParams
    let psT ← readNamesM ps
    let rules2 ← rulesAtLps cv.levelParams us lpsT (psT.map ConLeche.Level.param) rules
    pure (.recInfo cv2 mI rP isK rules2)
  | _ => pure pin

theorem atLps_split (pin : IConstantInfo) (ps : List NIdx) (h : 3 ≤ ciTag pin) :
    pin.atLps ps = pin.toConstantVal.atLps ps >>= atLpsK pin ps := by
  cases pin with
  | indInfo _ _ => rfl
  | ctorInfo _ _ _ _ => rfl
  | recInfo _ _ _ _ _ => rfl
  | axiomInfo _ => simp [ciTag] at h
  | defnInfo _ _ _ => simp [ciTag] at h
  | thmInfo _ => simp [ciTag] at h

theorem pinRulesAt_len {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} (hH : H.length ≤ C.HN) {o : Nat}
    {rs : List IRecRule} (h : PinRulesAt C H o rs) : rs.length < 2 ^ 61 := by
  have hlay := hok.heapLay
  have h0 := (List.getElem?_eq_some_iff.mp h.1).1
  rcases Nat.eq_zero_or_pos rs.length with e | e
  · omega
  · obtain ⟨q, hq, -⟩ := h.2 (rs.length - 1) (by omega)
    have := (List.getElem?_eq_some_iff.mp hq).1; omega

theorem pin_eblk_len {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} (hH : H.length ≤ C.HN) {o : Nat}
    {xs : List (BitVec 64)} (h : EBlk H o xs) : xs.length < 2 ^ 61 := by
  have := Ind.blkAt_len hok hH (xs := xs) (o := o) h; omega

theorem boolW_inj {a b : Bool} (h : boolW a = boolW b) : a = b := by
  cases a <;> cases b <;> simp_all [boolW]

theorem pcp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pcpLocals → (ctxEnv C ++ pcpParams.zip vals).get x = none :=
  Knot.params_none C pcpLocals pcpParams vals (by decide) (by decide)


def psB := ofString "ps_b"
def psQ := ofString "ps_q"
def psI := ofString "ps_i"
def psN := ofString "ps_n"
def psC := ofString "ps_c"
def psP := ofString "ps_p"
def psX := ofString "ps_x"
def fPcs := ofString "pinCopiesOk"

def pcsParams : List MlS := [psB, psQ, psI, psN]
def pcsLocals : List MlS := [psC, psP, psX]

/-- **`pinCopiesOk`** of the stream block at `b` and the pinned block at `q`, from `i` (hang unless it holds). -/
def pcsBody : ProgHOL 64 := prologue pcsLocals
  (.ite (.cmp .lower (vv psI) (vv psN))
    (.seq (.assign .local psC (.load .one (.op .add [vv psB, .op .add [.panop .mul [vv psI, .const 8], .const 8]])))
    (.seq (.assign .local psP (.load .one (.op .add [vv psQ, .op .add [.panop .mul [vv psI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, psX), none)) fPcp [vv psC, vv psP])
    (.seq (.call (some (some (.local, psX), none)) fPcs [vv psB, vv psQ, .op .add [vv psI, .const 1], vv psN])
      (.return (.const 1))))))
    (.return (.const 1)))

/-- The pin comparison's code. -/
structure PCCodes (C : Ctx) : Prop where
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  ilp1 : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  ilp : ILP.CodesILP C (ILP.ilpBody C)
  ndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  ndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
  prl : C.code.lookup fPrl = some (prlParams.map (fun p => (p, ShapeHOL.one)), prlBody, .one)
  pcp : C.code.lookup fPcp = some (pcpParams.map (fun p => (p, ShapeHOL.one)), pcpBody, .one)
  pcs : C.code.lookup fPcs = some (pcsParams.map (fun p => (p, ShapeHOL.one)), pcsBody, .one)

section
variable {σ : Type}

theorem prl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ prlLocals → (ctxEnv C ++ prlParams.zip vals).get x = none :=
  Knot.params_none C prlLocals prlParams vals (by decide) (by decide)

theorem fire_tag {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {f : IRecRuleFire} (h : FireE EB H o f) :
    ∃ w, H[o]? = some w ∧ (w = 0 → f = .plain) := by
  cases f with
  | plain => exact ⟨0, h, fun _ => rfl⟩
  | nested lv pins => exact ⟨1, h.1, fun e => absurd e (by decide)⟩
  | levels lv => exact ⟨2, h.1, fun e => absurd e (by decide)⟩

theorem natW_inj {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem rules_rhs_den {st : EStore} : ∀ (rs : List IRecRule) (Rs : List ConLeche.RecRule),
    Frontend.denoteRules st rs = some Rs → ∀ r ∈ rs, (denoteE st r.rhs).isSome = true
  | [], _, _, r, hr => by simp at hr
  | a :: as, Rs, h, r, hr => by
    obtain ⟨x, xs, h1, h2, -⟩ := denoteRules_cons h
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨-, -, h3, -⟩ := denoteRule_inv h1
      rw [h3]; rfl
    · exact rules_rhs_den as xs h2 r hr

set_option maxHeartbeats 4000000 in
/-- **The pin's rules from `j`**: their right-hand sides at the record's names (`rulesAtLps`), and the record's
rules from `j` are those (else hang). -/
theorem prl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PCCodes C)
    (lpsH : List NIdx) (ksv : List ConLeche.Name) (us : LsIdx) (usv : List ConLeche.Level)
    (lpsT : List ConLeche.Name) (usT : List ConLeche.Level) (ol : Nat)
    (crs prs : List IRecRule) (oc op : Nat) (hlen : crs.length = prs.length) (hn : prs.length < 2 ^ 61) :
    ∀ f j (H : List (BitVec 64)) (s : AState), C.H <+: H → prs.length - j = f → j ≤ prs.length →
      PinRulesAt C H oc crs → PinRulesAt C H op prs → BlkAt H ol (lpsH.map Enc.idxW) →
      Frontend.denoteNList s.store.ns lpsH = some ksv → denoteLs s.store.lss us = some usv →
      (∀ r ∈ prs, (denoteE s.store r.rhs).isSome = true) →
      SpecR (σ := σ) (Pre (ctxH C H) s (prlParams.zip [cellA C oc, cellA C op, cellA C ol, Enc.idxW us,
          BitVec.ofNat 64 j, BitVec.ofNat 64 prs.length])) prlBody s
        (rulesAtLps lpsH us lpsT usT (prs.drop j)) (PostPin (ctxH C H) (fun r => r = crs.drop j)) := by
  intro f
  induction f with
  | zero =>
    intro j H s hpH hf hj hcr hpr hlb hks hus hrh
    have hjl : j = prs.length := by omega
    subst hjl
    refine specR_prologue (postPin_locals _ _) (prl_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff prs.length prs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, prlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, rulesAtLps]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨by show [] = _; rw [← hlen]; simp, H, List.prefix_refl _,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hpH hf hj hcr hpr hlb hks hus hrh
    have hjl : j < prs.length := by omega
    have hjc : j < crs.length := by omega
    refine specR_prologue (postPin_locals _ _) (prl_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j prs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, prlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨qp, hqp, hRp⟩ := hpr.2 j hjl
    obtain ⟨qc, hqc, hRc⟩ := hcr.2 j hjc
    refine UD.specR_heapLoadI' (C := ctxH C H) pnPq _ (op + 1 + j) _ hqp (by decide)
      (by simp +decide [sev, Env.get, prlParams, ctxEnv]; exact cellA_mulIdx C op j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) pnCq _ (oc + 1 + j) _ hqc (by decide)
      (by simp +decide [sev, Env.get, Env.get_cons, prlParams, ctxEnv]; exact cellA_mulIdx C oc j (by omega)) ?_
    obtain ⟨wf, hwf, hwf0⟩ := fire_tag hRp.2.2.1
    refine UD.specR_heapLoadI' (C := ctxH C H) pnA _ (qp + 2) _ hwf (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C qp 2) ?_
    refine specR_guardNZ pnA wf (by simp [Env.get_cons]) (fun hw0 => ?_)
    have hfire : prs[j].fire = .plain := hwf0 hw0
    refine UD.specR_heapLoadI' (C := ctxH C H) pnA _ (qp + 5) _ hRp.2.2.2 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C qp 5) ?_
    rw [List.drop_eq_getElem_cons hjl]
    simp only [rulesAtLps, hfire, IRecRuleFire.atLps, pure_bind, bind_assoc]
    refine specR_atEntry fun t0 ht0 => ?_
    refine specR_callNIH (C := ctxH C H) pnH fInstLPF ilpParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv pnA, vv pnL, vv pnU] (ilpfBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW prs[j].rhs, cellA C ol, Enc.idxW us] (by decide) rfl
      (by decide) hc.ilpf
      ⟨rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv], trivial⟩
      (fun a w s' st => instLPFast coreWalkFuel lpsH us prs[j].rhs s = .ok (a, s') ∧ ILP.PostILP (ctxH C H) a w s' st)
      (fun a w s' _ => instLPFast coreWalkFuel lpsH us prs[j].rhs s = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hr, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt ol lpsH ksv us usv H s prs[j].rhs hks hus
          (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls (hrh _ (List.getElem_mem hjl)) hlb)))
      (fun rh wh s2 H2 hp2 ⟨hr2, hw2⟩ => ?_)
    subst hw2
    have hpH2 : C.H <+: H2 := hpH.trans hp2
    have hcr2 := pinRulesAt_mono hp2 hcr
    have hpr2 := pinRulesAt_mono hp2 hpr
    have hRc2 := ruleE_mono hp2 hRc
    have hRp2 := ruleE_mono hp2 hRp
    -- the twin's step facts
    obtain ⟨xr, hxr⟩ := Option.isSome_iff_exists.mp (hrh _ (List.getElem_mem hjl))
    obtain ⟨hst2, -⟩ := instLPFast_run (sr_stateOK ht0.sr) ⟨ht0.sr.cok.rn, ht0.sr.cok.rl, ht0.sr.cok.rls⟩ hks hus hxr hr2
    -- the constructor
    refine UD.specR_heapLoadI' (C := ctxH C H2) pnA _ qc _ hRc2.1 (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) pnB _ qp _ hRp2.1 (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    refine specR_guardNe pnA pnB (Enc.idxW crs[j].ctor) (Enc.idxW prs[j].ctor) (by simp +decide [Env.get_cons])
      (by simp +decide [Env.get_cons]) (fun hct => ?_)
    -- the field count
    refine UD.specR_heapLoadI' (C := ctxH C H2) pnA _ (qc + 1) _ hRc2.2.1.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C qc) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) pnB _ (qp + 1) _ hRp2.2.1.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C qp) ?_
    refine specR_guardNe pnA pnB (BitVec.ofNat 64 crs[j].nfields) (BitVec.ofNat 64 prs[j].nfields)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun hnf => ?_)
    -- the record's firing mode
    obtain ⟨wc, hwc, hwc0⟩ := fire_tag hRc2.2.2.1
    refine UD.specR_heapLoadI' (C := ctxH C H2) pnA _ (qc + 2) _ hwc (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C qc 2) ?_
    refine specR_guardNZ pnA wc (by simp [Env.get_cons]) (fun hwc' => ?_)
    have hcfire : crs[j].fire = .plain := hwc0 hwc'
    -- the right-hand side
    refine UD.specR_heapLoadI' (C := ctxH C H2) pnA _ (qc + 5) _ hRc2.2.2.2 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C qc 5) ?_
    refine specR_guardNe pnA pnH (Enc.idxW crs[j].rhs) (Enc.idxW rh) (by simp +decide [Env.get_cons])
      (by simp +decide [Env.get_cons]) (fun hrhs => ?_)
    have e1 : crs[j].ctor = prs[j].ctor := Enc.idxW_inj hct
    have e2 : crs[j].nfields = prs[j].nfields := natW_inj hRc2.2.1.2 hRp2.2.1.2 hnf
    have e4 : crs[j].rhs = rh := Enc.idxW_inj hrhs
    have hrule : crs[j] = { ctor := prs[j].ctor, nfields := prs[j].nfields, fire := .plain, rhs := rh } := by
      rw [← e1, ← e2, ← hcfire, ← e4]
    -- the rest
    refine specR_callNIH (C := ctxH C H2) pnX fPrl prlParams
      [vv pnC, vv pnP, vv pnL, vv pnU, .op .add [vv pnJ, .const 1], vv pnN] prlBody
      [cellA C oc, cellA C op, cellA C ol, Enc.idxW us, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 prs.length]
      (by decide) rfl (by decide) hc.prl
      ⟨by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv]; exact e_succ j,
        by simp +decide [sev, Env.get_cons, Env.get, prlParams, ctxEnv], trivial⟩
      (PostPin (ctxH C H2) (fun r => r = crs.drop (j + 1))) (fun r _ _ _ => r = crs.drop (j + 1))
      (fun a w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu prlParams _ rfl hlk)
        (ih (j + 1) H2 s2 hpH2 (by omega) (by omega) hcr2 hpr2 (blkAt_mono hlb hp2)
          (denoteNList_ext hst2.ext.lss.ls.ns _ _ hks) (denoteLs_ext hus hst2.ext)
          (fun r hr => by
            obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hrh r hr)
            rw [denote_ext hx hst2.ext]; rfl)))
      (fun rest w s3 H3 hp3 hrest => ?_)
    subst hrest
    exact specR_returnI _ 1 rfl (fun t ht => ⟨by rw [List.drop_eq_getElem_cons hjc, hrule], H3, hp2.trans hp3,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- `if t < 3 then hang; if 5 < t then hang` at a kind word in range. -/
theorem specR_tagRange {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (t : Nat) (ht : 3 ≤ t ∧ t ≤ 5)
    (hx : Γ.get x = some (BitVec.ofNat 64 t)) (h : SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .lower (vv x) (.const 3)) hang (.ite (.cmp .lower (.const 5) (vv x)) hang rest))
      s m R := by
  have : t = 3 ∨ t = 4 ∨ t = 5 := by omega
  rcases this with rfl | rfl | rfl <;>
  · refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_ifI _ 0 (by simp +decide [sev, sev_vv, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => h)

theorem ciTag_lt (ci : IConstantInfo) : ciTag ci < 6 := by cases ci <;> simp [ciTag]

theorem get_eq_of {H : List (BitVec 64)} {i j : Nat} {w : BitVec 64} (h : H[i]? = some w) (e : j = i) : H[j]? = some w :=
  e ▸ h

set_option maxHeartbeats 32000000 in
/-- **`pinCopyOk`** of a stream record and a pinned record: the port hangs unless it holds. -/
theorem pcp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PCCodes C)
    (ci pin : IConstantInfo) (oc op : Nat) (H : List (BitVec 64)) (s : AState) (hpH : C.H <+: H)
    (hci : CIE C.HB H oc ci) (hpin : PinRec C.HB H op pin)
    (B P : ConLeche.ConstantInfo) (hB : Frontend.denoteCI s.store ci = some B)
    (hP : Frontend.denoteCI s.store pin = some P) (hlc59 : ci.toConstantVal.levelParams.length < 2 ^ 59) :
    SpecR (σ := σ) (Pre (ctxH C H) s (pcpParams.zip [cellA C oc, cellA C op])) pcpBody s (pinCopyOk ci pin)
      (PostPin (ctxH C H) (fun b => b = true)) := by
  refine specR_prologue (postPin_locals _ _) (pcp_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have htagc := cie_tag hci
  have htagp := pinRec_tag hpin
  have hpk : 3 ≤ ciTag pin ∧ ciTag pin ≤ 5 := by
    have h2 := hpin.2
    cases pin <;> simp_all [ciTag]
  obtain ⟨hcn, ⟨wcl, hwcl, ocl, hwcl', hecl⟩, hcty⟩ := hci.1
  obtain ⟨hpn, ⟨wpl, hwpl, opl, hwpl', hepl⟩, hpty⟩ := hpin.1
  subst hwcl' hwpl'
  have hcvB := ConRon.Bridge.denoteCI_toConstantVal hB
  have hcvP := ConRon.Bridge.denoteCI_toConstantVal hP
  obtain ⟨-, hlpB, -⟩ := ConRon.Bridge.denoteCV_inv hcvB
  obtain ⟨-, hlpP, htyP⟩ := ConRon.Bridge.denoteCV_inv hcvP
  set ps := ci.toConstantVal.levelParams with hps
  set pcv := pin.toConstantVal with hpcv
  have hlc : ps.length < 2 ^ 61 := by have := pin_eblk_len hok hHN' hecl; simpa using this
  have hlp : pcv.levelParams.length < 2 ^ 61 := by have := pin_eblk_len hok hHN' hepl; simpa using this
  -- the two level-parameter blocks
  refine UD.specR_heapLoadI' (C := ctxH C H) pyCl _ (oc + 2) _ (get_eq_of hwcl (by omega)) (by decide)
    (by simp +decide [sev, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) pyCn _ ocl _ hecl.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) pyPl _ (op + 2) _ (get_eq_of hwpl (by omega)) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) pyPn _ opl _ hepl.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine specR_guardNe pyCn pyPn (BitVec.ofNat 64 (ps.map Enc.idxW).length)
    (BitVec.ofNat 64 (pcv.levelParams.map Enc.idxW).length) (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
    (fun hln => ?_)
  have hln' : ps.length = pcv.levelParams.length := by
    simp only [List.length_map] at hln
    exact natW_inj (by omega) (by omega) hln
  -- distinct
  refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H) pyX fNdg ndgParams [vv pyCl, .const 0, vv pyCn] ndgBody
    [cellA C ocl, BitVec.ofNat 64 0, BitVec.ofNat 64 ps.length] (nameNodup (ps.drop 0))
    (by decide) rfl (by decide) hc.ndg
    ⟨by simp +decide [sev, Env.get_cons]; rfl, rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
      (ndg_spec C hc.ndh hc.ndg ps ocl (by omega) _ 0 H s hpH hecl rfl (Nat.zero_le _)))
    (fun w H1 hp1 hw => ?_)
  subst hw
  refine specR_guardZ pyX (boolW (nameNodup (ps.drop 0))) (by simp +decide [Env.get_cons]) (fun hnd => ?_)
  have hnd' : nameNodup ps = true := by
    cases e : nameNodup ps
    · simp [e, boolW] at hnd
    · rfl
  have hpH1 : C.H <+: H1 := hpH.trans hp1
  unfold pinCopyOk
  rw [if_pos (by simp [hnd', ← hps, hln', ← hpcv])]
  rw [atLps_split pin ps hpk.1]
  unfold IConstantVal.atLps
  simp only [bind_assoc, pure_bind]
  -- the pin's kind
  refine UD.specR_heapLoadI' (C := ctxH C H1) pyT _ op _ (get_prefix htagp hp1) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv] <;> rfl) ?_
  refine specR_tagRange pyT (ciTag pin) hpk (by simp +decide [Env.get_cons]) ?_
  -- the pin at the record's names: `paramLevels`, then the type
  refine specR_atEntry fun t1 ht1 => ?_
  have hlpd1 : Frontend.denoteNList s.store.ns ps = some B.toConstantVal.levelParams := hlpB
  refine specR_callNIH (C := ctxH C H1) pyUs fParamLevels plParams [vv pyCl] (plBody C) [cellA C ocl] (by decide) rfl
    (by decide) hc.pl ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
    (fun a w s' st => paramLevels ps s = .ok (a, s') ∧ PostLsH (ctxH C H1) a w s' st)
    (fun a w s' H' => paramLevels ps s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.ls ps ocl (by omega) H1 s (eblk_mono hecl hp1) _
        (pre_of_lookups hu plParams _ rfl hlk)))
    (fun us wu s2 H2 hp2 ⟨hr2, hwu⟩ => ?_)
  subst hwu
  have hpH2 : C.H <+: H2 := hpH1.trans hp2
  have hp12 : H <+: H2 := hp1.trans hp2
  obtain ⟨hs2, hus⟩ := ConRon.Bridge.paramLevels_run (sr_stateOK ht1.sr) hlpd1 hr2
  have hlpP2 := denoteNList_ext hs2.ext.lss.ls.ns _ _ hlpP
  have htyP2 := denote_ext htyP hs2.ext
  refine UD.specR_heapLoadI' (C := ctxH C H2) pyA _ (op + 3) _ (get_prefix (get_eq_of hpty (by omega)) hp12)
    (by decide) (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 3) ?_
  refine specR_atEntry fun t2 ht2 => ?_
  refine specR_callNIH (C := ctxH C H2) pyTy fInstLPF ilpParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv pyA, vv pyPl, vv pyUs] (ilpfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW pcv.type, cellA C opl, Enc.idxW us] (by decide) rfl
    (by decide) hc.ilpf
    ⟨rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl,
      by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => instLPFast coreWalkFuel pcv.levelParams us pcv.type s2 = .ok (a, s') ∧
      ILP.PostILP (ctxH C H2) a w s' st)
    (fun a w s' _ => instLPFast coreWalkFuel pcv.levelParams us pcv.type s2 = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
      (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt opl pcv.levelParams _ us _ H2 s2 pcv.type hlpP2 hus
        (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls (by rw [htyP2]; rfl) (eblk_mono hepl hp12))))
    (fun ty wt s3 H3 hp3 ⟨hr3, hwt⟩ => ?_)
  subst hwt
  have hp13 : H <+: H3 := hp12.trans hp3
  have hpH3 : C.H <+: H3 := hpH.trans hp13
  obtain ⟨hs3, -⟩ := instLPFast_run (sr_stateOK ht2.sr) ⟨ht2.sr.cok.rn, ht2.sr.cok.rl, ht2.sr.cok.rls⟩ hlpP2 hus
    htyP2 hr3
  -- kinds, names, types
  refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ oc _ (get_prefix htagc hp13) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ op _ (get_prefix htagp hp13) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv] <;> rfl) ?_
  refine specR_guardNe pyA pyB (BitVec.ofNat 64 (ciTag ci)) (BitVec.ofNat 64 (ciTag pin)) (by simp +decide [Env.get_cons])
    (by simp +decide [Env.get_cons]) (fun htg => ?_)
  have htg' : ciTag ci = ciTag pin := natW_inj (by have := ciTag_lt ci; omega) (by omega) htg
  refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 1) _ (get_prefix hcn hp13) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add8 C oc) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ (op + 1) _ (get_prefix hpn hp13) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add8 C op) ?_
  refine specR_guardNe pyA pyB (Enc.idxW ci.toConstantVal.name) (Enc.idxW pcv.name) (by simp +decide [Env.get_cons])
    (by simp +decide [Env.get_cons]) (fun hnm => ?_)
  have hnm' : ci.toConstantVal.name = pcv.name := Enc.idxW_inj hnm
  refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 3) _ (get_prefix (get_eq_of hcty (by omega)) hp13)
    (by decide) (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 3) ?_
  refine specR_guardNe pyA pyTy (Enc.idxW ci.toConstantVal.type) (Enc.idxW ty) (by simp +decide [Env.get_cons])
    (by simp +decide [Env.get_cons]) (fun hty => ?_)
  have hty' : ci.toConstantVal.type = ty := Enc.idxW_inj hty
  have hcv' : (⟨pcv.name, ps, ty⟩ : IConstantVal) = ci.toConstantVal := by
    rw [← hnm', ← hty']
  rw [hcv']
  clear_value ps pcv
  have hk2 := hpin.2
  have hkc := hci.2
  cases pin with
  | indInfo pv pcaps =>
    cases ci with
    | indInfo cv ccaps =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [atLpsK, pure_bind]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨by simp [pinAgrees, IConstantInfo.toConstantVal], H3, hp13, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ => simp [ciTag] at htg'
  | ctorInfo pv pnP pnF pT =>
    cases ci with
    | ctorInfo cv cnP cnF cT =>
      obtain ⟨-, hc4, hc5, hc6⟩ := hkc
      obtain ⟨-, hp4, hp5, hp6⟩ := hk2
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold cmpW
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 4) _ (get_prefix hc4.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 4) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ (op + 4) _ (get_prefix hp4.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 4) ?_
      refine specR_guardNe pyA pyB (BitVec.ofNat 64 cnP) (BitVec.ofNat 64 pnP) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons]) (fun e4 => ?_)
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 5) _ (get_prefix hc5.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 5) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ (op + 5) _ (get_prefix hp5.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 5) ?_
      refine specR_guardNe pyA pyB (BitVec.ofNat 64 cnF) (BitVec.ofNat 64 pnF) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons]) (fun e5 => ?_)
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 6) _ (get_prefix hc6 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 6) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ (op + 6) _ (get_prefix hp6 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 6) ?_
      refine specR_guardNe pyA pyB (Enc.idxW cT) (Enc.idxW pT) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons]) (fun e6 => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [atLpsK, pure_bind]
      have f4 := natW_inj hc4.2 hp4.2 e4
      have f5 := natW_inj hc5.2 hp5.2 e5
      have f6 := Enc.idxW_inj e6
      subst f4 f5 f6
      exact specR_returnI _ 1 rfl (fun t ht => ⟨by simp [pinAgrees, IConstantInfo.toConstantVal], H3, hp13, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ => simp [ciTag] at htg'
  | recInfo pv pmI prP pK prs =>
    cases ci with
    | recInfo cv cmI crP cK crs =>
      subst hpcv
      obtain ⟨-, hc4, hc5, hc6, ⟨wcr, hwcr, hcr⟩⟩ := hkc
      obtain ⟨-, hp4, hp5, hp6, ⟨wpr, hwpr, hpr⟩⟩ := hk2
      obtain ⟨orc, rfl, hcr'⟩ := pinRulesAt_of hcr
      obtain ⟨orp, rfl, hpr'⟩ := pinRulesAt_of hpr
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      unfold cmpW
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 4) _ (get_prefix hc4.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 4) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ (op + 4) _ (get_prefix hp4.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 4) ?_
      refine specR_guardNe pyA pyB (BitVec.ofNat 64 cmI) (BitVec.ofNat 64 pmI) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons]) (fun e4 => ?_)
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 5) _ (get_prefix hc5.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 5) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ (op + 5) _ (get_prefix hp5.1 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 5) ?_
      refine specR_guardNe pyA pyB (BitVec.ofNat 64 crP) (BitVec.ofNat 64 prP) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons]) (fun e5 => ?_)
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyA _ (oc + 6) _ (get_prefix hc6 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 6) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) pyB _ (op + 6) _ (get_prefix hp6 hp13) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 6) ?_
      refine specR_guardNe pyA pyB (boolW cK) (boolW pK) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons]) (fun e6 => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      have f4 := natW_inj hc4.2 hp4.2 e4
      have f5 := natW_inj hc5.2 hp5.2 e5
      have f6 := boolW_inj e6
      subst f4 f5 f6
      simp only [atLpsK, bind_assoc]
      -- `paramLevels` again
      refine specR_atEntry fun t3 ht3 => ?_
      have hlpd3 : Frontend.denoteNList s3.store.ns ps = some B.toConstantVal.levelParams :=
        denoteNList_ext hs3.ext.lss.ls.ns _ _ (denoteNList_ext hs2.ext.lss.ls.ns _ _ hlpd1)
      refine specR_callNIH (C := ctxH C H3) pyUs fParamLevels plParams [vv pyCl] (plBody C) [cellA C ocl] (by decide)
        rfl (by decide) hc.pl ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
        (fun a w s' st => paramLevels ps s3 = .ok (a, s') ∧ PostLsH (ctxH C H3) a w s' st)
        (fun a w s' H' => paramLevels ps s3 = .ok (a, s') ∧ w = Enc.idxW a)
        (fun a w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (fun w hw => by
          subst hw
          exact pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.ls ps ocl (by omega) H3 s3 (eblk_mono hecl hp13) _
            (pre_of_lookups hu plParams _ rfl hlk)))
        (fun us2 wu s4 H4 hp4' ⟨hr4, hwu⟩ => ?_)
      subst hwu
      have hp14 : H <+: H4 := hp13.trans hp4'
      obtain ⟨hs4, hus2⟩ := ConRon.Bridge.paramLevels_run (sr_stateOK ht3.sr) hlpd3 hr4
      have hx04 : Ext s.store s4.store := hs2.ext.trans (hs3.ext.trans hs4.ext)
      have hlpP4 := denoteNList_ext hx04.lss.ls.ns _ _ hlpP
      have hlpB4 := denoteNList_ext hx04.lss.ls.ns _ _ hlpB
      refine specR_readNamesI _ _ hlpP4 (fun c1 => ?_)
      refine specR_readNamesI _ _ hlpB4 (fun c2 => ?_)
      -- the rule blocks
      refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN4 => ?_)
      refine UD.specR_heapLoadI' (C := ctxH C H4) pyCr _ (oc + 7) _ (get_prefix hwcr hp14) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C oc 7) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H4) pyPr _ (op + 7) _ (get_prefix hwpr hp14) (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, pcpParams, ctxEnv]; exact cellA_add_ofNat C op 7) ?_
      have hcr4 := pinRulesAt_mono hp14 hcr'
      have hpr4 := pinRulesAt_mono hp14 hpr'
      refine UD.specR_heapLoadI' (C := ctxH C H4) pyA _ orc _ hcr4.1 (by decide)
        (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H4) pyB _ orp _ hpr4.1 (by decide)
        (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
      refine specR_guardNe pyA pyB (BitVec.ofNat 64 crs.length) (BitVec.ofNat 64 prs.length)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun ecnt => ?_)
      have hcl := pinRulesAt_len hok hHN4 hcr4
      have hpl := pinRulesAt_len hok hHN4 hpr4
      have ecnt' : crs.length = prs.length := natW_inj (by omega) (by omega) ecnt
      obtain ⟨-, Rs, -, -, hRs⟩ := denoteCI_rec_inv hP
      have hrh : ∀ r ∈ prs, (denoteE s4.store r.rhs).isSome = true := fun r hr => by
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (rules_rhs_den prs Rs hRs r hr)
        rw [denote_ext hx hx04]; rfl
      refine specR_callNIH (C := ctxH C H4) pyX fPrl prlParams
        [vv pyCr, vv pyPr, vv pyPl, vv pyUs, .const 0, vv pyB] prlBody
        [cellA C orc, cellA C orp, cellA C opl, Enc.idxW us2, BitVec.ofNat 64 0, BitVec.ofNat 64 prs.length]
        (by decide) rfl (by decide) hc.prl
        ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
          by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], rfl,
          by simp +decide [sev, Env.get_cons], trivial⟩
        (PostPin (ctxH C H4) (fun r => r = crs.drop 0)) (fun r _ _ _ => r = crs.drop 0)
        (fun a w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
        (fun u hu _ hlk => by
          rw [List.drop_zero]
          exact Knot.specR_of_pre u (pre_of_lookups hu prlParams _ rfl hlk)
            (by
              have := prl_spec (σ := σ) ra C hok hc pcv.levelParams _ us2 _ P.toConstantVal.levelParams
                (List.map ConLeche.Level.param B.toConstantVal.levelParams) opl crs prs orc orp ecnt' (by omega)
                prs.length 0 H4 (withC (withC s4 c1) c2) (hpH.trans hp14) (by simp) (Nat.zero_le _) hcr4 hpr4
                (eblk_mono hepl hp14) hlpP4 hus2 hrh
              simpa using this))
        (fun rr w s5 H5 hp5' hrr => ?_)
      subst hrr
      simp only [pure_bind, List.drop_zero]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨by simp [pinAgrees, IConstantInfo.toConstantVal], H5, hp14.trans hp5',
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ => simp [ciTag] at htg'
  | _ => simp [ciTag] at hpk


theorem pcs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pcsLocals → (ctxEnv C ++ pcsParams.zip vals).get x = none :=
  Knot.params_none C pcsLocals pcsParams vals (by decide) (by decide)

set_option maxHeartbeats 8000000 in
/-- **The block's records against the pin's from `i`** (`pinCopiesOk`): the port hangs unless it holds. -/
theorem pcs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PCCodes C)
    (blk pins : List IConstantInfo) (ob opb : Nat) (hlen : blk.length = pins.length) (hbl : blk.length < 2 ^ 59)
    (hlb : ∀ c ∈ blk, c.toConstantVal.levelParams.length < 2 ^ 59) (B P : List ConLeche.ConstantInfo) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → PinBlk C H opb pins →
      Frontend.denoteCIList s.store blk = some B → Frontend.denoteCIList s.store pins = some P →
      blk.length - i = f → i ≤ blk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (pcsParams.zip [cellA C ob, cellA C opb, BitVec.ofNat 64 i,
          BitVec.ofNat 64 blk.length])) pcsBody s (pinCopiesOk (blk.drop i) (pins.drop i))
        (PostPin (ctxH C H) (fun b => b = true)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hpH hblk hpb hB hP hf hi
    have hil : i = blk.length := by omega
    subst hil
    refine specR_prologue (postPin_locals _ _) (pcs_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, pcsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, hlen, List.drop_length]
    simp only [pinCopiesOk]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hpH hblk hpb hB hP hf hi
    have hil : i < blk.length := by omega
    have hilp : i < pins.length := by omega
    refine specR_prologue (postPin_locals _ _) (pcs_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, pcsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨os, hosl, hosb, hosr⟩ := hblk
    obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hpb
    have hb1 := hosb.2 i (by simp; omega)
    simp only [List.getElem_map] at hb1
    have hb2 := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hb2
    refine UD.specR_heapLoadI' (C := ctxH C H) psC _ (ob + 1 + i) _ hb1 (by decide)
      (by simp +decide [sev, Env.get, pcsParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) psP _ (opb + 1 + i) _ hb2 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, pcsParams, ctxEnv]; exact cellA_mulIdx C opb i (by omega)) ?_
    obtain ⟨xb, -, hxb⟩ := denoteCIList_get blk B i blk[i] hB (List.getElem?_eq_getElem hil)
    obtain ⟨xp, -, hxp⟩ := denoteCIList_get pins P i pins[i] hP (List.getElem?_eq_getElem hilp)
    rw [List.drop_eq_getElem_cons hil, List.drop_eq_getElem_cons hilp]
    simp only [pinCopiesOk]
    refine specR_atEntry fun t0 ht0 => ?_
    refine specR_callNIH (C := ctxH C H) psX fPcp pcpParams [vv psC, vv psP] pcpBody
      [cellA C os[i], cellA C ps[i]] (by decide) rfl (by decide) hc.pcp
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
      (fun b w s' st => pinCopyOk blk[i] pins[i] s = .ok (b, s') ∧ PostPin (ctxH C H) (fun b => b = true) b w s' st)
      (fun b _ s' _ => pinCopyOk blk[i] pins[i] s = .ok (b, s') ∧ b = true)
      (fun a w s' st ⟨hr, h0, H', hp', hsr⟩ => ⟨H', hp', ⟨hr, h0⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu pcpParams _ rfl hlk)
        (pcp_spec ra C hok hc blk[i] pins[i] os[i] ps[i] H s hpH (hosr i hil (by omega)) (hpsr i hilp (by omega))
          xb xp hxb hxp (hlb _ (List.getElem_mem hil)))))
      (fun b w s1 H1 hp1 ⟨hr1, hb⟩ => ?_)
    subst hb
    simp only [if_true]
    obtain ⟨hst1, -⟩ := pinCopyOk_run (sr_stateOK ht0.sr) ⟨ht0.sr.cok.rn, ht0.sr.cok.rl, ht0.sr.cok.rls⟩ hxb hxp hr1
    have hp01 : H <+: H1 := hp1
    refine specR_congr (m' := pinCopiesOk (blk.drop (i + 1)) (pins.drop (i + 1)) >>= fun b => pure b) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) psX fPcs pcsParams
      [vv psB, vv psQ, .op .add [vv psI, .const 1], vv psN] pcsBody
      [cellA C ob, cellA C opb, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 blk.length] (by decide) rfl (by decide) hc.pcs
      ⟨by simp +decide [sev, Env.get_cons, Env.get, pcsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, pcsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, pcsParams, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, pcsParams, ctxEnv], trivial⟩
      (PostPin (ctxH C H1) (fun b => b = true)) (fun b _ _ _ => b = true)
      (fun a w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pcsParams _ rfl hlk)
        (ih (i + 1) H1 s1 (hpH.trans hp01)
          ⟨os, hosl, blkAt_mono hosb hp01, fun j hj ho => cie_mono hp01 (hosr j hj ho)⟩
          (pinBlk_mono ⟨ps, hpsl, hpsb, hpsr⟩ hp01) (denoteCIList_mono hst1.ext _ _ hB)
          (denoteCIList_mono hst1.ext _ _ hP) (by omega) (by omega)))
      (fun b w s2 H2 hp2 hb2 => ?_)
    subst hb2
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H2, hp01.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
