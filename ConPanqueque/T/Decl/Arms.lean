import ConPanqueque.T.Decl.LitShape
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The value arms: `valueGuards`, `checkDefnVal`, `checkOpaqueVal`

The value's guards are `checkConstantVal`'s four expression checks on the value; then its type is inferred and
compared with the declared type by the knot's `defeq` entry.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def vgQ := ofString "vg_q"
def vgV := ofString "vg_v"
def vgL := ofString "vg_l"
def vgLn := ofString "vg_ln"
def vgR := ofString "vg_r"
def fVg := ofString "valueGuards"
def vgParams : List MlS := [vgQ, vgV]
def vgLocals : List MlS := [vgL, vgLn, vgR]

/-- `valueGuards`: the record's constant value at `vgQ`, the value `vgV`. -/
def vgBody : ProgHOL 64 := prologue vgLocals
  (.seq (.assign .local vgL (.load .one (.op .add [vv vgQ, .const 8])))
  (.seq (.assign .local vgLn (.load .one (vv vgL)))
  (callR vgR ExM.fLBB [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv vgV]
  (.ite (.cmp .equal (vv vgR) (.const 0)) rejectP
  (callR vgR ExM.fHasFvar [.const (BitVec.ofNat 64 coreWalkFuel), vv vgV]
  (.ite (.cmp .notEqual (vv vgR) (.const 0)) rejectP
  (callR vgR fAt [vv vgV, vv vgL, vv vgLn]
  (.ite (.cmp .equal (vv vgR) (.const 0)) rejectP
  (callR vgR fCrff [vv vgV]
  (.ite (.cmp .equal (vv vgR) (.const 0)) rejectP
  (.return (.const 0))))))))))))

def dvQ := ofString "dv_q"
def dvV := ofString "dv_v"
def dvT := ofString "dv_t"
def dvX := ofString "dv_x"
def dvR := ofString "dv_r"
def fDv := ofString "checkValue"
def dvParams : List MlS := [dvQ, dvV]
def dvLocals : List MlS := [dvT, dvX, dvR]

/-- The value check shared by `def` and `opaque`: guards, then the value's type against the declared type. -/
def dvBody : ProgHOL 64 := prologue dvLocals
  (.seq (.assign .local dvT (.load .one (.op .add [vv dvQ, .const 16])))
  (callR dvX fVg [vv dvQ, vv dvV]
  (callR dvX fI [.const (BitVec.ofNat 64 checkFuel), .const 0, vv dvV]
  (callR dvR fD [.const (BitVec.ofNat 64 checkFuel), .const 0, vv dvX, vv dvT]
  (.ite (.cmp .equal (vv dvR) (.const 0)) rejectP (.return (.const 0)))))))

def thQ := ofString "th_q"
def thV := ofString "th_v"
def thT := ofString "th_t"
def thX := ofString "th_x"
def thU := ofString "th_u"
def thZ := ofString "th_z"
def thE := ofString "th_e"
def thR := ofString "th_r"
def fTh := ofString "checkThmArm"
def thParams : List MlS := [thQ, thV]
def thLocals : List MlS := [thT, thX, thU, thZ, thE, thR]

/-- `checkThmVal`: the statement is a proposition, then the value check. -/
def thBody (C : Ctx) : ProgHOL 64 := prologue thLocals
  (.seq (.assign .local thT (.load .one (.op .add [vv thQ, .const 16])))
  (callR thX fI [.const (BitVec.ofNat 64 checkFuel), .const 0, vv thT]
  (callR thU fEns [.const (BitVec.ofNat 64 checkFuel), .const 0, vv thX]
  (.seq (.assign .local thZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (callR thE LLeq.fEqv [vv thU, vv thZ]
  (.ite (.cmp .equal (vv thE) (.const 2))
    (callR thR fDv [vv thQ, vv thV] (.return (vv thR)))
    rejectP))))))

section
variable {σ : Type}

/-- A `Callee` with a Boolean answer, called. -/
theorem specR_callCB {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM Bool} {k : Bool → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : Callee (σ := σ) C ps vs Bd s m (PostB C))
    (hk : ∀ b s' H', C.H <+: H' → m s = .ok (b, s') →
      SpecR (Inv (ctxH C H') s' ((x, boolW b) :: Γ) [] D) rest s' (k b) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIH x f ps es Bd vs hnd hl hx hC hes (fun a w s' st => m s = .ok (a, s') ∧ PostB C a w s' st)
    (fun a w s' _ => w = boolW a ∧ m s = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp, hw, hsr⟩ => ⟨H', hp, ⟨hw, hrun⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (hspec u hu (fun i hi _ => hlk i (by omega))))
    (fun a w s' H' hp ⟨hw, hrun⟩ => by subst hw; exact hk a s' H' hp hrun)

theorem vg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ vgLocals → (ctxEnv C ++ vgParams.zip vals).get x = none :=
  Knot.params_none C vgLocals vgParams vals (by decide) (by decide)

/-- **`valueGuards`**. -/
theorem vg_spec (C : Ctx) (hok : CtxOK C)
    (hlbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one))
    (hcB : ExB.CodesB C (ExB.bodyB C))
    (hbvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one))
    (hhf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one))
    (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (hat : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)) (hal : AlCodes C)
    (hcrff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)) (hcrf : CrfCodes C)
    (fe : IFEnv) (hfe : fe = C.fe) (cv : IConstantVal) (v : EIdx) (q o : Nat)
    (hl : C.H[q + 1]? = some (cellA C o)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (vgParams.zip [cellA C q, Enc.idxW v])) vgBody s (valueGuards fe cv v) (PostU C) := by
  refine specR_prologue (postU_locals C) (vg_none C _) ?_
  unfold valueGuards
  dsimp only
  simp only [pure_bind]
  subst hfe
  refine UD.specR_heapLoadI' (C := C) vgL _ (q + 1) _ hl (by decide)
    (by simp +decide [sev, Env.get, vgParams, ctxEnv]; exact cellA_add8 C q) ?_
  refine UD.specR_heapLoadI' (C := C) vgLn _ o _ hb.1 (by decide) (by simp +decide [Env.get]) ?_
  refine specR_callNIH (C := C) vgR ExM.fLBB [pFu, ExM.pKb, pH]
    [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv vgV] ExM.lbbBody
    [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 0, Enc.idxW v] (by decide) rfl (by decide) hlbb
    ⟨rfl, rfl, (by simp +decide [Env.get, vgParams, ctxEnv]), trivial⟩ (ExM.PostB C) (fun b w _ H' => H' = C.H ∧ w = boolW b)
    (fun b w s' st ⟨hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, ExM.pKb, pH] _ rfl hlk)
      (ExM.lbb_spec C hok hcB hbvb s coreWalkFuel 0 v CV.coreWalkFuel_lt (by decide)))
    (fun b w s5 H5 hp5 ⟨eH5, hw⟩ => ?_)
  subst hw; subst H5
  refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  refine specR_callNIH (C := ctxH C C.H) vgR ExM.fHasFvar [pFu, pH]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv vgV] ExM.hasFvarBody
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW v] (by decide) rfl (by decide) hhf
    ⟨rfl, (by simp +decide [Env.get, vgParams, ctxEnv]), trivial⟩ (ExM.PostB (ctxH C C.H)) (fun b w _ H' => H' = C.H ∧ w = boolW b)
    (fun b w s' st ⟨hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExM.hasFvar_spec (ctxH C C.H) (ctxOK_H hok _) (by ctx_tr hcF) hfvb s5 coreWalkFuel v CV.coreWalkFuel_lt))
    (fun b w s6 H6 hp6 ⟨eH6, hw⟩ => ?_)
  subst hw; subst H6
  refine specR_failIteT (c := b) _ (boolW b) (by simp +decide [sev, Env.get]; exact nez_b b)
    (boolW_ne _) (boolW_eq _) (fun _ => ?_)
  refine specR_atEntry fun t6 ht6 => ?_
  have hL : LpsAt (ctxH C C.H) s6 o cv.levelParams ks :=
    ⟨hb, hkl, fun j hj => denoteN_ext (hks j hj) ht6.sr.floor, hlen⟩
  refine specR_callNIH (C := ctxH C C.H) vgR fAt atParams [vv vgV, vv vgL, vv vgLn] atBody
    [Enc.idxW v, cellA C o, BitVec.ofNat 64 cv.levelParams.length] (by decide) rfl (by decide) hat
    ⟨(by simp +decide [Env.get, vgParams, ctxEnv]), (by simp +decide [Env.get, vgParams, ctxEnv]), by simp +decide [Env.get, vgParams, ctxEnv], trivial⟩ (PostB (ctxH C C.H)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu atParams _ rfl hlk)
      (at_spec (ctxH C C.H) (ctxOK_H hok _) (by ctx_tr hal) s6 v hL))
    (fun b w s7 H7 hp7 hw => ?_)
  subst hw
  refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  have hok7 := ctxOK_H hok H7
  refine specR_callNIH (C := ctxH C H7) vgR fCrff [crffE] [vv vgV] crffBody [Enc.idxW v] (by decide) rfl
    (by decide) hcrff ⟨(by simp +decide [Env.get, vgParams, ctxEnv]), trivial⟩ (PostB (ctxH C H7)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
      (crff_spec (ctxH C H7) hok7 (by ctx_tr hcrf) s7 v))
    (fun b w s8 H8 hp8 hw => ?_)
  subst hw
  refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H8, hp7.trans hp8, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- An answer of a check that returns a record (built by the caller): the heap may have grown. -/
def PostCI (C : Ctx) (_ : IConstantInfo) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postCI_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCI C a w s' st → PostCI C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, h⟩ => ⟨H', hp, sr_of_eq h rfl rfl rfl rfl⟩

theorem dv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dvLocals → (ctxEnv C ++ dvParams.zip vals).get x = none :=
  Knot.params_none C dvLocals dvParams vals (by decide) (by decide)

/-- The value guards and the type comparison, at any continuation record `r`. -/
theorem dv_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C) (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C)
    (hvg : C.code.lookup fVg = some (vgParams.map (fun p => (p, ShapeHOL.one)), vgBody, .one))
    (cv : IConstantVal) (v : EIdx) (q : Nat)
    (hvgS : ∀ (H : List (BitVec 64)) (s : AState), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (vgParams.zip [cellA C q, Enc.idxW v])) vgBody s (valueGuards C.fe cv v)
        (PostU (ctxH C H)))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (r : IConstantInfo) (err : CheckError)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (dvParams.zip [cellA C q, Enc.idxW v])) dvBody s
      (do
        valueGuards C.fe cv v
        let vtype ← inferTypeCore mode C.fe checkFuel 0 v
        unless ← isDefEqCore mode C.fe checkFuel 0 vtype cv.type do
          fail err
        pure r) (PostCI C) := by
  refine specR_prologue (postCI_locals C) (dv_none C _) ?_
  refine UD.specR_heapLoadI' (C := C) dvT _ (q + 2) _ ht (by decide)
    (by simp +decide [sev, Env.get, dvParams, ctxEnv]; exact cellA_add_ofNat C q 2) ?_
  refine specR_callNIH (C := C) dvX fVg vgParams [vv dvQ, vv dvV] vgBody [cellA C q, Enc.idxW v] (by decide) rfl
    (by decide) hvg ⟨(by simp +decide [Env.get, dvParams, ctxEnv]), (by simp +decide [Env.get, dvParams, ctxEnv]), trivial⟩ (PostU C) (fun _ _ _ _ => True)
    (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu vgParams _ rfl hlk) (hvgS C.H s (List.prefix_refl _)))
    (fun _ w s1 H1 hp1 _ => ?_)
  have hok1 := ctxOK_H hok H1
  have hk1 := kcodes_H hk H1
  refine Big.specR_callKC (C := ctxH C H1) dvX fI kParams [.const (BitVec.ofNat 64 checkFuel), .const 0, vv dvV]
    (inferE (ctxH C H1) fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW v] (by decide) rfl
    (by decide) hk1.ei ⟨rfl, rfl, by simp +decide [Env.get, dvParams, ctxEnv], trivial⟩
    (Comp.inferTop ra mode hok1 hk1 (allCodes_H hac H1) hs s1 0 (by decide) v) (fun vt s2 H2 hp2 _ => ?_)
  have hok2 := ctxOK_H hok H2
  have hk2 := kcodes_H hk H2
  refine specR_callCB (C := ctxH C H2) dvR fD dParams [.const (BitVec.ofNat 64 checkFuel), .const 0, vv dvX, vv dvT]
    (dE (ctxH C H2)) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW vt, Enc.idxW cv.type] (by decide) rfl
    (by decide) hk2.ed ⟨rfl, rfl, by simp +decide [Env.get], by simp +decide [Env.get], trivial⟩
    (Comp.defeqTop ra mode hok2 hk2 (allCodes_H hac H2) hs s2 0 (by decide) vt cv.type) (fun b s3 H3 hp3 _ => ?_)
  simp only [pure_bind]
  refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- **`checkDefnVal`**. -/
theorem defn_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C) (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C)
    (hvg : C.code.lookup fVg = some (vgParams.map (fun p => (p, ShapeHOL.one)), vgBody, .one))
    (cv : IConstantVal) (v : EIdx) (q : Nat)
    (hvgS : ∀ (H : List (BitVec 64)) (s : AState), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (vgParams.zip [cellA C q, Enc.idxW v])) vgBody s (valueGuards C.fe cv v)
        (PostU (ctxH C H)))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hint : ConLeche.ReducibilityHint) (s : AState) :
    SpecR (σ := σ) (Pre C s (dvParams.zip [cellA C q, Enc.idxW v])) dvBody s
      (checkDefnVal mode C.fe cv v hint) (PostCI C) :=
  dv_spec mode C hok ra hs hk hac hvg cv v q hvgS ht _ _ s

/-- **`checkOpaqueVal`**. -/
theorem opaque_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C) (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C)
    (hvg : C.code.lookup fVg = some (vgParams.map (fun p => (p, ShapeHOL.one)), vgBody, .one))
    (cv : IConstantVal) (v : EIdx) (q : Nat)
    (hvgS : ∀ (H : List (BitVec 64)) (s : AState), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (vgParams.zip [cellA C q, Enc.idxW v])) vgBody s (valueGuards C.fe cv v)
        (PostU (ctxH C H)))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (s : AState) :
    SpecR (σ := σ) (Pre C s (dvParams.zip [cellA C q, Enc.idxW v])) dvBody s
      (checkOpaqueVal mode C.fe cv v) (PostCI C) :=
  dv_spec mode C hok ra hs hk hac hvg cv v q hvgS ht _ _ s


theorem th_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ thLocals → (ctxEnv C ++ thParams.zip vals).get x = none :=
  Knot.params_none C thLocals thParams vals (by decide) (by decide)

/-- **`checkThmVal`** (the level comparison's spec a hypothesis: `lvlEqQ_spec` at the bundled codes). -/
theorem thm_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C) (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C)
    (hens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one))
    (heq : C.code.lookup LLeq.fEqv = some ([LEq.pLa, LEq.pLb].map (fun p => (p, ShapeHOL.one)), LLeq.eqvBody, .one))
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (hdv : C.code.lookup fDv = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody, .one))
    (cv : IConstantVal) (v : EIdx) (q : Nat)
    (hdvS : ∀ (H : List (BitVec 64)) (s : AState), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (dvParams.zip [cellA C q, Enc.idxW v])) dvBody s
        (do
          valueGuards C.fe cv v
          let vtype ← inferTypeCore mode C.fe checkFuel 0 v
          unless ← isDefEqCore mode C.fe checkFuel 0 vtype cv.type do
            fail (.invalid "type mismatch in theorem")
          pure (IConstantInfo.thmInfo cv)) (PostCI (ctxH C H)))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (s : AState) :
    SpecR (σ := σ) (Pre C s (thParams.zip [cellA C q, Enc.idxW v])) (thBody C) s
      (checkThmVal mode C.fe cv v) (PostCI C) := by
  refine specR_prologue (postCI_locals C) (th_none C _) ?_
  unfold checkThmVal
  refine UD.specR_heapLoadI' (C := C) thT _ (q + 2) _ ht (by decide)
    (by simp +decide [sev, Env.get, thParams, ctxEnv]; exact cellA_add_ofNat C q 2) ?_
  refine Big.specR_callKC (C := C) thX fI kParams [.const (BitVec.ofNat 64 checkFuel), .const 0, vv thT]
    (inferE C fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW cv.type] (by decide) rfl
    (by decide) hk.ei ⟨rfl, rfl, by simp +decide [Env.get], trivial⟩
    (Comp.inferTop ra mode hok hk hac hs s 0 (by decide) cv.type) (fun st s1 H1 hp1 _ => ?_)
  have hok1 := ctxOK_H hok H1
  refine specR_callNIH (C := ctxH C H1) thU fEns kParams [.const (BitVec.ofNat 64 checkFuel), .const 0, vv thX]
    ensBody [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW st] (by decide) rfl (by decide) hens
    ⟨rfl, rfl, by simp +decide [Env.get], trivial⟩ (PostLH (ctxH C H1))
    (fun u w s' H' => w = Enc.idxW u ∧ ∃ h, s'.store.view h = some (.sort u))
    (fun u w s' st' ⟨H', hp', hw, hsr, hv⟩ => ⟨H', hp', ⟨hw, hv⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk)
      (ens_top ra mode hok1 (kcodes_H hk H1) (allCodes_H hac H1) hs s1 st))
    (fun u w s2 H2 hp2 ⟨hw, hh, hvu⟩ => ?_)
  subst hw
  have hok2 := ctxOK_H hok H2
  simp only [zeroLevel]
  refine specR_pinXI (C := ctxH C H2) hok2 pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H2) hok2 hp) (pin_zeroLevel_cell hok2) thZ (by decide) ?_
  refine specR_atEntry fun t2 ht2 => ?_
  obtain ⟨lu, hlu⟩ := sr_sortDen ht2.sr hh u hvu
  have hz := sr_zeroLevel ht2.sr
  refine specR_callNIH (C := ctxH C H2) thE LLeq.fEqv [LEq.pLa, LEq.pLb] [vv thU, vv thZ] LLeq.eqvBody
    [Enc.idxW u, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) heq
    ⟨by simp +decide [Env.get], by simp +decide [Env.get] <;> rfl, trivial⟩ (LLeq.PostOB (ctxH C H2))
    (fun o w s' H' => H' = H2 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H2, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
      (heqS H2 u C.pins.zeroLevel s2 lu .zero hlu hz ht2.sr.cok))
    (fun o w s3 H3 hp3 ⟨eH3, hw⟩ => ?_)
  subst hw; subst H3
  rcases o with _ | ⟨_ | _⟩
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => specR_rejectI)
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => specR_rejectI)
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [liftFueled, pure_bind, ite_true]
    refine specR_bindPure ?_
    refine specR_callNIH (C := ctxH C H2) thR fDv dvParams [vv thQ, vv thV] dvBody [cellA C q, Enc.idxW v] (by decide)
      rfl (by decide) hdv ⟨by simp +decide [Env.get, thParams, ctxEnv], by simp +decide [Env.get, thParams, ctxEnv], trivial⟩
      (PostCI (ctxH C H2)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu dvParams _ rfl hlk) (hdvS H2 s3 (hp1.trans hp2)))
      (fun a w s4 H4 hp4 _ => ?_)
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨H4, hp1.trans (hp2.trans hp4), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
