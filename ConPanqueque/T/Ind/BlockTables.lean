import ConPanqueque.T.Ind.StructTbl2

/-!
# The block's projection tables (`blockTables`, one member)

`btBody`: a member with one constructor and no indices is a structure: its table
`[name, levelParams, nP, ctor, nFields, bodies]` as a value record, in a one-entry block; otherwise an empty block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- A projection table as a value record. -/
def TblVRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (t : IProjTable) : Prop :=
  H[o]? = some (Enc.idxW t.structName) ∧ (∃ ol, H[o + 1]? = some (cellA C ol) ∧ BlkAt H ol (t.levelParams.map Enc.idxW)) ∧
    H[o + 2]? = some (BitVec.ofNat 64 t.numParams) ∧ H[o + 3]? = some (Enc.idxW t.ctor) ∧
    H[o + 4]? = some (BitVec.ofNat 64 t.numFields) ∧
    ∃ ob, H[o + 5]? = some (cellA C ob) ∧ BlkAt H ob (t.bodies.toList.map Enc.idxW)

theorem tblVRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {t : IProjTable}
    (h : TblVRep C H o t) : TblVRep C H' o t :=
  let ⟨a, ⟨ol, b, c⟩, d, e, f, ⟨ob, g, i⟩⟩ := h
  ⟨get_prefix a hp, ⟨ol, get_prefix b hp, blkAt_mono c hp⟩, get_prefix d hp, get_prefix e hp, get_prefix f hp,
    ⟨ob, get_prefix g hp, blkAt_mono i hp⟩⟩

def btM := ofString "bt_m"
def btNp := ofString "bt_np"
def btCv := ofString "bt_cv"
def btLp := ofString "bt_lp"
def btDc := ofString "bt_dc"
def btDn := ofString "bt_dn"
def btNi := ofString "bt_ni"
def btCs := ofString "bt_cs"
def btNc := ofString "bt_nc"
def btC0 := ofString "bt_c0"
def btCt := ofString "bt_ct"
def btCn := ofString "bt_cn"
def btNf := ofString "bt_nf"
def btBs := ofString "bt_bs"
def btT := ofString "bt_t"
def btQ := ofString "bt_q"
def fBt := ofString "blockTables"

def btParams : List MlS := [btM, btNp]
def btLocals : List MlS := [btCv, btLp, btDc, btDn, btNi, btCs, btNc, btC0, btCt, btCn, btNf, btBs, btT, btQ, lW]

def btEmpty (C : Ctx) : ProgHOL 64 := alloc1 C lW (.const 0) (.return (vv lW))

def btBody (C : Ctx) : ProgHOL 64 := prologue btLocals
  (.seq (.assign .local btCv (.load .one (vv btM)))
  (.seq (.assign .local btLp (.load .one (.op .add [vv btCv, .const 8])))
  (.seq (.assign .local btDc (.load .one (.op .add [vv btM, .const 8])))
  (.seq (.assign .local btDn (.load .one (vv btDc)))
  (.seq (.assign .local btNi (.load .one (.op .add [vv btM, .const 16])))
  (.seq (.assign .local btCs (.load .one (.op .add [vv btM, .const 24])))
  (.seq (.assign .local btNc (.load .one (vv btCs)))
  (.ite (.cmp .equal (vv btNc) (.const 1))
    (.ite (.cmp .equal (vv btNi) (.const 0))
      (.seq (.assign .local btC0 (.load .one (.op .add [vv btCs, .const 8])))
      (.seq (.assign .local btCt (.load .one (.op .add [vv btC0, .const 16])))
      (.seq (.assign .local btCn (.load .one (vv btC0)))
      (.seq (.assign .local btNf (.load .one (.op .add [vv btCs, .const 16])))
      (.seq (.call (some (some (.local, btBs), none)) fSpb [vv btDn, vv btNp, vv btNf, vv btCt])
      (alloc6 C btT (vv btDn) (vv btLp) (vv btNp) (vv btCn) (vv btNf) (vv btBs)
      (alloc2 C btQ (.const 1) (vv btT) (.return (vv btQ)))))))))
      (btEmpty C))
    (btEmpty C)))))))))

section
variable {σ : Type}

theorem bt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ btLocals → (ctxEnv C ++ btParams.zip vals).get x = none :=
  Knot.params_none C btLocals btParams vals (by decide) (by decide)

/-- Some tables, as a block of value records. -/
def PostBTb (C : Ctx) (o : Option (List IProjTable)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ Q H' ob, o = some Q ∧ C.H <+: H' ∧ w = cellA C ob ∧ PRep C H' ob (fun H o t => TblVRep C H o t) Q ∧
    SR (ctxH C H') s' st

theorem postBTb_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBTb C a w s' st → PostBTb C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨Q, H', ob, h0, h1, h2, h3, h4⟩ => ⟨Q, H', ob, h0, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

end

structure BTCodes (C : Ctx) : Prop where
  spb : SPBCodes C
  self : C.code.lookup fBt = some (btParams.map (fun p => (p, ShapeHOL.one)), btBody C, .one)

section
variable {σ : Type}

theorem bt_empty_spec (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} :
    SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ btLocals)) (btEmpty C) s (pure (some [])) (PostBTb C) := by
  unfold btEmpty
  refine specR_alloc1I hok lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
  have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
  have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
  exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]) (fun t ht => ⟨[], _, H2.length, rfl,
    (hp2 : C.H <+: H2).trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

set_option maxHeartbeats 32000000 in
/-- **`blockTables`** of one member (any member whose level parameters are the block's). -/
theorem bt_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BTCodes C)
    (p : BlockShape) (ms0 : MemberShape) (hlps : p.lps = ms0.cvT.levelParams) (om : Nat) (hmr : MemberRep C C.H om ms0)
    (hnP : p.nP < 2 ^ 57) (hni : ms0.nIdx < 2 ^ 64) (hnf : ∀ c ∈ ms0.ctors, c.2 < 2 ^ 57)
    (hcl : ms0.ctors.length < 2 ^ 63) (s : AState) :
    SpecR (σ := σ) (Pre C s (btParams.zip [cellA C om, BitVec.ofNat 64 p.nP])) (btBody C) s
      (blockTables p [ms0]) (PostBTb C) := by
  refine specR_prologue (postBTb_locals C) (bt_none C _) ?_
  obtain ⟨⟨oc, hoc, hcvT⟩, ⟨od, hod, hcvD⟩, hniw, ⟨ol, hol, hcr⟩⟩ := hmr
  obtain ⟨-, ⟨wl, hwl, olp, hwlo, hebl⟩, -⟩ := hcvT
  subst hwlo
  refine UD.specR_heapLoadI' (C := C) btCv _ om _ hoc (by decide) (by simp +decide [sev, Env.get, btParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) btLp _ (oc + 1) _ hwl (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oc) ?_
  refine UD.specR_heapLoadI' (C := C) btDc _ (om + 1) _ hod (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, btParams, ctxEnv]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := C) btDn (vv btDc) od _ hcvD.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) btNi _ (om + 2) _ hniw (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, btParams, ctxEnv]; exact cellA_add_ofNat C om 2) ?_
  refine UD.specR_heapLoadI' (C := C) btCs _ (om + 3) _ hol (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, btParams, ctxEnv]; exact cellA_add_ofNat C om 3) ?_
  refine UD.specR_heapLoadI' (C := C) btNc (vv btCs) ol _ hcr.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  simp only [blockTables, MemberShape.structCtor?]
  rcases hcs : ms0.ctors with _ | ⟨c, _ | ⟨c', cs'⟩⟩
  · simp only
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hcs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => bt_empty_spec C hok)
  swap
  · simp only
    have hne : BitVec.ofNat 64 (c :: c' :: cs').length ≠ 1#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [hcs] at hcl; simp at this hcl; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hcs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => bt_empty_spec C hok)
  rw [hcs] at hcr
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  by_cases h0 : ms0.nIdx = 0
  swap
  · have hne : BitVec.ofNat 64 ms0.nIdx ≠ 0#64 := fun e => h0 (by have := congrArg BitVec.toNat e; simp at this; omega)
    simp only [h0, beq_iff_eq, ite_false]
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => bt_empty_spec C hok)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  simp only [h0, beq_self_eq_true, ite_true]
  obtain ⟨oc0, hoc0, hcv0, ⟨hnf0, -⟩⟩ := hcr.2 0 (by simp)
  simp only [List.getElem_cons_zero] at hcv0 hnf0
  refine UD.specR_heapLoadI' (C := C) btC0 _ (ol + 1 + 2 * 0) _ hoc0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ol) ?_
  refine UD.specR_heapLoadI' (C := C) btCt _ (oc0 + 2) _ hcv0.2.2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc0 2) ?_
  refine UD.specR_heapLoadI' (C := C) btCn (vv btC0) oc0 _ hcv0.1 (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) btNf _ (ol + 2 + 2 * 0) _ hnf0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ol 2) ?_
  have hnfc := hnf c (by rw [hcs]; exact List.mem_cons_self ..)
  refine specR_callNIH (C := C) btBs fSpb spbParams [vv btDn, vv btNp, vv btNf, vv btCt] spbBody
    [Enc.idxW ms0.declared.name, BitVec.ofNat 64 p.nP, BitVec.ofNat 64 c.2, Enc.idxW c.1.type] (by decide) rfl (by decide)
    hc.spb.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, btParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostSA C) (fun o w _ H' => ∃ arr ob, o = some arr ∧ w = cellA C ob ∧ BlkAt H' ob (arr.toList.map Enc.idxW))
    (fun o w s' st ⟨arr, H', ob, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨arr, ob, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu spbParams _ rfl hlk)
      (spb_spec ra C hok hc.spb ms0.declared.name p.nP c.2 hnP hnfc c.1.type s))
    (fun o w s1 H1 hp1 ⟨arr, ob, ho, hw, hb⟩ => ?_)
  subst ho hw
  have hp1' : C.H <+: H1 := hp1
  simp only [pure_bind, Option.map_some]
  refine specR_alloc6I (ctxOK_H hok H1) btT (vv btDn) (vv btLp) (vv btNp) (vv btCn) (vv btNf) (vv btBs)
    (Enc.idxW ms0.declared.name) (cellA C olp) (BitVec.ofNat 64 p.nP) (Enc.idxW c.1.name) (BitVec.ofNat 64 c.2) (cellA C ob)
    (by decide) (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons]; rfl)
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, btParams, ctxEnv]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun H2 ws hp2 hws hroom => ?_)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := img6_get H2 ws (Enc.idxW ms0.declared.name) (cellA C olp) (BitVec.ofNat 64 p.nP)
    (Enc.idxW c.1.name) (BitVec.ofNat 64 c.2) (cellA C ob) hws
  have hp2' : H1 <+: img6 H2 ws (Enc.idxW ms0.declared.name) (cellA C olp) (BitVec.ofNat 64 p.nP)
      (Enc.idxW c.1.name) (BitVec.ofNat 64 c.2) (cellA C ob) := (hp2 : H1 <+: H2).trans (img6_prefix H2 ws _ _ _ _ _ _ hws)
  refine specR_alloc2I (ctxOK_H hok _) btQ (.const 1) (vv btT) 1 (cellA C H2.length) (by decide) (fun _ => rfl)
    (fun _ => by simp +decide [sev, Env.get_cons]; rfl) (fun H3 ws3 hp3 hws3 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H3 ws3 (1 : BitVec 64) (cellA C H2.length) hws3
  have hp3' : _ <+: _ := (hp3 : _ <+: H3).trans (img2_prefix H3 ws3 (1 : BitVec 64) (cellA C H2.length) hws3)
  exact specR_returnI _ (cellA C H3.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, _, H3.length, rfl,
    hp1'.trans (hp2'.trans hp3'), rfl,
    ⟨[H2.length], rfl, ⟨by simpa using k0, fun i hi => by simp at hi; subst hi; simpa using k1⟩,
      fun i hi hio => by
        simp at hi; subst hi
        exact tblVRep_mono hp3' ⟨g0, ⟨olp, g1, by have := blkAt_mono hebl (hp1'.trans hp2'); simpa [hlps, ctxH] using this⟩,
          g2, g3, g4, ⟨ob, g5, blkAt_mono hb hp2'⟩⟩⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
