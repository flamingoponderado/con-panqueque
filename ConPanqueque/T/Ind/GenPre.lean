import ConPanqueque.T.Ind.ClassCtor
import ConPanqueque.T.Ind.CloseTele
import ConPanqueque.T.Ind.CheckPos

/-!
# The generator's pieces: `targetPiDomsWith`

`tpwBody`: the domains of the first `|xs|` `∀` binders, each instantiated at the earlier `xs` (a non-`∀` hangs:
its callers fail at `none`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def tpwA := ofString "tpw_a"
def tpwI := ofString "tpw_i"
def tpwN := ofString "tpw_n"
def tpwE := ofString "tpw_e"
def tpwX := ofString "tpw_x"
def tpwD := ofString "tpw_d"
def tpwB := ofString "tpw_b"
def fTpw := ofString "targetPiDomsWith"

def tpwParams : List MlS := [tpwA, tpwI, tpwN, tpwE]
def tpwLocals : List MlS := gaaLocals ++ [tpwX, tpwD, tpwB]

def tpwBody (C : Ctx) : ProgHOL 64 := prologue tpwLocals
  (.ite (.cmp .lower (vv tpwI) (vv tpwN))
    (.ite (tagIsE tpwE 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv tpwE)) (.seq eViewP
      (.seq (.assign .local tpwD (.load .one (vv lRp)))
      (.seq (.assign .local tpwB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.assign .local tpwX (.load .one (.op .add [vv tpwA, .op .add [.panop .mul [vv tpwI, .const 8], .const 8]])))
      (.seq (.call (some (some (.local, tpwB), none)) fInst1F [.const (BitVec.ofNat 64 coreWalkFuel), vv tpwB, vv tpwX, .const 0])
      (.seq (.call (some (some (.local, ExS.lY), none)) fTpw [vv tpwA, .op .add [vv tpwI, .const 1], vv tpwN, vv tpwB])
        (prependP C tpwD)))))))))
      hang)
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure TPWCodes (C : Ctx) : Prop where
  i1f : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  i1c : Codes C (ExI.body C)
  self : C.code.lookup fTpw = some (tpwParams.map (fun p => (p, ShapeHOL.one)), tpwBody C, .one)

section
variable {σ : Type}

theorem tpw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tpwLocals → (ctxEnv C ++ tpwParams.zip vals).get x = none :=
  Knot.params_none C tpwLocals tpwParams vals (by decide) (by decide)

/-- `some` list, as a block. -/
def PostSL (C : Ctx) (o : Option (List EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ ds H' ob, o = some ds ∧ C.H <+: H' ∧ w = cellA C ob ∧ BlkAt H' ob (ds.map Enc.idxW) ∧ SR (ctxH C H') s' st

theorem postSL_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSL C a w s' st → PostSL C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨ds, H', ob, h0, h1, h2, h3, h4⟩ => ⟨ds, H', ob, h0, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **`targetPiDomsWith`** from position `i` (a non-`∀` hangs). -/
theorem tpw_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : TPWCodes C)
    (args : List EIdx) (pa : Nat) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hA : BlkAt H0 pa (args.map Enc.idxW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState) (e : EIdx), args.length - i = f → i ≤ args.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (tpwParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 args.length,
        Enc.idxW e])) (tpwBody C) s (targetPiDomsWith (args.drop i) e) (PostSL (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s e hf hi hp
    have hin : i = args.length := by omega
    subst hin
    refine specR_prologue (postSL_locals _) (tpw_none _ _) ?_
    have hal := blkAt_len_le (blkAt_mono hA hp)
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff args.length args.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, tpwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, targetPiDomsWith]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨[], _, H2.length, rfl,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s e hf hi hp
    have hin : i < args.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (postSL_locals _) (tpw_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le (blkAt_mono hA hp)
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i args.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tpwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, targetPiDomsWith]
    obtain ⟨w, hw, hiff⟩ := sev_tagIs (ctxEnv (ctxH C H) ++ tpwParams.zip [cellA C pa, BitVec.ofNat 64 i,
      BitVec.ofNat 64 args.length, Enc.idxW e]) tpwE e (by simp +decide [Env.get, tpwParams, ctxEnv]) 6 (by omega) (by omega)
    by_cases ht : e.tag = UInt32.ofNat 6
    case neg =>
      exact specR_ifI _ w hw (fun e' => absurd (hiff.mp e') ht) (fun _ => specR_hangI)
    have hb : (e.tag == ETag.forallE) = true := by simp [ht]; rfl
    rw [hb]; simp only [ite_true]
    refine specR_ifI _ w hw (fun _ => ?_) (fun e' => absurd (hiff.mpr ht) (by simp [e']))
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, tpwParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv tpwE) (Enc.idxW e) (by decide) (by simp +decide [Env.get_cons, Env.get, tpwParams, ctxEnv]) ?_
    refine specR_viewXI ConRon.Arena.viewBind projBind e (fun vw hvw => viewBind_run e (Or.inr ht) s vw hvw)
      (by simp) (by simp +decide <;> rfl) (by simp +decide [Env.get_cons, Env.get, tpwParams, ctxEnv] <;> rfl) (by decide)
      (fun vw P htg hsh => ?_)
    obtain ⟨ty, b, hpb, hwv⟩ : ∃ ty b, projBind vw = some (ty, b) ∧ encEView vw = [Enc.idxW ty, Enc.idxW b] := by
      have htT : e.tag.toNat = 6 := by rw [ht]; simp
      rw [htT] at htg
      cases vw with
      | lam ty b => exact ⟨ty, b, rfl, rfl⟩
      | forallE ty b => exact ⟨ty, b, rfl, rfl⟩
      | _ => simp [ENodeView.tagN] at htg <;> omega
    rw [hpb]; simp only
    refine specR_loadI' tpwD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide [sev]) (by simp)
      (by rw [hwv]; exact wordsAt_mem0 _ _ _ _) ?_
    refine specR_loadI' tpwB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons]) rfl
      (by rw [hwv]; exact wordsAt_mem1 _ _ _ _ _) ?_
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) tpwX _ (pa + 1 + i) _ (get_prefix hx hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, tpwParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine ILP.callE_spec (C := ctxH C H) tpwB fInst1F [pFu, pH, pV, pD]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv tpwB, vv tpwX, .const 0]
      (fastBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW args[i], BitVec.ofNat 64 0] (by decide) rfl
      (by decide) hc.i1f ⟨rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (fast_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.i1c) s coreWalkFuel b args[i] 0 (by decide) (by decide))
      (fun e1 s1 => ?_)
    refine specR_callNIH (C := ctxH C H) ExS.lY fTpw tpwParams [vv tpwA, .op .add [vv tpwI, .const 1], vv tpwN, vv tpwB]
      (tpwBody C) [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 args.length, Enc.idxW e1] (by decide) rfl
      (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tpwParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tpwParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, tpwParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostSL (ctxH C H)) (fun o w _ H' => ∃ ds ob, o = some ds ∧ w = cellA C ob ∧ BlkAt H' ob (ds.map Enc.idxW))
      (fun o w s' st ⟨ds, H', ob, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, ob, h0, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tpwParams _ rfl hlk)
        (ih (i + 1) H s1 e1 (by omega) (by omega) hp))
      (fun o w s2 H2 hp2 ⟨ds, oy, ho, hw, hb⟩ => ?_)
    subst ho hw
    have hp2' : H <+: H2 := hp2
    simp only
    refine ExPre.prepend_spec C hok (H := H2) tpwD (Enc.idxW ty) oy (ds.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hb (by decide)
      (by simp +decide [Env.get_cons, Env.get, tpwParams, ctxEnv]) (by decide) (fun H' o t hp' hb' hsr => ?_)
    exact ⟨ty :: ds, H', o, rfl, hp2'.trans hp', rfl, by simpa using hb', hsr⟩

end

/-! ## `ClassGen.minorTy.ihsGo` (recursive fields at class `0`) -/

/-- Field `j` as a recursive field `(j, t, tele)`, or none. -/
def recOf (x : ClassCtor) (j : Nat) : Option (Nat × Nat × Nat) :=
  match x.kinds.getD j ClassField.ordinary with
  | ClassField.recursive t tele => some (j, t, tele)
  | ClassField.ordinary => none

/-- The recursive fields from field `i` on: `(i, t, tele)`. -/
def recsFrom (x : ClassCtor) (i : Nat) : List (Nat × Nat × Nat) :=
  (List.range' i (x.nF - i)).filterMap (recOf x)

theorem recsFrom_zero_of (x : ClassCtor) (f : Nat → Option (Nat × Nat × Nat)) (hf : ∀ j, f j = recOf x j) :
    (List.range x.nF).filterMap f = recsFrom x 0 := by
  have : f = recOf x := funext hf
  subst this
  simp [recsFrom, List.range_eq_range']

theorem recsFrom_succ (x : ClassCtor) (i : Nat) (hi : i < x.nF) : recsFrom x i =
    (match x.kinds.getD i ClassField.ordinary with
      | ClassField.recursive t tele => [(i, t, tele)]
      | ClassField.ordinary => []) ++ recsFrom x (i + 1) := by
  unfold recsFrom
  rw [show x.nF - i = (x.nF - (i + 1)) + 1 by omega, List.range'_succ, List.filterMap_cons]
  cases h : x.kinds.getD i ClassField.ordinary <;> simp only [recOf, h] <;> simp

theorem recsFrom_end (x : ClassCtor) : recsFrom x x.nF = [] := by simp [recsFrom]

def mihKb := ofString "mih_kb"
def mihI := ofString "mih_i"
def mihN := ofString "mih_n"
def mihL := ofString "mih_l"
def mihFv := ofString "mih_fv"
def mihFn := ofString "mih_fn"
def mihWs := ofString "mih_ws"
def mihWn := ofString "mih_wn"
def mihE0 := ofString "mih_e0"
def mihNP := ofString "mih_np"
def mihNPc := ofString "mih_npc"
def mihK := ofString "mih_k"
def mihW := ofString "mih_w"
def mihX := ofString "mih_x"
def mihXs := ofString "mih_xs"
def mihLf := ofString "mih_lf"
def mihA := ofString "mih_a"
def mihAl := ofString "mih_al"
def mihF := ofString "mih_f"
def mihXl := ofString "mih_xl"
def mihFx := ofString "mih_fx"
def mihZ := ofString "mih_z"
def mihSz := ofString "mih_sz"
def mihMt := ofString "mih_mt"
def mihEb := ofString "mih_eb"
def mihB1 := ofString "mih_b1"
def mihB2 := ofString "mih_b2"
def mihB3 := ofString "mih_b3"
def mihB3l := ofString "mih_b3l"
def mihBd := ofString "mih_bd"
def mihBs := ofString "mih_bs"
def mihIh := ofString "mih_ih"
def mihBl := ofString "mih_bl"
def fMih := ofString "minorIhs"

def mihParams : List MlS := [mihKb, mihI, mihN, mihL, mihFv, mihFn, mihWs, mihWn, mihE0, mihNP, mihNPc]
def mihLocals : List MlS := gaaLocals ++ [mihK, mihW, mihX, mihXs, mihLf, mihA, mihAl, mihF, mihXl, mihFx, mihZ, mihSz,
  mihMt, mihEb, mihB1, mihB2, mihB3, mihB3l, mihBd, mihBs, mihIh, mihBl]

def mihRec (l : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, ExS.lY), none)) fMih [vv mihKb, .op .add [vv mihI, .const 1], vv mihN, l, vv mihFv,
    vv mihFn, vv mihWs, vv mihWn, vv mihE0, vv mihNP, vv mihNPc]

def mihBody (C : Ctx) : ProgHOL 64 := prologue mihLocals
  (.ite (.cmp .lower (vv mihI) (vv mihN))
    (.seq (.assign .local mihK (.load .one (.op .add [vv mihKb, .op .add [.panop .mul [vv mihI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv mihK) (.const 0))
      (.seq (mihRec (vv mihL)) (.return (vv ExS.lY)))
    (.ite (.cmp .lower (vv mihI) (vv mihWn))
    (.ite (.cmp .lower (vv mihI) (vv mihFn))
    (.seq (.assign .local mihK (.op .sub [vv mihK, .const 1]))
    (.seq (.assign .local mihW (.load .one (.op .add [vv mihWs, .op .add [.panop .mul [vv mihI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, mihX), none)) fOpenFvars [vv mihK, vv mihW, .op .add [vv mihE0, vv mihL]])
    (.ite (.cmp .equal (vv mihX) (.const 0)) hang
    (.seq (.assign .local mihXs (.load .one (vv mihX)))
    (.seq (.assign .local mihLf (.load .one (.op .add [vv mihX, .const 8])))
    (.seq (.call (some (some (.local, mihA), none)) fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), vv mihLf])
    (.seq (.assign .local mihAl (.load .one (vv mihA)))
    (.ite (.cmp .lower (vv mihAl) (vv mihNPc)) hang
    (.ite (.cmp .lower (vv mihAl) (.const (BitVec.ofNat 64 (2 ^ 56))))
    (.seq (.assign .local mihF (.load .one (.op .add [vv mihFv, .op .add [.panop .mul [vv mihI, .const 8], .const 8]])))
    (.seq (.assign .local mihXl (.load .one (vv mihXs)))
    (.ite (.cmp .lower (vv mihXl) (.const (BitVec.ofNat 64 (2 ^ 56))))
    (.seq (.call (some (some (.local, mihFx), none)) ExK.fMka [vv mihF, vv mihXs, .const 0, vv mihXl])
    (.seq (.assign .local mihZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, mihSz), none)) fInternSort [vv mihZ])
    (.seq (.call (some (some (.local, mihMt), none)) fInternFVar [vv mihSz, vv mihNP])
    (alloc1 C mihEb (.const 0)
    (.seq (.call (some (some (.local, mihB1), none)) fCat [vv mihEb, vv mihA, vv mihNPc])
    (alloc2 C mihB2 (.const 1) (vv mihFx)
    (.seq (.call (some (some (.local, mihB3), none)) fCat [vv mihB1, vv mihB2, .const 0])
    (.seq (.assign .local mihB3l (.load .one (vv mihB3)))
    (.seq (.call (some (some (.local, mihBd), none)) ExK.fMka [vv mihMt, vv mihB3, .const 0, vv mihB3l])
    (.seq (.call (some (some (.local, mihBs), none)) fFvtDs [vv mihXs])
    (.seq (.assign .local mihBl (.load .one (vv mihBs)))
    (.ite (.cmp .lower (vv mihBl) (.const (BitVec.ofNat 64 (2 ^ 56))))
    (.seq (.call (some (some (.local, mihIh), none)) fCtg [.op .add [vv mihE0, vv mihL], .const 0, vv mihBs, .const 0,
        vv mihBd])
    (.seq (mihRec (.op .add [vv mihL, .const 1]))
      (prependP C mihIh)))
    hang)))))))))))))
    hang)))
    hang))))))))))
    hang)
    hang)))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure MIHCodes (C : Ctx) : Prop where
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)
  cat : CatCodes C
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  ftd : C.code.lookup fFvtDs = some (ftdParams.map (fun p => (p, ShapeHOL.one)), ftdBody C, .one)
  ftf : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  ctg : CTGCodes C
  self : C.code.lookup fMih = some (mihParams.map (fun p => (p, ShapeHOL.one)), mihBody C, .one)

section
variable {σ : Type}

theorem mih_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mihLocals → (ctxEnv C ++ mihParams.zip vals).get x = none :=
  Knot.params_none C mihLocals mihParams vals (by decide) (by decide)

/-- The inductive hypotheses' answer: `some`, a fresh block, at most `n` of them. -/
def PostIH (C : Ctx) (n : Nat) (o : Option (List EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ ihs H' ob, o = some ihs ∧ C.H <+: H' ∧ w = cellA C ob ∧ BlkAt H' ob (ihs.map Enc.idxW) ∧ ihs.length ≤ n ∧
    SR (ctxH C H') s' st

theorem postIH_locals (C : Ctx) (n : Nat) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostIH C n a w s' st → PostIH C n a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨ihs, H', ob, h0, h1, h2, h3, h4, h5⟩ => ⟨ihs, H', ob, h0, h1, h2, h3, h4, sr_of_eq h5 rfl rfl rfl rfl⟩

theorem motiveSlot_zero' (sls : List ClassSlot) (k : ClassKey) (h : sls[0]? = some (.motive k)) :
    ClassRead.motiveSlot sls 0 = some 0 := by
  unfold ClassRead.motiveSlot
  cases sls with
  | nil => simp at h
  | cons a l =>
    simp at h; subst h
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
    simp

theorem mapM_binder_eq' (g : ClassGen) : ∀ l : List EIdx, l.mapM g.binder = fvarTypeDs l
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, fvarTypeDs, mapM_binder_eq' g l]; rfl

set_option maxHeartbeats 64000000 in
/-- **`ClassGen.minorTy.ihsGo g x d fvs ws l`** over the recursive fields from field `i` on (class `0`). -/
theorem mih_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : MIHCodes C)
    (g : ClassGen) (m : TargetMajor) (hcls : g.cls = [m]) (k : ClassKey) (hsl0 : g.slots[0]? = some (.motive k))
    (x : ClassCtor) (d : Nat) (fvs ws : List EIdx) (pk pf pw : Nat) (hko : KindsOK x.kinds) (hkl : x.kinds.length = x.nF)
    (hnf : x.nF < 2 ^ 56) (hd : d + x.nF < 2 ^ 61) (hnP : g.nP < 2 ^ 62) (hnpc : m.nPc < 2 ^ 62)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hkb : BlkAt H0 pk (x.kinds.map cfKindW))
    (hfb : BlkAt H0 pf (fvs.map Enc.idxW)) (hwb : BlkAt H0 pw (ws.map Enc.idxW)) :
    ∀ f i l (H : List (BitVec 64)) (s : AState), x.nF - i = f → i ≤ x.nF → l ≤ i → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (mihParams.zip [cellA C pk, BitVec.ofNat 64 i, BitVec.ofNat 64 x.nF,
        BitVec.ofNat 64 l, cellA C pf, BitVec.ofNat 64 fvs.length, cellA C pw, BitVec.ofNat 64 ws.length,
        BitVec.ofNat 64 (d + x.nF), BitVec.ofNat 64 g.nP, BitVec.ofNat 64 m.nPc])) (mihBody C) s
        (ClassGen.minorTy.ihsGo g x d fvs ws l (recsFrom x i)) (PostIH (ctxH C H) (x.nF - i)) := by
  intro f
  induction f with
  | zero =>
    intro i l H s hf hi hli hp
    have hin : i = x.nF := by omega
    subst hin
    refine specR_prologue (postIH_locals _ _) (mih_none _ _) ?_
    have hlw := nd_lt_iff x.nF x.nF (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mihParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [recsFrom_end]
    simp only [ClassGen.minorTy.ihsGo]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws2 hp2 hws => ?_)
    have hg : ((H2 ++ ws2).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws2).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨[], _, H2.length, rfl,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, by simp,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i l H s hf hi hli hp
    have hin : i < x.nF := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (postIH_locals _ _) (mih_none _ _) ?_
    have hlw := nd_lt_iff i x.nF (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mihParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hik : i < x.kinds.length := by omega
    have hkx := hkb.2 i (by simp; omega)
    simp only [List.getElem_map] at hkx
    refine UD.specR_heapLoadI' (C := ctxH C H) mihK _ (pk + 1 + i) _ (get_prefix hkx hp) (by decide)
      (by simp +decide [sev, Env.get, mihParams, ctxEnv]; exact cellA_mulIdx C pk i (by omega)) ?_
    rw [recsFrom_succ x i hin]
    have hgd : x.kinds.getD i ClassField.ordinary = x.kinds[i] := by simp [List.getD, List.getElem?_eq_getElem hik]
    rw [hgd]
    rcases hko x.kinds[i] (List.getElem_mem hik) with hk | ⟨tele, hk, htele⟩
    · rw [hk] at hkx ⊢
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, cfKindW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [List.nil_append]
      refine specR_congr (m' := ClassGen.minorTy.ihsGo g x d fvs ws l (recsFrom x (i + 1)) >>= fun r => pure r)
        (by simp) ?_
      unfold mihRec
      refine specR_callNIH (C := ctxH C H) ExS.lY fMih mihParams [vv mihKb, .op .add [vv mihI, .const 1], vv mihN, vv mihL,
          vv mihFv, vv mihFn, vv mihWs, vv mihWn, vv mihE0, vv mihNP, vv mihNPc] (mihBody C)
        [cellA C pk, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 x.nF, BitVec.ofNat 64 l, cellA C pf,
          BitVec.ofNat 64 fvs.length, cellA C pw, BitVec.ofNat 64 ws.length, BitVec.ofNat 64 (d + x.nF),
          BitVec.ofNat 64 g.nP, BitVec.ofNat 64 m.nPc] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], trivial⟩
        (PostIH (ctxH C H) (x.nF - (i + 1))) (fun o w _ H' => ∃ ihs ob, o = some ihs ∧ w = cellA C ob ∧
          BlkAt H' ob (ihs.map Enc.idxW) ∧ ihs.length ≤ x.nF - (i + 1))
        (fun o w s' st ⟨ihs, H', ob, h0, hp', hw, hb, hl, hsr⟩ => ⟨H', hp', ⟨ihs, ob, h0, hw, hb, hl⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mihParams _ rfl hlk)
          (ih (i + 1) l H s (by omega) (by omega) (by omega) hp))
        (fun o w s1 H1 hp1 ⟨ihs, ob, ho, hw, hb, hl⟩ => ?_)
      subst ho hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨ihs, H1, ob, rfl, hp1, rfl, hb, by omega,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [hk] at hkx ⊢
    have hkw : cfKindW (.recursive 0 tele) ≠ 0 := by
      simp only [cfKindW]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hkw)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN0 => ?_)
    have hHN0' : H.length ≤ C.HN := hHN0
    have hlay := hok.heapLay
    have hwl : ws.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos ws.length with h0 | hpos
      · omega
      · have h1 := (blkAt_mono hwb hp).2 (ws.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hfl : fvs.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos fvs.length with h0 | hpos
      · omega
      · have h1 := (blkAt_mono hfb hp).2 (fvs.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hlww := nd_lt_iff i ws.length (by omega) (by omega)
    by_cases hiw : i < ws.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mihParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mihParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlww.mpr hiw]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hlwf := nd_lt_iff i fvs.length (by omega) (by omega)
    by_cases hif : i < fvs.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mihParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mihParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwf.mpr hif]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI mihK _ (BitVec.ofNat 64 tele) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp [cfKindW]; exact ofNat_succ_sub_one tele) ?_
    have hwx := hwb.2 i (by simp; omega)
    simp only [List.getElem_map] at hwx
    refine UD.specR_heapLoadI' (C := ctxH C H) mihW _ (pw + 1 + i) _ (get_prefix hwx hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]; exact cellA_mulIdx C pw i (by omega)) ?_
    simp only [List.singleton_append, ClassGen.minorTy.ihsGo, exprGetD, List.getElem?_eq_getElem hiw, pure_bind]
    simp only [ClassGen.ihParts, hcls, List.getElem?_cons_zero, bind_assoc]
    refine specR_callNIH (C := ctxH C H) mihX fOpenFvars ofParams [vv mihK, vv mihW, .op .add [vv mihE0, vv mihL]]
      (ofBody C) [BitVec.ofNat 64 tele, Enc.idxW ws[i], BitVec.ofNat 64 (d + x.nF + l)] (by decide) rfl
      (by decide) hc.ofc ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]; simp only [BitVec.ofNat_add], trivial⟩
      (PostOF (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ xs e', o = some (xs, e') → ∃ ob oa,
        w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (xs.map Enc.idxW))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
        (of_spec ra C hok hc.op tele ws[i] (d + x.nF + l) (by omega) (by omega) H hpC s))
      (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
    have hp1' : H <+: H1 := hp1
    rcases o with _ | ⟨xs, lf⟩
    · have e0 := hn rfl
      subst e0
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨ob, oa, rfl, hob, hlf, hxb⟩ := hsm xs lf rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
    have hol : ob < H1.length := (List.getElem?_eq_some_iff.mp hob).1
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [bind_assoc]
    refine UD.specR_heapLoadI' (C := ctxH C H1) mihXs (vv mihX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) mihLf _ (ob + 1) _ hlf (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ob) ?_
    have hxl : xs.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
      · omega
      · have h1 := hxb.2 (xs.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    refine specR_callNIH (C := ctxH C H1) mihA fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv mihLf] (gaaBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW lf] (by decide) rfl (by decide) hc.gaa
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostA (ctxH C H1)) (fun rr w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rr.map Enc.idxW))
      (fun rr w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H1 lf s1))
      (fun args w s2 H2 hp2 ⟨oar, hw, harb⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    have harl := harb.1
    simp only [List.length_map] at harl
    refine UD.specR_heapLoadI' (C := ctxH C H2) mihAl (vv mihA) oar _ harl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN2 => ?_)
    have hHN2' : H2.length ≤ C.HN := hHN2
    have hargl : args.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos args.length with h0 | hpos
      · omega
      · have h1 := harb.2 (args.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hlwn := nd_lt_iff args.length m.nPc (by omega) (by omega)
    by_cases hnr : m.nPc ≤ args.length
    swap
    · exact specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mihParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwn.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mihParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hlwb := nd_lt_iff args.length (2 ^ 56) (by omega) (by omega)
    by_cases hlb : args.length < 2 ^ 56
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [List.getElem?_eq_getElem hif, pure_bind]
    have hpH2 : H <+: H2 := hp1'.trans hp2'
    have hfx := hfb.2 i (by simp; omega)
    simp only [List.getElem_map] at hfx
    refine UD.specR_heapLoadI' (C := ctxH C H2) mihF _ (pf + 1 + i) _ (get_prefix hfx (hp.trans hpH2)) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]; exact cellA_mulIdx C pf i (by omega)) ?_
    have hxb2 := blkAt_mono hxb hp2'
    have hxsl := hxb2.1
    simp only [List.length_map] at hxsl
    refine UD.specR_heapLoadI' (C := ctxH C H2) mihXl (vv mihXs) oa _ hxsl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    have hlwx := nd_lt_iff xs.length (2 ^ 56) (by omega) (by omega)
    by_cases hxb56 : xs.length < 2 ^ 56
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine ILP.callE_spec (C := ctxH C H2) mihFx ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
      [vv mihF, vv mihXs, .const 0, vv mihXl] ExK.mkaBody
      [Enc.idxW fvs[i], cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc.mka
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
        trivial⟩
      (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H2) (ctxOK_H hok H2) hc.mka hc.app oa xs hxb2
            (by omega) 0 (by omega) fvs[i] s2; simp only [List.drop_zero] at h; exact h)
      (fun fx s3 => ?_)
    simp only [ClassGen.motVar, motiveSlot_zero' g.slots k hsl0, Option.getD_some, ClassGen.slotVar, zeroLevel, bind_assoc,
      Nat.add_zero]
    have hok2 := ctxOK_H hok H2
    refine specR_pinXI (C := ctxH C H2) hok2 pinZeroLevel 1 C.pins.zeroLevel _
      (fun s hp => pinZeroLevel_run (C := ctxH C H2) hok2 hp) (pin_zeroLevel_cell hok2) mihZ (by decide) ?_
    refine ILP.callE_spec (C := ctxH C H2) mihSz fInternSort [lEu] [vv mihZ] sortBody [Enc.idxW C.pins.zeroLevel]
      (by decide) rfl (by decide) hc.srt ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
      (sort_body_spec ra (ctxH C H2) hok2 s3 _) (fun sz s4 => ?_)
    refine ILP.specR_internFVarI ra hok2 hc.fv mihMt (vv mihSz) (vv mihNP) sz g.nP (by omega) (by decide)
      (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]) (fun mt s5 => ?_)
    refine specR_alloc1I hok2 mihEb (.const 0) 0 (by decide) (fun _ => rfl) (fun H3 ws3 hp3 hws3 => ?_)
    have g3 : ((H3 ++ ws3).set H3.length 0)[H3.length]? = some 0 := by simp [List.getElem?_set, hws3]
    have hp3' : H2 <+: _ := (hp3 : H2 <+: H3).trans (img1_prefix H3 ws3 0 hws3)
    have he0 : BlkAt ((H3 ++ ws3).set H3.length 0) H3.length ([] : List (BitVec 64)) :=
      ⟨by simpa using g3, fun i hi => by simp at hi⟩
    refine specR_callPure (C := ctxH C _) mihB1 fCat catParams [vv mihEb, vv mihA, vv mihNPc] catBody
      [cellA C H3.length, cellA C oar, BitVec.ofNat 64 m.nPc] ([] ++ (args.map Enc.idxW).drop m.nPc) (by decide) rfl
      (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], trivial⟩
      (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s5 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
      (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
      (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
        (cat_spec C hok hc.cat (args.map Enc.idxW) oar (by simp; omega) _ m.nPc [] H3.length _ s5 rfl
          (by simp; omega) he0 (blkAt_mono harb hp3')))
      (fun w H4 hp4 ⟨o4, hw4, hb4⟩ => ?_)
    subst hw4
    have hp4' : _ <+: H4 := hp4
    refine specR_alloc2I (ctxOK_H hok H4) mihB2 (.const 1) (vv mihFx) (BitVec.ofNat 64 1) (Enc.idxW fx)
      (by decide) (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H5 ws5 hp5 hws5 => ?_)
    obtain ⟨k0, k1⟩ := img2_get H5 ws5 (BitVec.ofNat 64 1) (Enc.idxW fx) hws5
    have hp5' : H4 <+: _ := (hp5 : H4 <+: H5).trans (img2_prefix H5 ws5 (BitVec.ofNat 64 1) (Enc.idxW fx) hws5)
    have hb5 : BlkAt (((H5 ++ ws5).set H5.length (BitVec.ofNat 64 1)).set (H5.length + 1) (Enc.idxW fx)) H5.length
        [Enc.idxW fx] := ⟨by simpa using k0, fun i hi => by simp at hi; subst hi; simpa using k1⟩
    refine specR_callPure (C := ctxH C _) mihB3 fCat catParams [vv mihB1, vv mihB2, .const 0] catBody
      [cellA C o4, cellA C H5.length, BitVec.ofNat 64 0] (([] ++ (args.map Enc.idxW).drop m.nPc) ++ [Enc.idxW fx].drop 0)
      (by decide) rfl (by decide) hc.cat.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, rfl, trivial⟩
      (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s5 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
      (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
      (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
        (cat_spec C hok hc.cat [Enc.idxW fx] H5.length (by simp) _ 0 _ o4 _ s5 rfl (by simp) (blkAt_mono hb4 hp5')
          hb5))
      (fun w H6 hp6 ⟨o6, hw6, hb6⟩ => ?_)
    subst hw6
    have hp6' : _ <+: H6 := hp6
    have hb6' : BlkAt H6 o6 ((args.drop m.nPc ++ [fx]).map Enc.idxW) := by simpa [List.map_drop] using hb6
    have hl6 := hb6'.1
    simp only [List.length_map] at hl6
    have hp26 : H2 <+: H6 := hp3'.trans (hp4'.trans (hp5'.trans hp6'))
    refine UD.specR_heapLoadI' (C := ctxH C H6) mihB3l (vv mihB3) o6 _ hl6 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine ILP.callE_spec (C := ctxH C H6) mihBd ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
      [vv mihMt, vv mihB3, .const 0, vv mihB3l] ExK.mkaBody
      [Enc.idxW mt, cellA C o6, BitVec.ofNat 64 0, BitVec.ofNat 64 (args.drop m.nPc ++ [fx]).length] (by decide) rfl
      (by decide) hc.mka
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
        trivial⟩
      (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H6) (ctxOK_H hok H6) hc.mka hc.app o6 (args.drop m.nPc ++ [fx]) hb6'
            (by simp; omega) 0 (by omega) mt s5; simp only [List.drop_zero] at h; exact h)
      (fun body s6 => ?_)
    rw [mapM_binder_eq' g xs]
    refine specR_callNIH (C := ctxH C H6) mihBs fFvtDs ftdParams [vv mihXs] (ftdBody C) [cellA C oa] (by decide) rfl
      (by decide) hc.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (PostA (ctxH C H6)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
      (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
        (ftd_spec C hok hc.ftd hc.ftf hc.fvt xs oa (by omega) H6 s6 (blkAt_mono hxb2 hp26)))
      (fun bs w s7 H7 hp7 ⟨o7, hw7, hb7⟩ => ?_)
    subst hw7
    have hp7' : H6 <+: H7 := hp7
    have hpC7 : C.H <+: H7 := hpC.trans (hpH2.trans (hp26.trans hp7'))
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN7 => ?_)
    have hHN7' : H7.length ≤ C.HN := hHN7
    have hbsl0 : bs.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos bs.length with h0 | hpos
      · omega
      · have h1 := hb7.2 (bs.length - 1) (by simp; omega)
        have := (List.getElem?_eq_some_iff.mp h1).1; omega
    have hb7l := hb7.1
    simp only [List.length_map] at hb7l
    refine UD.specR_heapLoadI' (C := ctxH C H7) mihBl (vv mihBs) o7 _ hb7l (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    have hlwbs := nd_lt_iff bs.length (2 ^ 56) (by omega) (by omega)
    by_cases hbsl : bs.length < 2 ^ 56
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun _ => ?_) (fun h => absurd h (by decide))
    unfold closeTelescope
    refine specR_callNIH (C := ctxH C H7) mihIh fCtg ctgParams [.op .add [vv mihE0, vv mihL], .const 0, vv mihBs, .const 0,
        vv mihBd] ctgBody
      [BitVec.ofNat 64 (d + x.nF + l), BitVec.ofNat 64 0, cellA C o7, BitVec.ofNat 64 0, Enc.idxW body] (by decide) rfl
      (by decide) hc.ctg.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]; simp only [BitVec.ofNat_add], rfl,
        by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostK (ctxH C H7)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctgParams _ rfl hlk)
        (by have h := ctg_spec (σ := σ) ra C hok hc.ctg (d + x.nF + l) (by omega) bs o7 (by omega) body bs.length 0 0 H7 s7
              (by omega) (by omega) (by omega) hpC7 hb7; simp only [List.drop_zero] at h; exact h))
      (fun ih1 w s8 H8 hp8 hw => ?_)
    subst hw
    have hp8' : H7 <+: H8 := hp8
    unfold mihRec
    refine specR_callNIH (C := ctxH C H8) ExS.lY fMih mihParams [vv mihKb, .op .add [vv mihI, .const 1], vv mihN,
        .op .add [vv mihL, .const 1], vv mihFv, vv mihFn, vv mihWs, vv mihWn, vv mihE0, vv mihNP, vv mihNPc] (mihBody C)
      [cellA C pk, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 x.nF, BitVec.ofNat 64 (l + 1), cellA C pf,
        BitVec.ofNat 64 fvs.length, cellA C pw, BitVec.ofNat 64 ws.length, BitVec.ofNat 64 (d + x.nF),
        BitVec.ofNat 64 g.nP, BitVec.ofNat 64 m.nPc] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv]; exact word_add1_eq l,
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mihParams, ctxEnv], trivial⟩
      (PostIH (ctxH C H8) (x.nF - (i + 1))) (fun o w _ H' => ∃ ihs ob, o = some ihs ∧ w = cellA C ob ∧
        BlkAt H' ob (ihs.map Enc.idxW) ∧ ihs.length ≤ x.nF - (i + 1))
      (fun o w s' st ⟨ihs, H', ob, h0, hp', hw, hb, hl, hsr⟩ => ⟨H', hp', ⟨ihs, ob, h0, hw, hb, hl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mihParams _ rfl hlk)
        (ih (i + 1) (l + 1) H8 s8 (by omega) (by omega) (by omega) (hp.trans (hpH2.trans (hp26.trans (hp7'.trans hp8'))))))
      (fun o w s9 H9 hp9 ⟨ihs, oy, ho, hw, hry, hl⟩ => ?_)
    subst ho hw
    have hp9' : H8 <+: H9 := hp9
    simp only
    refine ExPre.prepend_spec C hok (H := H9) mihIh (Enc.idxW ih1) oy (ihs.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hry (by decide)
      (by simp +decide [Env.get_cons, Env.get, mihParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨ih1 :: ihs, H', o, rfl, hpH2.trans (hp26.trans (hp7'.trans (hp8'.trans (hp9'.trans hp')))), rfl,
      by simpa using hb, by simp; omega, hsr⟩

end

/-! ## `ClassGen.minorTy`, no inductive hypotheses -/

def mtyCc := ofString "mty_cc"
def mtyD := ofString "mty_d"
def mtyDs := ofString "mty_ds"
def mtyNP := ofString "mty_np"
def mtyLv := ofString "mty_lv"
def mtyNPc := ofString "mty_npc"
def mtyNf := ofString "mty_nf"
def mtyTd := ofString "mty_td"
def mtyTn := ofString "mty_tn"
def mtyCvp := ofString "mty_cvp"
def mtyNm := ofString "mty_nm"
def mtyX := ofString "mty_x"
def mtyFv := ofString "mty_fv"
def mtyRs := ofString "mty_rs"
def mtyLf := ofString "mty_lf"
def mtyW := ofString "mty_w"
def mtyRa := ofString "mty_ra"
def mtyCn0 := ofString "mty_cn0"
def mtyA1 := ofString "mty_a1"
def mtyL1 := ofString "mty_l1"
def mtyCapp := ofString "mty_capp"
def mtyZ := ofString "mty_z"
def mtySz := ofString "mty_sz"
def mtyMv := ofString "mty_mv"
def mtyE0 := ofString "mty_e0"
def mtyA2 := ofString "mty_a2"
def mtyB1 := ofString "mty_b1"
def mtyA3 := ofString "mty_a3"
def mtyL3 := ofString "mty_l3"
def mtyCn := ofString "mty_cn"
def mtyFb := ofString "mty_fb"
def mtyR := ofString "mty_r"
def mtyLa := ofString "mty_la"
def mtyLb := ofString "mty_lb"
def mtyKb := ofString "mty_kb"
def mtyWl := ofString "mty_wl"
def mtyIh := ofString "mty_ih"
def mtyCt := ofString "mty_ct"
def fMty := ofString "minorTy"

def mtyParams : List MlS := [mtyCc, mtyD, mtyDs, mtyNP, mtyLv, mtyNPc]
def mtyLocals : List MlS := [mtyNf, mtyTd, mtyTn, mtyCvp, mtyNm, mtyX, mtyFv, mtyRs, mtyLf, mtyW, mtyRa, mtyCn0, mtyA1, mtyL1, mtyCapp, mtyZ, mtySz, mtyMv, mtyE0, mtyA2, mtyB1, mtyA3, mtyL3, mtyCn, mtyFb, mtyR, mtyLa, mtyLb, mtyKb, mtyWl, mtyIh, mtyCt]

def mtyBody (C : Ctx) : ProgHOL 64 := prologue mtyLocals
  (.seq (.assign .local mtyNf (.load .one (.op .add [vv mtyCc, .const 8])))
  (.seq (.assign .local mtyTd (.load .one (.op .add [vv mtyCc, .const 16])))
  (.seq (.assign .local mtyTn (.load .one (.op .add [vv mtyCc, .const 24])))
  (.seq (.assign .local mtyCvp (.load .one (vv mtyCc)))
  (.seq (.assign .local mtyNm (.load .one (vv mtyCvp)))
  (.seq (.call (some (some (.local, mtyX), none)) fOpenFvars [vv mtyNf, vv mtyTd, vv mtyD])
  (.ite (.cmp .equal (vv mtyX) (.const 0))
  hang
  (.seq (.assign .local mtyFv (.load .one (vv mtyX)))
  (.seq (.assign .local mtyRs (.load .one (.op .add [vv mtyX, .const 8])))
  (.seq (.assign .local mtyLf (.load .one (vv mtyFv)))
  (.ite (.cmp .equal (vv mtyLf) (vv mtyNf))
  (.seq (.call (some (some (.local, mtyW), none)) fTpw [vv mtyFv, .const 0, vv mtyLf, vv mtyTn])
  (.seq (.assign .local mtyKb (.load .one (.op .add [vv mtyCc, .const 40])))
  (.seq (.assign .local mtyWl (.load .one (vv mtyW)))
  (.seq (.call (some (some (.local, mtyIh), none)) fMih [vv mtyKb, .const 0, vv mtyNf, .const 0, vv mtyFv, vv mtyLf,
      vv mtyW, vv mtyWl, .op .add [vv mtyD, vv mtyNf], vv mtyNP, vv mtyNPc])
  (.seq (.call (some (some (.local, mtyRa), none)) fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), vv mtyRs])
  (.seq (.assign .local mtyLa (.load .one (vv mtyRa)))
  (.ite (.cmp .lower (vv mtyLa) (vv mtyNPc))
  hang
  (.ite (.cmp .lower (vv mtyLa) (.const (BitVec.ofNat 64 (2 ^ 56))))
  (.seq (.call (some (some (.local, mtyCn0), none)) fInternConst [vv mtyNm, vv mtyLv])
  (.seq (.call (some (some (.local, mtyA1), none)) fCat [vv mtyDs, vv mtyFv, .const 0])
  (.seq (.assign .local mtyL1 (.load .one (vv mtyA1)))
  (.seq (.call (some (some (.local, mtyCapp), none)) ExK.fMka [vv mtyCn0, vv mtyA1, .const 0, vv mtyL1])
  (.seq (.assign .local mtyZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, mtySz), none)) fInternSort [vv mtyZ])
  (.seq (.call (some (some (.local, mtyMv), none)) fInternFVar [vv mtySz, vv mtyNP])
  (alloc1 C mtyE0 (.const 0)
  (.seq (.call (some (some (.local, mtyA2), none)) fCat [vv mtyE0, vv mtyRa, vv mtyNPc])
  (alloc2 C mtyB1 (.const 1) (vv mtyCapp)
  (.seq (.call (some (some (.local, mtyA3), none)) fCat [vv mtyA2, vv mtyB1, .const 0])
  (.seq (.assign .local mtyL3 (.load .one (vv mtyA3)))
  (.seq (.call (some (some (.local, mtyCn), none)) ExK.fMka [vv mtyMv, vv mtyA3, .const 0, vv mtyL3])
  (.seq (.call (some (some (.local, mtyFb), none)) fFvtDs [vv mtyFv])
  (.seq (.assign .local mtyLb (.load .one (vv mtyFb)))
  (.ite (.cmp .equal (vv mtyLb) (vv mtyNf))
  (.seq (.call (some (some (.local, mtyCt), none)) fCat [vv mtyFb, vv mtyIh, .const 0])
  (.seq (.call (some (some (.local, mtyR), none)) fCtg [vv mtyD, .const 0, vv mtyCt, .const 0, vv mtyCn])
  (.return (vv mtyR))))
  hang))))))))))))))))
  hang))))))))
  hang)))))))))))

structure MTYCodes (C : Ctx) : Prop where
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  tpw : TPWCodes C
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  cat : CatCodes C
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  ftd : C.code.lookup fFvtDs = some (ftdParams.map (fun p => (p, ShapeHOL.one)), ftdBody C, .one)
  ftf : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  ctg : CTGCodes C
  mih : MIHCodes C
  self : C.code.lookup fMty = some (mtyParams.map (fun p => (p, ShapeHOL.one)), mtyBody C, .one)

section
variable {σ : Type}

theorem mty_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mtyLocals → (ctxEnv C ++ mtyParams.zip vals).get x = none :=
  Knot.params_none C mtyLocals mtyParams vals (by decide) (by decide)

theorem motiveSlot_zero (sls : List ClassSlot) (k : ClassKey) (h : sls[0]? = some (.motive k)) :
    ClassRead.motiveSlot sls 0 = some 0 := by
  unfold ClassRead.motiveSlot
  cases sls with
  | nil => simp at h
  | cons a l =>
    simp at h; subst h
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
    simp


theorem mapM_binder_eq (g : ClassGen) : ∀ l : List EIdx, l.mapM g.binder = fvarTypeDs l
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, fvarTypeDs, mapM_binder_eq g l]; rfl

theorem ihs_recs_nil (x : ClassCtor) (hko : ∀ k ∈ x.kinds, k = .ordinary) :
    (List.range x.nF).filterMap (fun i => match x.kinds.getD i ClassField.ordinary with
      | ClassField.recursive t tele => some (i, t, tele)
      | ClassField.ordinary => none) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro i _
  have : x.kinds.getD i .ordinary = .ordinary := by
    rcases h : x.kinds[i]? with _ | k
    · simp [List.getD, h]
    · simp [List.getD, h]; exact hko k (List.mem_of_getElem? h)
  rw [this]

set_option maxHeartbeats 16000000 in
/-- **`ClassGen.minorTy 0 x d`** for a constructor of the one class (recursive fields at class `0`). -/
theorem mty_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : MTYCodes C)
    (g : ClassGen) (m : TargetMajor) (hcls : g.cls = [m]) (k : ClassKey) (hsl0 : g.slots[0]? = some (.motive k))
    (x : ClassCtor) (oc : Nat) (hcc : CCRep C C.H oc x) (hnf : x.nF < 2 ^ 56) (d : Nat) (hd : d + x.nF < 2 ^ 61)
    (pd : Nat) (hds : BlkAt C.H pd (m.ds.map Enc.idxW)) (hdl : m.ds.length < 2 ^ 56) (hnP : g.nP < 2 ^ 62)
    (hnpc : m.nPc < 2 ^ 62) (s : AState) :
    SpecR (σ := σ) (Pre C s (mtyParams.zip [cellA C oc, BitVec.ofNat 64 d, cellA C pd, BitVec.ofNat 64 g.nP,
        Enc.idxW m.lvls, BitVec.ofNat 64 m.nPc])) (mtyBody C) s (g.minorTy 0 x d) (PostSomeH C) := by
  refine specR_prologue (postSomeH_locals _) (mty_none _ _) ?_
  obtain ⟨⟨ocv, hocv, hcv⟩, hnfw, htd, htn, -, ⟨okb, hokb, hkb⟩, hko, hkl⟩ := hcc
  unfold ClassGen.minorTy
  simp only [hcls, targetMajorAt, List.getElem?_cons_zero, pure_bind]
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mtyNf _ (oc + 1) _ hnfw (by decide) (by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv]; exact cellA_add8 C oc) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mtyTd _ (oc + 2) _ htd (by decide) (by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mtyTn _ (oc + 3) _ htn (by decide) (by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv]; exact cellA_add_ofNat C oc 3) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mtyCvp _ oc _ hocv (by decide) (by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) mtyNm (vv mtyCvp) ocv _ hcv.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_callNIH (C := ctxH C C.H) mtyX fOpenFvars ofParams [vv mtyNf, vv mtyTd, vv mtyD]
    (ofBody C) [BitVec.ofNat 64 x.nF, Enc.idxW x.tyD, BitVec.ofNat 64 d] (by decide) rfl
    (by decide) hc.ofc ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv], trivial⟩
    (PostOF (ctxH C C.H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op x.nF x.tyD d (by omega) (by omega) C.H hp0 s))
    (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
  have hp1' : C.H <+: H1 := hp1
  rcases o with _ | ⟨fvs, res⟩
  · have e0 := hn rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, oa, rfl, hob, hres, hfb⟩ := hsm fvs res rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol : ob < H1.length := (List.getElem?_eq_some_iff.mp hob).1
  have hHN' : H1.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H1) mtyFv (vv mtyX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) mtyRs _ (ob + 1) _ hres (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ob) ?_
  have hfl : H1[oa]? = some (BitVec.ofNat 64 fvs.length) := by simpa using hfb.1
  refine UD.specR_heapLoadI' (C := ctxH C H1) mtyLf (vv mtyFv) oa _ hfl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfvl0 : fvs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos fvs.length with h0 | hpos
    · omega
    · have h1 := hfb.2 (fvs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hfn : fvs.length = x.nF
  swap
  · have hne2 : BitVec.ofNat 64 fvs.length ≠ BitVec.ofNat 64 x.nF := fun e => hfn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfn]) (fun _ => ?_) (fun h => absurd h (by decide))
  have hfvl : fvs.length < 2 ^ 56 := by omega
  refine specR_callNIH (C := ctxH C H1) mtyW fTpw tpwParams [vv mtyFv, .const 0, vv mtyLf, vv mtyTn] (tpwBody C)
    [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, Enc.idxW x.tyN] (by decide) rfl (by decide) hc.tpw.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv], trivial⟩
    (PostSL (ctxH C H1)) (fun o w _ H' => ∃ ds ow, o = some ds ∧ w = cellA C ow ∧ BlkAt H' ow (ds.map Enc.idxW))
    (fun o w s' st ⟨ds, H', ow, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, ow, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tpwParams _ rfl hlk)
      (by have h := tpw_spec (σ := σ) ra C hok hc.tpw fvs oa H1 hp1' hfb fvs.length 0 H1 s1 x.tyN (by omega) (by omega)
            (List.prefix_refl _); simp only [List.drop_zero] at h; exact h))
    (fun o w s2 H2 hp2 ⟨ws, ow, ho, hw, hwb⟩ => ?_)
  subst ho hw
  have hp2' : H1 <+: H2 := hp2
  simp only
  rw [recsFrom_zero_of x]
  swap
  · intro j; rfl
  have hpC2' : C.H <+: H2 := hp1'.trans hp2'
  refine UD.specR_heapLoadI' (C := ctxH C H2) mtyKb _ (oc + 5) _ (get_prefix hokb hpC2') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv]; exact cellA_add_ofNat C oc 5) ?_
  have hwl0 := hwb.1
  simp only [List.length_map] at hwl0
  refine UD.specR_heapLoadI' (C := ctxH C H2) mtyWl (vv mtyW) ow _ hwl0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_callNIH (C := ctxH C H2) mtyIh fMih mihParams [vv mtyKb, .const 0, vv mtyNf, .const 0, vv mtyFv, vv mtyLf,
      vv mtyW, vv mtyWl, .op .add [vv mtyD, vv mtyNf], vv mtyNP, vv mtyNPc] (mihBody C)
    [cellA C okb, BitVec.ofNat 64 0, BitVec.ofNat 64 x.nF, BitVec.ofNat 64 0, cellA C oa, BitVec.ofNat 64 fvs.length,
      cellA C ow, BitVec.ofNat 64 ws.length, BitVec.ofNat 64 (d + x.nF), BitVec.ofNat 64 g.nP, BitVec.ofNat 64 m.nPc]
    (by decide) rfl (by decide) hc.mih.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], rfl,
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv]; rw [BitVec.ofNat_add],
      by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv],
      trivial⟩
    (PostIH (ctxH C H2) (x.nF - 0)) (fun o w _ H' => ∃ ihs ob, o = some ihs ∧ w = cellA C ob ∧
      BlkAt H' ob (ihs.map Enc.idxW) ∧ ihs.length ≤ x.nF - 0)
    (fun o w s' st ⟨ihs, H', ob, h0, hp', hw, hb, hl, hsr⟩ => ⟨H', hp', ⟨ihs, ob, h0, hw, hb, hl⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mihParams _ rfl hlk)
      (mih_spec ra C hok hc.mih g m hcls k hsl0 x d fvs ws okb oa ow hko hkl hnf hd (by omega) hnpc H2 hpC2'
        (blkAt_mono hkb hpC2') (blkAt_mono hfb hp2') hwb x.nF 0 0 H2 s2 (by omega) (by omega) (by omega)
        (List.prefix_refl _)))
    (fun o w s2 H2 hp2x ⟨ihs, oih, ho, hw, hihb, hihl⟩ => ?_)
  subst ho hw
  simp only
  have hp2' : H1 <+: H2 := hp2'.trans hp2x
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  refine specR_callNIH (C := ctxH C H2) mtyRa fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv mtyRs] (gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW res] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H2)) (fun rr w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rr.map Enc.idxW))
    (fun rr w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H2 res s2))
    (fun rargs w s3 H3 hp3 ⟨ora, hw, hrab⟩ => ?_)
  subst hw
  have hp3' : H2 <+: H3 := hp3
  have hpC3 : C.H <+: H3 := hpC2.trans hp3'
  have hral := hrab.1
  simp only [List.length_map] at hral
  refine UD.specR_heapLoadI' (C := ctxH C H3) mtyLa (vv mtyRa) ora _ hral (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN3 => ?_)
  have hHN3' : H3.length ≤ C.HN := hHN3
  have hral' : rargs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos rargs.length with h0 | hpos
    · omega
    · have h1 := hrab.2 (rargs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  have hlwn := nd_lt_iff rargs.length m.nPc (by omega) (by omega)
  by_cases hnr : m.nPc ≤ rargs.length
  swap
  · exact specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mtyParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        hlwn.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, mtyParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hlwb := nd_lt_iff rargs.length (2 ^ 56) (by omega) (by omega)
  by_cases hlb : rargs.length < 2 ^ 56
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine ILP.callE_spec (C := ctxH C H3) mtyCn0 fInternConst [lEn, lEus] [vv mtyNm, vv mtyLv] constBody
    [Enc.idxW x.cv.name, Enc.idxW m.lvls] (by decide) rfl (by decide) hc.ic
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv], trivial⟩
    (const_body_spec ra (ctxH C H3) (ctxOK_H hok H3) s3 _ _) (fun cc s4 => ?_)
  refine specR_callPure (C := ctxH C H3) mtyA1 fCat catParams [vv mtyDs, vv mtyFv, .const 0] catBody
    [cellA C pd, cellA C oa, BitVec.ofNat 64 0] (m.ds.map Enc.idxW ++ (fvs.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H3 <+: H' ∧ s' = s4 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (fvs.map Enc.idxW) oa (by simp; omega) _ 0 _ pd H3 s4 rfl (by omega)
        (blkAt_mono hds hpC3) (blkAt_mono hfb (hp2'.trans hp3'))))
    (fun w H4 hp4 ⟨o4, hw4, hb4⟩ => ?_)
  subst hw4
  have hp4' : H3 <+: H4 := hp4
  have hb4' : BlkAt H4 o4 ((m.ds ++ fvs).map Enc.idxW) := by simpa using hb4
  have hl4 := hb4'.1
  simp only [List.length_map] at hl4
  refine UD.specR_heapLoadI' (C := ctxH C H4) mtyL1 (vv mtyA1) o4 _ hl4 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine ILP.callE_spec (C := ctxH C H4) mtyCapp ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv mtyCn0, vv mtyA1, .const 0, vv mtyL1] ExK.mkaBody
    [Enc.idxW cc, cellA C o4, BitVec.ofNat 64 0, BitVec.ofNat 64 (m.ds ++ fvs).length] (by decide) rfl (by decide) hc.mka
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
      trivial⟩
    (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H4) (ctxOK_H hok H4) hc.mka hc.app o4 (m.ds ++ fvs) hb4'
          (by simp; omega) 0 (by omega) cc s4; simp only [List.drop_zero] at h; exact h)
    (fun capp s5 => ?_)
  simp only [ClassGen.motVar, motiveSlot_zero g.slots k hsl0, Option.getD_some, ClassGen.slotVar, zeroLevel, bind_assoc,
    Nat.add_zero]
  have hok4 := ctxOK_H hok H4
  refine specR_pinXI (C := ctxH C H4) hok4 pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H4) hok4 hp) (pin_zeroLevel_cell hok4) mtyZ (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H4) mtySz fInternSort [lEu] [vv mtyZ] sortBody [Enc.idxW C.pins.zeroLevel]
    (by decide) rfl (by decide) hc.srt ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
    (sort_body_spec ra (ctxH C H4) hok4 s5 _) (fun sz s6 => ?_)
  refine ILP.specR_internFVarI ra hok4 hc.fv mtyMv (vv mtySz) (vv mtyNP) sz g.nP (by omega) (by decide)
    (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv]) (fun mv s7 => ?_)
  refine specR_alloc1I hok4 mtyE0 (.const 0) 0 (by decide) (fun _ => rfl) (fun H5 ws5 hp5 hws5 => ?_)
  have g5 : ((H5 ++ ws5).set H5.length 0)[H5.length]? = some 0 := by simp [List.getElem?_set, hws5]
  have hp5' : H4 <+: _ := (hp5 : H4 <+: H5).trans (img1_prefix H5 ws5 0 hws5)
  have he0 : BlkAt ((H5 ++ ws5).set H5.length 0) H5.length ([] : List (BitVec 64)) :=
    ⟨by simpa using g5, fun i hi => by simp at hi⟩
  have h35 : H3 <+: ((H5 ++ ws5).set H5.length 0) := hp4'.trans hp5'
  refine specR_callPure (C := ctxH C _) mtyA2 fCat catParams [vv mtyE0, vv mtyRa, vv mtyNPc] catBody
    [cellA C H5.length, cellA C ora, BitVec.ofNat 64 m.nPc] ([] ++ (rargs.map Enc.idxW).drop m.nPc) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv], trivial⟩
    (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s7 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (rargs.map Enc.idxW) ora (by simp; omega) _ m.nPc [] H5.length _ s7 rfl
        (by simp; omega) he0 (blkAt_mono hrab h35)))
    (fun w H6 hp6 ⟨o6, hw6, hb6⟩ => ?_)
  subst hw6
  have hp6' : _ <+: H6 := hp6
  refine specR_alloc2I (ctxOK_H hok H6) mtyB1 (.const 1) (vv mtyCapp) (BitVec.ofNat 64 1) (Enc.idxW capp)
    (by decide) (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H7 ws7 hp7 hws7 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H7 ws7 (BitVec.ofNat 64 1) (Enc.idxW capp) hws7
  have hp7' : H6 <+: _ := (hp7 : H6 <+: H7).trans (img2_prefix H7 ws7 (BitVec.ofNat 64 1) (Enc.idxW capp) hws7)
  have hb7 : BlkAt (((H7 ++ ws7).set H7.length (BitVec.ofNat 64 1)).set (H7.length + 1) (Enc.idxW capp)) H7.length
      [Enc.idxW capp] := ⟨by simpa using k0, fun i hi => by simp at hi; subst hi; simpa using k1⟩
  refine specR_callPure (C := ctxH C _) mtyA3 fCat catParams [vv mtyA2, vv mtyB1, .const 0] catBody
    [cellA C o6, cellA C H7.length, BitVec.ofNat 64 0] (([] ++ (rargs.map Enc.idxW).drop m.nPc) ++ [Enc.idxW capp].drop 0)
    (by decide) rfl (by decide) hc.cat.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, rfl, trivial⟩
    (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s7 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat [Enc.idxW capp] H7.length (by simp) _ 0 _ o6 _ s7 rfl (by simp) (blkAt_mono hb6 hp7')
        hb7))
    (fun w H8 hp8 ⟨o8, hw8, hb8⟩ => ?_)
  subst hw8
  have hp8' : _ <+: H8 := hp8
  have hb8' : BlkAt H8 o8 ((rargs.drop m.nPc ++ [capp]).map Enc.idxW) := by simpa [List.map_drop] using hb8
  have hl8 := hb8'.1
  simp only [List.length_map] at hl8
  have hpC8 : C.H <+: H8 := hpC3.trans (hp4'.trans (hp5'.trans (hp6'.trans (hp7'.trans hp8'))))
  refine UD.specR_heapLoadI' (C := ctxH C H8) mtyL3 (vv mtyA3) o8 _ hl8 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine ILP.callE_spec (C := ctxH C H8) mtyCn ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv mtyMv, vv mtyA3, .const 0, vv mtyL3] ExK.mkaBody
    [Enc.idxW mv, cellA C o8, BitVec.ofNat 64 0, BitVec.ofNat 64 (rargs.drop m.nPc ++ [capp]).length] (by decide) rfl
    (by decide) hc.mka
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
      trivial⟩
    (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H8) (ctxOK_H hok H8) hc.mka hc.app o8 (rargs.drop m.nPc ++ [capp]) hb8'
          (by simp; omega) 0 (by omega) mv s7; simp only [List.drop_zero] at h; exact h)
    (fun concl s8 => ?_)
  rw [mapM_binder_eq g fvs]
  refine specR_callNIH (C := ctxH C H8) mtyFb fFvtDs ftdParams [vv mtyFv] (ftdBody C) [cellA C oa] (by decide) rfl
    (by decide) hc.ftd ⟨by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H8)) (fun bs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (bs.map Enc.idxW))
    (fun bs w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftdParams _ rfl hlk)
      (ftd_spec C hok hc.ftd hc.ftf hc.fvt fvs oa (by omega) H8 s8 (blkAt_mono hfb (hp2'.trans (hp3'.trans (hp4'.trans
        (hp5'.trans (hp6'.trans (hp7'.trans hp8')))))))))
    (fun fbs w s9 H9 hp9 ⟨o9, hw9, hb9⟩ => ?_)
  subst hw9
  have hp9' : H8 <+: H9 := hp9
  have hb9l := hb9.1
  simp only [List.length_map] at hb9l
  refine UD.specR_heapLoadI' (C := ctxH C H9) mtyLb (vv mtyFb) o9 _ hb9l (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN9 => ?_)
  have hHN9' : H9.length ≤ C.HN := hHN9
  have hfbl0 : fbs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos fbs.length with h0 | hpos
    · omega
    · have h1 := hb9.2 (fbs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hfbn : fbs.length = x.nF
  swap
  · have hne3 : BitVec.ofNat 64 fbs.length ≠ BitVec.ofNat 64 x.nF := fun e => hfbn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne3) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfbn]) (fun _ => ?_) (fun h => absurd h (by decide))
  have hihb9 : BlkAt H9 oih (ihs.map Enc.idxW) := blkAt_mono hihb (hp3'.trans (hp4'.trans (hp5'.trans (hp6'.trans
    (hp7'.trans (hp8'.trans hp9'))))))
  refine specR_callPure (C := ctxH C H9) mtyCt fCat catParams [vv mtyFb, vv mtyIh, .const 0] catBody
    [cellA C o9, cellA C oih, BitVec.ofNat 64 0] (fbs.map Enc.idxW ++ (ihs.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H9 <+: H' ∧ s' = s9 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (ihs.map Enc.idxW) oih (by simp; omega) _ 0 _ o9 H9 s9 rfl (by omega) hb9 hihb9))
    (fun w H10 hp10 ⟨o10, hw10, hb10⟩ => ?_)
  subst hw10
  have hp10' : H9 <+: H10 := hp10
  have hb10' : BlkAt H10 o10 ((fbs ++ ihs).map Enc.idxW) := by simpa using hb10
  unfold closeTelescope
  refine specR_callNIH (C := ctxH C H10) mtyR fCtg ctgParams [vv mtyD, .const 0, vv mtyCt, .const 0, vv mtyCn] ctgBody
    [BitVec.ofNat 64 d, BitVec.ofNat 64 0, cellA C o10, BitVec.ofNat 64 0, Enc.idxW concl] (by decide) rfl (by decide)
    hc.ctg.self ⟨by simp +decide [sev, Env.get_cons, Env.get, mtyParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostK (ctxH C H10)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctgParams _ rfl hlk)
      (by have h := ctg_spec (σ := σ) ra C hok hc.ctg d (by omega) (fbs ++ ihs) o10 (by simp; omega) concl
            (fbs ++ ihs).length 0 0 H10 s9 (by omega) (by omega) (by simp; omega) ((hpC8.trans hp9').trans hp10') hb10'
          simp only [List.drop_zero] at h; exact h))
    (fun r w s10 H11 hp11 hw => ?_)
  subst hw
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H11, r, ((hpC8.trans hp9').trans hp10').trans hp11,
    rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
