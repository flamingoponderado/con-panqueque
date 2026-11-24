import ConPanqueque.T.Decl.Install
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The literal flags after an install

The pushed environment's flags are its lookups' (con-ron's `FlagsOK.push`), and the base's literal names are the
pinned literal handles, so the port recomputes them after every install by looking the pinned names up and
writes the literal word `gLit`.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The environment with other literal flags (same lookups). -/
def ctxFe (C : Ctx) (fe : IFEnv) : Ctx := { C with fe := fe }

theorem envDen_congr {fe fe' : IFEnv} {p : Pins} {st : EStore} (hf : ∀ n, fe'.find? n = fe.find? n)
    (ht : ∀ n, fe'.findTable? n = fe.findTable? n) (h : EnvDen fe p st) : EnvDen fe' p st := by
  obtain ⟨hc, htb, hp, hr⟩ := h
  exact ⟨fun c ci hci => hc c ci (by rw [← hf]; exact hci), fun T tbl h' => htb T tbl (by rw [← ht]; exact h'), hp,
    fun c cv mI rP isK rules hci => hr c cv mI rP isK rules (by rw [← hf]; exact hci)⟩

theorem envRel_fe {C : Ctx} (h : EnvRel C) {fe : IFEnv} (hf : ∀ n, fe.find? n = C.fe.find? n)
    (ht : ∀ n, fe.findTable? n = C.fe.findTable? n) : EnvRel (ctxFe C fe) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · show match fe.find? n with
      | none => C.envM[n]? = none
      | some ci => ∃ o, C.envM[n]? = some (ecell C o) ∧ CIE C.EB C.EH o ci
    rw [hf]; exact h.1 n
  · show match fe.findTable? n with
      | none => C.tblM[n]? = none
      | some tb => ∃ o, C.tblM[n]? = some (ecell C o) ∧ TblE C.EB C.EH o tb
    rw [ht]; exact h.2 n

theorem ctxOK_fe {C : Ctx} (hok : CtxOK C) {fe : IFEnv} (hf : ∀ n, fe.find? n = C.fe.find? n)
    (ht : ∀ n, fe.findTable? n = C.fe.findTable? n) : CtxOK (ctxFe C fe) := by
  have h1 := envRel_fe hok.envRel hf ht
  have h2 : PinsE (ctxFe C fe) := hok.pinsRel
  cases hok; constructor <;> first | assumption | exact h1 | exact h2

section
variable {σ : Type}

/-- `gLit := e`: the context's environment takes the flags `e` encodes (same lookups). -/
theorem specR_setLitI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {fe : IFEnv}
    (hf : ∀ n, fe.find? n = C.fe.find? n) (ht : ∀ n, fe.findTable? n = C.fe.findTable? n)
    (e : ExpHOL 64) (he : sev Γ e = some (litW fe))
    (h : SpecR (Inv (ctxFe C fe) s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .global gLit e) rest) s m R := by
  intro t ht0
  obtain ⟨hH, hm1, hm2, hl⟩ := ht0.sr.env
  rw [seq_normal _ (assign_ok t .global gLit e (.val (.word (litW fe))) (inv_ev ht0 he)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hl, shapeOfHOLExact, shapeEqHOL]))]
  let t2 := setKvarHOLFinite .global gLit (.val (.word (litW fe))) t
  have hgl : ∀ y, y ≠ gLit → t2.globals.lookup y = t.globals.lookup y := fun y hy => by
    simp [t2, setKvarHOLFinite, setGlobalHOLFinite, FUPDATE, Ne.symm hy]
  have hsr := ht0.sr
  refine h t2 ⟨⟨srep_frame hsr.rep ⟨rfl, rfl, rfl, rfl⟩ rfl (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩),
      by rw [hgl _ (by decide)]; exact hsr.gdir, by rw [hgl _ (by decide)]; exact hsr.gfln,
      by rw [hgl _ (by decide)]; exact hsr.gfll, by rw [hgl _ (by decide)]; exact hsr.gfls,
      by rw [hgl _ (by decide)]; exact hsr.gfle, by rw [hgl _ (by decide)]; exact hsr.gkb, hsr.code,
      hsr.kbuf, fun k => memoAt_of_eq (hsr.memo k) rfl rfl, fun k => memoAtN_frame (hsr.memoN k) (fun _ _ => rfl)
        (fun _ _ => rfl) rfl, fun k => cacheAt_frame (hsr.cache k) (fun _ _ => rfl) (fun _ _ => rfl) rfl,
      modeAt_frame hsr.mode (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl (hgl _ (by decide)),
      ⟨⟨by rw [hgl _ (by decide)]; exact hH.top, hH.len, hH.lay, hH.dom, hH.val, hH.words⟩,
        memoAtG_frame hm1 (fun _ _ => rfl) (fun _ _ => rfl) rfl, memoAtG_frame hm2 (fun _ _ => rfl) (fun _ _ => rfl) rfl,
        by simp [t2, setKvarHOLFinite, setGlobalHOLFinite, FUPDATE]; rfl⟩, hsr.pins,
      heapEx_frame hsr.heap (fun _ _ => rfl) rfl (hgl _ (by decide)), hsr.twf, envDen_congr hf ht hsr.envd, hsr.floor,
      hsr.cok⟩, ht0.env, ht0.mem, ht0.decl⟩

end


def fNatF := ofString "natLitFound"
def fStrF := ofString "strLitFound"
def flA := ofString "fl_a"
def flB := ofString "fl_b"
def fFlags := ofString "litFlags"

def natFBody (C : Ctx) : ProgHOL 64 := prologue [crX, crY] (crPins C natPins)
def strFBody (C : Ctx) : ProgHOL 64 := prologue [crX, crY] (crPins C strPins)

/-- Recompute the literal word from the pinned literal names' lookups. -/
def flBody : ProgHOL 64 := prologue [flA, flB]
  (.seq (.call (some (some (.local, flA), none)) fNatF [])
  (.seq (.call (some (some (.local, flB), none)) fStrF [])
  (.seq (.assign .global gLit (.op .add [vv flA, .op .add [vv flB, vv flB]]))
  (.return (.const 0)))))

/-- The base's literal names are the pinned literal handles. -/
def LitsPinned (fe : IFEnv) (p : Pins) : Prop := fe.base.lits = strPins.map (fun i => p.names[i]!)

theorem natLitStoredBy_pins {fe : IFEnv} {p : Pins} (hL : LitsPinned fe p) :
    fe.natLitStoredBy = natPins.all (fun i => (fe.find? p.names[i]!).isSome) := by
  unfold IFEnv.natLitStoredBy NAT_LIT_COUNT
  rw [IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl), IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl), IFEnv.litsStored_self]
  simp [natPins, Bool.and_assoc]

theorem strLitStoredBy_pins {fe : IFEnv} {p : Pins} (hL : LitsPinned fe p) :
    fe.strLitStoredBy = strPins.all (fun i => (fe.find? p.names[i]!).isSome) := by
  unfold IFEnv.strLitStoredBy
  rw [natLitStoredBy_pins hL]
  unfold STR_LIT_COUNT NAT_LIT_COUNT
  rw [IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl), IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl), IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl), IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl),
    IFEnv.litsStored_step fe (by decide) (by rw [hL]; rfl), IFEnv.litsStored_self]
  simp [natPins, strPins, Bool.and_assoc]

section
variable {σ : Type}

theorem natF_spec (C : Ctx) (hok : CtxOK C)
    (hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)) (s : AState) :
    SpecR (σ := σ) (Pre C s (([] : List MlS).zip ([] : List (BitVec 64)))) (natFBody C) s (pure (pinsFound C natPins)) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [crX, crY] [] [] (by decide) (by decide)) ?_
  exact specR_crPinsI hok hg hp ⟨by decide, by decide⟩ natPins _ (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl)

theorem strF_spec (C : Ctx) (hok : CtxOK C)
    (hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)) (s : AState) :
    SpecR (σ := σ) (Pre C s (([] : List MlS).zip ([] : List (BitVec 64)))) (strFBody C) s (pure (pinsFound C strPins)) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [crX, crY] [] [] (by decide) (by decide)) ?_
  exact specR_crPinsI hok hg hp ⟨by decide, by decide⟩ strPins _ (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl)


/-- After the flags: the heap may have grown, the environment is `fe` (same lookups as before). -/
def PostFl (C : Ctx) (fe : IFEnv) (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxFe (ctxH C H') fe) s' st

theorem postFl_locals (C : Ctx) (fe : IFEnv) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostFl C fe a w s' st → PostFl C fe a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, h⟩ => ⟨H', hp, sr_of_eq h rfl rfl rfl rfl⟩

theorem litW_found (a b : Bool) {fe : IFEnv} (hn : fe.natLit = a) (hs : fe.strLit = b) :
    boolW a + (boolW b + boolW b) = litW fe := by
  unfold litW; rw [hn, hs]; cases a <;> cases b <;> decide

/-- **The flags**: from a context whose environment answers as `fe`, `fe`'s flags being the lookups'. -/
theorem fl_spec (C : Ctx) (hok : CtxOK C)
    (hcN : C.code.lookup fNatF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), natFBody C, .one))
    (hcS : C.code.lookup fStrF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), strFBody C, .one))
    (hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)) (s : AState)
    {fe : IFEnv} (hf : ∀ n, fe.find? n = C.fe.find? n) (ht : ∀ n, fe.findTable? n = C.fe.findTable? n)
    (hn : fe.natLit = pinsFound C natPins) (hs : fe.strLit = pinsFound C strPins) :
    SpecR (σ := σ) (Pre C s (([] : List MlS).zip ([] : List (BitVec 64)))) flBody s (pure ()) (PostFl C fe) := by
  refine specR_prologue (postFl_locals C fe) (Knot.params_none C [flA, flB] [] [] (by decide) (by decide)) ?_
  refine specR_callPure (C := C) flA fNatF [] [] (natFBody C) [] (pinsFound C natPins) (by decide) rfl (by decide) hcN
    trivial (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk) (natF_spec C hok hg hp s))
    (fun w H1 hp1 hw => ?_)
  subst hw
  have hok1 := ctxOK_H hok H1
  refine specR_callPure (C := ctxH C H1) flB fStrF [] [] (strFBody C) [] (pinsFound C strPins) (by decide) rfl
    (by decide) hcS trivial (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk) (strF_spec (ctxH C H1) hok1 hg hp s))
    (fun w H2 hp2 hw => ?_)
  subst hw
  refine specR_setLitI (C := ctxH C H2) hf ht _ (by simp +decide [sev, Env.get]; exact litW_found _ _ hn hs) ?_
  exact specR_returnI _ 0 rfl (fun t ht' => ⟨H2, hp1.trans hp2, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)


/-- The pushed environment's flags are the lookups at the installed context (old flags in it). -/
theorem push_flags_found {C : Ctx} (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins) (ci : IConstantInfo) (o : Nat)
    (EH : List (BitVec 64)) :
    (C.fe.push ci).natLit =
        pinsFound (ctxIns C ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH (C.envM.insert ci.name (ecell C o)))
          natPins ∧
      (C.fe.push ci).strLit =
        pinsFound (ctxIns C ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH (C.envM.insert ci.name (ecell C o)))
          strPins := by
  have hF' := hF.push ci
  have hL' : LitsPinned (C.fe.push ci) C.pins := by unfold LitsPinned; rw [IFEnv.push_base]; exact hL
  refine ⟨?_, ?_⟩
  · rw [hF'.nat, natLitStoredBy_pins hL']
    unfold pinsFound ctxIns
    simp only [IFEnv.setFlags_find?]
  · rw [hF'.str, strLitStoredBy_pins hL']
    unfold pinsFound ctxIns
    simp only [IFEnv.setFlags_find?]

end

end ConPanqueque.T.Decl
