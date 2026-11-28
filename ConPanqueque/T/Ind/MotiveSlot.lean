import ConPanqueque.T.Ind.KindDecode

/-!
# The slot of a class's motive (`ClassRead.motiveSlot`)

`msl` ("motiveSlotOf"): the slot of the `c`-th motive in the slot stream, `0` when there is none (the twin's
`(ClassRead.motiveSlot slots c).getD 0`, read by `ClassGen.motVar`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## The slot of class `c`'s motive (`ClassRead.motiveSlot`, defaulting to `0`) -/

/-- Slot `s` is a motive. -/
def isMotSlot (sls : List ClassSlot) (s : Nat) : Bool :=
  match sls[s]? with
  | some (.motive _) => true
  | _ => false

theorem motiveSlot_eq (sls : List ClassSlot) (c : Nat) :
    ClassRead.motiveSlot sls c = ((List.range' 0 (sls.length - 0)).filter (isMotSlot sls))[c]? := by
  simp only [ClassRead.motiveSlot, Nat.sub_zero, List.range_eq_range']
  rfl

def mslS := ofString "msl_s"
def mslI := ofString "msl_i"
def mslN := ofString "msl_n"
def mslC := ofString "msl_c"
def mslP := ofString "msl_p"
def mslTg := ofString "msl_tg"
def mslR := ofString "msl_r"
def fMsl := ofString "motiveSlotOf"

def mslParams : List MlS := [mslS, mslI, mslN, mslC]
def mslLocals : List MlS := [mslP, mslTg, mslR]

def mslBody : ProgHOL 64 := prologue mslLocals
  (.ite (.cmp .lower (vv mslI) (vv mslN))
    (.seq (.assign .local mslP (.load .one (.op .add [vv mslS, .op .add [.panop .mul [vv mslI, .const 8], .const 8]])))
    (.seq (.assign .local mslTg (.load .one (vv mslP)))
    (.ite (.cmp .equal (vv mslTg) (.const 0))
      (.ite (.cmp .equal (vv mslC) (.const 0)) (.return (vv mslI))
        (.seq (.call (some (some (.local, mslR), none)) fMsl
            [vv mslS, .op .add [vv mslI, .const 1], vv mslN, .op .sub [vv mslC, .const 1]])
          (.return (vv mslR))))
      (.seq (.call (some (some (.local, mslR), none)) fMsl [vv mslS, .op .add [vv mslI, .const 1], vv mslN, vv mslC])
        (.return (vv mslR))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem msl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mslLocals → (ctxEnv C ++ mslParams.zip vals).get x = none :=
  Knot.params_none C mslLocals mslParams vals (by decide) (by decide)

/-- A natural-number answer, the state unchanged. -/
def PostMSL (C : Ctx) (s : AState) (r : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = BitVec.ofNat 64 r ∧ SR C s' st

theorem postMSL_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostMSL C s a w s' st → PostMSL C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem range'_step (i n : Nat) (h : i < n) : List.range' i (n - i) = i :: List.range' (i + 1) (n - (i + 1)) := by
  rw [show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]

/-- **`motiveSlotOf`** from slot `i`: the slot of the `c`-th motive at or after `i`, else `0`. -/
theorem msl_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMsl = some (mslParams.map (fun p => (p, ShapeHOL.one)), mslBody, .one))
    (sls : List ClassSlot) (os : Nat) (hsl : sls.length < 2 ^ 58) (H : List (BitVec 64)) (hsb : SlotBlk C H os sls) :
    ∀ f i c (s : AState), sls.length - i = f → i ≤ sls.length → c < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (mslParams.zip [cellA C os, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length,
        BitVec.ofNat 64 c])) mslBody s
        (pure ((((List.range' i (sls.length - i)).filter (isMotSlot sls))[c]?).getD 0)) (PostMSL (ctxH C H) s) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hsb
  intro f
  induction f with
  | zero =>
    intro i c s hf hi hc63
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (postMSL_locals _ s) (msl_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mslParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Nat.sub_self, List.range'_zero, List.filter_nil, List.getElem?_nil, Option.getD_none]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i c s hf hi hc63
    have hin : i < sls.length := by omega
    refine specR_prologue (postMSL_locals _ s) (msl_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mslParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hsr⟩ := hpsr i hin
    have hio : i < ps.length := by omega
    have hpe := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hpi : ps[i] = op := by simpa [List.getElem?_eq_getElem hio] using hop
    rw [hpi] at hpe
    refine UD.specR_heapLoadI' (C := ctxH C H) mslP _ (os + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, mslParams, ctxEnv]; exact cellA_mulIdx C os i (by omega)) ?_
    rw [range'_step i sls.length hin, List.filter_cons]
    -- the recursive call at count `c'`
    have hcall : ∀ (Γ : Env) (c' : Nat), c' < 2 ^ 63 → Γ.get mslS = some (cellA C os) →
        Γ.get mslI = some (BitVec.ofNat 64 i) → Γ.get mslN = some (BitVec.ofNat 64 sls.length) →
        ∀ (ec : ExpHOL 64), sev Γ ec = some (BitVec.ofNat 64 c') →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ mslLocals))
          (.seq (.call (some (some (.local, mslR), none)) fMsl [vv mslS, .op .add [vv mslI, .const 1], vv mslN, ec])
            (.return (vv mslR))) s
          (pure ((((List.range' (i + 1) (sls.length - (i + 1))).filter (isMotSlot sls))[c']?).getD 0))
          (PostMSL (ctxH C H) s) := by
      intro Γ c' hc' gS gI gN ec hec
      refine specR_congr (m' := (pure ((((List.range' (i + 1) (sls.length - (i + 1))).filter (isMotSlot sls))[c']?).getD 0) : AM Nat) >>=
        fun r => pure r) (by simp) ?_
      refine specR_callNIM mslR fMsl mslParams [vv mslS, .op .add [vv mslI, .const 1], vv mslN, ec] mslBody
        [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length, BitVec.ofNat 64 c'] (by decide) rfl (by decide) hc
        ⟨by simp [sev, gS], by simp [sev, sev_vv, gI]; exact word_add1_eq i, by simp [sev, gN], hec, trivial⟩
        (PostMSL (ctxH C H) s) (fun _ _ _ _ h => h.2.2)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mslParams _ rfl hlk)
          (ih (i + 1) c' s (by omega) (by omega) hc'))
        (fun r w s1 st ⟨hs1, hw, _⟩ => ?_)
      subst hs1 hw
      exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    generalize hsl' : sls[i] = sl at hsr
    have hmi : isMotSlot sls i = (match sl with | .motive _ => true | .minor _ _ _ => false) := by
      simp only [isMotSlot, List.getElem?_eq_getElem hin, hsl']; cases sl <;> rfl
    cases sl with
    | motive k =>
      refine UD.specR_heapLoadI' (C := ctxH C H) mslTg (vv mslP) op _ hsr.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [hmi, ite_true]
      rcases c with _ | c'
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mslParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_returnI _ (BitVec.ofNat 64 i) (by simp +decide [sev, Env.get_cons, Env.get, mslParams, ctxEnv])
          (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · have hne : BitVec.ofNat 64 (c' + 1) ≠ 0 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, mslParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only [List.getElem?_cons_succ]
        exact hcall _ c' (by omega) (by simp +decide [Env.get_cons, Env.get, mslParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, mslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, mslParams, ctxEnv])
          _ (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Env.get, mslParams, ctxEnv]; exact ofNat_succ_sub_one c')
    | minor cc cn ihs =>
      refine UD.specR_heapLoadI' (C := ctxH C H) mslTg (vv mslP) op _ hsr.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hmi]
      exact hcall _ c hc63 (by simp +decide [Env.get_cons, Env.get, mslParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, mslParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, mslParams, ctxEnv])
        _ (by simp +decide [sev, Env.get_cons, Env.get, mslParams, ctxEnv])

end

end ConPanqueque.T.Ind
