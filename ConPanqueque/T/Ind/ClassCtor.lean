import ConPanqueque.T.Ind.ClassNfs
import ConPanqueque.T.Ind.NestPos

/-!
# A class's constructor for the generator (`classCtorOf`, member classes with ordinary fields)

`ffe`: the first table entry of a constructor (none hangs).  `cfo`: `classFieldsOf` with no inductive
hypotheses, every field ordinary (a field naming a member hangs).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## The first entry of a constructor -/

def ffeT := ofString "ffe_t"
def ffeI := ofString "ffe_i"
def ffeK := ofString "ffe_k"
def ffeC := ofString "ffe_c"
def ffeP := ofString "ffe_p"
def ffeX := ofString "ffe_x"
def ffeR := ofString "ffe_r"
def fFfe := ofString "firstEntry"

def ffeParams : List MlS := [ffeT, ffeI, ffeK, ffeC]
def ffeLocals : List MlS := [ffeP, ffeX, ffeR]

def ffeBody : ProgHOL 64 := prologue ffeLocals
  (.ite (.cmp .lower (vv ffeI) (vv ffeK))
    (.seq (.assign .local ffeP (.load .one (.op .add [vv ffeT, .op .add [.panop .mul [vv ffeI, .const 8], .const 8]])))
    (.seq (.assign .local ffeX (.load .one (vv ffeP)))
    (.ite (.cmp .equal (vv ffeX) (vv ffeC)) (.return (vv ffeP))
      (.seq (.call (some (some (.local, ffeR), none)) fFfe [vv ffeT, .op .add [vv ffeI, .const 1], vv ffeK, vv ffeC])
        (.return (vv ffeR))))))
    hang)

section
variable {σ : Type}

theorem ffe_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ffeLocals → (ctxEnv C ++ ffeParams.zip vals).get x = none :=
  Knot.params_none C ffeLocals ffeParams vals (by decide) (by decide)

/-- An entry list's first element at a constructor, as a record (the state kept). -/
def PostFE (C : Ctx) (s : AState) (r : List NestCtorNf) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ e es o, r = e :: es ∧ w = cellA C o ∧ NfRep C C.H o e ∧ SR C s' st

/-- **The first entry of `cn`** from entry `i` on (none hangs). -/
theorem ffe_spec (C : Ctx) (hc : C.code.lookup fFfe = some (ffeParams.map (fun p => (p, ShapeHOL.one)), ffeBody, .one))
    (tbl : List NestCtorNf) (ot : Nat) (htl : tbl.length < 2 ^ 58) (cn : NIdx) (H : List (BitVec 64))
    (htb : PRep C H ot (fun H o nf => NfRep C H o nf) tbl) :
    ∀ f i (s : AState), tbl.length - i = f → i ≤ tbl.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ffeParams.zip [cellA C ot, BitVec.ofNat 64 i, BitVec.ofNat 64 tbl.length,
        Enc.idxW cn])) ffeBody s (pure ((tbl.drop i).filter (·.ctor == cn))) (PostFE (ctxH C H) s) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := htb
  have hpost : ∀ (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostFE (ctxH C H) s a w s' st → PostFE (ctxH C H) s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ ⟨h0, e, es, o, h1, h2, h3, h4⟩ => ⟨h0, e, es, o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = tbl.length := by omega
    subst hin
    refine specR_prologue (hpost s) (ffe_none _ _) ?_
    have hlw := nd_lt_iff tbl.length tbl.length (by omega) (by omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ffeParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  | succ f ih =>
    intro i s hf hi
    have hin : i < tbl.length := by omega
    refine specR_prologue (hpost s) (ffe_none _ _) ?_
    have hlw := nd_lt_iff i tbl.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ffeParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : i < os.length := by omega
    have hpe := hosb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hnf := hosr i hin hio
    refine UD.specR_heapLoadI' (C := ctxH C H) ffeP _ (ot + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get, ffeParams, ctxEnv]; exact cellA_mulIdx C ot i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ffeX (vv ffeP) _ _ hnf.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin, List.filter_cons]
    by_cases he : tbl[i].ctor = cn
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [he, beq_self_eq_true, ↓reduceIte]
      exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons]; rfl) (fun t ht => ⟨rfl, tbl[i], _, os[i], rfl, rfl, hnf,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hne : Enc.idxW tbl[i].ctor ≠ Enc.idxW cn := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    have hbe : (tbl[i].ctor == cn) = false := beq_eq_false_iff_ne.mpr he
    simp only [hbe, Bool.false_eq_true, ↓reduceIte]
    refine specR_congr (m' := (pure ((tbl.drop (i + 1)).filter (·.ctor == cn)) : AM (List NestCtorNf)) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ffeR fFfe ffeParams [vv ffeT, .op .add [vv ffeI, .const 1], vv ffeK, vv ffeC]
      ffeBody [cellA C ot, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 tbl.length, Enc.idxW cn] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv], trivial⟩
      (PostFE (ctxH C H) s) (fun r w s' H' => H' = H ∧ s' = s ∧ ∃ e es o, r = e :: es ∧ w = cellA C o ∧ NfRep C H o e)
      (fun r w s' st ⟨h0, e, es, o, h1, h2, h3, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, e, es, o, h1, h2, h3⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ffeParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun r w s3 H3 hp3 ⟨eH, es3, e, es, o, h1, h2, h3⟩ => ?_)
    subst eH es3 h2
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨rfl, e, es, o, h1, rfl, h3,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classFieldsOf`, every field ordinary -/

def cfoA := ofString "cfo_a"
def cfoI := ofString "cfo_i"
def cfoN := ofString "cfo_n"
def cfoMs := ofString "cfo_ms"
def cfoX := ofString "cfo_x"
def cfoT := ofString "cfo_t"
def cfoO := ofString "cfo_o"
def cfoR := ofString "cfo_r"
def fCfo := ofString "classFieldsOrd"

def cfoParams : List MlS := [cfoA, cfoI, cfoN, cfoMs]
def cfoLocals : List MlS := [cfoX, cfoT, cfoO, cfoR]

def cfoBody : ProgHOL 64 := prologue cfoLocals
  (.ite (.cmp .lower (vv cfoI) (vv cfoN))
    (.seq (.assign .local cfoX (.load .one (.op .add [vv cfoA, .op .add [.panop .mul [vv cfoI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, cfoT), none)) fFvt [vv cfoX])
    (.seq (.call (some (some (.local, cfoO), none)) fNocTop [vv cfoT, vv cfoMs, .const 0, .const 0])
    (.ite (.cmp .equal (vv cfoO) (.const 0))
      (.seq (.call (some (some (.local, cfoR), none)) fCfo [vv cfoA, .op .add [vv cfoI, .const 1], vv cfoN, vv cfoMs])
        (.return (.const 0)))
      hang))))
    (.return (.const 0)))

structure CFOCodes (C : Ctx) : Prop where
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  nt : NTCodes C
  self : C.code.lookup fCfo = some (cfoParams.map (fun p => (p, ShapeHOL.one)), cfoBody, .one)

section
variable {σ : Type}

theorem cfo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cfoLocals → (ctxEnv C ++ cfoParams.zip vals).get x = none :=
  Knot.params_none C cfoLocals cfoParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`classFieldsOf p [] i`** over the fields from `i` on: all ordinary (a member-naming field hangs). -/
theorem cfo_spec (C : Ctx) (hok : CtxOK C) (hc : CFOCodes C) (p : BlockShape) (ms : List MemberShape) (om : Nat)
    (hms : p.members = ms) (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59)
    (fvs : List EIdx) (pa : Nat) (hfl : fvs.length < 2 ^ 58) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0)
    (hA : BlkAt H0 pa (fvs.map Enc.idxW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState), fvs.length - i = f → i ≤ fvs.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cfoParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 fvs.length,
        cellA C om])) cfoBody s (classFieldsOf p [] i (fvs.drop i))
        (fun r w s' st => r = (fvs.drop i).map (fun _ => ClassField.ordinary) ∧ Decl.PostU (ctxH C H) () w s' st) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = fvs.length := by omega
    subst hin
    refine specR_prologue (fun a w s' st L ⟨h1, H', hp', hsr⟩ => ⟨h1, H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩)
      (cfo_none _ _) ?_
    have hlw := nd_lt_iff fvs.length fvs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cfoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨by simp [classFieldsOf], H, List.prefix_refl _,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < fvs.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (fun a w s' st L ⟨h1, H', hp', hsr⟩ => ⟨h1, H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩)
      (cfo_none _ _) ?_
    have hlw := nd_lt_iff i fvs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cfoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) cfoX _ (pa + 1 + i) _ (get_prefix hx hp) (by decide)
      (by simp +decide [sev, Env.get, cfoParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin]
    unfold classFieldsOf
    refine ILP.callE_spec (C := ctxH C H) cfoT fFvt [pH] [vv cfoX] ExM.fvtBody [Enc.idxW fvs[i]] (by decide) rfl
      (by decide) hc.fvt ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (ExM.fvt_spec (ctxH C H) s fvs[i]) (fun w s1 => ?_)
    refine specR_callNIH (C := ctxH C H) cfoO fNocTop ntParams [vv cfoT, vv cfoMs, .const 0, .const 0] ntBody
      [Enc.idxW w, cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.nt.top
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cfoParams, ctxEnv], rfl, rfl,
        trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
        (by simp only [BlockShape.memberNames, hms]; exact nt_spec C hok hc.nt ms om hM hml 0 0 (by decide) (by decide) w H s1 hpC))
      (fun b wb s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H <+: H2 := hp2
    cases b
    swap
    · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [List.filter_nil, List.length_nil, Bool.not_false, beq_self_eq_true, Bool.and_self, ↓reduceIte, bind_assoc]
    refine specR_callNIH (C := ctxH C H2) cfoR fCfo cfoParams [vv cfoA, .op .add [vv cfoI, .const 1], vv cfoN, vv cfoMs]
      cfoBody [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 fvs.length, cellA C om] (by decide) rfl (by decide)
      hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cfoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfoParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cfoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfoParams, ctxEnv], trivial⟩
      (fun r w s' st => r = (fvs.drop (i + 1)).map (fun _ => ClassField.ordinary) ∧ Decl.PostU (ctxH C H2) () w s' st)
      (fun r _ _ _ => r = (fvs.drop (i + 1)).map (fun _ => ClassField.ordinary))
      (fun r w s' st ⟨h1, H', hp', hsr⟩ => ⟨H', hp', h1, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfoParams _ rfl hlk)
        (ih (i + 1) H2 s2 (by omega) (by omega) (hp.trans hp2')))
      (fun r w s3 H3 hp3 hr => ?_)
    subst hr
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl,
      H3, hp2'.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classMinorSlot` at class `0` -/

/-- A minor slot of class `0` at constructor `cn`. -/
def isHitC (cn : NIdx) : ClassSlot → Bool
  | .minor c C _ => c == 0 && C == cn
  | .motive _ => false

def ihsOf : ClassSlot → List (Nat × Nat)
  | .minor _ _ ihs => ihs
  | .motive _ => []

/-- The twin's hit function of `classMinorSlot rd 0 cn`. -/
def cmsHit (l : List ClassSlot) (cn : NIdx) (s : Nat) : Option (Nat × List (Nat × Nat)) :=
  match (l[s]? : Option ClassSlot) with
  | some (.minor c' C' ihs) => if c' == 0 && C' == cn then some (s, ihs) else none
  | _ => none

theorem cmsHits_cons (a : ClassSlot) (l : List ClassSlot) (cn : NIdx) :
    (List.range (a :: l).length).filterMap (cmsHit (a :: l) cn) =
      (cmsHit [a] cn 0).toList ++ ((List.range l.length).filterMap (cmsHit l cn)).map (fun h => (h.1 + 1, h.2)) := by
  rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map, List.map_filterMap]
  have h0 : cmsHit (a :: l) cn 0 = cmsHit [a] cn 0 := by simp [cmsHit]
  have h1 : ∀ s, cmsHit (a :: l) cn (s + 1) = (cmsHit l cn s).map (fun h => (h.1 + 1, h.2)) := by
    intro s; unfold cmsHit; simp only [List.getElem?_cons_succ]
    split <;> simp_all
  rw [h0]
  have h2 : (List.range l.length).filterMap (cmsHit (a :: l) cn ∘ Nat.succ) =
      (List.range l.length).filterMap (fun s => (cmsHit l cn s).map (fun h => (h.1 + 1, h.2))) := by
    congr 1; funext s; exact h1 s
  rw [h2]
  cases cmsHit [a] cn 0 <;> rfl

theorem cmsHits_props (cn : NIdx) : ∀ l : List ClassSlot,
    ((List.range l.length).filterMap (cmsHit l cn)).length = (l.filter (isHitC cn)).length ∧
    ∀ h ∈ (List.range l.length).filterMap (cmsHit l cn), ∃ sl ∈ l, isHitC cn sl = true ∧ h.2 = ihsOf sl
  | [] => by simp
  | a :: l => by
    obtain ⟨ih1, ih2⟩ := cmsHits_props cn l
    rw [cmsHits_cons]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, List.length_map, ih1, List.filter_cons]
      cases a with
      | motive k => simp [cmsHit, isHitC]
      | minor c C ihs =>
        by_cases hh : (c == 0 && C == cn) = true
        · simp [cmsHit, isHitC, hh]; omega
        · simp only [Bool.not_eq_true] at hh; simp [cmsHit, isHitC, hh]
    · intro h hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases a with
        | motive k => simp [cmsHit] at hm
        | minor c C ihs =>
          by_cases hh : (c == 0 && C == cn) = true
          · simp [cmsHit, hh] at hm; subst hm; exact ⟨_, List.mem_cons_self, by simp [isHitC, hh], rfl⟩
          · simp only [Bool.not_eq_true] at hh; simp [cmsHit, hh] at hm
      · rw [List.mem_map] at hm
        obtain ⟨h', hm', rfl⟩ := hm
        obtain ⟨sl, hsl, hh, he⟩ := ih2 h' hm'
        exact ⟨sl, List.mem_cons_of_mem _ hsl, hh, he⟩

/-- One minor slot at `(0, cn)`, its inductive hypotheses none: `classMinorSlot` answers it. -/
theorem classMinorSlot_one (rd : ClassRead) (cn : NIdx) (h1 : (rd.slots.filter (isHitC cn)).length = 1)
    (h2 : ∀ sl ∈ rd.slots, isHitC cn sl = true → ihsOf sl = []) :
    ∃ k, classMinorSlot rd 0 cn = pure (k, []) := by
  obtain ⟨hl, hp⟩ := cmsHits_props cn rd.slots
  rw [h1] at hl
  obtain ⟨h, hh⟩ := List.length_eq_one_iff.mp hl
  obtain ⟨sl, hsl, hhit, he⟩ := hp h (by rw [hh]; exact List.mem_singleton_self _)
  have hih : h.2 = [] := by rw [he]; exact h2 sl hsl hhit
  have key : (List.range rd.slots.length).filterMap (cmsHit rd.slots cn) = [(h.1, [])] := by
    rw [hh, show h = (h.1, []) from Prod.ext rfl hih]
  have e : ∀ f : Nat → Option (Nat × List (Nat × Nat)), (∀ k, f k = cmsHit rd.slots cn k) →
      (List.range rd.slots.length).filterMap f = [(h.1, [])] := by
    intro f hf; rw [← key]; congr 1; funext k; exact hf k
  refine ⟨h.1, ?_⟩
  unfold classMinorSlot
  rw [e _ (fun k => by unfold cmsHit; rcases rd.slots[k]? with _ | (_ | _) <;> rfl)]

def cmsS := ofString "cms_s"
def cmsI := ofString "cms_i"
def cmsN := ofString "cms_n"
def cmsCn := ofString "cms_cn"
def cmsP := ofString "cms_p"
def cmsTg := ofString "cms_tg"
def cmsR := ofString "cms_r"
def cmsCc := ofString "cms_cc"
def cmsCv := ofString "cms_cv"
def cmsIh := ofString "cms_ih"
def cmsL := ofString "cms_l"
def fCms := ofString "minorSlotCount"

def cmsParams : List MlS := [cmsS, cmsI, cmsN, cmsCn]
def cmsLocals : List MlS := [cmsP, cmsTg, cmsR, cmsCc, cmsCv, cmsIh, cmsL]

def cmsBody : ProgHOL 64 := prologue cmsLocals
  (.ite (.cmp .lower (vv cmsI) (vv cmsN))
    (.seq (.assign .local cmsP (.load .one (.op .add [vv cmsS, .op .add [.panop .mul [vv cmsI, .const 8], .const 8]])))
    (.seq (.assign .local cmsTg (.load .one (vv cmsP)))
    (.seq (.call (some (some (.local, cmsR), none)) fCms [vv cmsS, .op .add [vv cmsI, .const 1], vv cmsN, vv cmsCn])
    (.ite (.cmp .equal (vv cmsTg) (.const 1))
      (.seq (.assign .local cmsCc (.load .one (.op .add [vv cmsP, .const 8])))
      (.seq (.assign .local cmsCv (.load .one (.op .add [vv cmsP, .const 16])))
      (.ite (.cmp .equal (vv cmsCc) (.const 0))
        (.ite (.cmp .equal (vv cmsCv) (vv cmsCn))
          (.seq (.assign .local cmsIh (.load .one (.op .add [vv cmsP, .const 24])))
          (.seq (.assign .local cmsL (.load .one (vv cmsIh)))
          (.ite (.cmp .equal (vv cmsL) (.const 0)) (.return (.op .add [vv cmsR, .const 1])) hang)))
          (.return (vv cmsR)))
        (.return (vv cmsR)))))
      (.return (vv cmsR))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem cms_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cmsLocals → (ctxEnv C ++ cmsParams.zip vals).get x = none :=
  Knot.params_none C cmsLocals cmsParams vals (by decide) (by decide)

/-- The count of minor slots at `(0, cn)`, each without inductive hypotheses (else a hang). -/
def PostCMS (C : Ctx) (sls : List ClassSlot) (cn : NIdx) (s : AState) (r : Nat) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ sls.length ∧ (∀ sl ∈ sls, isHitC cn sl = true → ihsOf sl = []) ∧ SR C s' st

set_option maxHeartbeats 16000000 in
theorem cms_spec (C : Ctx) (hc : C.code.lookup fCms = some (cmsParams.map (fun p => (p, ShapeHOL.one)), cmsBody, .one))
    (sls : List ClassSlot) (os : Nat) (hsl : sls.length < 2 ^ 58) (cn : NIdx)
    (hcb : ∀ sl ∈ sls, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63) (H : List (BitVec 64))
    (hsb : SlotBlk C H os sls) :
    ∀ f i (s : AState), sls.length - i = f → i ≤ sls.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cmsParams.zip [cellA C os, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length,
        Enc.idxW cn])) cmsBody s (pure ((sls.drop i).filter (isHitC cn)).length)
        (PostCMS (ctxH C H) (sls.drop i) cn s) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hsb
  have hpost : ∀ (l : List ClassSlot) (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostCMS (ctxH C H) l cn s a w s' st → PostCMS (ctxH C H) l cn s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ _ ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (hpost _ s) (cms_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, by simp, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < sls.length := by omega
    refine specR_prologue (hpost _ s) (cms_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hsr⟩ := hpsr i hin
    have hio : i < ps.length := by omega
    have hpe := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hpi : ps[i] = op := by simpa [List.getElem?_eq_getElem hio] using hop
    rw [hpi] at hpe
    refine UD.specR_heapLoadI' (C := ctxH C H) cmsP _ (os + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv]; exact cellA_mulIdx C os i (by omega)) ?_
    have hsli := List.getElem_mem hin
    rw [List.drop_eq_getElem_cons hin]
    generalize hsl : sls[i] = sl at hsr hsli
    have hcb' := hcb sl hsli
    cases sl with
    | motive k =>
      obtain ⟨h0, -, -, -⟩ := hsr
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsTg (vv cmsP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_congr (m' := (pure ((sls.drop (i + 1)).filter (isHitC cn)).length : AM Nat) >>= fun r => pure r)
        (by simp [List.filter_cons, isHitC]) ?_
      refine specR_callNIH (C := ctxH C H) cmsR fCms cmsParams [vv cmsS, .op .add [vv cmsI, .const 1], vv cmsN, vv cmsCn]
        cmsBody [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length, Enc.idxW cn] (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], trivial⟩
        (PostCMS (ctxH C H) (sls.drop (i + 1)) cn s)
        (fun r w s' H' => H' = H ∧ s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ (sls.drop (i + 1)).length ∧
          ∀ sl ∈ sls.drop (i + 1), isHitC cn sl = true → ihsOf sl = [])
        (fun r w s' st ⟨h0, h1, h2, h3, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, h1, h2, h3⟩, h4⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmsParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun r w s3 H3 hp3 ⟨eH, es, hw, hr, hall⟩ => ?_)
      subst H3 s3 hw
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, rfl, by simp at hr ⊢; omega,
        fun sl hm hh => by
          rcases List.mem_cons.mp hm with e | hm
          · subst e; simp [isHitC] at hh
          · exact hall sl hm hh, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | minor c C' ihs =>
      obtain ⟨h0, h1, h2, oi, h3, hpr⟩ := hsr
      have hc63 := hcb' c C' ihs rfl
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsTg (vv cmsP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_congr (m' := (pure ((sls.drop (i + 1)).filter (isHitC cn)).length : AM Nat) >>= fun r =>
        pure (if isHitC cn (.minor c C' ihs) then r + 1 else r)) (by simp [List.filter_cons]; split <;> simp) ?_
      refine specR_callNIH (C := ctxH C H) cmsR fCms cmsParams [vv cmsS, .op .add [vv cmsI, .const 1], vv cmsN, vv cmsCn]
        cmsBody [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length, Enc.idxW cn] (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], trivial⟩
        (PostCMS (ctxH C H) (sls.drop (i + 1)) cn s)
        (fun r w s' H' => H' = H ∧ s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ (sls.drop (i + 1)).length ∧
          ∀ sl ∈ sls.drop (i + 1), isHitC cn sl = true → ihsOf sl = [])
        (fun r w s' st ⟨h0, h1, h2, h3, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, h1, h2, h3⟩, h4⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmsParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun r w s3 H3 hp3 ⟨eH, es, hw, hr, hall⟩ => ?_)
      subst H3 s3 hw
      obtain ⟨hc63', hil⟩ := hc63
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsCc _ (op + 1) _ h1 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsCv _ (op + 2) _ h2 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 2) ?_
      have hret : isHitC cn (.minor c C' ihs) = false → ∀ (Γ : Env), Γ.get cmsR = some (BitVec.ofNat 64 r) →
          SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ cmsLocals)) (.return (vv cmsR)) s
            (pure (if isHitC cn (.minor c C' ihs) then r + 1 else r))
            (PostCMS (ctxH C H) (.minor c C' ihs :: sls.drop (i + 1)) cn s) := by
        intro hf Γ gR
        refine specR_returnI _ (BitVec.ofNat 64 r) (by simp [sev, gR]) (fun t ht => ?_)
        rw [hf]
        exact ⟨rfl, by simp, by simp at hr ⊢; omega, fun sl hm hh => by
          rcases List.mem_cons.mp hm with e | hm
          · subst e; rw [hf] at hh; exact absurd hh (by decide)
          · exact hall sl hm hh, sr_of_eq ht.sr rfl rfl rfl rfl⟩
      by_cases hc0 : c = 0
      swap
      · have hne : BitVec.ofNat 64 c ≠ 0#64 := fun e => hc0 (by have := congrArg BitVec.toNat e; simp at this; omega)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
        refine hret (by simp [isHitC, hc0]) _ ?_
        simp +decide [Env.get_cons]
      subst hc0
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases hcv : C' = cn
      swap
      · have hne : Enc.idxW C' ≠ Enc.idxW cn := fun e => hcv (Enc.idxW_inj e)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        refine hret (by simp [isHitC, hcv]) _ ?_
        simp +decide [Env.get_cons]
      subst C'
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsIh _ (op + 3) _ h3 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 3) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsL (vv cmsIh) oi _ hpr.1 (by decide)
        (by simp [sev, Env.get_cons]; rfl) ?_
      by_cases hie : ihs = []
      swap
      · have hne : BitVec.ofNat 64 ihs.length ≠ 0#64 := fun e => hie (by
          have := congrArg BitVec.toNat e; simp at this; exact List.eq_nil_of_length_eq_zero (by omega))
        exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
          (fun _ => specR_hangI)
      subst hie
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      have hh : isHitC cn (.minor 0 cn []) = true := by simp [isHitC]
      refine specR_returnI _ (BitVec.ofNat 64 (r + 1)) (by simp +decide [sev, Env.get_cons]; exact word_add1_eq r)
        (fun t ht => ?_)
      rw [hh]
      exact ⟨rfl, by simp, by simp at hr ⊢; omega, fun sl hm hh' => by
          rcases List.mem_cons.mp hm with e | hm
          · subst e; rfl
          · exact hall sl hm hh', sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

/-! ## `classCtorOf` (a member class, ordinary fields) -/

theorem classFieldsAgree_ord (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx)
    (ms : List TargetMajor) (fvs : List EIdx) (es : List NestCtorNf) :
    ∀ (ks : List ClassField) (i : Nat), (∀ k ∈ ks, k = .ordinary) →
      classFieldsAgree mode fe p formerTys ms fvs es i ks = pure ()
  | [], i, _ => by simp [classFieldsAgree]
  | k :: ks, i, h => by
    rw [h k List.mem_cons_self, classFieldsAgree]
    exact classFieldsAgree_ord mode fe p formerTys ms fvs es ks (i + 1) (fun k hk => h k (List.mem_cons_of_mem _ hk))

/-- A class constructor `[cv, nF, tyD, tyN, |kinds|, 0]`, every kind ordinary. -/
def CCRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (cc : ClassCtor) : Prop :=
  (∃ ocv, H[o]? = some (cellA C ocv) ∧ CVRep C H ocv cc.cv) ∧ H[o + 1]? = some (BitVec.ofNat 64 cc.nF) ∧
    H[o + 2]? = some (Enc.idxW cc.tyD) ∧ H[o + 3]? = some (Enc.idxW cc.tyN) ∧
    H[o + 4]? = some (BitVec.ofNat 64 cc.kinds.length) ∧ (∀ k ∈ cc.kinds, k = .ordinary)

def ccoTb := ofString "cco_tb"
def ccoTk := ofString "cco_tk"
def ccoCv := ofString "cco_cv"
def ccoNf := ofString "cco_nf"
def ccoSl := ofString "cco_sl"
def ccoSk := ofString "cco_sk"
def ccoNk := ofString "cco_nk"
def ccoMs := ofString "cco_ms"
def ccoDs := ofString "cco_ds"
def ccoDn := ofString "cco_dn"
def ccoCn := ofString "cco_cn"
def ccoE := ofString "cco_e"
def ccoCt := ofString "cco_ct"
def ccoTy := ofString "cco_ty"
def ccoX := ofString "cco_x"
def ccoFv := ofString "cco_fv"
def ccoL := ofString "cco_l"
def ccoU := ofString "cco_u"
def ccoT0 := ofString "cco_t0"
def ccoD := ofString "cco_d"
def ccoR := ofString "cco_r"
def fCco := ofString "classCtorOf"

def ccoParams : List MlS := [ccoTb, ccoTk, ccoCv, ccoNf, ccoSl, ccoSk, ccoNk, ccoMs, ccoDs, ccoDn]
def ccoLocals : List MlS := [ccoCn, ccoE, ccoCt, ccoTy, ccoX, ccoFv, ccoL, ccoU, ccoT0, ccoD, ccoR]

def ccoBody (C : Ctx) : ProgHOL 64 := prologue ccoLocals
  (.seq (.assign .local ccoCn (.load .one (vv ccoCv)))
  (.seq (.call (some (some (.local, ccoE), none)) fFfe [vv ccoTb, .const 0, vv ccoTk, vv ccoCn])
  (.seq (.call (some (some (.local, ccoCt), none)) fCms [vv ccoSl, .const 0, vv ccoSk, vv ccoCn])
  (.ite (.cmp .equal (vv ccoCt) (.const 1))
  (.seq (.assign .local ccoTy (.load .one (.op .add [vv ccoE, .const 24])))
  (.seq (.call (some (some (.local, ccoX), none)) fOpenFvars [vv ccoNf, vv ccoTy, vv ccoNk])
  (.ite (.cmp .equal (vv ccoX) (.const 0))
  hang
  (.seq (.assign .local ccoFv (.load .one (vv ccoX)))
  (.seq (.assign .local ccoL (.load .one (vv ccoFv)))
  (.ite (.cmp .equal (vv ccoL) (vv ccoNf))
  (.seq (.call (some (some (.local, ccoU), none)) fCfo [vv ccoFv, .const 0, vv ccoL, vv ccoMs])
  (.seq (.assign .local ccoT0 (.load .one (.op .add [vv ccoCv, .const 16])))
  (.seq (.call (some (some (.local, ccoD), none)) fInstPis [vv ccoDs, .const 0, vv ccoDn, vv ccoT0])
  (alloc6 C ccoR (vv ccoCv) (vv ccoNf) (vv ccoD) (vv ccoTy) (vv ccoL) (.const 0) (.return (vv ccoR))))))
  hang))))))
  hang))))

structure CCOCodes (C : Ctx) : Prop where
  ffe : C.code.lookup fFfe = some (ffeParams.map (fun p => (p, ShapeHOL.one)), ffeBody, .one)
  cms : C.code.lookup fCms = some (cmsParams.map (fun p => (p, ShapeHOL.one)), cmsBody, .one)
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  cfo : CFOCodes C
  ipw : C.code.lookup fInstPis = some (ipwParams.map (fun p => (p, ShapeHOL.one)), ipwBody, .one)
  i1f : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  i1c : Codes C (ExI.body C)
  self : C.code.lookup fCco = some (ccoParams.map (fun p => (p, ShapeHOL.one)), ccoBody C, .one)

section
variable {σ : Type}

theorem cco_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ccoLocals → (ctxEnv C ++ ccoParams.zip vals).get x = none :=
  Knot.params_none C ccoLocals ccoParams vals (by decide) (by decide)

/-- A class constructor, as its record. -/
def PostCC (C : Ctx) (cc : ClassCtor) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ CCRep C H' o cc ∧ SR (ctxH C H') s' st

theorem postCC_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCC C a w s' st → PostCC C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **`classCtorOf`** at class `0` (a member), the constructor's fields ordinary. -/
theorem cco_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : CCOCodes C) (p : BlockShape) (formerTys : List EIdx) (rd : ClassRead) (m : TargetMajor)
    (hmm : m.member = some 0) (ms : List MemberShape) (om : Nat) (hms : p.members = ms)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59)
    (ctor : IConstantVal × Nat) (ocv : Nat) (hcv : CVRep C C.H ocv ctor.1) (hnf : ctor.2 < 2 ^ 56)
    (ot osl pd : Nat) (htl : m.nfs.length < 2 ^ 58) (htb : PRep C C.H ot (fun H o nf => NfRep C H o nf) m.nfs)
    (hsl : rd.slots.length < 2 ^ 58) (hcb : ∀ sl ∈ rd.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63)
    (hsb : SlotBlk C C.H osl rd.slots) (hdl : m.ds.length < 2 ^ 58) (hds : BlkAt C.H pd (m.ds.map Enc.idxW))
    (hnk : p.nP + p.k < 2 ^ 56) (s : AState) :
    SpecR (σ := σ) (Pre C s (ccoParams.zip [cellA C ot, BitVec.ofNat 64 m.nfs.length, cellA C ocv,
        BitVec.ofNat 64 ctor.2, cellA C osl, BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 (p.nP + p.k), cellA C om,
        cellA C pd, BitVec.ofNat 64 m.ds.length])) (ccoBody C) s
      (classCtorOf mode C.fe p formerTys rd [m] 0 ctor) (PostCC C) := by
  refine specR_prologue (postCC_locals _) (cco_none _ _) ?_
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine UD.specR_heapLoadI' (C := ctxH C C.H) ccoCn (vv ccoCv) ocv _ hcv.1 (by decide) (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv]; rfl) ?_
  unfold classCtorOf
  simp only [targetMajorAt, List.getElem?_cons_zero, pure_bind]
  refine specR_callPure (C := ctxH C C.H) ccoE fFfe ffeParams [vv ccoTb, .const 0, vv ccoTk, vv ccoCn] ffeBody
    [cellA C ot, BitVec.ofNat 64 0, BitVec.ofNat 64 m.nfs.length, Enc.idxW ctor.1.name]
    ((m.nfs.drop 0).filter (·.ctor == ctor.1.name)) (by decide) rfl (by decide) hc.ffe
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩ (PostFE (ctxH C C.H) s)
    (fun r w s' H' => H' = C.H ∧ ∃ e es o, r = e :: es ∧ w = cellA C o ∧ NfRep C C.H o e)
    (fun r w s' st ⟨_, e, es, o, h1, h2, h3, h4⟩ => ⟨C.H, hp0, ⟨rfl, e, es, o, h1, h2, h3⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ffeParams _ rfl hlk)
      (ffe_spec C hc.ffe m.nfs ot htl ctor.1.name C.H htb m.nfs.length 0 s (by omega) (by omega)))
    (fun w H1 hp1 ⟨eH, e, es, oe, hfe, hw, hnfr⟩ => ?_)
  subst eH hw
  simp only [List.drop_zero] at hfe
  rw [hfe]
  simp only
  refine specR_callPure (C := ctxH C C.H) ccoCt fCms cmsParams [vv ccoSl, .const 0, vv ccoSk, vv ccoCn] cmsBody
    [cellA C osl, BitVec.ofNat 64 0, BitVec.ofNat 64 rd.slots.length, Enc.idxW ctor.1.name]
    ((rd.slots.drop 0).filter (isHitC ctor.1.name)).length (by decide) rfl (by decide) hc.cms
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩ (PostCMS (ctxH C C.H) (rd.slots.drop 0) ctor.1.name s)
    (fun r w s' H' => H' = C.H ∧ w = BitVec.ofNat 64 r ∧ r ≤ (rd.slots.drop 0).length ∧
      ∀ sl ∈ rd.slots.drop 0, isHitC ctor.1.name sl = true → ihsOf sl = [])
    (fun r w s' st ⟨_, h1, h2, h3, h4⟩ => ⟨C.H, hp0, ⟨rfl, h1, h2, h3⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmsParams _ rfl hlk)
      (cms_spec C hc.cms rd.slots osl hsl ctor.1.name hcb C.H hsb rd.slots.length 0 s (by omega) (by omega)))
    (fun w H2 hp2 ⟨eH, hw, hr, hall⟩ => ?_)
  subst eH hw
  simp only [List.drop_zero] at hr hall
  by_cases hcnt : (rd.slots.filter (isHitC ctor.1.name)).length = 1
  swap
  · have hne : BitVec.ofNat 64 (rd.slots.filter (isHitC ctor.1.name)).length ≠ 1#64 := fun e => hcnt (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hcnt]) (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨k, hk⟩ := classMinorSlot_one rd ctor.1.name hcnt hall
  rw [hk]
  simp only [pure_bind]
  refine UD.specR_heapLoadI' (C := ctxH C C.H) ccoTy _ (oe + 3) _ hnfr.2.2.2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oe 3) ?_
  refine specR_callNIH (C := ctxH C C.H) ccoX fOpenFvars ofParams [vv ccoNf, vv ccoTy, vv ccoNk]
    (ofBody C) [BitVec.ofNat 64 ctor.2, Enc.idxW e.ty, BitVec.ofNat 64 (p.nP + p.k)] (by decide) rfl
    (by decide) hc.ofc ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], trivial⟩
    (PostOF (ctxH C C.H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op ctor.2 e.ty (p.nP + p.k) (by omega) (by omega) C.H hp0 s))
    (fun o w s2 H3 hp3 ⟨hn, hsm⟩ => ?_)
  have hp3' : C.H <+: H3 := hp3
  rcases o with _ | ⟨fvs, e'⟩
  · have e0 := hn rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, oa, rfl, hob, hoe, hfb⟩ := hsm fvs e' rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol : ob < H3.length := (List.getElem?_eq_some_iff.mp hob).1
  have hHN' : H3.length ≤ C.HN := hHN
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H3) ccoFv (vv ccoX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfl : H3[oa]? = some (BitVec.ofNat 64 fvs.length) := by simpa using hfb.1
  refine UD.specR_heapLoadI' (C := ctxH C H3) ccoL (vv ccoFv) oa _ hfl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfvl : fvs.length < 2 ^ 63 := by
    rcases Nat.eq_zero_or_pos fvs.length with h0 | hpos
    · omega
    · have h1 := hfb.2 (fvs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      have hlay := hok.heapLay
      omega
  by_cases hfn : fvs.length = ctor.2
  swap
  · have hne2 : BitVec.ofNat 64 fvs.length ≠ BitVec.ofNat 64 ctor.2 := fun e => hfn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfn]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  refine specR_callNIH (C := ctxH C H3) ccoU fCfo cfoParams [vv ccoFv, .const 0, vv ccoL, vv ccoMs] cfoBody
    [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, cellA C om] (by decide) rfl (by decide) hc.cfo.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], trivial⟩
    (fun r w s' st => r = (fvs.drop 0).map (fun _ => ClassField.ordinary) ∧ Decl.PostU (ctxH C H3) () w s' st)
    (fun r _ _ _ => r = (fvs.drop 0).map (fun _ => ClassField.ordinary))
    (fun r w s' st ⟨h1, H', hp', hsr⟩ => ⟨H', hp', h1, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfoParams _ rfl hlk)
      (cfo_spec C hok hc.cfo p ms om hms hM hml fvs oa (by omega) H3 hp3' hfb fvs.length 0 H3 s2 (by omega) (by omega)
        (List.prefix_refl _)))
    (fun kinds w s4 H4 hp4 hk4 => ?_)
  subst hk4
  have hp4' : H3 <+: H4 := hp4
  simp only [List.drop_zero]
  rw [classFieldsAgree_ord mode C.fe p formerTys [m] fvs (e :: es) _ 0 (by simp)]
  simp only [pure_bind, targetCtorAt, hmm]
  refine UD.specR_heapLoadI' (C := ctxH C H4) ccoT0 _ (ocv + 2) _ (get_prefix hcv.2.2 (hp3'.trans hp4')) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv]; exact cellA_add_ofNat C ocv 2) ?_
  refine specR_callNIH (C := ctxH C H4) ccoD fInstPis ipwParams [vv ccoDs, .const 0, vv ccoDn, vv ccoT0] ipwBody
    [cellA C pd, BitVec.ofNat 64 0, BitVec.ofNat 64 m.ds.length, Enc.idxW ctor.1.type] (by decide) rfl (by decide) hc.ipw
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostSome (ctxH C H4)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
    (fun o w s' st ⟨t, h1, h2, hsr⟩ => ⟨H4, List.prefix_refl _, ⟨t, h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipwParams _ rfl hlk)
      (by have hip := ipw_spec (σ := σ) ra C hok hc.ipw hc.i1f hc.i1c m.ds pd H4 (blkAt_mono hds (hp3'.trans hp4')) m.ds.length 0 s4 ctor.1.type (by omega) (by omega); simp only [List.drop_zero] at hip; exact hip))
    (fun o w s5 H5 hp5 ⟨t, ho, hw⟩ => ?_)
  subst ho hw
  have hp5' : H4 <+: H5 := hp5
  have hpC5 : C.H <+: H5 := hp3'.trans (hp4'.trans hp5')
  simp only
  refine specR_alloc6I (ctxOK_H hok H5) ccoR (vv ccoCv) (vv ccoNf) (vv ccoD) (vv ccoTy) (vv ccoL) (.const 0)
    (cellA C ocv) (BitVec.ofNat 64 ctor.2) (Enc.idxW t) (Enc.idxW e.ty) (BitVec.ofNat 64 fvs.length) 0 (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv])
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => rfl) (fun H6 ws hp6 hws => ?_)
  obtain ⟨g0, g1, g2, g3, g4, -⟩ := img6_get H6 ws (cellA C ocv) (BitVec.ofNat 64 ctor.2) (Enc.idxW t) (Enc.idxW e.ty)
    (BitVec.ofNat 64 fvs.length) 0 hws
  have hp6' := (hp6 : H5 <+: H6).trans (img6_prefix H6 ws (cellA C ocv) (BitVec.ofNat 64 ctor.2) (Enc.idxW t)
    (Enc.idxW e.ty) (BitVec.ofNat 64 fvs.length) 0 hws)
  intro _
  exact specR_returnI _ (cellA C H6.length) rfl (fun tt htt =>
    ⟨_, H6.length, hpC5.trans hp6', rfl,
      ⟨⟨ocv, by simpa using g0, cvRep_mono (hpC5.trans hp6') hcv⟩, g1, g2, g3, by simpa using g4, by simp⟩,
      sr_of_eq htt.sr rfl rfl rfl rfl⟩)

end

/-! ## `classCtorsOf` (the member's constructors) -/

def cclCs := ofString "ccl_cs"
def cclI := ofString "ccl_i"
def cclN := ofString "ccl_n"
def cclTb := ofString "ccl_tb"
def cclTk := ofString "ccl_tk"
def cclSl := ofString "ccl_sl"
def cclSk := ofString "ccl_sk"
def cclNk := ofString "ccl_nk"
def cclMs := ofString "ccl_ms"
def cclDs := ofString "ccl_ds"
def cclDn := ofString "ccl_dn"
def cclO := ofString "ccl_o"
def cclF := ofString "ccl_f"
def cclX := ofString "ccl_x"
def fCcl := ofString "classCtorsOf"

def cclParams : List MlS := [cclCs, cclI, cclN, cclTb, cclTk, cclSl, cclSk, cclNk, cclMs, cclDs, cclDn]
def cclLocals : List MlS := gaaLocals ++ [cclO, cclF, cclX]

def cclBody (C : Ctx) : ProgHOL 64 := prologue cclLocals
  (.ite (.cmp .lower (vv cclI) (vv cclN))
    (.seq (.assign .local cclO (.load .one (.op .add [vv cclCs, .op .add [.panop .mul [vv cclI, .const 16], .const 8]])))
    (.seq (.assign .local cclF (.load .one (.op .add [vv cclCs, .op .add [.panop .mul [vv cclI, .const 16], .const 16]])))
    (.seq (.call (some (some (.local, cclX), none)) fCco
        [vv cclTb, vv cclTk, vv cclO, vv cclF, vv cclSl, vv cclSk, vv cclNk, vv cclMs, vv cclDs, vv cclDn])
    (.seq (.call (some (some (.local, ExS.lY), none)) fCcl
        [vv cclCs, .op .add [vv cclI, .const 1], vv cclN, vv cclTb, vv cclTk, vv cclSl, vv cclSk, vv cclNk, vv cclMs,
          vv cclDs, vv cclDn])
      (prependP C cclX)))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure CCLCodes (C : Ctx) : Prop where
  cco : CCOCodes C
  self : C.code.lookup fCcl = some (cclParams.map (fun p => (p, ShapeHOL.one)), cclBody C, .one)

section
variable {σ : Type}

theorem ccl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cclLocals → (ctxEnv C ++ cclParams.zip vals).get x = none :=
  Knot.params_none C cclLocals cclParams vals (by decide) (by decide)

/-- Class constructors, as a block of records. -/
def PostCCs (C : Ctx) (ccs : List ClassCtor) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ PRep C H' o (fun H o cc => CCRep C H o cc) ccs ∧ SR (ctxH C H') s' st

theorem postCCs_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCCs C a w s' st → PostCCs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem ccRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {cc : ClassCtor}
    (h : CCRep C H o cc) : CCRep C H' o cc :=
  let ⟨⟨ocv, a1, a2⟩, b, c, d, e, f⟩ := h
  ⟨⟨ocv, get_prefix a1 hp, cvRep_mono hp a2⟩, get_prefix b hp, get_prefix c hp, get_prefix d hp, get_prefix e hp, f⟩

set_option maxHeartbeats 16000000 in
/-- **`classCtorsOf`** at class `0` from constructor `i` on. -/
theorem ccl_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : CCLCodes C) (p : BlockShape) (formerTys : List EIdx) (rd : ClassRead) (m : TargetMajor)
    (hmm : m.member = some 0) (ms : List MemberShape) (om : Nat) (hms : p.members = ms)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59)
    (cs : List (IConstantVal × Nat)) (oq : Nat) (hcr : CtorsRep C C.H oq cs) (hcsl : cs.length < 2 ^ 58)
    (hnf : ∀ c ∈ cs, c.2 < 2 ^ 56)
    (ot osl pd : Nat) (htl : m.nfs.length < 2 ^ 58) (htb : PRep C C.H ot (fun H o nf => NfRep C H o nf) m.nfs)
    (hsl : rd.slots.length < 2 ^ 58) (hcb : ∀ sl ∈ rd.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63)
    (hsb : SlotBlk C C.H osl rd.slots) (hdl : m.ds.length < 2 ^ 58) (hds : BlkAt C.H pd (m.ds.map Enc.idxW))
    (hnk : p.nP + p.k < 2 ^ 56) :
    ∀ f i (H : List (BitVec 64)) (s : AState), cs.length - i = f → i ≤ cs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cclParams.zip [cellA C oq, BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length,
        cellA C ot, BitVec.ofNat 64 m.nfs.length, cellA C osl, BitVec.ofNat 64 rd.slots.length,
        BitVec.ofNat 64 (p.nP + p.k), cellA C om, cellA C pd, BitVec.ofNat 64 m.ds.length])) (cclBody C) s
        (classCtorsOf mode C.fe p formerTys rd [m] 0 (cs.drop i)) (PostCCs (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = cs.length := by omega
    subst hin
    refine specR_prologue (postCCs_locals _) (ccl_none _ _) ?_
    have hlw := nd_lt_iff cs.length cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    simp only [classCtorsOf]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
        fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < cs.length := by omega
    refine specR_prologue (postCCs_locals _) (ccl_none _ _) ?_
    have hlw := nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, hoc, hcv, hnfe⟩ := hcr.2 i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) cclO _ (oq + 1 + 2 * i) _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; exact cellA_pair1 C oq i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cclF _ (oq + 2 + 2 * i) _ (get_prefix hnfe.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; exact cellA_pair2 C oq i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin]
    simp only [classCtorsOf]
    refine specR_callNIH (C := ctxH C H) cclX fCco ccoParams
      [vv cclTb, vv cclTk, vv cclO, vv cclF, vv cclSl, vv cclSk, vv cclNk, vv cclMs, vv cclDs, vv cclDn] (ccoBody C)
      [cellA C ot, BitVec.ofNat 64 m.nfs.length, cellA C oc, BitVec.ofNat 64 cs[i].2, cellA C osl,
        BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 (p.nP + p.k), cellA C om, cellA C pd, BitVec.ofNat 64 m.ds.length]
      (by decide) rfl (by decide) hc.cco.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], trivial⟩
      (PostCC (ctxH C H)) (fun cc w _ H' => ∃ o, w = cellA C o ∧ CCRep C H' o cc)
      (fun cc w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccoParams _ rfl hlk)
        (cco_spec mode ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.cco) p formerTys rd m hmm ms om hms
          (ptrsRep_mono hp (fun _ _ => memberRep_mono hp) hM) hml cs[i] oc (cvRep_mono hp hcv)
          (hnf cs[i] (List.getElem_mem hin)) ot osl pd htl (pRep_mono hp (fun _ _ => nfRep_mono hp) htb) hsl hcb
          (slotBlk_mono hp hsb) hdl (blkAt_mono hds hp) hnk s))
      (fun cc w s1 H1 hp1 ⟨ox, hw, hrx⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fCcl cclParams
      [vv cclCs, .op .add [vv cclI, .const 1], vv cclN, vv cclTb, vv cclTk, vv cclSl, vv cclSk, vv cclNk, vv cclMs,
        vv cclDs, vv cclDn] (cclBody C)
      [cellA C oq, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length, cellA C ot, BitVec.ofNat 64 m.nfs.length,
        cellA C osl, BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 (p.nP + p.k), cellA C om, cellA C pd,
        BitVec.ofNat 64 m.ds.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], trivial⟩
      (PostCCs (ctxH C H1)) (fun ccs w _ H' => ∃ o, w = cellA C o ∧ PRep C H' o (fun H o cc => CCRep C H o cc) ccs)
      (fun ccs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cclParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun ccs w s2 H2 hp2 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    obtain ⟨oss, hossl, hossb, hossr⟩ := hry
    refine ExPre.prepend_spec C hok (H := H2) cclX (cellA C ox) oy (oss.map (cellA C)) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hossb (by decide)
      (by simp +decide [Env.get_cons, Env.get, cclParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, hp1'.trans (hp2'.trans hp'), rfl,
      ⟨ox :: oss, by simp [hossl], hb, fun j hj hjo => by
        rcases j with _ | j
        · exact ccRep_mono (hp2'.trans hp') hrx
        · exact ccRep_mono hp' (hossr j (by simpa using hj) (by simpa using hjo))⟩, hsr⟩

end

end ConPanqueque.T.Ind
