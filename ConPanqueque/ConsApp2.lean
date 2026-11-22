import ConPanqueque.ConsGeo
import ConRon.Arena.Monad
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsLoop ConPanqueque.ConsIns ConPanqueque.ConsTbl
open ConRon.Arena ConPanqueque.ConsIntern ConPanqueque.ConsProbe ConPanqueque.ConsGeo

/-!
# The two-tier `app` intern, twin side

`EStore.intern` at an `app` view touches only the two tiers' `apps` tables:
the persistent probe (skipped when the scratch tier is on and a child is a
scratch handle), then, with the scratch tier on, `tierApp` on the scratch
table at tier 1, else `tierApp` on the persistent table at tier 0 (whose own
probe repeats the missed one).
-/

namespace ConPanqueque.ConsApp2

abbrev ATbl := Tbl AppNode EIdx UInt64

/-- The `app` arm of `EStore.intern` over the two `apps` tables. -/
def appIntern (P Sc : ATbl) (on sk : Bool) (x : AppNode) (d : UInt64) : ATbl × ATbl × EIdx :=
  match (if on && sk then none else P.find? x) with
  | some h => (P, Sc, h)
  | none =>
    if on then ((P, (tierApp Sc x d 1).1, (tierApp Sc x d 1).2))
    else ((tierApp P x d 0).1, Sc, (tierApp P x d 0).2)

theorem intern_app (st : EStore) (f a : EIdx) :
    st.intern (.app f a) =
      let r := appIntern st.pers.apps st.scr.apps st.scratchOn (EStore.eViewHasScratchChild (.app f a)) ⟨f, a⟩
        (st.derOfView (.app f a))
      ({ st with pers := { st.pers with apps := r.1 }, scr := { st.scr with apps := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, appIntern, ETables.find?, ETables.push, tierApp,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.apps.find? ⟨f, a⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.app f a) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.apps.find? ⟨f, a⟩ <;> simp only
      cases h2 : scr.apps.find? ⟨f, a⟩ <;> simp
    · cases h2 : scr.apps.find? ⟨f, a⟩ <;> simp

/-- On a probe hit, `intern` returns the stored handle and leaves the store alone. -/
theorem intern_app_of_find (st : EStore) (f a h : EIdx) (hf : st.find? (.app f a) = some h) :
    st.intern (.app f a) = (st, h) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.find?, EStore.persFindMaybe, ETables.find?] at hf
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?]
  revert hf
  split <;> simp_all

/-- The monadic `app` intern (probe, capacity test, intern) when the active tier's `apps`
table is below the wide capacity: the store moves as `intern` says. -/
theorem internAppE_ok (s : AState) (f a : EIdx)
    (hcap : (if s.store.scratchOn then s.store.scr.apps.size else s.store.pers.apps.size) < Idx.wideCap) :
    internAppE f a s = .ok ((s.store.intern (.app f a)).2, { s with store := (s.store.intern (.app f a)).1 }) := by
  simp only [internAppE, internE, internNodeE]
  cases hf : s.store.find? (.app f a) with
  | some h =>
    rw [intern_app_of_find _ _ _ _ hf]
    simp [hf, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, Except.bind]
  | none =>
    have hc : (if s.store.scratchOn then s.store.scr.sizeOf (.app f a) else s.store.pers.sizeOf (.app f a)) <
        ENodeView.cap (.app f a) := by
      simpa [ETables.sizeOf, ENodeView.cap] using hcap
    simp [hf, hc, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, set,
      StateT.set, MonadStateOf.set, Except.bind]

/-! ## The Pancake side

`internApp`: with the scratch tier on, the persistent probe (skipped on a
scratch child), then the scratch tier's intern; with it off, the persistent
tier's intern. Each tier's geometry comes from its descriptor (`pgeo`, `sgeo`). -/

def lPg := ofString "pgeo"
def lSg := ofString "sgeo"
def lOn := ofString "son"

def internApp : ProgHOL 64 :=
  .ite (.cmp .notEqual (ConsIntern.vv lOn) (.const 0))
    (.seq (.ite (.cmp .notEqual skE (.const 0)) .skip (withGeo lPg (0 : UInt32).toUInt64.toBitVec probeTier))
          (withGeo lSg (1 : UInt32).toUInt64.toBitVec internTier))
    (withGeo lPg (0 : UInt32).toUInt64.toBitVec internTier)

/-- One tier's geometry: `n = 2^b` slots, `cap` rows, the region's parts, the descriptor. -/
structure Geo where
  n : Nat
  b : Nat
  cap : Nat
  C : BitVec 64
  S : BitVec 64
  R : BitVec 64
  D : BitVec 64
  G : BitVec 64

/-- A tier table represented in memory, with the twin's table and handles at `tier`. -/
structure TierRep {σ : Type} (t : PanSemStateFiniteExact 64 σ) (g : Geo) (tb : ATbl) (rows : List AppNode)
    (ders : List (BitVec 64)) (slots : List Nat) (tier : UInt32) : Prop where
  mem : TMem t encApp rows ders slots g.n g.cap g.C g.S g.R g.D
  inv : Inv (α := AppNode) (homeApp g.b) rows slots g.n
  rel : TblRel tb rows (fun i => Idx.mkWide tier (UInt32.ofNat i))
  der : tb.der.toList.map (·.toBitVec) = ders

def inG (g : Geo) (a : BitVec 64) : Prop := inReg g.C g.D g.cap a

/-- What `internApp` guarantees: a stop, or `appIntern`'s handle with both new tables represented. -/
def ARes {σ : Type} (t : PanSemStateFiniteExact 64 σ) (P Sc : ATbl) (gp gs : Geo) (on sk : Bool) (x : AppNode)
    (dv : UInt64) (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨
    (r.1 = some (.returned (.val (.word (appIntern P Sc on sk x dv).2.2.word.toUInt64.toBitVec))) ∧
      (∃ rp dp sp, TierRep r.2 gp (appIntern P Sc on sk x dv).1 rp dp sp 0) ∧
      (∃ rs ds ss, TierRep r.2 gs (appIntern P Sc on sk x dv).2.1 rs ds ss 1) ∧
      r.2.code = t.code ∧ r.2.globals = t.globals ∧ r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
      ∀ a, ¬ inG gp a → ¬ inG gs a → r.2.memory a = t.memory a)

theorem appIntern_off (P Sc : ATbl) (sk : Bool) (x : AppNode) (d : UInt64) :
    appIntern P Sc false sk x d = ((tierApp P x d 0).1, Sc, (tierApp P x d 0).2) := by
  simp only [appIntern, Bool.false_and, Bool.false_eq_true, ite_false, tierApp]
  cases P.find? x <;> rfl

theorem appIntern_sk (P Sc : ATbl) (x : AppNode) (d : UInt64) :
    appIntern P Sc true true x d = (P, (tierApp Sc x d 1).1, (tierApp Sc x d 1).2) := by
  simp [appIntern]

theorem appIntern_hit (P Sc : ATbl) (x : AppNode) (d : UInt64) (h : EIdx) (hf : P.find? x = some h) :
    appIntern P Sc true false x d = (P, Sc, h) := by
  simp [appIntern, hf]

theorem appIntern_miss (P Sc : ATbl) (x : AppNode) (d : UInt64) (hf : P.find? x = none) :
    appIntern P Sc true false x d = (P, (tierApp Sc x d 1).1, (tierApp Sc x d 1).2) := by
  simp [appIntern, hf]

theorem seq_abort {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p q : ProgHOL 64) (res : PanSemResultExact 64)
    (h : (evaluateHOLFiniteState s p).1 = some res) :
    evaluateHOLFiniteState s (.seq p q) = evaluateHOLFiniteState s p := by
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq p q)]
  generalize hr : evaluateHOLFiniteState s p = r at h
  obtain ⟨r1, r2⟩ := r
  simp only at h; subst h; simp [hr]

theorem pres_mono {σ : Type} {A : List MlS} {y : MlS} {s : PanSemStateFiniteExact 64 σ} {tb : ATbl} {n : Nat}
    {x : AppNode} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : PRes A s tb n x r) : PRes (y :: A) s tb n x r := by
  obtain ⟨m, d, c, g, ta, h | ⟨hf, hr, hc, hfr⟩⟩ := h
  · exact ⟨m, d, c, g, ta, Or.inl h⟩
  · exact ⟨m, d, c, g, ta, Or.inr ⟨hf, hr, hc, fun z hz => hfr z (fun hm => hz (List.mem_cons_of_mem _ hm))⟩⟩

theorem geo_loc {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : AppNode) (g : Geo) (dv tw : BitVec 64)
    (hkf : s.locals.lookup lKf = some (.val (.word (encApp x).1)))
    (hka : s.locals.lookup lKa = some (.val (.word (encApp x).2)))
    (hdv : s.locals.lookup lDv = some (.val (.word dv))) :
    Locals (geoState s g.S g.R g.n g.C g.cap g.D tw) x g.n g.cap g.C g.S g.R g.D dv tw := by
  constructor <;> simp only [geoState] <;>
    repeat (first | exact lookup_setVar_same _ _ _ | rw [lookup_setVar_other _ _ (by decide)])
  · exact hkf
  · exact hka
  · exact hdv

theorem desc_of_eq {σ : Type} {t u : PanSemStateFiniteExact 64 σ} {G S R : BitVec 64} {n : Nat} {C : BitVec 64}
    {cap : Nat} {D : BitVec 64} (h : Desc t G S R n C cap D) (hm : u.memory = t.memory)
    (hd : u.memaddrs = t.memaddrs) : Desc u G S R n C cap D := by
  intro k hk; rw [hm, hd]; exact h k hk

section
variable {σ : Type}

/-- `internTier` in the tier whose descriptor `gn` points at. -/
theorem tier_run (u : PanSemStateFiniteExact 64 σ) (g : Geo) (tb : ATbl) (rows : List AppNode)
    (ders : List (BitVec 64)) (slots : List Nat) (tier : UInt32) (x : AppNode) (dv : UInt64) (gn : MlS)
    (htier : tier ≤ 1) (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hc : g.cap < 2 ^ 30)
    (hR : TierRep u g tb rows ders slots tier) (hd : Desc u g.G g.S g.R g.n g.C g.cap g.D)
    (hg : u.locals.lookup gn = some (.val (.word g.G))) (hgn : gn ≠ lS ∧ gn ≠ lR ∧ gn ≠ lM ∧ gn ≠ lC0 ∧ gn ≠ lCap)
    (hkf : u.locals.lookup lKf = some (.val (.word (encApp x).1)))
    (hka : u.locals.lookup lKa = some (.val (.word (encApp x).2)))
    (hdv : u.locals.lookup lDv = some (.val (.word dv.toBitVec))) (hck : g.n + 2 ≤ u.clock) :
    IRes u tb g.n g.b g.cap g.C g.S g.R g.D x dv tier
      (evaluateHOLFiniteState u (withGeo gn tier.toUInt64.toBitVec internTier)) :=
  withGeo_lift (fun s r => IRes s tb g.n g.b g.cap g.C g.S g.R g.D x dv tier r) (fun _ _ _ _ h => ires_locals _ h)
    u gn g.G g.S g.R g.n g.C g.cap g.D _ internTier hg hgn hd
    (internTier_spec _ tb rows ders slots g.n g.b g.cap g.C g.S g.R g.D x dv tier hn hb hc
      (tmem_of_eq hR.mem rfl rfl) hR.inv hR.rel hR.der htier (geo_loc u x g _ _ hkf hka hdv) hck)

/-- `probeTier` in the tier whose descriptor `gn` points at. -/
theorem probe_run (u : PanSemStateFiniteExact 64 σ) (g : Geo) (tb : ATbl) (rows : List AppNode)
    (ders : List (BitVec 64)) (slots : List Nat) (tier : UInt32) (x : AppNode) (dv : UInt64) (gn : MlS)
    (htier : tier ≤ 1) (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hc : g.cap < 2 ^ 30)
    (hR : TierRep u g tb rows ders slots tier) (hd : Desc u g.G g.S g.R g.n g.C g.cap g.D)
    (hg : u.locals.lookup gn = some (.val (.word g.G))) (hgn : gn ≠ lS ∧ gn ≠ lR ∧ gn ≠ lM ∧ gn ≠ lC0 ∧ gn ≠ lCap)
    (hkf : u.locals.lookup lKf = some (.val (.word (encApp x).1)))
    (hka : u.locals.lookup lKa = some (.val (.word (encApp x).2)))
    (hdv : u.locals.lookup lDv = some (.val (.word dv.toBitVec))) (hck : g.n + 2 ≤ u.clock) :
    PRes [] u tb g.n x (evaluateHOLFiniteState u (withGeo gn tier.toUInt64.toBitVec probeTier)) :=
  withGeo_lift (fun s r => PRes [] s tb g.n x r) (fun _ _ _ _ h => pres_dec (pres_mono h))
    u gn g.G g.S g.R g.n g.C g.cap g.D _ probeTier hg hgn hd
    (probeTier_spec _ tb rows ders slots g.n g.b g.cap g.C g.S g.R g.D x dv.toBitVec tier hn hb hc
      (tmem_of_eq hR.mem rfl rfl) hR.inv hR.rel htier (geo_loc u x g _ _ hkf hka hdv) hck)

/-- A tier table survives memory changes outside its region. -/
theorem tierRep_frame {t t' : PanSemStateFiniteExact 64 σ} {g : Geo} {tb : ATbl} {rows : List AppNode}
    {ders : List (BitVec 64)} {slots : List Nat} {tier : UInt32} (h : TierRep t g tb rows ders slots tier)
    (hm : ∀ a, inG g a → t'.memory a = t.memory a) (hd : t'.memaddrs = t.memaddrs) :
    TierRep t' g tb rows ders slots tier :=
  ⟨tmem_frame h.mem hm hd, h.inv, h.rel, h.der⟩

theorem internApp_spec (t : PanSemStateFiniteExact 64 σ) (P Sc : ATbl) (gp gs : Geo)
    (rp : List AppNode) (dp : List (BitVec 64)) (sp : List Nat)
    (rs : List AppNode) (ds : List (BitVec 64)) (ss : List Nat)
    (on : Bool) (f a : EIdx) (dv : UInt64)
    (hnp : gp.n = 2 ^ gp.b) (hbp : gp.b ≤ 56) (hcp : gp.cap < 2 ^ 30)
    (hns : gs.n = 2 ^ gs.b) (hbs : gs.b ≤ 56) (hcs : gs.cap < 2 ^ 30)
    (hP : TierRep t gp P rp dp sp 0) (hS : TierRep t gs Sc rs ds ss 1)
    (hdp : Desc t gp.G gp.S gp.R gp.n gp.C gp.cap gp.D) (hds : Desc t gs.G gs.S gs.R gs.n gs.C gs.cap gs.D)
    (hdis : ∀ a, inG gp a → ¬ inG gs a)
    (hkf : t.locals.lookup lKf = some (.val (.word (encApp ⟨f, a⟩).1)))
    (hka : t.locals.lookup lKa = some (.val (.word (encApp ⟨f, a⟩).2)))
    (hdv : t.locals.lookup lDv = some (.val (.word dv.toBitVec)))
    (hpg : t.locals.lookup lPg = some (.val (.word gp.G)))
    (hsg : t.locals.lookup lSg = some (.val (.word gs.G)))
    (hon : t.locals.lookup lOn = some (.val (.word (if on then 1 else 0))))
    (hck : gp.n + gs.n + 3 ≤ t.clock) :
    ARes t P Sc gp gs on (EStore.eViewHasScratchChild (.app f a)) ⟨f, a⟩ dv
      (evaluateHOLFiniteState t internApp) := by
  have hpgn : lPg ≠ lS ∧ lPg ≠ lR ∧ lPg ≠ lM ∧ lPg ≠ lC0 ∧ lPg ≠ lCap := by decide
  have hsgn : lSg ≠ lS ∧ lSg ≠ lR ∧ lSg ≠ lM ∧ lSg ≠ lC0 ∧ lSg ≠ lCap := by decide
  have hon' : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .notEqual (ConsIntern.vv lOn) (.const 0)) = some (.val (.word (if on then 1 else 0))) := by
    cases on <;> simp [ConsIntern.vv, evalHOLExact, hon, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  unfold internApp; rw [ite_word t _ _ _ _ hon']
  cases on
  · -- scratch tier off: the persistent tier's intern
    simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    simp only [ARes]; rw [appIntern_off]
    rcases tier_run t gp P rp dp sp 0 ⟨f, a⟩ dv lPg (by decide) hnp hbp hcp hP hdp hpg hpgn hkf hka hdv (by omega) with
      h | ⟨hr, rows', ders', slots', hT', hi', hrel', hd', c1, c2, c3, c4, c5⟩
    · exact Or.inl h
    · refine Or.inr ⟨hr, ⟨rows', ders', slots', hT', hi', hrel', hd'⟩, ⟨rs, ds, ss, tierRep_frame hS
        (fun b hb => c5 b (fun hp => hdis b hp hb)) c3⟩, c1, c2, c3, c4, fun b hb _ => c5 b hb⟩
  · -- scratch tier on
    simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hv : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) skE =
        some (.val (.word (f.word.toUInt64.toBitVec >>> 31 ||| a.word.toUInt64.toBitVec >>> 31))) := by
      simp [skE, ConsIntern.vv, evalHOLExact, evalListHOLExact, hkf, hka, encApp, wordOpHOL, wordOp, valueIsWord,
        valueWord, wordShiftHOL]
      show _ ||| (_ ||| 0#64) = _
      rw [BitVec.or_zero]
    have hskw : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notEqual skE (.const 0)) =
        some (.val (.word (if EStore.eViewHasScratchChild (.app f a) then 1 else 0))) := by
      rw [eval_cmp_of t .notEqual skE (.const 0) _ 0 hv (by simp [evalHOLExact])]
      have := sk_word f a
      cases hsk : EStore.eViewHasScratchChild (.app f a)
      · rw [this.mpr hsk]; rfl
      · have hne : ¬ (f.word.toUInt64.toBitVec >>> 31 ||| a.word.toUInt64.toBitVec >>> 31 = 0) := fun e => by
          rw [this.mp e] at hsk; cases hsk
        have hb : (f.word.toUInt64.toBitVec >>> 31 ||| a.word.toUInt64.toBitVec >>> 31 == 0) = false := by
          simpa using hne
        simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb, Bool.not_false, ite_true]
    -- the scratch tier's intern from a state that agrees with `t`
    have scr : ∀ (sk' : Bool) (u : PanSemStateFiniteExact 64 σ), u.memory = t.memory → u.memaddrs = t.memaddrs →
        u.code = t.code → u.globals = t.globals → u.topAddr = t.topAddr →
        (∀ y, u.locals.lookup y = t.locals.lookup y) → gs.n + 2 ≤ u.clock →
        appIntern P Sc true sk' ⟨f, a⟩ dv = (P, (tierApp Sc ⟨f, a⟩ dv 1).1, (tierApp Sc ⟨f, a⟩ dv 1).2) →
        ARes t P Sc gp gs true sk' ⟨f, a⟩ dv
          (evaluateHOLFiniteState u (withGeo lSg (1 : UInt32).toUInt64.toBitVec internTier)) := by
      intro sk' u m d c g ta hl hc hA
      have hSu : TierRep u gs Sc rs ds ss 1 := tierRep_frame hS (fun b _ => by rw [m]) d
      have hPu : TierRep u gp P rp dp sp 0 := tierRep_frame hP (fun b _ => by rw [m]) d
      rcases tier_run u gs Sc rs ds ss 1 ⟨f, a⟩ dv lSg (by decide) hns hbs hcs hSu (desc_of_eq hds m d)
          (by rw [hl]; exact hsg) hsgn (by rw [hl]; exact hkf) (by rw [hl]; exact hka) (by rw [hl]; exact hdv) hc with
        h | ⟨hr, rows', ders', slots', hT', hi', hrel', hd', c1, c2, c3, c4, c5⟩
      · exact Or.inl h
      · simp only [ARes]; rw [hA]
        refine Or.inr ⟨hr, ⟨rp, dp, sp, tierRep_frame hPu (fun b hb => c5 b (hdis b hb)) c3⟩,
          ⟨rows', ders', slots', hT', hi', hrel', hd'⟩, by rw [c1, c], by rw [c2, g], by rw [c3, d], by rw [c4, ta],
          fun b _ hb => by rw [c5 b hb, m]⟩
    have eite := ite_word t _ .skip (withGeo lPg (0 : UInt32).toUInt64.toBitVec probeTier) _ hskw
    cases hsk : EStore.eViewHasScratchChild (.app f a)
    · -- no scratch child: probe the persistent tier first
      rw [hsk] at eite
      simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at eite
      obtain ⟨m1, d1, c1, g1, ta1, hit | ⟨hf, hr, hc, hfr⟩⟩ := probe_run t gp P rp dp sp 0 ⟨f, a⟩ dv lPg (by decide)
        hnp hbp hcp hP hdp hpg hpgn hkf hka hdv (by omega)
      · obtain ⟨h, hf, hr⟩ := hit
        rw [seq_abort _ _ _ _ (by rw [eite]; exact hr), eite]
        simp only [ARes]; rw [appIntern_hit P Sc _ dv h hf]
        exact Or.inr ⟨hr, ⟨rp, dp, sp, tierRep_frame hP (fun b _ => by rw [m1]) d1⟩,
          ⟨rs, ds, ss, tierRep_frame hS (fun b _ => by rw [m1]) d1⟩, c1, g1, d1, ta1, fun b _ _ => by rw [m1]⟩
      · generalize hq : evaluateHOLFiniteState t (withGeo lPg (0 : UInt32).toUInt64.toBitVec probeTier) = q
          at hr hc hfr m1 d1 c1 g1 ta1 eite
        obtain ⟨q1, u⟩ := q
        simp only at hr; subst hr
        rw [seq_normal _ eite]
        exact scr false u m1 d1 c1 g1 ta1 (fun y => hfr y (by simp)) (by simp only at hc; omega)
          (appIntern_miss P Sc _ dv hf)
    · rw [hsk] at eite
      simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true] at eite
      rw [seq_normal _ (eite.trans (skip_eval t))]
      exact scr true t rfl rfl rfl rfl rfl (fun _ => rfl) (by omega) (appIntern_sk P Sc _ dv)
end

end ConPanqueque.ConsApp2
