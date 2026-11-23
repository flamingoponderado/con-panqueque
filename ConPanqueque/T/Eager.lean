import ConPanqueque.T.Mode
import ConPanqueque.T.Loop
import ConRon.Arena.Core
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The eager tower's switches

The twin's `enterEager`/`leaveEager` move six tables between the active fields and the eager slot. The
port moves nothing: it flips `gEo` between `0` and `EO`, which selects the side the mode-memo code
addresses, and the context records the plain memos the twin's caller holds (`Ctx.saved`).

In the port the twin's `eager` flag is `gEo ≠ 0`; code tests it instead of carrying it.
-/

namespace ConPanqueque.T

/-- The twin state after `enterEager false`. -/
def eagerIn (s : AState) : AState :=
  let c := s.caches
  let em := c.eagerMemos
  { s with caches :=
      { c with whnfCoreC := em.whnfCoreC, whnfCoreCheapC := em.whnfCoreCheapC,
               whnfC := em.whnfC, inferC := em.inferC, inferIOC := em.inferIOC,
               defeqC := em.defeqC, eagerMemos := ModeMemos.empty } }

/-- The twin state after `leaveEager (some mm)`. -/
def eagerOut (s : AState) (mm : ModeMemos) : AState :=
  let c := s.caches
  { s with caches :=
      { c with eagerMemos := c.modeMemos,
               whnfCoreC := mm.whnfCoreC, whnfCoreCheapC := mm.whnfCoreCheapC,
               whnfC := mm.whnfC, inferC := mm.inferC, inferIOC := mm.inferIOC,
               defeqC := mm.defeqC } }

theorem enterEager_false_run (s : AState) : enterEager false s = .ok (some s.caches.modeMemos, eagerIn s) := rfl
theorem enterEager_true_run (s : AState) : enterEager true s = .ok (none, s) := rfl
theorem leaveEager_some_run (s : AState) (mm : ModeMemos) : leaveEager (some mm) s = .ok ((), eagerOut s mm) := rfl
theorem leaveEager_none_run (s : AState) : leaveEager none s = .ok ((), s) := rfl

section
variable {σ : Type}

theorem specR_runBind {α β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s s1 : AState} {m : AM α} {a : α}
    {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (hrun : m s = .ok (a, s1))
    (h : SpecR P c s1 (k a) R) : SpecR P c s (m >>= k) R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, b, s', hm, hq⟩
  · exact Or.inl hs
  · refine Or.inr ⟨w, hr, b, s', ?_, hq⟩
    show (do let r ← m s; match r with | (a, s) => k a s) = _
    rw [hrun]; exact hm

theorem modeAt_none {C : Ctx} {t : PState σ} {cs : Caches} (hsv : C.saved = none) (h : ModeAt t C cs) :
    t.globals.lookup gEo = some (.val (.word 0)) ∧ SideAt t C false cs.modeMemos ∧ SideAt t C true cs.eagerMemos := by
  unfold ModeAt Ctx.eo Ctx.side at h
  rw [hsv] at h
  exact h

theorem modeAt_some {C : Ctx} {t : PState σ} {cs : Caches} {mm : ModeMemos} (hsv : C.saved = some mm)
    (h : ModeAt t C cs) :
    t.globals.lookup gEo = some (.val (.word C.EO)) ∧ SideAt t C true cs.modeMemos ∧ SideAt t C false mm ∧
      cs.eagerMemos = ModeMemos.empty := by
  unfold ModeAt Ctx.eo Ctx.side at h
  rw [hsv] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem sideAt_ctx {C : Ctx} {t u : PState σ} {b : Bool} {mm : ModeMemos} (sv : Option ModeMemos)
    (h : SideAt t C b mm) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) :
    SideAt u { C with saved := sv } b mm :=
  sideAt_frame (C := C) h (fun _ _ _ => by rw [hm]) (fun _ _ _ => by rw [hm]) hd

/-- Rebuilding `SR` after a change of the eager tower: only `gEo`, the context's saved memos and the
mode memos may change. -/
theorem sr_mode {C : Ctx} {s s' : AState} {t u : PState σ} (sv : Option ModeMemos) (h : SR C s t)
    (hst : s'.store = s.store) (hme : s'.memos = s.memos) (hpn : s'.pins = s.pins)
    (hfix : s'.caches.constTyC = s.caches.constTyC ∧ s'.caches.constValC = s.caches.constValC ∧
      s'.caches.ruleBodyC = s.caches.ruleBodyC)
    (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code)
    (hgl : ∀ y, y ≠ gEo → u.globals.lookup y = t.globals.lookup y)
    (hmode : ModeAt u { C with saved := sv } s'.caches) : SR { C with saved := sv } s' u := by
  obtain ⟨e7, e8, e9⟩ := hfix
  have hrep : SRep u C.L C.FLn C.FLl C.FLs C.FLe s'.store := by
    rw [hst]
    exact srep_frame h.rep ⟨by rw [hm], by rw [hm], by rw [hm], by rw [hm]⟩ hd
      (fun _ _ _ _ => ⟨fun _ _ => by rw [hm], fun _ _ => by rw [hm]⟩)
  refine ⟨hrep,
    by rw [hgl _ (by decide)]; exact h.gdir, by rw [hgl _ (by decide)]; exact h.gfln,
    by rw [hgl _ (by decide)]; exact h.gfll, by rw [hgl _ (by decide)]; exact h.gfls,
    by rw [hgl _ (by decide)]; exact h.gfle, by rw [hgl _ (by decide)]; exact h.gkb, by rw [hc]; exact h.code,
    fun j hj => by rw [hd]; exact h.kbuf j hj,
    fun k => by rw [hme]; exact memoAt_of_eq (h.memo k) hm hd,
    fun k => by rw [hme]; exact memoAtN_frame (h.memoN k) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd,
    fun k => ?_, hmode,
    envAt_frame h.env (fun _ _ _ => by rw [hm]) (fun _ _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd
      ⟨hgl _ (by decide), hgl _ (by decide)⟩, (hpn.trans h.pins), heapEx_frame h.heap (fun _ _ => by rw [hm]) hd (hgl _ (by decide))⟩
  have := cacheAt_frame (h.cache k) (u := u) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd
  cases k <;> simp only [CacheAt] at this ⊢ <;> first | trivial | (rw [e7]; exact this) | (rw [e8]; exact this) |
    (rw [e9]; exact this)

theorem setG_locals (t : PState σ) (g : MlS) (v : ValueHOL 64) :
    (setKvarHOLFinite .global g v t).locals = t.locals := rfl
theorem setG_memory (t : PState σ) (g : MlS) (v : ValueHOL 64) :
    (setKvarHOLFinite .global g v t).memory = t.memory := rfl
theorem setG_memaddrs (t : PState σ) (g : MlS) (v : ValueHOL 64) :
    (setKvarHOLFinite .global g v t).memaddrs = t.memaddrs := rfl
theorem setG_code (t : PState σ) (g : MlS) (v : ValueHOL 64) :
    (setKvarHOLFinite .global g v t).code = t.code := rfl
theorem setG_same (t : PState σ) (g : MlS) (v : ValueHOL 64) :
    (setKvarHOLFinite .global g v t).globals.lookup g = some v := by
  simp [setKvarHOLFinite, setGlobalHOLFinite, FUPDATE]
theorem setG_other (t : PState σ) (g y : MlS) (v : ValueHOL 64) (h : y ≠ g) :
    (setKvarHOLFinite .global g v t).globals.lookup y = t.globals.lookup y := by
  simp [setKvarHOLFinite, setGlobalHOLFinite, FUPDATE, Ne.symm h]

/-- `gEo := v`, switching the context's saved memos and the twin state. -/
theorem step_setEo {C : Ctx} {s s' : AState} {Γ : Env} {M : Mem} {D : List MlS} (sv : Option ModeMemos)
    (v : BitVec 64) (hst : s'.store = s.store) (hme : s'.memos = s.memos) (hpn : s'.pins = s.pins)
    (hfix : s'.caches.constTyC = s.caches.constTyC ∧ s'.caches.constValC = s.caches.constValC ∧
      s'.caches.ruleBodyC = s.caches.ruleBodyC)
    (hmode : ∀ t : PState σ, SR C s t →
      ModeAt (setKvarHOLFinite .global gEo (.val (.word v)) t) { C with saved := sv } s'.caches) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .global gEo (.const v)) (Inv { C with saved := sv } s' Γ M D) := by
  intro t ht
  have g := ht.sr.mode.1
  rw [assign_ok t .global gEo _ (.val (.word v)) (eval_const t v)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, g, shapeOfHOLExact, shapeEqHOL])]
  refine Or.inr ⟨rfl, ⟨sr_mode sv ht.sr hst hme hpn hfix (setG_memory t _ _) (setG_memaddrs t _ _) (setG_code t _ _)
    (fun y hy => setG_other t _ y _ hy) (hmode t ht.sr), fun y w hy => ?_, fun a w ha => ?_, fun y hy => ?_⟩⟩
  · rw [setG_locals]; exact ht.env y w hy
  · rw [setG_memory, setG_memaddrs]; exact ht.mem a w ha
  · rw [setG_locals]; exact ht.decl y hy

def lSaved := ofString "msv"

/-- `meo := gEo; if meo then x := 0 else (gEo := EO; x := 1)`: the twin's `enterEager`, its result
`some`/`none` as `1`/`0`. -/
def enterBlk (C : Ctx) (x : MlS) : ProgHOL 64 :=
  .seq (.assign .local lEo (.var .global gEo))
    (.ite (vv lEo) (.assign .local x (.const 0))
      (.seq (.assign .global gEo (.const C.EO)) (.assign .local x (.const 1))))

/-- `if e then gEo := 0`: the twin's `leaveEager`. -/
def leaveBlk (e : ExpHOL 64) : ProgHOL 64 := .ite e (.assign .global gEo (.const 0)) .skip

theorem eo_none {C : Ctx} (h : C.saved = none) : C.eo = 0 := by simp [Ctx.eo, h]
theorem eo_some {C : Ctx} {mm : ModeMemos} (h : C.saved = some mm) : C.eo = C.EO := by simp [Ctx.eo, h]

/-- `enterEager false` from plain mode: the context now saves the plain memos. -/
theorem specR_enterPlainI {β : Type} {C : Ctx} (hok : CtxOK C) (hsv : C.saved = none) {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Option ModeMemos → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (hx : x ∈ D) (heo : lEo ∈ D)
    (hk : SpecR (Inv { C with saved := some s.caches.modeMemos } (eagerIn s) ((x, 1) :: (lEo, 0) :: Γ) M D) rest
      (eagerIn s) (k (some s.caches.modeMemos)) R) :
    SpecR (Inv C s Γ M D) (.seq (enterBlk C x) rest) s (enterEager false >>= k) R := by
  refine specR_runBind (enterEager_false_run s) (specR_step ?_ hk)
  refine step_seq (step_mono (Q := Inv C s ((lEo, 0) :: Γ) M D) ?_ (fun _ h => h) (fun _ h => h)) ?_
  · intro t ht
    obtain ⟨w0, h0⟩ := ht.decl lEo heo
    have g := (modeAt_none hsv ht.sr.mode).1
    rw [ConsLoop.assign_local t lEo _ 0 w0 (eval_gv t gEo 0 g) h0]
    exact Or.inr ⟨rfl, inv_set ht lEo 0⟩
  intro t ht
  rw [ite_word t (vv lEo) _ _ 0 (inv_ev ht (by simp [sev, Env.get])), if_neg (by simp)]
  refine step_seq (step_setEo (s := s) (s' := eagerIn s) (some s.caches.modeMemos) C.EO rfl rfl rfl ⟨rfl, rfl, rfl⟩ (fun u hu => ?_))
    (step_assignI x (.const 1) 1 hx rfl) t ht
  obtain ⟨_, h1, h2⟩ := modeAt_none hsv hu.mode
  refine ⟨setG_same u _ _, ?_, ?_⟩
  · exact sideAt_ctx _ h2 (setG_memory u _ _) (setG_memaddrs u _ _)
  · exact ⟨sideAt_ctx _ h1 (setG_memory u _ _) (setG_memaddrs u _ _), rfl⟩

/-- `enterEager true` inside an eager comparison: nothing moves. -/
theorem specR_enterEagerI {β : Type} {C : Ctx} (hok : CtxOK C) {mm : ModeMemos} (hsv : C.saved = some mm)
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Option ModeMemos → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (hx : x ∈ D) (heo : lEo ∈ D)
    (hk : SpecR (Inv C s ((x, 0) :: (lEo, C.EO) :: Γ) M D) rest s (k none) R) :
    SpecR (Inv C s Γ M D) (.seq (enterBlk C x) rest) s (enterEager true >>= k) R := by
  refine specR_runBind (enterEager_true_run s) (specR_step ?_ hk)
  refine step_seq (step_mono (Q := Inv C s ((lEo, C.EO) :: Γ) M D) ?_ (fun _ h => h) (fun _ h => h)) ?_
  · intro t ht
    obtain ⟨w0, h0⟩ := ht.decl lEo heo
    have g := (modeAt_some hsv ht.sr.mode).1
    rw [ConsLoop.assign_local t lEo _ C.EO w0 (eval_gv t gEo _ g) h0]
    exact Or.inr ⟨rfl, inv_set ht lEo C.EO⟩
  intro t ht
  rw [ite_word t (vv lEo) _ _ C.EO (inv_ev ht (by simp [sev, Env.get])), if_pos hok.eoNe]
  exact step_assignI x (.const 0) 0 hx rfl t ht

/-- `leaveEager (some mm)` back to plain mode. -/
theorem specR_leaveSomeI {β : Type} {C : Ctx} (hok : CtxOK C) {mm : ModeMemos} (hsv : C.saved = some mm)
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64) (w : BitVec 64) (he : sev Γ e = some w)
    (hw : w ≠ 0)
    (hk : SpecR (Inv { C with saved := none } (eagerOut s mm) Γ M D) rest (eagerOut s mm) (k ()) R) :
    SpecR (Inv C s Γ M D) (.seq (leaveBlk e) rest) s (leaveEager (some mm) >>= k) R := by
  refine specR_runBind (leaveEager_some_run s mm) (specR_step ?_ hk)
  intro t ht
  rw [leaveBlk, ite_word t e _ _ w (inv_ev ht he), if_pos hw]
  refine step_setEo (s := s) (s' := eagerOut s mm) none 0 rfl rfl rfl ⟨rfl, rfl, rfl⟩ (fun u hu => ?_) t ht
  obtain ⟨_, h1, h2, _⟩ := modeAt_some hsv hu.mode
  refine ⟨setG_same u _ _, ?_, ?_⟩
  · exact sideAt_ctx _ h2 (setG_memory u _ _) (setG_memaddrs u _ _)
  · exact sideAt_ctx _ h1 (setG_memory u _ _) (setG_memaddrs u _ _)

/-- `leaveEager none`: nothing moves. -/
theorem specR_leaveNoneI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {k : Unit → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64)
    (he : sev Γ e = some 0) (hk : SpecR (Inv C s Γ M D) rest s (k ()) R) :
    SpecR (Inv C s Γ M D) (.seq (leaveBlk e) rest) s (leaveEager none >>= k) R := by
  refine specR_runBind (leaveEager_none_run s) (specR_step ?_ hk)
  intro t ht
  rw [leaveBlk, ite_word t e _ _ 0 (inv_ev ht he), if_neg (by simp)]
  exact Or.inr ⟨by rw [evaluateHOLFiniteState_eq_evaluate_def], by rw [evaluateHOLFiniteState_eq_evaluate_def]; exact ht⟩

end

end ConPanqueque.T
