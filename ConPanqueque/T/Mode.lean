import ConPanqueque.T.MemoN
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The mode memos: reads and writes through the eager tower

A mode memo's active descriptor is `mG (.m false k) + gEo`: side `false` in plain mode, side `true`
(at offset `EO`) inside an eager comparison. The access code loads `gEo` into the local `meo` first.
-/

namespace ConPanqueque.T

/-- The `EIdx → EIdx` mode memos. -/
inductive ModeKE | whnfCore | whnfCoreCheap | whnf | infer | inferIO
  deriving DecidableEq

def ModeKE.toK : ModeKE → CacheK
  | .whnfCore => .whnfCore | .whnfCoreCheap => .whnfCoreCheap | .whnf => .whnf | .infer => .infer
  | .inferIO => .inferIO

def ModeKE.sel : ModeKE → ModeMemos → Std.HashMap EIdx EIdx
  | .whnfCore, m => m.whnfCoreC | .whnfCoreCheap, m => m.whnfCoreCheapC | .whnf, m => m.whnfC
  | .infer, m => m.inferC | .inferIO, m => m.inferIOC

def ModeKE.updM : ModeKE → ModeMemos → Std.HashMap EIdx EIdx → ModeMemos
  | .whnfCore, m, x => { m with whnfCoreC := x } | .whnfCoreCheap, m, x => { m with whnfCoreCheapC := x }
  | .whnf, m, x => { m with whnfC := x } | .infer, m, x => { m with inferC := x }
  | .inferIO, m, x => { m with inferIOC := x }

/-- The twin's write of the active table. -/
def ModeKE.upd : ModeKE → Caches → Std.HashMap EIdx EIdx → Caches
  | .whnfCore, c, x => { c with whnfCoreC := x } | .whnfCoreCheap, c, x => { c with whnfCoreCheapC := x }
  | .whnf, c, x => { c with whnfC := x } | .infer, c, x => { c with inferC := x }
  | .inferIO, c, x => { c with inferIOC := x }

theorem ModeKE.upd_mode (k : ModeKE) (c : Caches) (x : Std.HashMap EIdx EIdx) :
    (k.upd c x).modeMemos = k.updM c.modeMemos x := by cases k <;> rfl

theorem ModeKE.upd_eager (k : ModeKE) (c : Caches) (x : Std.HashMap EIdx EIdx) :
    (k.upd c x).eagerMemos = c.eagerMemos := by cases k <;> rfl

theorem ModeKE.sel_updM (k : ModeKE) (m : ModeMemos) (x : Std.HashMap EIdx EIdx) : k.sel (k.updM m x) = x := by
  cases k <;> rfl

section
variable {σ : Type}

theorem ModeKE.cacheAt_upd (k : ModeKE) (t : PState σ) (C : Ctx) (c : Caches) (x : Std.HashMap EIdx EIdx)
    (k' : CacheK) : CacheAt t C (k.upd c x) k' = CacheAt t C c k' := by cases k <;> cases k' <;> rfl

theorem cacheAtM_sel (k : ModeKE) (t : PState σ) (C : Ctx) (b : Bool) (m : ModeMemos) :
    CacheAtM t C b m k.toK = MemoAtG encN Enc.idxW t (C.mG (.m b k.toK)) (C.mg (.m b k.toK)) (k.sel m) := by
  cases k <;> rfl

theorem cacheAtM_updM_ne (k : ModeKE) (k' : CacheK) (h : k' ≠ k.toK) (t : PState σ) (C : Ctx) (b : Bool)
    (m : ModeMemos) (x : Std.HashMap EIdx EIdx) : CacheAtM t C b (k.updM m x) k' = CacheAtM t C b m k' := by
  cases k <;> cases k' <;> first | rfl | exact absurd rfl h

theorem cacheAtM_frame {C : Ctx} {mm : ModeMemos} {t u : PState σ} {b : Bool} {k : CacheK}
    (h : CacheAtM t C b mm k) (hm : ∀ c, inR (C.mg (.m b k)) c → u.memory c = t.memory c)
    (hdsc : ∀ j, j < 8 → u.memory (C.mG (.m b k) + BitVec.ofNat 64 (8 * j)) =
      t.memory (C.mG (.m b k) + BitVec.ofNat 64 (8 * j)))
    (hd : u.memaddrs = t.memaddrs) : CacheAtM u C b mm k := by
  cases k <;> first | trivial | exact memoAtG_frame h hm hdsc hd

theorem mG_side {C : Ctx} (hok : CtxOK C) (k : CacheK) : C.mG (.m false k) + C.eo = C.mG (.m C.side k) := by
  unfold Ctx.eo Ctx.side
  cases C.saved with
  | none => simp
  | some _ => simp [hok.eoSide k]

/-- A write to the active side's table `k` (descriptor and region; nothing else of the memos). -/
theorem modeAt_set {C : Ctx} (hok : CtxOK C) {cs : Caches} {t u : PState σ} (h : ModeAt t C cs) (k : ModeKE)
    (x : Std.HashMap EIdx EIdx)
    (hmem : MemoAtG encN Enc.idxW u (C.mG (.m C.side k.toK)) (C.mg (.m C.side k.toK)) x)
    (hfr : ∀ c, ¬ inR (C.mg (.m C.side k.toK)) c → u.memory c = t.memory c)
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals.lookup gEo = t.globals.lookup gEo) :
    ModeAt u C (k.upd cs x) := by
  obtain ⟨g, h1, h2⟩ := h
  have fr : ∀ b k', (Region.m b k' ≠ Region.m C.side k.toK) → ∀ mm, CacheAtM t C b mm k' → CacheAtM u C b mm k' :=
    fun b k' hne mm hc => cacheAtM_frame hc (fun c hc' => hfr c (hok.memoDis _ _ c hne hc'))
      (fun j hj => hfr _ (hok.mdescMemo _ _ j hj)) hd
  refine ⟨by rw [hg]; exact g, ?_, ?_⟩
  · rw [k.upd_mode]
    intro k'
    by_cases e : k' = k.toK
    · subst e; rw [cacheAtM_sel, ModeKE.sel_updM]; exact hmem
    · rw [cacheAtM_updM_ne k k' e]
      exact fr _ k' (fun x => e (by injection x)) _ (h1 k')
  · rw [k.upd_eager]
    revert h2 fr
    unfold Ctx.side
    cases C.saved with
    | none =>
      intro h2 fr k'
      exact fr true k' (by simp) _ (h2 k')
    | some mm =>
      intro ⟨h2, h3⟩ fr
      exact ⟨fun k' => fr false k' (by simp) _ (h2 k'), h3⟩

/-- `x := global g`, the global's value known from `SR`. -/
theorem specR_assignGI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x g : MlS) (v : BitVec 64) (hx : x ∈ D)
    (hg : ∀ u : PState σ, SR C s u → u.globals.lookup g = some (.val (.word v)))
    (h : SpecR (Inv C s ((x, v) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.var .global g)) rest) s m R :=
  specR_pre_assign x _ (fun _ => v) (fun t ht => eval_gv t g v (hg t ht.sr)) (fun t ht => ht.decl x hx)
    (fun t ht => inv_set ht x v) h

def lEo := ofString "meo"

/-- The active descriptor of mode memo `k`. -/
def modeD (C : Ctx) (k : CacheK) : ExpHOL 64 := .op .add [.const (C.mG (.m false k)), vv lEo]

/-- `meo := gEo; KB[0] := eh; x := memoGet(desc k, 1); rest`. -/
def modeGetP (C : Ctx) (k : CacheK) (x : MlS) (eh : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lEo (.var .global gEo))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eh)
      (.seq (.call (some (some (.local, x), none)) fMemoGet [modeD C k, .const 1]) rest))

/-- `meo := gEo; KB[0] := eh; x := memoSet(desc k, 1, ev); rest`. -/
def modeSetP (C : Ctx) (k : CacheK) (x : MlS) (eh ev : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lEo (.var .global gEo))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eh)
      (.seq (.call (some (some (.local, x), none)) fMemoSet [modeD C k, .const 1, ev]) rest))

theorem sev_modeD {C : Ctx} (hok : CtxOK C) (k : CacheK) (Γ : Env) :
    sev ((lEo, C.eo) :: Γ) (modeD C k) = some (C.mG (.m C.side k)) := by
  simp only [modeD, sev, Env.get, if_pos rfl]
  rw [← mG_side hok k]; rfl

theorem get_kb_eo {Γ : Env} {C : Ctx} (hkb : Γ.get lKb = some C.KB) : Env.get ((lEo, C.eo) :: Γ) lKb = some C.KB := by
  simp only [Env.get]; rw [if_neg (by decide)]; exact hkb

/-- A twin read of mode memo `k`, in a caller. -/
theorem specR_modeGetI {β : Type} {C : Ctx} (hok : CtxOK C) (k : ModeKE) (getOp : EIdx → AM (Option EIdx))
    (hget : ∀ e s, getOp e s = .ok ((k.sel s.caches.modeMemos)[e]?, s))
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k' : Option EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eh : ExpHOL 64) (h : EIdx) (hx : x ∈ D) (heo : lEo ∈ D)
    (heh : sev ((lEo, C.eo) :: Γ) eh = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ r, SpecR (Inv C s ((x, optW r) :: (lEo, C.eo) :: Γ) [] D) rest s (k' r) R) :
    SpecR (Inv C s Γ M D) (modeGetP C k.toK x eh rest) s (getOp h >>= k') R := by
  refine specR_assignGI lEo gEo C.eo heo (fun u hu => hu.mode.1) ?_
  refine specR_storeKBI hok 0 (by decide) eh (Enc.idxW h) heh (get_kb_eo hkb) ?_
  refine specR_call2IM x fMemoGet pG pLen (by decide) (modeD C k.toK) (.const 1) memoGetBody
    (C.mG (.m C.side k.toK)) 1 hx hcodeG (sev_modeD hok _ _) rfl
    (fun a w s' st => s' = s ∧ w = optW a ∧ SR C s st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2.2)
    (fun u hsr hM h1 h2 => ?_) (fun a w s' st hp => by obtain ⟨rfl, rfl, _⟩ := hp; exact hk a)
  have hW : Words u C.KB (encN h) := by
    intro j hj
    have e : j = 0 := by simp [encN] at hj; omega
    subst e; exact hM _ _ (by simp [encN])
  have hma := hsr.mode.2.1 k.toK
  rw [cacheAtM_sel] at hma
  have G := memoGet_spec (σ := σ) (α := Unit) (C.mG (.m C.side k.toK)) C.KB (C.mg (.m C.side k.toK)) encN_inj
    (k.sel s.caches.modeMemos) h s u hma hW (by simp [encN]) hsr.gkb h1 h2 (by rw [hsr.code]; exact hcodeP)
  refine specR_congr (hget h s) (specR_mono G (fun v hv => hv) (fun a w s' st hp => ?_))
  obtain ⟨hs, hw, hm, hd', hg, hc⟩ := hp
  exact ⟨hs, hw, sr_of_eq hsr hm hd' hg hc⟩

/-- The state after the twin's write of mode memo `k` at `e ↦ r`. -/
def modeSetS (k : ModeKE) (s : AState) (e r : EIdx) : AState :=
  { s with caches := k.upd s.caches ((k.sel s.caches.modeMemos).insert e r) }

/-- A twin write of mode memo `k`, in a caller. -/
theorem specR_modeSetI {β : Type} {C : Ctx} (hok : CtxOK C) (k : ModeKE) (setOp : EIdx → EIdx → AM Unit)
    (hset : ∀ e r s, setOp e r s = .ok ((), modeSetS k s e r))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k' : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eh ev : ExpHOL 64) (h r : EIdx) (hx : x ∈ D) (heo : lEo ∈ D)
    (heh : sev ((lEo, C.eo) :: Γ) eh = some (Enc.idxW h)) (hev : sev ((lEo, C.eo) :: Γ) ev = some (Enc.idxW r))
    (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv C (modeSetS k s h r) ((x, w) :: (lEo, C.eo) :: Γ) [] D) rest (modeSetS k s h r) (k' ()) R) :
    SpecR (Inv C s Γ M D) (modeSetP C k.toK x eh ev rest) s (setOp h r >>= k') R := by
  refine specR_assignGI lEo gEo C.eo heo (fun u hu => hu.mode.1) ?_
  refine specR_storeKBI hok 0 (by decide) eh (Enc.idxW h) heh (get_kb_eo hkb) ?_
  refine specR_call3IM x fMemoSet pG pLen pVal (by decide) (by decide) (by decide) (modeD C k.toK) (.const 1) ev
    memoSetBody (C.mG (.m C.side k.toK)) 1 (Enc.idxW r) hx hcodeS (sev_modeD hok _ _) rfl hev
    (fun _ _ s'' st => s'' = modeSetS k s h r ∧ SR C (modeSetS k s h r) st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2)
    (fun u hsr hM h1 h2 h3 => ?_) (fun a w s'' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk w)
  have hW : Words u C.KB (encN h) := by
    intro j hj
    have e : j = 0 := by simp [encN] at hj; omega
    subst e; exact hM _ _ (by simp [encN])
  have hma := hsr.mode.2.1 k.toK
  rw [cacheAtM_sel] at hma
  have S := memoSet_spec (σ := σ) (C.mG (.m C.side k.toK)) C.KB (C.mg (.m C.side k.toK)) encN_inj
    (k.sel s.caches.modeMemos) h r s u hma hW (by simp [encN])
    (fun j hj => hok.kbMemo _ j (by simp [encN] at hj; omega)) (fun j hj => hok.mdescMemo _ _ j hj)
    hsr.gkb h1 h2 h3 (by rw [hsr.code]; exact hcodeI)
  intro t ht
  rcases S t ht with hs | ⟨w, hr', _, s'', _, hp⟩
  · exact Or.inl hs
  obtain ⟨_, hmem, hfr, hd', hg, hc⟩ := hp
  subst ht
  have rg : Region.m C.side k.toK = Region.m C.side k.toK := rfl
  refine Or.inr ⟨w, hr', (), modeSetS k s h r, hset h r s, rfl, ⟨srep_frame hsr.rep
      ⟨hfr _ (hok.flMemo _ _ (Or.inl rfl)), hfr _ (hok.flMemo _ _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo _ _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo _ _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd'
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo _ kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut _ c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩),
    by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll, by rw [hg]; exact hsr.gfls,
    by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd']; exact hsr.kbuf j hj,
    fun mk => memoAt_frame (hsr.memo mk) (fun c hc => hfr c (hok.memoDis (.e mk) _ c (by simp) hc))
      (fun kk hkk => hfr _ (hok.mdescMemo _ (.e mk) kk hkk)) hd',
    fun nk => memoAtN_frame (hsr.memoN nk) (fun c hc => hfr c (hok.memoDis (.n nk) _ c (by simp) hc))
      (fun kk hkk => hfr _ (hok.mdescMemo _ (.n nk) kk hkk)) hd',
    fun ck => by
      show CacheAt _ C (k.upd s.caches _) ck
      rw [ModeKE.cacheAt_upd]
      exact cacheAt_frame (hsr.cache ck) (fun c hc => hfr c (hok.memoDis (.c ck) _ c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo _ (.c ck) kk hkk)) hd',
    modeAt_set hok hsr.mode k _ hmem hfr hd' (by rw [hg]),
    envAt_frame hsr.env (fun b c hc => hfr c (hok.memoDis (envR b) _ c (by simp) hc))
      (fun b kk hkk => hfr _ (hok.mdescMemo _ (envR b) kk hkk)) (fun i hi => hfr _ (hok.envMemo _ i hi)) hd'
      ⟨by rw [hg], by rw [hg]⟩, hsr.pins,
    heapEx_frame hsr.heap (fun i hi => hfr _ (hok.heapMemo _ i hi)) hd' (by rw [hg]), hsr.twf, hsr.envd, hsr.floor, cachesOK_congr hsr.cok rfl (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> cases k <;> rfl)⟩⟩

end

end ConPanqueque.T
