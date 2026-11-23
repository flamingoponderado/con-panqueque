import ConPanqueque.T.Eager
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Generic memo reads and writes, the key already in the key buffer

`specR_memoGetGI`/`specR_memoSetGI` work for any table `MemoAtG enc valW` that `SR` provides; the caller
stores the key words first (`specR_storeKBI`/`specR_storeKB2I`), and for a write supplies how `SR` is
rebuilt after the table's region changes (`sr_upd_mode` for a mode memo, `sr_upd_fix` for a fixed cache).
-/

namespace ConPanqueque.T

section
variable {σ : Type} {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
  {enc : K → List (BitVec 64)} {valW : V → BitVec 64}

theorem specR_memoGetGI {β : Type} {C : Ctx} (hinj : ∀ x y, enc x = enc y → x = y)
    (G : BitVec 64) (g : VGeo) (m : Std.HashMap K V) (key : K) (getOp : AM (Option V)) {s : AState}
    (hget : getOp s = .ok (m[key]?, s))
    (hmem : ∀ u : PState σ, SR C s u → MemoAtG enc valW u G g m)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Option V → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eG eL : ExpHOL 64) (hx : x ∈ D) (heG : sev Γ eG = some G)
    (heL : sev Γ eL = some (BitVec.ofNat 64 (enc key).length)) (hkl : (enc key).length < 2 ^ 61)
    (hW : ∀ u : PState σ, (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) → Words u C.KB (enc key))
    (hk : SpecR (Inv C s ((x, optWG valW m[key]?) :: Γ) [] D) rest s (k m[key]?) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fMemoGet [eG, eL]) rest) s (getOp >>= k) R := by
  refine specR_call2IM x fMemoGet pG pLen (by decide) eG eL memoGetBody G
    (BitVec.ofNat 64 (enc key).length) hx hcodeG heG heL
    (fun a w s' st => a = m[key]? ∧ s' = s ∧ w = optWG valW a ∧ SR C s st)
    (fun _ _ _ _ hp => by rw [hp.2.1]; exact hp.2.2.2)
    (fun u hsr hM h1 h2 => ?_) (fun a w s' st hp => by obtain ⟨rfl, rfl, rfl, _⟩ := hp; exact hk)
  have G' := memoGet_spec (σ := σ) (α := Unit) G C.KB g hinj m key s u (hmem u hsr) (hW u hM) hkl hsr.gkb h1 h2
    (by rw [hsr.code]; exact hcodeP)
  refine specR_congr hget (specR_mono (specR_run G') (fun v hv => hv) (fun a w s' st hp => ?_))
  obtain ⟨hrun, hs, hw, hm, hd', hg, hc⟩ := hp
  have ha : a = m[key]? := by
    simp only [pure, StateT.pure, Except.pure] at hrun; cases hrun; rfl
  exact ⟨ha, hs, hw, sr_of_eq hsr hm hd' hg hc⟩

theorem specR_memoSetGI {β : Type} {C : Ctx} (hinj : ∀ x y, enc x = enc y → x = y)
    (G : BitVec 64) (g : VGeo) (m : Std.HashMap K V) (key : K) (v : V) (setOp : AM Unit) {s s' : AState}
    (hset : setOp s = .ok ((), s'))
    (hmem : ∀ u : PState σ, SR C s u → MemoAtG enc valW u G g m)
    (hKout : ∀ i, i < (enc key).length → ¬ inR g (C.KB + BitVec.ofNat 64 (8 * i)))
    (hGout : ∀ j, j < 8 → ¬ inR g (G + BitVec.ofNat 64 (8 * j)))
    (hsr' : ∀ u u' : PState σ, SR C s u → MemoAtG enc valW u' G g (m.insert key v) →
      (∀ c, ¬ inR g c → u'.memory c = u.memory c) → u'.memaddrs = u.memaddrs → u'.globals = u.globals →
      u'.code = u.code → SR C s' u')
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eG eL ev : ExpHOL 64) (hx : x ∈ D) (heG : sev Γ eG = some G)
    (heL : sev Γ eL = some (BitVec.ofNat 64 (enc key).length)) (hev : sev Γ ev = some (valW v))
    (hkl : (enc key).length < 2 ^ 61)
    (hW : ∀ u : PState σ, (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) → Words u C.KB (enc key))
    (hk : ∀ w, SpecR (Inv C s' ((x, w) :: Γ) [] D) rest s' (k ()) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fMemoSet [eG, eL, ev]) rest) s
      (setOp >>= k) R := by
  refine specR_call3IM x fMemoSet pG pLen pVal (by decide) (by decide) (by decide) eG eL ev memoSetBody G
    (BitVec.ofNat 64 (enc key).length) (valW v) hx hcodeS heG heL hev
    (fun _ _ s'' st => s'' = s' ∧ SR C s' st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2)
    (fun u hsr hM h1 h2 h3 => ?_) (fun a w s'' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk w)
  have S := memoSet_spec (σ := σ) G C.KB g hinj m key v s u (hmem u hsr) (hW u hM) hkl hKout hGout hsr.gkb h1 h2 h3
    (by rw [hsr.code]; exact hcodeI)
  intro t ht
  rcases S t ht with hs | ⟨w, hr', _, s'', _, hp⟩
  · exact Or.inl hs
  obtain ⟨_, hmem', hfr, hd', hg, hc⟩ := hp
  subst ht
  exact Or.inr ⟨w, hr', (), s', hset, rfl, hsr' t _ hsr hmem' hfr hd' hg hc⟩

end

section
variable {σ : Type}

/-- A write to the active side's table `k` changes `ModeAt` by that table only. -/
theorem modeAt_setG {C : Ctx} (hok : CtxOK C) {cs cs' : Caches} {t u : PState σ} (h : ModeAt t C cs) (k : CacheK)
    (hk : CacheAtM u C C.side cs'.modeMemos k)
    (hoth : ∀ k', k' ≠ k → CacheAtM t C C.side cs'.modeMemos k' = CacheAtM t C C.side cs.modeMemos k')
    (heag : cs'.eagerMemos = cs.eagerMemos)
    (hfr : ∀ c, ¬ inR (C.mg (.m C.side k)) c → u.memory c = t.memory c)
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals.lookup gEo = t.globals.lookup gEo) :
    ModeAt u C cs' := by
  obtain ⟨g, h1, h2⟩ := h
  have fr : ∀ b k', (Region.m b k' ≠ Region.m C.side k) → ∀ mm, CacheAtM t C b mm k' → CacheAtM u C b mm k' :=
    fun b k' hne mm hc => cacheAtM_frame hc (fun c hc' => hfr c (hok.memoDis _ _ c hne hc'))
      (fun j hj => hfr _ (hok.mdescMemo _ _ j hj)) hd
  refine ⟨by rw [hg]; exact g, ?_, ?_⟩
  · intro k'
    by_cases e : k' = k
    · subst e; exact hk
    · exact fr _ k' (fun x => e (by injection x)) _ (by rw [hoth k' e]; exact h1 k')
  · rw [heag]
    revert h2 fr
    unfold Ctx.side
    cases C.saved with
    | none =>
      intro h2 fr k'
      exact fr true k' (by simp) _ (h2 k')
    | some mm =>
      intro ⟨h2, h3⟩ fr
      exact ⟨fun k' => fr false k' (by simp) _ (h2 k'), h3⟩

/-- Rebuilding `SR` after a write confined to the active side's mode memo `k`. -/
theorem sr_upd_mode {C : Ctx} (hok : CtxOK C) (k : CacheK) {s s' : AState} {t u : PState σ} (hsr : SR C s t)
    (hfr : ∀ c, ¬ inR (C.mg (.m C.side k)) c → u.memory c = t.memory c) (hd : u.memaddrs = t.memaddrs)
    (hg : u.globals = t.globals) (hc : u.code = t.code) (hst : s'.store = s.store) (hme : s'.memos = s.memos) (hpn : s'.pins = s.pins)
    (hfix : s'.caches.constTyC = s.caches.constTyC ∧ s'.caches.constValC = s.caches.constValC ∧
      s'.caches.ruleBodyC = s.caches.ruleBodyC)
    (hM : ModeAt u C s'.caches) (hco : CachesOK s') : SR C s' u := by
  obtain ⟨e7, e8, e9⟩ := hfix
  have hrep : SRep u C.L C.FLn C.FLl C.FLs C.FLe s'.store := by
    rw [hst]
    exact srep_frame hsr.rep ⟨hfr _ (hok.flMemo _ _ (Or.inl rfl)), hfr _ (hok.flMemo _ _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo _ _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo _ _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo _ kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut _ c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩)
  refine ⟨hrep, by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll,
    by rw [hg]; exact hsr.gfls, by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd]; exact hsr.kbuf j hj,
    fun mk => by
      rw [hme]
      exact memoAt_frame (hsr.memo mk) (fun c hc => hfr c (hok.memoDis (.e mk) _ c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo _ (.e mk) kk hkk)) hd,
    fun nk => by
      rw [hme]
      exact memoAtN_frame (hsr.memoN nk) (fun c hc => hfr c (hok.memoDis (.n nk) _ c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo _ (.n nk) kk hkk)) hd,
    fun ck => ?_, hM,
    envAt_frame hsr.env (fun b c hc => hfr c (hok.memoDis (envR b) _ c (by simp) hc))
      (fun b kk hkk => hfr _ (hok.mdescMemo _ (envR b) kk hkk)) (fun i hi => hfr _ (hok.envMemo _ i hi)) hd
      ⟨by rw [hg], by rw [hg]⟩, (hpn.trans hsr.pins), heapEx_frame hsr.heap (fun i hi => hfr _ (hok.heapMemo _ i hi)) hd (by rw [hg]), by rw [hst]; exact hsr.twf, by rw [hst]; exact hsr.envd, by rw [hst]; exact hsr.floor, hco⟩
  have := cacheAt_frame (hsr.cache ck) (u := u) (fun c hc => hfr c (hok.memoDis (.c ck) _ c (by simp) hc))
    (fun kk hkk => hfr _ (hok.mdescMemo _ (.c ck) kk hkk)) hd
  cases ck <;> simp only [CacheAt] at this ⊢ <;> first | trivial | (rw [e7]; exact this) | (rw [e8]; exact this) |
    (rw [e9]; exact this)

/-- Rebuilding `SR` after a write confined to fixed cache `k`'s region. -/
theorem sr_upd_fix {C : Ctx} (hok : CtxOK C) (k : CacheK) {s s' : AState} {t u : PState σ} (hsr : SR C s t)
    (hfr : ∀ c, ¬ inR (C.mg (.c k)) c → u.memory c = t.memory c) (hd : u.memaddrs = t.memaddrs)
    (hg : u.globals = t.globals) (hc : u.code = t.code) (hst : s'.store = s.store) (hme : s'.memos = s.memos) (hpn : s'.pins = s.pins)
    (hk : CacheAt u C s'.caches k)
    (hoth : ∀ k', k' ≠ k → CacheAt t C s'.caches k' = CacheAt t C s.caches k')
    (hmo : s'.caches.modeMemos = s.caches.modeMemos ∧ s'.caches.eagerMemos = s.caches.eagerMemos) (hco : CachesOK s') :
    SR C s' u := by
  have hrep : SRep u C.L C.FLn C.FLl C.FLs C.FLe s'.store := by
    rw [hst]
    exact srep_frame hsr.rep ⟨hfr _ (hok.flMemo _ _ (Or.inl rfl)), hfr _ (hok.flMemo _ _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo _ _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo _ _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo _ kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut _ c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩)
  have hmode : ModeAt t C s'.caches := by
    unfold ModeAt; rw [hmo.1, hmo.2]; exact hsr.mode
  refine ⟨hrep, by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll,
    by rw [hg]; exact hsr.gfls, by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd]; exact hsr.kbuf j hj,
    fun mk => by
      rw [hme]
      exact memoAt_frame (hsr.memo mk) (fun c hc => hfr c (hok.memoDis (.e mk) _ c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo _ (.e mk) kk hkk)) hd,
    fun nk => by
      rw [hme]
      exact memoAtN_frame (hsr.memoN nk) (fun c hc => hfr c (hok.memoDis (.n nk) _ c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo _ (.n nk) kk hkk)) hd,
    fun ck => ?_,
    modeAt_frame hmode (fun b ck c hc => hfr c (hok.memoDis (.m b ck) _ c (by simp) hc))
      (fun b ck kk hkk => hfr _ (hok.mdescMemo _ (.m b ck) kk hkk)) hd (by rw [hg]),
    envAt_frame hsr.env (fun b c hc => hfr c (hok.memoDis (envR b) _ c (by simp) hc))
      (fun b kk hkk => hfr _ (hok.mdescMemo _ (envR b) kk hkk)) (fun i hi => hfr _ (hok.envMemo _ i hi)) hd
      ⟨by rw [hg], by rw [hg]⟩, (hpn.trans hsr.pins),
    heapEx_frame hsr.heap (fun i hi => hfr _ (hok.heapMemo _ i hi)) hd (by rw [hg]), by rw [hst]; exact hsr.twf, by rw [hst]; exact hsr.envd, by rw [hst]; exact hsr.floor, hco⟩
  by_cases e : ck = k
  · subst e; exact hk
  · have h0 := hsr.cache ck
    rw [← hoth ck e] at h0
    exact cacheAt_frame h0 (fun c hc => hfr c (hok.memoDis (.c ck) _ c (fun x => e (by injection x)) hc))
      (fun kk hkk => hfr _ (hok.mdescMemo _ (.c ck) kk hkk)) hd

end

end ConPanqueque.T
