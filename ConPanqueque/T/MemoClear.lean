import ConPanqueque.T.RowClear
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Clearing a memo

The twin drops a memo (`inst1Clear`: the map becomes `∅`); Pancake zeroes the slot array (a loop
over the static geometry), the row count, and resets the key-heap top.
-/

namespace ConPanqueque.T

def clearLoop (g : VGeo) : ProgHOL 64 :=
  .while (.cmp .lower (vv lJ0) (.const (BitVec.ofNat 64 g.n)))
    (.seq (.store (.op .add [.const g.S, .shift .lsl (vv lJ0) (.const 3)]) (.const 0))
      (.assign .local lJ0 (.op .add [vv lJ0, .const 1])))

variable {σ : Type}

/-- The loop's invariant from `u`: slots below `j` zeroed, everything else as in `u`. -/
def ClearI (u : PState σ) (g : VGeo) (s : PState σ) : Prop :=
  ∃ j, j ≤ g.n ∧ s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 j))) ∧
    (∀ j', j' < j → s.memory (g.S + BitVec.ofNat 64 (8 * j')) = .word 0) ∧
    (∀ c, (∀ j', j' < j → c ≠ g.S + BitVec.ofNat 64 (8 * j')) → s.memory c = u.memory c) ∧
    s.memaddrs = u.memaddrs ∧ s.code = u.code ∧ s.globals = u.globals ∧ s.topAddr = u.topAddr ∧
    (∀ y, y ≠ lJ0 → s.locals.lookup y = u.locals.lookup y)

theorem clearLoop_spec (u : PState σ) (g : VGeo) (hn : g.n ≤ 2 ^ 56) (hS : g.S.toNat + 8 * g.n < 2 ^ 64)
    (hdom : ∀ j, j < g.n → u.memaddrs (g.S + BitVec.ofNat 64 (8 * j)))
    (hj0 : u.locals.lookup lJ0 = some (.val (.word 0))) :
    Stop (evaluateHOLFiniteState u (clearLoop g)).1 ∨ ((evaluateHOLFiniteState u (clearLoop g)).1 = none ∧
      ClearI u g (evaluateHOLFiniteState u (clearLoop g)).2 ∧
        (evaluateHOLFiniteState u (clearLoop g)).2.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 g.n)))) := by
  have hloop := while_stop _ _ (ClearI u g)
    (fun s => ClearI u g s ∧ s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 g.n))))
    (fun s hs => by
      obtain ⟨j, hjn, hj, hz, hfr, hd, hc, hg, hta, hl⟩ := hs
      have hcmp : @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .lower (vv lJ0) (.const (BitVec.ofNat 64 g.n))) = some (.val (.word (bw (j < g.n)))) := by
        simp only [evalHOLFinite]
        rw [ConsLoop.eval_cmp_of s .lower _ _ _ _ (eval_vv s lJ0 _ hj) (eval_const s _)]
        have e : (BitVec.ofNat 64 j < BitVec.ofNat 64 g.n) ↔ j < g.n := by
          rw [BitVec.lt_def]; simp; omega
        by_cases h : j < g.n
        · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]
        · have : ¬ BitVec.ofNat 64 j < BitVec.ofNat 64 g.n := fun x => h (e.mp x)
          simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
      by_cases h : j < g.n
      · refine ⟨1, by rw [hcmp]; simp [bw, h], fun e => absurd e (by decide), fun _ _ => ?_⟩
        let s1 := decClockHOLFinite s
        have hj1 : s1.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 j))) := hj
        have hadr : g.S + BitVec.ofNat 64 j <<< (3 : BitVec 64).toNat = g.S + BitVec.ofNat 64 (8 * j) := by
          rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
        have hA : T.EV s1 (.op .add [.const g.S, .shift .lsl (vv lJ0) (.const 3)]) =
            some (.val (.word (g.S + BitVec.ofNat 64 (8 * j)))) := by
          rw [← hadr]; exact eval_add2 s1 _ _ _ _ (eval_const s1 _) (eval_shl s1 _ _ _ (eval_vv s1 lJ0 _ hj1) (by decide))
        rw [seq_normal _ (store_word s1 _ _ _ 0 hA (eval_const s1 0) (by show s.memaddrs _; rw [hd]; exact hdom j h))]
        let s2 : PState σ :=
          { s1 with memory := fun c => (if c = g.S + BitVec.ofNat 64 (8 * j) then HolWordLab.word 0 else s1.memory c) }
        have hj2 : s2.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 j))) := hj
        rw [ConsLoop.assign_local s2 lJ0 _ (BitVec.ofNat 64 (j + 1)) _
          (by rw [← word_add1_eq]; exact eval_add2 s2 _ _ _ _ (eval_vv s2 lJ0 _ hj2) (eval_const s2 1)) hj2]
        refine Or.inr ⟨rfl, j + 1, by omega, lookup_setVar_same _ _ _, fun j' hj' => ?_, fun c hc' => ?_, hd, hc, hg,
          hta, fun y hy => by rw [lookup_setVar_other _ _ hy]; exact hl y hy⟩
        · show (if g.S + BitVec.ofNat 64 (8 * j') = g.S + BitVec.ofNat 64 (8 * j) then _ else s.memory _) = _
          by_cases e : j' = j
          · subst e; simp
          · have hne : g.S + BitVec.ofNat 64 (8 * j') ≠ g.S + BitVec.ofNat 64 (8 * j) := by
              intro x; have := congrArg BitVec.toNat x
              rw [toNat_add_of_lt _ _ (by omega), toNat_add_of_lt _ _ (by omega)] at this; omega
            rw [ite_eq_right hne]; exact hz j' (by omega)
        · show (if c = g.S + BitVec.ofNat 64 (8 * j) then _ else s.memory c) = _
          rw [ite_eq_right (hc' j (by omega))]; exact hfr c (fun j' hj' => hc' j' (by omega))
      · have hjn' : j = g.n := by omega
        subst hjn'
        exact ⟨0, by rw [hcmp]; simp [bw, h], fun _ => ⟨⟨g.n, hjn, hj, hz, hfr, hd, hc, hg, hta, hl⟩, hj⟩,
          fun e => absurd rfl e⟩)
    u ⟨0, by omega, hj0, fun j' hj' => absurd hj' (by omega), fun c _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  rcases hloop with hs | ⟨hn', hq, hj⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hn', hq, hj⟩

/-- `rowClear; C := 0; C + 8 := KH; rest` (the full sweep `clearLoop` is kept for reference). -/
def clearCode (g : VGeo) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (rowClear g)
    (.seq (.store (.const g.C) (.const 0)) (.seq (.store (.const (g.C + 8)) (.const g.KH)) rest))

theorem inst1Clear_run (s : AState) :
    inst1Clear s = .ok ((), { s with memos := memoUpd .inst1 s.memos ∅ }) := rfl

/-- Rebuilding `SR` after a write confined to region `r`'s table (and the scratch locals): every other
memo is framed; the caller supplies region `r`'s new table. -/
theorem sr_upd_region {C : Ctx} (hok : CtxOK C) (r : Region) {s s' : AState} {t u : PState σ} (hsr : SR C s t)
    (hfr : ∀ c, ¬ inR (C.mg r) c → u.memory c = t.memory c) (hd : u.memaddrs = t.memaddrs)
    (hg : u.globals = t.globals) (hc : u.code = t.code) (hst : s'.store = s.store) (hpn : s'.pins = s.pins)
    (hoE : ∀ k, Region.e k ≠ r → memoSel k s'.memos = memoSel k s.memos)
    (hoN : ∀ k, Region.n k ≠ r → memoSelN k s'.memos = memoSelN k s.memos)
    (hsE : ∀ k, Region.e k = r → MemoAt u (C.mG (.e k)) (C.mg (.e k)) (memoSel k s'.memos))
    (hsN : ∀ k, Region.n k = r → MemoAtN u (C.mG (.n k)) (C.mg (.n k)) (memoSelN k s'.memos))
    (hoC : ∀ k, Region.c k ≠ r → MirrorEq s'.caches s.caches)
    (hsC : ∀ k, Region.c k = r → CacheAt u C s'.caches k)
    (hrM : ∀ b k, Region.m b k ≠ r) (hrE : ∀ b, envR b ≠ r) (hoM : MirrorEq s'.caches s.caches) (hco : CachesOK s') :
    SR C s' u := by
  refine ⟨hst ▸ srep_frame hsr.rep ⟨hfr _ (hok.flMemo r _ (Or.inl rfl)), hfr _ (hok.flMemo r _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo r _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo r _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo r kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut r c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩),
    by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll, by rw [hg]; exact hsr.gfls,
    by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd]; exact hsr.kbuf j hj, fun k => ?_, fun k => ?_, fun k => ?_,
    modeAt_frame (modeAt_mirror hsr.mode hoM) (fun b k c hc => hfr c (hok.memoDis (.m b k) r c (hrM b k) hc))
      (fun b k kk hkk => hfr _ (hok.mdescMemo r (.m b k) kk hkk)) hd (by rw [hg]),
    envAt_frame hsr.env (fun b c hc => hfr c (hok.memoDis (envR b) r c (hrE b) hc))
      (fun b kk hkk => hfr _ (hok.mdescMemo r (envR b) kk hkk)) (fun i hi => hfr _ (hok.envMemo r i hi)) hd
      ⟨by rw [hg], by rw [hg]⟩, (hpn.trans hsr.pins),
    heapEx_frame hsr.heap (fun i hi => hfr _ (hok.heapMemo r i hi)) hd (by rw [hg]), by rw [hst]; exact hsr.twf, by rw [hst]; exact hsr.envd, by rw [hst]; exact hsr.floor, hco⟩
  · by_cases e : Region.e k = r
    · exact hsE k e
    · rw [hoE k e]
      exact memoAt_frame (hsr.memo k) (fun c hc => hfr c (hok.memoDis (.e k) r c e hc))
        (fun kk hkk => hfr _ (hok.mdescMemo r (.e k) kk hkk)) hd
  · by_cases e : Region.n k = r
    · exact hsN k e
    · rw [hoN k e]
      exact memoAtN_frame (hsr.memoN k) (fun c hc => hfr c (hok.memoDis (.n k) r c e hc))
        (fun kk hkk => hfr _ (hok.mdescMemo r (.n k) kk hkk)) hd
  · by_cases e : Region.c k = r
    · exact hsC k e
    · have h0 : CacheAt t C s'.caches k := cacheAt_mirror (hsr.cache k) (hoC k e)
      exact cacheAt_frame h0 (fun c hc => hfr c (hok.memoDis (.c k) r c e hc))
        (fun kk hkk => hfr _ (hok.mdescMemo r (.c k) kk hkk)) hd

/-- The clearing code on any one-tier table: afterwards it holds `∅`, memory outside its region and its
descriptor is untouched, and only `cj0` among the locals changed. -/
theorem clearCode_core {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
    {enc : K → List (BitVec 64)} {valW : V → BitVec 64} (t : PState σ) (G : BitVec 64) (g : VGeo)
    (m : Std.HashMap K V) (hm : MemoAtG enc valW t G g m) (rest : ProgHOL 64) (w0 : BitVec 64)
    (hw0 : t.locals.lookup lJ0 = some (.val (.word w0)))
    (hGout : ∀ j, j < 8 → ¬ inR g (G + BitVec.ofNat 64 (8 * j))) :
    Stop (evaluateHOLFiniteState t (clearCode g rest)).1 ∨
    ∃ t4 : PState σ, evaluateHOLFiniteState t (clearCode g rest) = evaluateHOLFiniteState t4 rest ∧
      MemoAtG enc valW t4 G g (∅ : Std.HashMap K V) ∧ (∀ c, ¬ inR g c → t4.memory c = t.memory c) ∧
      t4.memaddrs = t.memaddrs ∧ t4.globals = t.globals ∧ t4.code = t.code ∧
      (∀ y, y ≠ lJ0 → t4.locals.lookup y = t.locals.lookup y) ∧ ∃ w, t4.locals.lookup lJ0 = some (.val (.word w)) := by
  obtain ⟨hdesc, hn, hb, hcap, tb, rows, ders, slots, hu, hT, hinv, hr, hder, hrel⟩ := hm
  have lC := hT.layC; have lS := hT.layS; have lR := hT.layR; have lD := hT.layD; have lK := hT.layK
  have hn56 : g.n ≤ 2 ^ 56 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  have hpos : 0 < g.n := hinv.pos
  unfold clearCode
  rcases rowClear_spec t g enc rows ders slots hu hT hinv hn hb hcap w0 hw0 with hs | ⟨hn1, hz, hfr, hd2, hc2, hg2, hta2, hl2, hjw⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  have e1 : evaluateHOLFiniteState t (rowClear g) = (none, (evaluateHOLFiniteState t (rowClear g)).2) := by
    rw [← hn1]
  rw [seq_normal _ e1]
  generalize (evaluateHOLFiniteState t (rowClear g)).2 = t2 at hz hfr hd2 hc2 hg2 hta2 hl2 hjw
  have hdom : ∀ j, j < g.n → t.memaddrs (g.S + BitVec.ofNat 64 (8 * j)) := fun j hj' => by
    obtain ⟨_, _, _, a, _⟩ := hT.slot j hj'; exact a
  have hCd : t2.memaddrs g.C := by rw [hd2]; exact hT.cnt.1
  rw [seq_normal _ (store_word t2 (.const g.C) (.const 0) g.C 0 (eval_const t2 _) (eval_const t2 0) hCd)]
  let t3 : PState σ := { t2 with memory := fun c => (if c = g.C then HolWordLab.word 0 else t2.memory c) }
  have hC8 : t3.memaddrs (g.C + 8) := by show t2.memaddrs _; rw [hd2]; exact hT.top.1
  rw [seq_normal _ (store_word t3 (.const (g.C + 8)) (.const g.KH) (g.C + 8) g.KH (eval_const t3 _)
    (eval_const t3 _) hC8)]
  let t4 : PState σ := { t3 with memory := fun c => (if c = g.C + 8 then HolWordLab.word g.KH else t3.memory c) }
  have hCne : g.C ≠ g.C + 8 := kb_ne_kb8 _
  have hCval : (g.C).toNat + 8 < 2 ^ 64 := by omega
  have hSne : ∀ j, j < g.n → g.S + BitVec.ofNat 64 (8 * j) ≠ g.C ∧ g.S + BitVec.ofNat 64 (8 * j) ≠ g.C + 8 := by
    intro j hj'
    refine ⟨fun x => ?_, fun x => ?_⟩ <;> have := congrArg BitVec.toNat x
    · rw [toNat_add_of_lt _ _ (by omega)] at this; omega
    · rw [toNat_add_of_lt _ _ (by omega), toNat_add8 _ hCval] at this; omega
  have m4 : ∀ c, t4.memory c = if c = g.C + 8 then .word g.KH else if c = g.C then .word 0 else t2.memory c :=
    fun c => rfl
  have hout : ∀ c, ¬ inR g c → t4.memory c = t.memory c := by
    intro c hc
    have hc1 : c ≠ g.C + 8 := fun e => hc (by rw [e]; refine ⟨?_, ?_⟩ <;> rw [toNat_add8 _ hCval] <;> omega)
    have hc2 : c ≠ g.C := fun e => hc (by rw [e]; exact ⟨Nat.le_refl _, by omega⟩)
    rw [m4, ite_eq_right hc1, ite_eq_right hc2, hfr c (fun j hj' e => hc (by
      rw [e]; refine ⟨?_, ?_⟩ <;> rw [toNat_add_of_lt _ _ (by omega)] <;> omega))]
  have hVT : VT t4 enc [] [] (List.replicate g.n 0) g 0 := by
    refine ⟨fun j hj' => ⟨0, by simp [hj'], by decide, ?_, ?_⟩, fun i hi => absurd hi (by simp),
      fun i hi => absurd hi (by simp), ⟨by show t2.memaddrs _; exact hCd, ?_⟩, ⟨hC8, ?_⟩, Nat.zero_le _, rfl,
      fun i hi => absurd hi (by simp), Nat.zero_le _, fun i hi => ?_, fun i hi => ?_, lC, lS, lR, lD, lK⟩
    · show t2.memaddrs _; rw [hd2]; exact hdom j hj'
    · rw [m4, ite_eq_right (hSne j hj').2, ite_eq_right (hSne j hj').1, hz j hj']; rfl
    · rw [m4, ite_eq_right hCne]; simp
    · rw [m4]; simp
    · have := hT.room i hi; show t2.memaddrs _ ∧ _; rw [hd2]; exact this
    · have := hT.hroom i hi; show t2.memaddrs _; rw [hd2]; exact this
  have hinv' : ConsModel.Inv (homeV enc g.b) ([] : List K) (List.replicate g.n 0) g.n :=
    ⟨by simp, hpos, hinv.home_lt, fun j i hji => by
      simp [List.getElem?_replicate] at hji, fun i hi => absurd hi (by simp), List.nodup_nil,
      fun j _ i hji _ => by simp [List.getElem?_replicate] at hji⟩
  have hd4 : t4.memaddrs = t.memaddrs := by show t2.memaddrs = _; rw [hd2]
  have hds : DescV t4 G g 1 := fun j hj' =>
    ⟨by rw [hd4]; exact (hdesc j hj').1, by rw [hout _ (hGout j hj')]; exact (hdesc j hj').2⟩
  refine Or.inr ⟨t4, rfl, ⟨hds, hn, hb, hcap, ⟨#[], #[], ∅⟩, [], [], List.replicate g.n 0, 0, hVT, hinv',
      ⟨rfl, fun a => by simp⟩, rfl, memoRel_empty⟩, hout, hd4, by show t2.globals = _; rw [hg2],
    by show t2.code = _; rw [hc2], fun y hy => ?_, hjw⟩
  show t2.locals.lookup y = _
  exact hl2 y hy (by simp)

/-- The continuation after a clear: `cj0` dropped from the environment. -/
theorem inv_after_clear {C : Ctx} {s s' : AState} {Γ : Env} {M : Mem} {D : List MlS} {t u : PState σ}
    (ht : Inv C s Γ M D t) (hsr : SR C s' u) (hl : ∀ y, y ≠ lJ0 → u.locals.lookup y = t.locals.lookup y)
    (hj : ∃ w, u.locals.lookup lJ0 = some (.val (.word w))) : Inv C s' (Γ.kill [lJ0]) [] D u := by
  refine ⟨hsr, fun y w hy => ?_, fun _ _ h => absurd h (by simp), fun y hy => ?_⟩
  · obtain ⟨hk1, hy'⟩ := Env.get_kill Γ _ y w hy
    have hne : y ≠ lJ0 := by simpa using hk1
    rw [hl y hne]; exact ht.env y w hy'
  · by_cases e : y = lJ0
    · subst e; exact hj
    · rw [hl y e]; exact ht.decl y hy

theorem specR_memoClearI {β : Type} {C : Ctx} (hok : CtxOK C) (mk : MemoK) (clearOp : AM Unit)
    (hclear : ∀ s, clearOp s = .ok ((), { s with memos := memoUpd mk s.memos ∅ }))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {k : Unit → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (hj : lJ0 ∈ D)
    (hk : SpecR (Inv C { s with memos := memoUpd mk s.memos ∅ } (Γ.kill [lJ0]) [] D) rest
      { s with memos := memoUpd mk s.memos ∅ } (k ()) R) :
    SpecR (Inv C s Γ M D) (clearCode (C.mg (.e mk)) rest) s (clearOp >>= k) R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl lJ0 hj
  rcases clearCode_core t _ _ _ (ht.sr.memo mk) rest w0 hw0 (fun j hj' => hok.mdescMemo (.e mk) (.e mk) j hj') with
    hs | ⟨t4, he, hmem, hout, hd4, hg4, hc4, hl4, hj4⟩
  · exact Or.inl hs
  have hsr' : SR C { s with memos := memoUpd mk s.memos ∅ } t4 :=
    sr_upd_region hok (.e mk) ht.sr hout hd4 hg4 hc4 rfl rfl
      (fun k' e => memoSel_upd_ne mk k' (fun x => e (by rw [x])) _ _)
      (fun k' _ => memoSelN_upd k' mk _ _)
      (fun k' e => by injection e with e; subst e; show MemoAt _ _ _ (memoSel k' (memoUpd k' s.memos ∅)); rw [memoSel_upd_same]; exact hmem)
      (fun k' e => by simp at e)
      (fun _ _ => mirrorEq_refl _) (fun _ e => by simp at e)
      (fun _ _ => by simp) (fun _ => by simp) (mirrorEq_refl _) (cachesOK_congr ht.sr.cok rfl ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [he]
  rcases hk t4 (inv_after_clear ht hsr' hl4 hj4) with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← clearOp s; match r with | (a, s) => k a s) = _
  rw [hclear]; exact hk'

theorem specR_memoClearNI {β : Type} {C : Ctx} (hok : CtxOK C) (mk : MemoNK) (clearOp : AM Unit)
    (hclear : ∀ s, clearOp s = .ok ((), { s with memos := memoUpdN mk s.memos ∅ }))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {k : Unit → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (hj : lJ0 ∈ D)
    (hk : SpecR (Inv C { s with memos := memoUpdN mk s.memos ∅ } (Γ.kill [lJ0]) [] D) rest
      { s with memos := memoUpdN mk s.memos ∅ } (k ()) R) :
    SpecR (Inv C s Γ M D) (clearCode (C.mg (.n mk)) rest) s (clearOp >>= k) R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl lJ0 hj
  rcases clearCode_core t _ _ _ (ht.sr.memoN mk).1 rest w0 hw0 (fun j hj' => hok.mdescMemo (.n mk) (.n mk) j hj') with
    hs | ⟨t4, he, hmem, hout, hd4, hg4, hc4, hl4, hj4⟩
  · exact Or.inl hs
  have hsr' : SR C { s with memos := memoUpdN mk s.memos ∅ } t4 :=
    sr_upd_region hok (.n mk) ht.sr hout hd4 hg4 hc4 rfl rfl
      (fun k' _ => memoSel_updN k' mk _ _)
      (fun k' e => memoSelN_upd_ne mk k' (fun x => e (by rw [x])) _ _)
      (fun k' e => by simp at e)
      (fun k' e => by
        injection e with e; subst e; show MemoAtN _ _ _ (memoSelN k' (memoUpdN k' s.memos ∅)); rw [memoSelN_upd_same]
        exact ⟨hmem, fun _ _ h => by simp at h⟩)
      (fun _ _ => mirrorEq_refl _) (fun _ e => by simp at e)
      (fun _ _ => by simp) (fun _ => by simp) (mirrorEq_refl _) (cachesOK_congr ht.sr.cok rfl ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [he]
  rcases hk t4 (inv_after_clear ht hsr' hl4 hj4) with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← clearOp s; match r with | (a, s) => k a s) = _
  rw [hclear]; exact hk'

end ConPanqueque.T
