import ConPanqueque.T.Decl.Arms
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Growing the environment heap

A context whose environment-heap image is extended keeps every static fact: the stored constants' and tables'
blocks and the pin table are read at cells below the old top, which the extension leaves alone.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The context with environment-heap image `EH`. -/
def ctxE (C : Ctx) (EH : List (BitVec 64)) : Ctx := { C with EH := EH }

section
variable {H H' : List (BitVec 64)} (hp : H <+: H')
include hp

theorem eblk_mono {o : Nat} {xs : List (BitVec 64)} (h : EBlk H o xs) : EBlk H' o xs :=
  ⟨get_prefix h.1 hp, fun i hi => get_prefix (h.2 i hi) hp⟩

theorem enlist_mono {k : IdxKind} {EB w : BitVec 64} {xs : List (Idx k)} (h : ENList EB H w xs) : ENList EB H' w xs :=
  let ⟨o, hw, hb⟩ := h; ⟨o, hw, eblk_mono hp hb⟩

theorem natE_mono {i n : Nat} (h : NatE H i n) : NatE H' i n := ⟨get_prefix h.1 hp, h.2⟩

theorem cve_mono {EB : BitVec 64} {o : Nat} {v : IConstantVal} (h : CVE EB H o v) : CVE EB H' o v :=
  ⟨get_prefix h.1 hp, let ⟨w, hw, hl⟩ := h.2.1; ⟨w, get_prefix hw hp, enlist_mono hp hl⟩, get_prefix h.2.2 hp⟩

theorem fireE_mono {EB : BitVec 64} {o : Nat} {f : IRecRuleFire} (h : FireE EB H o f) : FireE EB H' o f := by
  cases f with
  | plain => exact get_prefix h hp
  | nested lv pins =>
    obtain ⟨h0, ⟨w1, hw1, hl1⟩, ⟨w2, hw2, hl2⟩⟩ := h
    exact ⟨get_prefix h0 hp, ⟨w1, get_prefix hw1 hp, enlist_mono hp hl1⟩, ⟨w2, get_prefix hw2 hp, enlist_mono hp hl2⟩⟩
  | levels lv =>
    obtain ⟨h0, ⟨w1, hw1, hl1⟩⟩ := h
    exact ⟨get_prefix h0 hp, ⟨w1, get_prefix hw1 hp, enlist_mono hp hl1⟩⟩

theorem ruleE_mono {EB : BitVec 64} {o : Nat} {r : IRecRule} (h : RuleE EB H o r) : RuleE EB H' o r :=
  ⟨get_prefix h.1 hp, natE_mono hp h.2.1, fireE_mono hp h.2.2.1, get_prefix h.2.2.2 hp⟩

theorem rulesE_mono {EB w : BitVec 64} {rs : List IRecRule} (h : RulesE EB H w rs) : RulesE EB H' w rs :=
  let ⟨o, hw, hl, hr⟩ := h
  ⟨o, hw, get_prefix hl hp, fun i hi => let ⟨q, hq, hrq⟩ := hr i hi; ⟨q, get_prefix hq hp, ruleE_mono hp hrq⟩⟩

theorem cie_mono {EB : BitVec 64} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) : CIE EB H' o ci := by
  refine ⟨cve_mono hp h.1, ?_⟩
  have h2 := h.2
  cases ci with
  | axiomInfo _ => exact get_prefix h2 hp
  | defnInfo _ val hint => exact ⟨get_prefix h2.1 hp, get_prefix h2.2.1 hp, natE_mono hp h2.2.2⟩
  | thmInfo _ => exact get_prefix h2 hp
  | indInfo _ caps =>
    obtain ⟨a, b, ⟨w, hw, hl⟩, c, d, ⟨w2, hw2, hl2⟩, e⟩ := h2
    exact ⟨get_prefix a hp, get_prefix b hp, ⟨w, get_prefix hw hp, enlist_mono hp hl⟩, natE_mono hp c, natE_mono hp d,
      ⟨w2, get_prefix hw2 hp, enlist_mono hp hl2⟩, get_prefix e hp⟩
  | ctorInfo _ np nf ind =>
    obtain ⟨a, b, c, d⟩ := h2
    exact ⟨get_prefix a hp, natE_mono hp b, natE_mono hp c, get_prefix d hp⟩
  | recInfo _ mi rp isK rules =>
    obtain ⟨a, b, c, d, ⟨w, hw, hr⟩⟩ := h2
    exact ⟨get_prefix a hp, natE_mono hp b, natE_mono hp c, get_prefix d hp, ⟨w, get_prefix hw hp, rulesE_mono hp hr⟩⟩

theorem tblE_mono {EB : BitVec 64} {o : Nat} {t : IProjTable} (h : TblE EB H o t) : TblE EB H' o t := by
  obtain ⟨a, ⟨w, hw, hl⟩, b, c, d, ⟨w2, hw2, hl2⟩⟩ := h
  exact ⟨get_prefix a hp, ⟨w, get_prefix hw hp, enlist_mono hp hl⟩, natE_mono hp b, get_prefix c hp, natE_mono hp d,
    ⟨w2, get_prefix hw2 hp, enlist_mono hp hl2⟩⟩

end

theorem envRel_E {C : Ctx} (h : EnvRel C) {EH : List (BitVec 64)} (hp : C.EH <+: EH) : EnvRel (ctxE C EH) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · have := h.1 n
    show match C.fe.find? n with
      | none => C.envM[n]? = none
      | some ci => ∃ o, C.envM[n]? = some (ecell C o) ∧ CIE C.EB EH o ci
    revert this
    cases C.fe.find? n with
    | none => exact id
    | some ci => exact fun ⟨o, hm, hc⟩ => ⟨o, hm, cie_mono hp hc⟩
  · have := h.2 n
    show match C.fe.findTable? n with
      | none => C.tblM[n]? = none
      | some tb => ∃ o, C.tblM[n]? = some (ecell C o) ∧ TblE C.EB EH o tb
    revert this
    cases C.fe.findTable? n with
    | none => exact id
    | some tb => exact fun ⟨o, hm, hc⟩ => ⟨o, hm, tblE_mono hp hc⟩

theorem pinsE_E {C : Ctx} (h : PinsE C) {EH : List (BitVec 64)} (hp : C.EH <+: EH) : PinsE (ctxE C EH) := by
  obtain ⟨a, b, c, d, e, f, ⟨w, hw, hl⟩⟩ := h
  exact ⟨a, fun i hi => get_prefix (b i hi) hp, get_prefix c hp, get_prefix d hp, get_prefix e hp, natE_mono hp f,
    ⟨w, get_prefix hw hp, enlist_mono hp hl⟩⟩

theorem ctxOK_E {C : Ctx} (hok : CtxOK C) {EH : List (BitVec 64)} (hp : C.EH <+: EH) : CtxOK (ctxE C EH) := by
  have h1 := envRel_E hok.envRel hp
  have h2 := pinsE_E hok.pinsRel hp
  cases hok; constructor <;> first | assumption | exact h1 | exact h2


section
variable {σ : Type}

theorem ecell_inj {C : Ctx} (lay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64) {i j : Nat} (hi : i < C.EN) (hj : j < C.EN)
    (e : ecell C i = ecell C j) : i = j := by
  have := congrArg BitVec.toNat e
  simp only [ecell, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (show 8 * i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show C.EB.toNat + 8 * i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show C.EB.toNat + 8 * j < 2 ^ 64 by omega)] at this
  omega

theorem sr_envStore {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (h : SR C s t) (j : Nat)
    (hj : j < C.EH.length) (w : BitVec 64) :
    SR (ctxE C (C.EH.set j w)) s
      { t with memory := fun c => if c = ecell C j then .word w else t.memory c } := by
  obtain ⟨hH, hm1, hm2, hl⟩ := h.env
  have hjN : j < C.EN := by have := hH.len; omega
  have hne : ∀ c, c ≠ ecell C j →
      (fun c => if c = ecell C j then HolWordLab.word w else t.memory c) c = t.memory c :=
    fun c hc => by simp [hc]
  refine ⟨srep_frame h.rep ⟨hne _ (fun e => hok.flEnv j _ hjN (Or.inl rfl) e.symm),
      hne _ (fun e => hok.flEnv j _ hjN (Or.inr (Or.inl rfl)) e.symm),
      hne _ (fun e => hok.flEnv j _ hjN (Or.inr (Or.inr (Or.inl rfl))) e.symm),
      hne _ (fun e => hok.flEnv j _ hjN (Or.inr (Or.inr (Or.inr rfl))) e.symm)⟩ rfl
      (fun k tier hk ht => ⟨fun mm hm => hne _ (fun e => hok.dirEnv j k tier mm hjN hk ht hm e.symm),
        fun c hc => hne c (fun e => hok.envOut j hjN ⟨k, tier, hk, ht, (e ▸ hc : inR _ (ecell C j))⟩)⟩),
    h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf,
    fun mk => memoAt_frame (h.memo mk) (fun c hc => hne c (fun e => hok.envMemo (.e mk) j hjN (e ▸ hc : inR _ (ecell C j))))
      (fun k hk => hne _ (fun e => hok.mdescEnv (.e mk) j k hjN hk e.symm)) rfl,
    fun mk => memoAtN_frame (h.memoN mk) (fun c hc => hne c (fun e => hok.envMemo (.n mk) j hjN (e ▸ hc : inR _ (ecell C j))))
      (fun k hk => hne _ (fun e => hok.mdescEnv (.n mk) j k hjN hk e.symm)) rfl,
    fun ck => cacheAt_frame (h.cache ck) (fun c hc => hne c (fun e => hok.envMemo (.c ck) j hjN (e ▸ hc : inR _ (ecell C j))))
      (fun k hk => hne _ (fun e => hok.mdescEnv (.c ck) j k hjN hk e.symm)) rfl,
    modeAt_frame h.mode (fun b ck c hc => hne c (fun e => hok.envMemo (.m b ck) j hjN (e ▸ hc : inR _ (ecell C j))))
      (fun b ck k hk => hne _ (fun e => hok.mdescEnv (.m b ck) j k hjN hk e.symm)) rfl rfl,
    ⟨⟨by simp only [ctxE, List.length_set]; exact hH.top, by simp only [ctxE, List.length_set]; exact hH.len, hH.lay,
        hH.dom, fun i hi => ?_, fun i hi => ?_⟩,
      memoAtG_frame hm1 (fun c hc => hne c (fun e => hok.envMemo (envR true) j hjN (e ▸ hc : inR _ (ecell C j))))
        (fun k hk => hne _ (fun e => hok.mdescEnv (envR true) j k hjN hk e.symm)) rfl,
      memoAtG_frame hm2 (fun c hc => hne c (fun e => hok.envMemo (envR false) j hjN (e ▸ hc : inR _ (ecell C j))))
        (fun k hk => hne _ (fun e => hok.mdescEnv (envR false) j k hjN hk e.symm)) rfl, hl⟩, h.pins,
    heapEx_frame h.heap (fun i hi => hne _ (fun e => hok.heapEnv i j hi hjN e)) rfl rfl, h.twf, h.envd, h.floor, h.cok⟩
  · simp only [ctxE, List.length_set] at hi
    show (if ecell C i = ecell C j then _ else _) = HolWordLab.word (C.EH.set j w)[i]
    by_cases e : i = j
    · subst e; simp only [ite_true]; exact congrArg HolWordLab.word (List.getElem_set_self _).symm
    · have : ecell C i ≠ ecell C j := fun x => e (ecell_inj hok.envLay (by have := hH.len; omega) hjN x)
      simp only [this, ite_false]
      exact (hH.val i hi).trans (congrArg _ (List.getElem_set_ne (fun h => e h.symm) _).symm)
  · show ∃ w', (if ecell C i = ecell C j then _ else _) = _
    by_cases e : i = j
    · subst e; exact ⟨w, by simp⟩
    · have : ecell C i ≠ ecell C j := fun x => e (ecell_inj hok.envLay hi hjN x)
      simp only [this, ite_false]
      exact hH.words i hi

/-- `*(ea) := ev` at an environment cell of the image: the image follows. Memory facts are dropped. -/
theorem specR_envStoreI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (ea ev : ExpHOL 64) (j : Nat)
    (hj : j < C.EH.length) (w : BitVec 64) (hea : sev Γ ea = some (ecell C j)) (hev : sev Γ ev = some w)
    (h : SpecR (Inv (ctxE C (C.EH.set j w)) s Γ [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.store ea ev) rest) s m R := by
  refine specR_seq (fun t ht => ?_) h
  obtain ⟨hH, _, _, _⟩ := ht.sr.env
  rw [store_word t ea ev _ w (inv_ev ht hea) (inv_ev ht hev) (hH.dom j (by have := hH.len; omega))]
  exact Or.inr ⟨rfl, sr_envStore hok ht.sr j hj w, fun y v hy => ht.env y v hy, fun _ _ h => absurd h (by simp),
    ht.decl⟩


/-- `x := Get; if (EB + 8·EN − x < eN) hang; Get := x + eN; rest` (`eN` is `8 n`): fresh environment cells. -/
def envAllocP (C : Ctx) (x : MlS) (eN : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local x (.var .global gEt))
    (.ite (.cmp .lower (.op .sub [.const (C.EB + BitVec.ofNat 64 (8 * C.EN)), vv x]) eN) hang
      (.seq (.assign .global gEt (.op .add [vv x, eN])) rest))

theorem specR_envAllocI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (eN : ExpHOL 64)
    (n : Nat) (hn : 8 * n < 2 ^ 64) (hx : x ∈ D) (hN : ∀ v, sev ((x, v) :: Γ) eN = some (BitVec.ofNat 64 (8 * n)))
    (hk : ∀ (ws : List (BitVec 64)), ws.length = n → C.EH.length + n ≤ C.EN →
      SpecR (Inv (ctxE C (C.EH ++ ws)) s ((x, ecell C C.EH.length) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (envAllocP C x eN rest) s m R := by
  intro t ht
  obtain ⟨ha, hm1, hm2, hl⟩ := ht.sr.env
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  unfold envAllocP
  rw [seq_normal _ (ConsLoop.assign_local t x _ (ecell C C.EH.length) w0 (by simp [evalHOLExact, ha.top]; rfl) hw0)]
  let t1 := setVarHOLFinite x (.val (.word (ecell C C.EH.length))) t
  have ht1 : Inv C s ((x, ecell C C.EH.length) :: Γ) M D t1 := inv_set ht x _
  have hlen := ha.len
  have lay := ha.lay
  have hfree : C.EB + BitVec.ofNat 64 (8 * C.EN) - ecell C C.EH.length = BitVec.ofNat 64 (8 * (C.EN - C.EH.length)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [ecell, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 8 * C.EN < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * C.EH.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show C.EB.toNat + 8 * C.EN < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show C.EB.toNat + 8 * C.EH.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * (C.EN - C.EH.length) < 2 ^ 64 by omega)]
    omega
  have hc : EV t1 (.cmp .lower (.op .sub [.const (C.EB + BitVec.ofNat 64 (8 * C.EN)), vv x]) eN) =
      some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower
        (BitVec.ofNat 64 (8 * (C.EN - C.EH.length))) (BitVec.ofNat 64 (8 * n)) then 1 else 0))) := by
    refine inv_ev ht1 ?_
    simp [sev, hN, hfree]
  rw [ite_word t1 _ _ _ _ hc]
  by_cases full : C.EN - C.EH.length < n
  · have : BitVec.ofNat 64 (8 * (C.EN - C.EH.length)) < BitVec.ofNat 64 (8 * n) := by
      rw [BitVec.lt_def]; simp; omega
    have hw1 : (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 (8 * (C.EN - C.EH.length)))
        (BitVec.ofNat 64 (8 * n)) then (1 : BitVec 64) else 0) = 1 := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
    rw [hw1, if_pos (by decide)]
    exact Or.inl (Or.inl (hang_spec t1.clock t1 rfl))
  have hnf : ¬ BitVec.ofNat 64 (8 * (C.EN - C.EH.length)) < BitVec.ofNat 64 (8 * n) := by
    rw [BitVec.lt_def]; simp; omega
  have hw0 : (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 (8 * (C.EN - C.EH.length)))
      (BitVec.ofNat 64 (8 * n)) then (1 : BitVec 64) else 0) = 0 := by
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnf]
  rw [hw0, if_neg (by decide)]
  have htop1 : t1.globals.lookup gEt = some (.val (.word (ecell C C.EH.length))) := ha.top
  rw [seq_normal _ (assign_ok t1 .global gEt _ (.val (.word (ecell C C.EH.length + BitVec.ofNat 64 (8 * n))))
    (by have := inv_ev ht1 (e := .op .add [vv x, eN]) (v := ecell C C.EH.length + BitVec.ofNat 64 (8 * n))
          (by simp [sev, hN]); exact this)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, htop1, shapeOfHOLExact, shapeEqHOL]))]
  let t2 := setKvarHOLFinite .global gEt (.val (.word (ecell C C.EH.length + BitVec.ofNat 64 (8 * n)))) t1
  let ws : List (BitVec 64) := (List.range n).map fun i => labW (t.memory (ecell C (C.EH.length + i)))
  have hws : ws.length = n := by simp [ws]
  have hgl : ∀ y, y ≠ gEt → t2.globals.lookup y = t.globals.lookup y := fun y hy => by
    simp [t2, t1, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite, FUPDATE, Ne.symm hy]
  have hEA : EHeapAt t2 C.EB C.EN (C.EH ++ ws) := by
    refine ⟨?_, by rw [List.length_append, hws]; omega, lay, fun i hi => ha.dom i hi, fun i hi => ?_,
      fun i hi => ha.words i hi⟩
    · have e8 : ecell C C.EH.length + BitVec.ofNat 64 (8 * n) = C.EB + BitVec.ofNat 64 (8 * (C.EH ++ ws).length) := by
        rw [List.length_append, hws]
        apply BitVec.eq_of_toNat_eq
        simp only [ecell, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show 8 * C.EH.length < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * n < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show 8 * (C.EH.length + n) < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show C.EB.toNat + 8 * C.EH.length < 2 ^ 64 by omega)]
        omega
      rw [← e8]
      simp [t2, setKvarHOLFinite, setGlobalHOLFinite, FUPDATE]
    · show t.memory _ = _
      rw [List.length_append, hws] at hi
      by_cases hl' : i < C.EH.length
      · rw [List.getElem_append_left hl']; exact ha.val i hl'
      · rw [List.getElem_append_right (by omega)]
        obtain ⟨w', hw'⟩ := ha.words i (by omega)
        simp only [ws, List.getElem_map, List.getElem_range]
        rw [show C.EH.length + (i - C.EH.length) = i by omega]
        show t.memory (ecell C i) = _
        rw [show ecell C i = C.EB + BitVec.ofNat 64 (8 * i) from rfl, hw']; rfl
  have hInv : Inv (ctxE C (C.EH ++ ws)) s ((x, ecell C C.EH.length) :: Γ) M D t2 := by
    have hsr1 := ht1.sr
    refine ⟨⟨srep_frame hsr1.rep ⟨rfl, rfl, rfl, rfl⟩ rfl (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩),
      by rw [hgl _ (by decide)]; exact ht.sr.gdir, by rw [hgl _ (by decide)]; exact ht.sr.gfln,
      by rw [hgl _ (by decide)]; exact ht.sr.gfll, by rw [hgl _ (by decide)]; exact ht.sr.gfls,
      by rw [hgl _ (by decide)]; exact ht.sr.gfle, by rw [hgl _ (by decide)]; exact ht.sr.gkb, hsr1.code,
      hsr1.kbuf, fun k => memoAt_of_eq (hsr1.memo k) rfl rfl, fun k => memoAtN_frame (hsr1.memoN k) (fun _ _ => rfl)
        (fun _ _ => rfl) rfl, fun k => cacheAt_frame (hsr1.cache k) (fun _ _ => rfl) (fun _ _ => rfl) rfl,
        modeAt_frame ht.sr.mode (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl (hgl _ (by decide)),
        ⟨hEA, memoAtG_frame hm1 (fun _ _ => rfl) (fun _ _ => rfl) rfl, memoAtG_frame hm2 (fun _ _ => rfl) (fun _ _ => rfl) rfl,
          by rw [hgl _ (by decide)]; exact hl⟩, ht.sr.pins,
        heapEx_frame ht.sr.heap (fun _ _ => rfl) rfl (hgl _ (by decide)), hsr1.twf, hsr1.envd, hsr1.floor, hsr1.cok⟩,
      ht1.env, ht1.mem, ht1.decl⟩
  exact hk ws hws (by omega) t2 hInv

end

end ConPanqueque.T.Decl
