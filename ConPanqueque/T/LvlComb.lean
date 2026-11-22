import ConPanqueque.T.LvlMk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `combining`

con-leche's `Level.combining`: `zero` is a unit, two `succ`s share theirs, otherwise a `max` node.
`comb(a, b)` returns the input word on the unit cases and builds blocks otherwise.
-/

namespace ConPanqueque.T.LComb
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq

def fComb := ofString "combining"

def combB (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lX) (.const 0)) (.return (vv pLa))
    (.ite (.op .and [.cmp .equal (vv lA2) (.const 1), .cmp .equal (vv lX) (.const 1)])
      (.seq (.assign .local lD1 (.load .one (vv lA3))) (.seq (.assign .local lB (.load .one (vv lY)))
        (.seq (.call (some (some (.local, lZ), none)) fComb [vv lD1, vv lB])
          (alloc2 C lW (.const 1) (vv lZ) (.return (vv lW))))))
      (alloc3 C lW (.const 2) (vv pLa) (vv pLb) (.return (vv lW))))

def combCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv pLa)) (lvViewP
    (.seq (.assign .local lA2 (vv lX)) (.seq (.assign .local lA3 (vv lY))
      (.ite (.cmp .equal (vv lA2) (.const 0)) (.return (vv pLb))
        (.seq (.assign .local lQ (vv pLb)) (lvViewP (combB C)))))))

def combBody (C : Ctx) : ProgHOL 64 := prologue lvlLocals (combCore C)

theorem combining_zero_left (r : ConLeche.Level) : ConLeche.Level.combining .zero r = r := by
  cases r <;> rfl

theorem combining_zero_right (l : ConLeche.Level) (hl : l ≠ .zero) : ConLeche.Level.combining l .zero = l := by
  cases l <;> simp_all [ConLeche.Level.combining]

theorem combining_max (l r : ConLeche.Level) (hl : l ≠ .zero) (hr : r ≠ .zero)
    (hs : ¬ (ltag l = 1 ∧ ltag r = 1)) : ConLeche.Level.combining l r = .max l r := by
  cases l <;> cases r <;> simp_all [ConLeche.Level.combining, ltag]

section
variable {σ : Type}

theorem ofNat_ltag_ne (a b : Nat) (ha : a < 5) (hb : b < 5) (h : a ≠ b) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b :=
  fun e => h ((word_eq_iff a b (by omega) (by omega)).mp e)

theorem combB_spec (C : Ctx) (hok : CtxOK C)
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    {s : AState} {Γ : Env} {M : Mem} (la lb : ConLeche.Level) (a b Pa Pb : BitVec 64) (hla : la ≠ .zero)
    (ha : Γ.get pLa = some a) (hb : Γ.get pLb = some b) (hA2 : Γ.get lA2 = some (BitVec.ofNat 64 (ltag la)))
    (hA3 : Γ.get lA3 = some Pa) (hX : Γ.get lX = some (BitVec.ofNat 64 (ltag lb))) (hY : Γ.get lY = some Pb)
    (hra : LRep C.HB C.H s.store.ls a la) (hrb : LRep C.HB C.H s.store.ls b lb)
    (hka : LKids C.HB C.H s.store.ls Pa M la) (hkb : LKids C.HB C.H s.store.ls Pb M lb)
    (hrec : ∀ u v wu wv, la = .succ u → LRep C.HB C.H s.store.ls wu u → LRep C.HB C.H s.store.ls wv v →
      SpecR (Pre (σ := σ) C s [(pLa, wu), (pLb, wv)]) (combBody C) s (pure (ConLeche.Level.combining u v))
        (PostLv C)) :
    SpecR (Inv (σ := σ) C s Γ M DL) (combB C) s (pure (ConLeche.Level.combining la lb)) (PostLv C) := by
  unfold combB
  by_cases hz : lb = .zero
  · subst hz
    refine specR_ifI _ 1 (by simp +decide [sev, hX, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    rw [combining_zero_right la hla]
    exact specR_returnI (vv pLa) a (by simp [ha]) (fun t ht => ⟨C.H, List.prefix_refl _, hra,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hz' : ltag lb ≠ 0 := by cases lb <;> simp_all [ltag]
  refine specR_ifI _ 0 (by simp +decide [sev, hX, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_ltag_ne _ 0 (ltag_lt lb) (by decide) hz'])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  by_cases hs : ltag la = 1 ∧ ltag lb = 1
  · obtain ⟨u, rfl⟩ : ∃ u, la = .succ u := by cases la <;> simp_all [ltag]
    obtain ⟨v, rfl⟩ : ∃ v, lb = .succ v := by cases lb <;> simp_all [ltag]
    refine specR_ifI _ 1 (by simp +decide [sev, hA2, hX, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    obtain ⟨wu, m1, r1⟩ := hka
    obtain ⟨wv, m2, r2⟩ := hkb
    refine specR_loadI' lD1 (vv lA3) Pa (Pa + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [hA3])
      (by simp) m1 ?_
    refine specR_loadI' lB (vv lY) Pb (Pb + BitVec.ofNat 64 (8 * 0)) wv (by decide) (by simp +decide [hY])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (ConLeche.Level.combining u v) >>= fun c => pure (ConLeche.Level.succ c)) rfl ?_
    refine callLv_spec lZ fComb [pLa, pLb] [vv lD1, vv lB] (combBody C) [wu, wv] (by decide) rfl (by decide) hcC
      ⟨by simp +decide, by simp +decide, trivial⟩ _ (hrec u v wu wv rfl r1 r2) (fun H1 c hp1 hc => ?_)
    refine specR_alloc2I (ctxOK_H hok H1) lW (.const 1) (vv lZ) 1 c (by decide) (fun _ => rfl)
      (fun _ => by simp +decide) (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp2' : H1 <+: H2 := hp2
    refine ⟨_, hp1.trans (hp2'.trans (img2_prefix H2 ws _ c hws)), ?_, sr_of_eq ht.sr rfl rfl rfl rfl⟩
    exact lrep_mkSucc (ctxH C H1) s.store.ls H2 ws c (ConLeche.Level.combining u v) hws hp2 hc
  · have hand : ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 (ltag la)) 1 then (1 : BitVec 64) else 0) &&&
        (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 (ltag lb)) 1 then 1 else 0)) = 0 := by
      by_cases h1 : ltag la = 1
      · have h2 : ltag lb ≠ 1 := fun h2 => hs ⟨h1, h2⟩
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h1, ofNat_ltag_ne _ 1 (ltag_lt lb) (by decide) h2]
      · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_ltag_ne _ 1 (ltag_lt la) (by decide) h1]
    refine specR_ifI _ _ (by simp +decide [sev, hA2, hX]) (fun hw => absurd hand hw) (fun _ => ?_)
    rw [combining_max la lb hla (by cases lb <;> simp_all [ltag]) hs]
    refine specR_alloc3I hok lW (.const 2) (vv pLa) (vv pLb) 2 a b (by decide) (fun _ => rfl)
      (fun _ => by simp +decide [ha]) (fun _ => by simp +decide [hb]) (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide) (fun t ht => ?_)
    exact ⟨_, hp2.trans (img3_prefix H2 ws _ a b hws),
      lrep_mkMax C s.store.ls H2 ws a b la lb hws hp2 hra hrb 2 rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

section
variable {σ : Type}


theorem comb_nz (C : Ctx) (hok : CtxOK C)
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (la lb : ConLeche.Level) (a b : BitVec 64) (s : AState) (hla : la ≠ .zero)
    (ha : LRep C.HB C.H s.store.ls a la) (hb : LRep C.HB C.H s.store.ls b lb)
    (hrec : ∀ u v wu wv, la = .succ u → LRep C.HB C.H s.store.ls wu u → LRep C.HB C.H s.store.ls wv v →
      SpecR (Pre (σ := σ) C s [(pLa, wu), (pLb, wv)]) (combBody C) s (pure (ConLeche.Level.combining u v))
        (PostLv C)) :
    SpecR (Pre (σ := σ) C s [(pLa, a), (pLb, b)]) (combBody C) s (pure (ConLeche.Level.combining la lb))
      (PostLv C) := by
  refine specR_prologue (postLv_locals C) (params_noneLE _ _ C) ?_
  unfold combCore
  refine specR_assignI lQ (vv pLa) a (by decide) (by simp +decide [ctxEnv]) ?_
  refine specR_lvViewI hok a la (by simp) ha (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) lvScratch_DL
    (fun Γ1 M1 Pa hp1 hx1 hy1 _ hk1 => ?_)
  refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 (ltag la)) (by decide) (by simp [hx1]) ?_
  refine specR_assignI lA3 (vv lY) Pa (by decide) (by simp +decide [hy1]) ?_
  have hz' : ltag la ≠ 0 := by cases la <;> simp_all [ltag]
  refine specR_ifI _ 0 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_ltag_ne _ 0 (ltag_lt la) (by decide) hz'])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_assignI lQ (vv pLb) b (by decide)
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv]) ?_
  refine specR_lvViewI hok b lb (by simp) hb (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv])
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv]) lvScratch_DL
    (fun Γ2 M2 Pb hp2 hx2 hy2 hmm2 hk2 => ?_)
  have hka : LKids C.HB C.H s.store.ls Pa M2 la := by
    cases la with
    | zero => trivial
    | succ u => obtain ⟨wu, h1, h2⟩ := hk1; exact ⟨wu, hmm2 _ h1, h2⟩
    | max u v => obtain ⟨wu, wv, h1, h2, h3, h4⟩ := hk1; exact ⟨wu, wv, hmm2 _ h1, hmm2 _ h2, h3, h4⟩
    | imax u v => obtain ⟨wu, wv, h1, h2, h3, h4⟩ := hk1; exact ⟨wu, wv, hmm2 _ h1, hmm2 _ h2, h3, h4⟩
    | param n => obtain ⟨nh, f, h1, h2⟩ := hk1; exact ⟨nh, f, hmm2 _ h1, h2⟩
  exact combB_spec C hok hcC la lb a b Pa Pb hla
    (by rw [hp2 _ (by decide)]; simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv])
    (by rw [hp2 _ (by decide)]; simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv])
    (by rw [hp2 _ (by decide)]; simp +decide) (by rw [hp2 _ (by decide)]; simp +decide) hx2 hy2 ha hb hka hk2 hrec

/-- `combining` refined, for any trees the words represent. -/
theorem comb_spec (C : Ctx) (hok : CtxOK C)
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one)) :
    ∀ (la : ConLeche.Level) (a b : BitVec 64) (lb : ConLeche.Level) (s : AState),
      LRep C.HB C.H s.store.ls a la → LRep C.HB C.H s.store.ls b lb →
      SpecR (Pre (σ := σ) C s [(pLa, a), (pLb, b)]) (combBody C) s (pure (ConLeche.Level.combining la lb))
        (PostLv C) := by
  intro la
  induction la with
  | zero =>
    intro a b lb s ha hb
    refine specR_prologue (postLv_locals C) (params_noneLE _ _ C) ?_
    unfold combCore
    refine specR_assignI lQ (vv pLa) a (by decide) (by simp +decide [ctxEnv]) ?_
    refine specR_lvViewI hok a .zero (by simp) ha (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) lvScratch_DL
      (fun Γ1 M1 Pa hp1 hx1 hy1 _ _ => ?_)
    refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 0) (by decide) (by simp [hx1, ltag]) ?_
    refine specR_assignI lA3 (vv lY) Pa (by decide) (by simp +decide [hy1]) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    rw [combining_zero_left]
    exact specR_returnI (vv pLb) b (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv])
      (fun t ht => ⟨C.H, List.prefix_refl _, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ u ih =>
    intro a b lb s ha hb
    exact comb_nz C hok hcC _ lb a b s (by simp) ha hb
      (fun u' v wu wv e r1 r2 => by cases e; exact ih wu wv v s r1 r2)
  | max u v _ _ =>
    intro a b lb s ha hb
    exact comb_nz C hok hcC _ lb a b s (by simp) ha hb (fun _ _ _ _ e _ _ => by cases e)
  | imax u v _ _ =>
    intro a b lb s ha hb
    exact comb_nz C hok hcC _ lb a b s (by simp) ha hb (fun _ _ _ _ e _ _ => by cases e)
  | param n =>
    intro a b lb s ha hb
    exact comb_nz C hok hcC _ lb a b s (by simp) ha hb (fun _ _ _ _ e _ _ => by cases e)

end

end ConPanqueque.T.LComb
