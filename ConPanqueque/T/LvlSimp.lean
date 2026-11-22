import ConPanqueque.T.LvlComb
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `simplify`

con-leche's `Level.simplify`: `succ` and `max` normalize their children (`combining` for `max`), and an
`imax` collapses when its left side is `0` or `1` or its right side is `0` or a successor.
-/

namespace ConPanqueque.T.LSimp
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.LComb

def fSimp := ofString "simplify"

/-- With `ls` in `a1` and `rs` in `z`: the right side's shape. -/
def imaxR (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv lZ)) (lvViewP
    (.ite (.cmp .equal (vv lX) (.const 0)) (.return (vv lZ))
      (.ite (.cmp .equal (vv lX) (.const 1))
        (.seq (.call (some (some (.local, lW), none)) fComb [vv lA1, vv lZ]) (.return (vv lW)))
        (alloc3 C lW (.const 3) (vv lA1) (vv lZ) (.return (vv lW))))))

/-- The left side `0` or `1` answers `rs`; otherwise the right side decides. -/
def imaxT (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv lA1)) (lvViewP
    (.ite (.cmp .equal (vv lX) (.const 0)) (.return (vv lZ))
      (.ite (.cmp .equal (vv lX) (.const 1))
        (.seq (.assign .local lD1 (.load .one (vv lY))) (.seq (.assign .local lQ (vv lD1)) (lvViewP
          (.ite (.cmp .equal (vv lX) (.const 0)) (.return (vv lZ)) (imaxR C)))))
        (imaxR C))))

def simpRest (C : Ctx) : ProgHOL 64 :=
    .ite (.cmp .equal (vv lA2) (.const 0)) (.return (vv pLa))
    (.ite (.cmp .equal (vv lA2) (.const 4)) (.return (vv pLa))
    (.seq (.assign .local lD1 (.load .one (vv lA3)))
    (.ite (.cmp .equal (vv lA2) (.const 1))
      (.seq (.call (some (some (.local, lA1), none)) fSimp [vv lD1])
        (alloc2 C lW (.const 1) (vv lA1) (.return (vv lW))))
      (.seq (.assign .local lB (.load .one (.op .add [vv lA3, .const 8])))
      (.seq (.call (some (some (.local, lA1), none)) fSimp [vv lD1])
      (.seq (.call (some (some (.local, lZ), none)) fSimp [vv lB])
      (.ite (.cmp .equal (vv lA2) (.const 2))
        (.seq (.call (some (some (.local, lW), none)) fComb [vv lA1, vv lZ]) (.return (vv lW)))
        (imaxT C))))))))

def simpCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv pLa)) (lvViewP
    (.seq (.assign .local lA2 (vv lX)) (.seq (.assign .local lA3 (vv lY)) (simpRest C))))

def simpBody (C : Ctx) : ProgHOL 64 := prologue lvlLocals (simpCore C)

/-- The twin's `imax` case after both sides are simplified. -/
def imaxTw (ls rs : ConLeche.Level) : ConLeche.Level :=
  if ls = .zero || ls = .succ .zero then rs
  else match rs with
    | .zero => .zero
    | .succ _ => ConLeche.Level.combining ls rs
    | _ => .imax ls rs

/-- The `imax` case once the left side is neither `0` nor `1`. -/
def imaxRTw (ls rs : ConLeche.Level) : ConLeche.Level :=
  match rs with
  | .zero => .zero
  | .succ _ => ConLeche.Level.combining ls rs
  | _ => .imax ls rs

theorem simplify_imax (l r : ConLeche.Level) :
    ConLeche.Level.simplify (.imax l r) = imaxTw (ConLeche.Level.simplify l) (ConLeche.Level.simplify r) := by
  simp only [ConLeche.Level.simplify, imaxTw]
  split <;> rfl

section
variable {σ : Type}

theorem imaxR_spec (C : Ctx) (hok : CtxOK C)
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    {s : AState} {Γ : Env} {M : Mem} (ls rs : ConLeche.Level) (wl wr : BitVec 64)
    (h1 : Γ.get lA1 = some wl) (hz : Γ.get lZ = some wr) (hfl : Γ.get lFll = some C.FLl)
    (hdir : Γ.get lDir = some C.L.DIR)
    (hrl : LRep C.HB C.H s.store.ls wl ls) (hrr : LRep C.HB C.H s.store.ls wr rs) :
    SpecR (Inv (σ := σ) C s Γ M DL) (imaxR C) s (pure (imaxRTw ls rs)) (PostLv C) := by
  unfold imaxR
  refine specR_assignI lQ (vv lZ) wr (by decide) (by simp +decide [hz]) ?_
  refine specR_lvViewI hok wr rs (by simp) hrr (by simp +decide [hfl]) (by simp +decide [hdir]) lvScratch_DL
    (fun Γ1 M1 Pc hp1 hx1 hy1 hmm1 hkd1 => ?_)
  have hA1 : Γ1.get lA1 = some wl := by rw [hp1 _ (by decide)]; simp +decide [h1]
  have hZ : Γ1.get lZ = some wr := by rw [hp1 _ (by decide)]; simp +decide [hz]
  cases rs
  case zero =>
    simp only [imaxRTw]
    refine specR_ifI _ 1 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    exact specR_returnI (vv lZ) wr (by simp [hZ]) (fun t ht => ⟨C.H, List.prefix_refl _, hrr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  case succ v =>
    simp only [imaxRTw]
    refine specR_ifI _ 0 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure (ConLeche.Level.combining ls (.succ v)) >>= fun r => pure r) (by simp) ?_
    refine callLv_spec lW fComb [pLa, pLb] [vv lA1, vv lZ] (combBody C) [wl, wr] (by decide) rfl (by decide) hcC
      ⟨by simp [hA1], by simp [hZ], trivial⟩ _ (comb_spec C hok hcC ls wl wr (.succ v) s hrl hrr)
      (fun H1 c hp hc => ?_)
    exact specR_returnI (vv lW) c (by simp) (fun t ht => ⟨H1, hp, hc, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  all_goals
    simp only [imaxRTw]
    refine specR_ifI _ 0 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_alloc3I hok lW (.const 3) (vv lA1) (vv lZ) 3 wl wr (by decide) (fun _ => rfl)
      (fun _ => by simp +decide [hA1]) (fun _ => by simp +decide [hZ]) (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide) (fun t ht => ?_)
    exact ⟨_, hp2.trans (img3_prefix H2 ws _ wl wr hws),
      lrep_mkImax C s.store.ls H2 ws wl wr ls _ hws hp2 hrl hrr, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

section
variable {σ : Type}

theorem imaxTw_else (ls rs : ConLeche.Level) (h0 : ls ≠ .zero) (h1 : ls ≠ .succ .zero) :
    imaxTw ls rs = imaxRTw ls rs := by
  simp [imaxTw, imaxRTw, h0, h1]

theorem imaxT_spec (C : Ctx) (hok : CtxOK C)
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    {s : AState} {Γ : Env} {M : Mem} (ls rs : ConLeche.Level) (wl wr : BitVec 64)
    (h1 : Γ.get lA1 = some wl) (hz : Γ.get lZ = some wr) (hfl : Γ.get lFll = some C.FLl)
    (hdir : Γ.get lDir = some C.L.DIR)
    (hrl : LRep C.HB C.H s.store.ls wl ls) (hrr : LRep C.HB C.H s.store.ls wr rs) :
    SpecR (Inv (σ := σ) C s Γ M DL) (imaxT C) s (pure (imaxTw ls rs)) (PostLv C) := by
  unfold imaxT
  refine specR_assignI lQ (vv lA1) wl (by decide) (by simp +decide [h1]) ?_
  refine specR_lvViewI hok wl ls (by simp) hrl (by simp +decide [hfl]) (by simp +decide [hdir]) lvScratch_DL
    (fun Γ1 M1 Pc hp1 hx1 hy1 hmm1 hkd1 => ?_)
  have hA1 : Γ1.get lA1 = some wl := by rw [hp1 _ (by decide)]; simp +decide [h1]
  have hZ : Γ1.get lZ = some wr := by rw [hp1 _ (by decide)]; simp +decide [hz]
  have hFl : Γ1.get lFll = some C.FLl := by rw [hp1 _ (by decide)]; simp +decide [hfl]
  have hDir : Γ1.get lDir = some C.L.DIR := by rw [hp1 _ (by decide)]; simp +decide [hdir]
  by_cases e0 : ls = .zero
  · subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    rw [show imaxTw .zero rs = rs by simp [imaxTw]]
    exact specR_returnI (vv lZ) wr (by simp [hZ]) (fun t ht => ⟨C.H, List.prefix_refl _, hrr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have ht0 : ltag ls ≠ 0 := by cases ls <;> simp_all [ltag]
  refine specR_ifI _ 0 (by simp +decide [sev, hx1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_ltag_ne _ 0 (ltag_lt ls) (by decide) ht0])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  by_cases e1 : ltag ls = 1
  · obtain ⟨c, rfl⟩ : ∃ c, ls = .succ c := by cases ls <;> simp_all [ltag]
    refine specR_ifI _ 1 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    obtain ⟨wc, mc, rc⟩ := hkd1
    refine specR_loadI' lD1 (vv lY) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wc (by decide) (by simp +decide [hy1])
      (by simp) mc ?_
    refine specR_assignI lQ (vv lD1) wc (by decide) (by simp +decide) ?_
    refine specR_lvViewI hok wc c (by simp) rc (by simp +decide [hFl]) (by simp +decide [hDir]) lvScratch_DL
      (fun Γ2 M2 Pd hp2 hx2 hy2 hmm2 hkd2 => ?_)
    by_cases ec : c = .zero
    · subst ec
      refine specR_ifI _ 1 (by simp +decide [sev, hx2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
      rw [show imaxTw (.succ .zero) rs = rs by simp [imaxTw]]
      exact specR_returnI (vv lZ) wr (by simp only [sev_vv]; rw [hp2 _ (by decide)]; simp +decide [hZ])
        (fun t ht => ⟨C.H, List.prefix_refl _, hrr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hc0 : ltag c ≠ 0 := by cases c <;> simp_all [ltag]
    refine specR_ifI _ 0 (by simp +decide [sev, hx2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_ltag_ne _ 0 (ltag_lt c) (by decide) hc0])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    rw [imaxTw_else _ rs (by simp) (by simpa using ec)]
    exact imaxR_spec C hok hcC (.succ c) rs wl wr (by rw [hp2 _ (by decide)]; simp +decide [hA1])
      (by rw [hp2 _ (by decide)]; simp +decide [hZ]) (by rw [hp2 _ (by decide)]; simp +decide [hFl])
      (by rw [hp2 _ (by decide)]; simp +decide [hDir]) hrl hrr
  · refine specR_ifI _ 0 (by simp +decide [sev, hx1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_ltag_ne _ 1 (ltag_lt ls) (by decide) e1])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    rw [imaxTw_else ls rs e0 (fun e => by rw [e] at e1; simp [ltag] at e1)]
    exact imaxR_spec C hok hcC ls rs wl wr hA1 hZ hFl hDir hrl hrr

end

section
variable {σ : Type}

theorem params_noneS (va : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ lvlLocals → (ctxEnv C ++ [(pLa, va)]).get x = none := by
  intro x hx
  simp only [lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem simp_view (C : Ctx) (hok : CtxOK C) (H : List (BitVec 64)) (w : BitVec 64) (l : ConLeche.Level)
    (s : AState) (hl : LRep C.HB H s.store.ls w l) (m : AM ConLeche.Level)
    (hk : ∀ (Γ1 : Env) (M1 : Mem) (Pc : BitVec 64), Γ1.get lA2 = some (BitVec.ofNat 64 (ltag l)) →
      Γ1.get lA3 = some Pc → Γ1.get pLa = some w → Γ1.get lFll = some C.FLl → Γ1.get lDir = some C.L.DIR →
      Γ1.get lA1 = none → Γ1.get lZ = none → Γ1.get lB = none → Γ1.get lD1 = none → Γ1.get lW = none →
      LKids C.HB H s.store.ls Pc M1 l →
      SpecR (Inv (σ := σ) (ctxH C H) s Γ1 M1 DL) (simpRest C) s m (PostLv (ctxH C H))) :
    SpecR (Pre (σ := σ) (ctxH C H) s [(pLa, w)]) (simpBody C) s m (PostLv (ctxH C H)) := by
  refine specR_prologue (postLv_locals _) (params_noneS _ _) ?_
  unfold simpCore
  refine specR_assignI lQ (vv pLa) w (by decide) (by simp +decide [ctxEnv]) ?_
  refine specR_lvViewI (C := ctxH C H) (ctxOK_H hok H) w l (by simp) hl (by simp +decide [ctxEnv] <;> rfl)
    (by simp +decide [ctxEnv] <;> rfl) lvScratch_DL (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => ?_)
  refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 (ltag l)) (by decide) (by simp [hx1]) ?_
  refine specR_assignI lA3 (vv lY) Pc (by decide) (by simp +decide [hy1]) ?_
  refine hk _ _ Pc (by simp +decide) (by simp +decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hk1 <;>
    (simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv]) <;> rfl

/-- `simplify` refined, at any image. -/
theorem simp_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one)) :
    ∀ (l : ConLeche.Level) (H : List (BitVec 64)) (w : BitVec 64) (s : AState),
      LRep C.HB H s.store.ls w l →
      SpecR (Pre (σ := σ) (ctxH C H) s [(pLa, w)]) (simpBody C) s (pure (ConLeche.Level.simplify l))
        (PostLv (ctxH C H)) := by
  intro l
  induction l with
  | zero =>
    intro H w s hl
    refine simp_view C hok H w _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hfl hdir _ _ _ _ _ _ => ?_)
    unfold simpRest
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    exact specR_returnI (vv pLa) w (by simp [hw]) (fun t ht => ⟨H, List.prefix_refl _, hl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | param n =>
    intro H w s hl
    refine simp_view C hok H w _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hfl hdir _ _ _ _ _ _ => ?_)
    unfold simpRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    exact specR_returnI (vv pLa) w (by simp [hw]) (fun t ht => ⟨H, List.prefix_refl _, hl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ u ih =>
    intro H w s hl
    refine simp_view C hok H w _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hfl hdir n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, m1, r1⟩ := hk1
    unfold simpRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    refine specR_congr (m' := pure (ConLeche.Level.simplify u) >>= fun c => pure (ConLeche.Level.succ c)) rfl ?_
    refine callLv_spec (C := ctxH C H) lA1 fSimp [pLa] [vv lD1] (simpBody C) [wu] (by decide) rfl (by decide) hcS
      ⟨by simp +decide, trivial⟩ _ (ih H wu s r1) (fun H1 c hp1 hc => ?_)
    refine specR_alloc2I (C := ctxH C H1) (ctxOK_H hok H1) lW (.const 1) (vv lA1) 1 c (by decide) (fun _ => rfl)
      (fun _ => by simp +decide) (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp2' : H1 <+: H2 := hp2
    exact ⟨_, hp1.trans (hp2'.trans (img2_prefix H2 ws _ c hws)),
      lrep_mkSucc (ctxH C H1) s.store.ls H2 ws c _ hws hp2 hc, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | max u v ihu ihv =>
    intro H w s hl
    refine simp_view C hok H w _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hfl hdir n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, wv, m1, m2, r1, r2⟩ := hk1
    unfold simpRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lB _ (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv (by decide) (by simp +decide [sev, h3])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (ConLeche.Level.simplify u) >>= fun a =>
      pure (ConLeche.Level.simplify v) >>= fun b => pure (ConLeche.Level.combining a b)) (by simp [ConLeche.Level.simplify]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSimp [pLa] [vv lD1] (simpBody C) [wu] (by decide) rfl (by decide) hcS
      ⟨by simp +decide, trivial⟩ _ (ihu H wu s r1) (fun H1 c1 hp1 hc1 => ?_)
    refine callLv_spec (C := ctxH C H1) lZ fSimp [pLa] [vv lB] (simpBody C) [wv] (by decide) rfl (by decide) hcS
      ⟨by simp +decide, trivial⟩ _ (ihv H1 wv s (lrep_mono hp1 v wv r2)) (fun H2 c2 hp2 hc2 => ?_)
    have hc1' := lrep_mono hp2 _ c1 hc1
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    refine specR_congr (m' := pure (ConLeche.Level.combining (ConLeche.Level.simplify u) (ConLeche.Level.simplify v))
      >>= fun r => pure r) (by simp) ?_
    refine callLv_spec (C := ctxH C H2) lW fComb [pLa, pLb] [vv lA1, vv lZ] (combBody C) [c1, c2] (by decide) rfl
      (by decide) hcC ⟨by simp +decide, by simp +decide, trivial⟩ _
      (comb_spec (ctxH C H2) (ctxOK_H hok H2) hcC _ c1 c2 _ s hc1' hc2) (fun H3 r hp3 hr => ?_)
    exact specR_returnI (vv lW) r (by simp) (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), hr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | imax u v ihu ihv =>
    intro H w s hl
    refine simp_view C hok H w _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hfl hdir n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, wv, m1, m2, r1, r2⟩ := hk1
    unfold simpRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lB _ (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv (by decide) (by simp +decide [sev, h3])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (ConLeche.Level.simplify u) >>= fun a =>
      pure (ConLeche.Level.simplify v) >>= fun b => pure (imaxTw a b)) (by simp only [pure_bind, simplify_imax]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSimp [pLa] [vv lD1] (simpBody C) [wu] (by decide) rfl (by decide) hcS
      ⟨by simp +decide, trivial⟩ _ (ihu H wu s r1) (fun H1 c1 hp1 hc1 => ?_)
    refine callLv_spec (C := ctxH C H1) lZ fSimp [pLa] [vv lB] (simpBody C) [wv] (by decide) rfl (by decide) hcS
      ⟨by simp +decide, trivial⟩ _ (ihv H1 wv s (lrep_mono hp1 v wv r2)) (fun H2 c2 hp2 hc2 => ?_)
    have hc1' := lrep_mono hp2 _ c1 hc1
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_mono (imaxT_spec (ctxH C H2) (ctxOK_H hok H2) hcC _ _ c1 c2 (by simp +decide)
      (by simp +decide) (by simp +decide; rw [hfl]; rfl) (by simp +decide; rw [hdir]; rfl) hc1' hc2) (fun _ h => h)
      (fun a w' s' st ⟨H3, hp3, hr, hs⟩ => ⟨H3, hp1.trans (hp2.trans hp3), hr, hs⟩)

end

end ConPanqueque.T.LSimp
