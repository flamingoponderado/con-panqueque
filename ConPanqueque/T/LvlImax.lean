import ConPanqueque.T.LvlLeq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `imaxRules`

`innerTag(l)`: the tag of `b` when `l = imax a b`, else `9`. `imaxRules` calls it on both sides, then
picks con-leche's first matching rule, re-viewing the side it rewrites.
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub

def fITag := ofString "innerTag"

def innerCode : ConLeche.Level → Nat
  | .imax _ b => ltag b
  | _ => 9

def itagBody : ProgHOL 64 :=
  prologue lvlLocals
   (.seq (.assign .local lQ (vv pLa)) (lvViewP
    (.ite (.cmp .equal (vv lX) (.const 3))
      (.seq (.assign .local lQ (.load .one (.op .add [vv lY, .const 8]))) (lvViewP (.return (vv lX))))
      (.return (.const 9)))))

section
variable {σ : Type}

def PostNat (C : Ctx) (a : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = BitVec.ofNat 64 a ∧ SR C s' st

theorem postNat_locals (C : Ctx) : ∀ (a : Nat) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostNat C a w s' st → PostNat C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

theorem itag_spec (C : Ctx) (hok : CtxOK C) (H : List (BitVec 64)) (w : BitVec 64) (l : ConLeche.Level)
    (s : AState) (hl : LRep C.HB H s.store.ls w l) :
    SpecR (Pre (σ := σ) (ctxH C H) s [(pLa, w)]) itagBody s (pure (innerCode l)) (PostNat (ctxH C H)) := by
  refine specR_prologue (postNat_locals _) (params_noneS _ _) ?_
  refine specR_assignI lQ (vv pLa) w (by decide) (by simp +decide [ctxEnv]) ?_
  refine specR_lvViewI (C := ctxH C H) (ctxOK_H hok H) w l (by simp) hl (by simp +decide [ctxEnv] <;> rfl)
    (by simp +decide [ctxEnv] <;> rfl) lvScratch_DL (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => ?_)
  by_cases e3 : ltag l = 3
  · obtain ⟨a, b, rfl⟩ : ∃ a b, l = .imax a b := by cases l <;> simp_all [ltag]
    refine specR_ifI _ 1 (by simp +decide [sev, hx1, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun hw => absurd hw (by decide))
    obtain ⟨wa, wb, ma, mb, ra, rb⟩ := hk1
    refine specR_loadI' lQ (.op .add [vv lY, .const 8]) (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wb (by decide)
      (by simp +decide [sev, hy1]) (by simp) mb ?_
    refine specR_lvViewI (C := ctxH C H) (ctxOK_H hok H) wb b (by simp) rb
      (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv] <;> rfl)
      (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv] <;> rfl) lvScratch_DL
      (fun Γ2 M2 P2 hp2 hx2 hy2 _ _ => ?_)
    exact specR_returnI (vv lX) (BitVec.ofNat 64 (ltag b)) (by simp [hx2]) (fun t ht => ⟨by simp [innerCode], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 0 (by simp +decide [sev, hx1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      ofNat_ltag_ne _ 3 (ltag_lt l) (by decide) e3]) (fun hw => absurd rfl hw) (fun _ => ?_)
    have e9 : innerCode l = 9 := by cases l <;> simp_all [ltag, innerCode]
    rw [e9]
    exact specR_returnI (.const 9) _ rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem callNat_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Nat → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs) (o : Nat)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s (pure o) (PostNat C))
    (hk : SpecR (Inv C s ((x, BitVec.ofNat 64 o) :: Γ) [] D) rest s (k o) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (pure o >>= k) R := by
  refine specR_callNIM x f ps es B vs hnd hl hx hC hes (fun a w s' st => s' = s ∧ a = o ∧ PostNat C a w s' st)
    (fun _ _ _ _ hp => hp.2.2.2)
    (fun u hu _ hlk => by
      have H0 : SpecR (· = u) B s (pure o : AM Nat) (PostNat C) :=
        fun w hw => by subst hw; exact hspec _ (pre_of_lookups hu ps vs hl hlk)
      refine specR_mono (specR_run H0) (fun _ h => h) (fun a w s' st hp => ?_)
      obtain ⟨hrun, hp⟩ := hp
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨hrun.2.symm, hrun.1.symm, hp⟩)
    (fun a w s' st ⟨hs, ha, hw, _⟩ => by subst hs ha hw; exact hk)

end

/-! ## The twin's rule order by inner tags -/

theorem ir_c1 (n : Nat) (l r : ConLeche.Level) (d : Int) (h : innerCode l = 4) :
    ∃ u p, l = .imax u (.param p) ∧ ConLeche.Level.imaxRules n l r d = ConLeche.Level.byCases n p l r d := by
  cases l with
  | imax u b => cases b <;> simp_all [innerCode, ltag, ConLeche.Level.imaxRules]; exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
  | _ => simp [innerCode] at h

theorem ir_c2 (n : Nat) (l r : ConLeche.Level) (d : Int) (h1 : innerCode l ≠ 4) (h : innerCode r = 4) :
    ∃ u p, r = .imax u (.param p) ∧ ConLeche.Level.imaxRules n l r d = ConLeche.Level.byCases n p l r d := by
  cases r with
  | imax u b =>
    cases b <;> simp [innerCode, ltag] at h
    rename_i p
    refine ⟨u, p, rfl, ?_⟩
    cases l with
    | imax a c => cases c <;> simp_all [innerCode, ltag, ConLeche.Level.imaxRules]
    | _ => simp [ConLeche.Level.imaxRules]
  | _ => simp [innerCode] at h

theorem ir_c3 (n : Nat) (l r : ConLeche.Level) (d : Int) (h1 : innerCode l = 3) (h2 : innerCode r ≠ 4) :
    ∃ a x y, l = .imax a (.imax x y) ∧
      ConLeche.Level.imaxRules n l r d = ConLeche.Level.leqCore n (.max (.imax a y) (.imax x y)) r d := by
  cases l with
  | imax a b =>
    cases b <;> simp [innerCode, ltag] at h1
    rename_i x y
    refine ⟨a, x, y, rfl, ?_⟩
    cases r with
    | imax u c => cases c <;> simp_all [innerCode, ltag, ConLeche.Level.imaxRules]
    | _ => simp [ConLeche.Level.imaxRules]
  | _ => simp [innerCode] at h1

theorem ir_c4 (n : Nat) (l r : ConLeche.Level) (d : Int) (h1 : innerCode l = 2) (h2 : innerCode r ≠ 4) :
    ∃ a x y, l = .imax a (.max x y) ∧
      ConLeche.Level.imaxRules n l r d = ConLeche.Level.leqCore n (ConLeche.Level.simplify (.max (.imax a x) (.imax a y))) r d := by
  cases l with
  | imax a b =>
    cases b <;> simp [innerCode, ltag] at h1
    rename_i x y
    refine ⟨a, x, y, rfl, ?_⟩
    cases r with
    | imax u c => cases c <;> simp_all [innerCode, ltag, ConLeche.Level.imaxRules]
    | _ => simp [ConLeche.Level.imaxRules]
  | _ => simp [innerCode] at h1

theorem ir_c5 (n : Nat) (l r : ConLeche.Level) (d : Int) (h1 : innerCode l ≠ 4) (h2 : innerCode l ≠ 3)
    (h3 : innerCode l ≠ 2) (h : innerCode r = 3) :
    ∃ x j k, r = .imax x (.imax j k) ∧
      ConLeche.Level.imaxRules n l r d = ConLeche.Level.leqCore n l (.max (.imax x k) (.imax j k)) d := by
  cases r with
  | imax u b =>
    cases b <;> simp [innerCode, ltag] at h
    rename_i x y
    refine ⟨u, x, y, rfl, ?_⟩
    cases l with
    | imax a c => cases c <;> simp_all [innerCode, ltag, ConLeche.Level.imaxRules]
    | _ => simp [ConLeche.Level.imaxRules]
  | _ => simp [innerCode] at h

theorem ir_c6 (n : Nat) (l r : ConLeche.Level) (d : Int) (h1 : innerCode l ≠ 4) (h2 : innerCode l ≠ 3)
    (h3 : innerCode l ≠ 2) (h : innerCode r = 2) :
    ∃ x j k, r = .imax x (.max j k) ∧
      ConLeche.Level.imaxRules n l r d = ConLeche.Level.leqCore n l (ConLeche.Level.simplify (.max (.imax x j) (.imax x k))) d := by
  cases r with
  | imax u b =>
    cases b <;> simp [innerCode, ltag] at h
    rename_i x y
    refine ⟨u, x, y, rfl, ?_⟩
    cases l with
    | imax a c => cases c <;> simp_all [innerCode, ltag, ConLeche.Level.imaxRules]
    | _ => simp [ConLeche.Level.imaxRules]
  | _ => simp [innerCode] at h

theorem ir_c7 (n : Nat) (l r : ConLeche.Level) (d : Int) (h1 : innerCode l ≠ 4) (h2 : innerCode l ≠ 3)
    (h3 : innerCode l ≠ 2) (h4 : innerCode r ≠ 4) (h5 : innerCode r ≠ 3) (h6 : innerCode r ≠ 2) :
    ConLeche.Level.imaxRules n l r d = none := by
  unfold ConLeche.Level.imaxRules
  split <;> simp_all [innerCode, ltag]

/-! ## Fetching the parts of `imax a b` -/

def fetch1 (src : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv src)) (lvViewP
  (.seq (.assign .local lA0 (.load .one (vv lY)))
  (.seq (.assign .local lQ (.load .one (.op .add [vv lY, .const 8]))) (lvViewP
  (.seq (.assign .local lBx (.load .one (vv lY))) rest)))))

def fetch2 (src : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  fetch1 src (.seq (.assign .local lBy (.load .one (.op .add [vv lY, .const 8]))) rest)

theorem lvScratch_DM : ∀ z, z ∈ lvScratch → z ∈ DM := by
  intro z hz
  simp only [lvScratch, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def fScr : List MlS := lvScratch ++ [lQ, lA0, lBx, lBy]

section
variable {σ : Type}

/-- The view and the two loads of `fetch1`, for any final child shape. -/
theorem fetch1_gen {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (src : MlS) (w : BitVec 64) (a b : ConLeche.Level) (hb0 : b ≠ .zero) (hw : Γ.get src = some w)
    (hl : LRep C.HB C.H s.store.ls w (.imax a b))
    (hfl : Γ.get lFll = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR)
    (hk : ∀ (Γ' : Env) (M' : Mem) (Pc wa wx : BitVec 64), (∀ z, z ∉ fScr → Γ'.get z = Γ.get z) →
      Γ'.get lA0 = some wa → LRep C.HB C.H s.store.ls wa a → Γ'.get lY = some Pc →
      Γ'.get lX = some (BitVec.ofNat 64 (ltag b)) → (Pc + BitVec.ofNat 64 (8 * 0), wx) ∈ M' →
      Γ'.get lBx = some wx → LKids C.HB C.H s.store.ls Pc M' b →
      SpecR (Inv C s Γ' M' DM) rest s m R) :
    SpecR (Inv C s Γ M DM) (fetch1 src rest) s m R := by
  unfold fetch1
  refine specR_assignI lQ (vv src) w (by decide) (by simp [hw]) ?_
  refine specR_lvViewI hok w _ (by simp) hl (by simp +decide [hfl]) (by simp +decide [hdir]) lvScratch_DM
    (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => ?_)
  obtain ⟨wa, wb, ma, mb, ra, rb⟩ := hk1
  refine specR_loadI' lA0 (vv lY) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wa (by decide) (by simp +decide [hy1])
    (by simp) ma ?_
  refine specR_loadI' lQ (.op .add [vv lY, .const 8]) (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wb (by decide)
    (by simp +decide [sev, hy1]) (by simp) mb ?_
  refine specR_lvViewI hok wb b (by simp) rb
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [hfl])
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [hdir]) lvScratch_DM
    (fun Γ2 M2 P2 hp2 hx2 hy2 hmm2 hk2 => ?_)
  rcases (show ∃ wx, (P2 + BitVec.ofNat 64 (8 * 0), wx) ∈ M2 by
    cases b with
    | zero => exact absurd rfl hb0
    | succ u => obtain ⟨wu, mu, _⟩ := hk2; exact ⟨wu, mu⟩
    | max u v => obtain ⟨wu, _, mu, _⟩ := hk2; exact ⟨wu, mu⟩
    | imax u v => obtain ⟨wu, _, mu, _⟩ := hk2; exact ⟨wu, mu⟩
    | param n => obtain ⟨nh, _, mu, _⟩ := hk2; exact ⟨_, mu⟩) with ⟨wx, mx⟩
  refine specR_loadI' lBx (vv lY) P2 (P2 + BitVec.ofNat 64 (8 * 0)) wx (by decide) (by simp +decide [hy2])
    (by simp) mx ?_
  refine hk _ M2 P2 wa wx (fun z hz => ?_) ?_ ra (by simp +decide [hy2]) (by simp +decide [hx2]) mx (by simp) hk2
  · simp only [fScr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
    simp only [Env.get_cons, hz4, if_false]
    rw [hp2 _ hz1]; simp only [Env.get_cons, hz2, hz3, if_false]; rw [hp1 _ hz1]; simp [hz2]
  · simp +decide; rw [hp2 _ (by decide)]; simp +decide

end

end ConPanqueque.T.LLeq
