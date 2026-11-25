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

/-- The view and the two loads of `fetch1`; `Q` is what the caller learns about the first child word. -/
theorem fetch1_gen {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (src : MlS) (w : BitVec 64) (a b : ConLeche.Level) (Q : Mem → BitVec 64 → BitVec 64 → Prop)
    (hQ : ∀ M' Pc, LKids C.HB C.H s.store.ls Pc M' b → ∃ wx, (Pc + BitVec.ofNat 64 (8 * 0), wx) ∈ M' ∧ Q M' Pc wx)
    (hw : Γ.get src = some w) (hl : LRep C.HB C.H s.store.ls w (.imax a b))
    (hfl : Γ.get lFll = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR)
    (hk : ∀ (Γ' : Env) (M' : Mem) (Pc wa wx : BitVec 64), (∀ z, z ∉ fScr → Γ'.get z = Γ.get z) →
      Γ'.get lA0 = some wa → LRep C.HB C.H s.store.ls wa a → Γ'.get lY = some Pc →
      Γ'.get lBx = some wx → Q M' Pc wx → SpecR (Inv C s Γ' M' DM) rest s m R) :
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
  obtain ⟨wx, mx, qx⟩ := hQ M2 P2 hk2
  refine specR_loadI' lBx (vv lY) P2 (P2 + BitVec.ofNat 64 (8 * 0)) wx (by decide) (by simp +decide [hy2])
    (by simp) mx ?_
  refine hk _ M2 P2 wa wx (fun z hz => ?_) ?_ ra (by simp +decide [hy2]) (by simp) qx
  · simp only [fScr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
    simp only [Env.get_cons, hz4, ite_false]
    rw [hp2 _ hz1]; simp only [Env.get_cons, hz2, hz3, ite_false]; rw [hp1 _ hz1]; simp [hz2]
  · simp +decide; rw [hp2 _ (by decide)]; simp +decide

/-- `fetch1` at `imax a (param p)`: the name handle lands in `bx`. -/
theorem fetch1P_spec {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (src : MlS) (w : BitVec 64) (a : ConLeche.Level) (p : ConLeche.Name)
    (hw : Γ.get src = some w) (hl : LRep C.HB C.H s.store.ls w (.imax a (.param p)))
    (hfl : Γ.get lFll = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR)
    (hk : ∀ (Γ' : Env) (M' : Mem) (nh : NIdx) (f : Nat), (∀ z, z ∉ fScr → Γ'.get z = Γ.get z) →
      Γ'.get lBx = some (Enc.idxW nh) → denoteNAux s.store.ls.ns f nh = some p →
      SpecR (Inv C s Γ' M' DM) rest s m R) :
    SpecR (Inv C s Γ M DM) (fetch1 src rest) s m R :=
  fetch1_gen hok src w a (.param p) (fun _ _ wx => ∃ (nh : NIdx) (f : Nat), wx = Enc.idxW nh ∧
      denoteNAux s.store.ls.ns f nh = some p)
    (fun _ _ ⟨nh, f, mn, hd⟩ => ⟨_, mn, nh, f, rfl, hd⟩) hw hl hfl hdir
    (fun Γ' M' _ _ _ hp _ _ _ hbx ⟨nh, f, e, hd⟩ => by subst e; exact hk Γ' M' nh f hp hbx hd)

/-- `fetch2` at `imax a b` with `b` a binary node over `x`, `y`. -/
theorem fetch2_spec {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (src : MlS) (w : BitVec 64) (a b x y : ConLeche.Level) (hb : b = .imax x y ∨ b = .max x y)
    (hw : Γ.get src = some w) (hl : LRep C.HB C.H s.store.ls w (.imax a b))
    (hfl : Γ.get lFll = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR)
    (hk : ∀ (Γ' : Env) (M' : Mem) (wa wx wy : BitVec 64), (∀ z, z ∉ fScr → Γ'.get z = Γ.get z) →
      Γ'.get lA0 = some wa → LRep C.HB C.H s.store.ls wa a →
      Γ'.get lBx = some wx → LRep C.HB C.H s.store.ls wx x →
      Γ'.get lBy = some wy → LRep C.HB C.H s.store.ls wy y →
      SpecR (Inv C s Γ' M' DM) rest s m R) :
    SpecR (Inv C s Γ M DM) (fetch2 src rest) s m R := by
  unfold fetch2
  refine fetch1_gen hok src w a b (fun M' Pc wx => LRep C.HB C.H s.store.ls wx x ∧
      ∃ wy, (Pc + BitVec.ofNat 64 (8 * 1), wy) ∈ M' ∧ LRep C.HB C.H s.store.ls wy y)
    (fun M' Pc hk2 => by
      rcases hb with rfl | rfl <;>
      · obtain ⟨wu, wv, mu, mv, ru, rv⟩ := hk2; exact ⟨wu, mu, ru, wv, mv, rv⟩)
    hw hl hfl hdir (fun Γ' M' Pc wa wx hp ga ra gy gx ⟨rx, wy, my, ry⟩ => ?_)
  refine specR_loadI' lBy (.op .add [vv lY, .const 8]) (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wy (by decide)
    (by simp +decide [sev, gy]) (by simp) my ?_
  refine hk _ M' wa wx wy (fun z hz => ?_) (by simp +decide [ga]) ra (by simp +decide [gx]) rx (by simp) ry
  simp only [fScr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  simp only [Env.get_cons, hz.2.2.2.2, ite_false]; exact hp z (by
    simp only [fScr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hz)

end

/-! ## The body -/

def callBC : ProgHOL 64 :=
  .seq (.call (some (some (.local, lV), none)) fByC [vv pFu, vv lBx, vv pLa, vv pLb, vv pD]) (.return (vv lV))

def leqRet (a b : MlS) : ProgHOL 64 := .seq (callLeqP lV a b (vv pD)) (.return (vv lV))

def simpW (rest : ProgHOL 64) : ProgHOL 64 := .seq (.call (some (some (.local, lW), none)) fSimp [vv lW]) rest

def eqC (x : MlS) (k : Nat) : ExpHOL 64 := .cmp .equal (vv x) (.const (BitVec.ofNat 64 k))

def imBody (C : Ctx) : ProgHOL 64 :=
  prologue imLocals
   (.seq (.call (some (some (.local, lTb), none)) fITag [vv pLa])
   (.seq (.call (some (some (.local, lPb), none)) fITag [vv pLb])
   (.ite (eqC lTb 4) (fetch1 pLa callBC)
   (.ite (eqC lPb 4) (fetch1 pLb callBC)
   (.ite (eqC lTb 3) (fetch2 pLa (mkMI C lA0 lBy lBx lBy (leqRet lW pLb)))
   (.ite (eqC lTb 2) (fetch2 pLa (mkMI C lA0 lBx lA0 lBy (simpW (leqRet lW pLb))))
   (.ite (eqC lPb 3) (fetch2 pLb (mkMI C lA0 lBy lBx lBy (leqRet pLa lW)))
   (.ite (eqC lPb 2) (fetch2 pLb (mkMI C lA0 lBx lA0 lBy (simpW (leqRet pLa lW))))
   (.return (.const 0))))))))))

theorem innerCode_lt (l : ConLeche.Level) : innerCode l < 10 := by
  cases l <;> simp [innerCode]; have := ltag_lt ‹_›; omega

section
variable {σ : Type}

theorem specR_ifEq {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (a b : Nat) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) (hx : Γ.get x = some (BitVec.ofNat 64 a))
    (h1 : a = b → SpecR (Inv C s Γ M D) c1 s m R) (h2 : a ≠ b → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite (eqC x b) c1 c2) s m R := by
  by_cases e : a = b
  · subst e
    exact specR_ifI _ 1 (by simp [eqC, sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => h1 rfl)
      (fun h => absurd h (by decide))
  · exact specR_ifI _ 0 (by simp [eqC, sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_eq_iff a b ha hb, e])
      (fun h => absurd rfl h) (fun _ => h2 e)

theorem params_noneIM (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ imLocals → (ctxEnv C ++ leqParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ leqParams := by
    simp only [imLocals, leqLocals, lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [imLocals, leqLocals, lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have hz : ∀ (ps : List MlS) (vs : List (BitVec 64)), x ∉ ps → Env.get (ps.zip vs) x = none := by
    intro ps vs hp
    induction ps generalizing vs with
    | nil => rfl
    | cons p ps ih =>
      cases vs with
      | nil => rfl
      | cons v vs =>
        simp only [List.mem_cons, not_or] at hp
        simp only [List.zip_cons_cons, Env.get, hp.1, ite_false]; exact ih vs hp.2
  have happ : ∀ (A B : Env), A.get x = none → B.get x = none → (A ++ B).get x = none := by
    intro A B hA hB
    induction A with
    | nil => exact hB
    | cons p A ih =>
      obtain ⟨y, v⟩ := p
      simp only [List.cons_append, Env.get] at hA ⊢
      split at hA
      · simp at hA
      · rename_i e; simp only [e, ite_false]; exact ih hA
  exact happ _ _ hc (hz _ _ hnot)

end

section
variable {σ : Type}

theorem im_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (hcB : C.code.lookup fByC = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody C, .one))
    (hcI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one))
    (B : ProgHOL 64) (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), B, .one))
    (n : Nat) (hn : n < 2 ^ 64) (ih : RecLeq (σ := σ) C B n) :
    ∀ (H : List (BitVec 64)) (l r : ConLeche.Level) (wl wr : BitVec 64) (d : Int) (s : AState),
      LRep C.HB H s.store.ls wl l → LRep C.HB H s.store.ls wr r → d.natAbs + n < 2 ^ 62 →
      SpecR (Pre (σ := σ) (ctxH C H) s (leqParams.zip [BitVec.ofNat 64 n, wl, wr, iW d])) (imBody C) s
        (pure (ConLeche.Level.imaxRules n l r d)) (PostOB (ctxH C H)) := by
  intro H l r wl wr d s hl hr hd
  refine specR_prologue (postOB_locals _) (params_noneIM _ _) ?_
  refine specR_congr (m' := pure (innerCode l) >>= fun _ => pure (innerCode r) >>= fun _ =>
    pure (ConLeche.Level.imaxRules n l r d)) (by simp) ?_
  refine callNat_spec (C := ctxH C H) lTb fITag [pLa] [vv pLa] itagBody [wl] (by decide) rfl (by decide) hcI
    ⟨by simp +decide [ctxEnv, leqParams], trivial⟩ _ (itag_spec C hok H wl l s hl) ?_
  refine callNat_spec (C := ctxH C H) lPb fITag [pLa] [vv pLb] itagBody [wr] (by decide) rfl (by decide) hcI
    ⟨by simp +decide [ctxEnv, leqParams], trivial⟩ _ (itag_spec C hok H wr r s hr) ?_
  generalize hG : ((lPb, BitVec.ofNat 64 (innerCode r)) :: (lTb, BitVec.ofNat 64 (innerCode l)) ::
    (ctxEnv (ctxH C H) ++ leqParams.zip [BitVec.ofNat 64 n, wl, wr, iW d])) = G
  have gFu : Env.get G pFu = some (BitVec.ofNat 64 n) := by subst hG; simp +decide [ctxEnv, leqParams]
  have gLa : Env.get G pLa = some wl := by subst hG; simp +decide [ctxEnv, leqParams]
  have gLb : Env.get G pLb = some wr := by subst hG; simp +decide [ctxEnv, leqParams]
  have gD : Env.get G pD = some (iW d) := by subst hG; simp +decide [ctxEnv, leqParams]
  have gFl : Env.get G lFll = some (ctxH C H).FLl := by subst hG; simp +decide [ctxEnv, leqParams]
  have gDir : Env.get G lDir = some (ctxH C H).L.DIR := by subst hG; simp +decide [ctxEnv, leqParams]
  have gTl : Env.get G lTb = some (BitVec.ofNat 64 (innerCode l)) := by subst hG; simp +decide
  have gTr : Env.get G lPb = some (BitVec.ofNat 64 (innerCode r)) := by subst hG; simp +decide
  have il := innerCode_lt l
  have ir := innerCode_lt r
  have hok' := ctxOK_H hok H
  refine specR_ifEq lTb (innerCode l) 4 (by omega) (by decide) gTl (fun e => ?_) (fun e1 => ?_)
  · obtain ⟨u, p, rfl, heq⟩ := ir_c1 n l r d e
    rw [heq]
    refine fetch1P_spec hok' pLa wl u p gLa hl gFl gDir (fun Γ' M' nh f hp gbx hnd => ?_)
    refine specR_congr (m' := pure (ConLeche.Level.byCases n p (.imax u (.param p)) r d) >>= fun o => pure o) (by simp) ?_
    refine callOB_spec (C := ctxH C H) lV fByC bcParams [vv pFu, vv lBx, vv pLa, vv pLb, vv pD] (bcBody C)
      [BitVec.ofNat 64 n, Enc.idxW nh, wl, wr, iW d] (by decide) rfl (by decide) hcB
      ⟨by simp only [sev_vv]; rw [hp _ (by decide)]; exact gFu, by simp [gbx], by simp only [sev_vv]; rw [hp _ (by decide)]; exact gLa, by simp only [sev_vv]; rw [hp _ (by decide)]; exact gLb, by simp only [sev_vv]; rw [hp _ (by decide)]; exact gD, trivial⟩ _
      (bc_spec C hok hcS hcN hcM hcC B hcL n hn ih H nh f p _ _ wl wr d s hnd hl hr hd) ?_
    exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifEq lPb (innerCode r) 4 (by omega) (by decide) gTr (fun e => ?_) (fun e2 => ?_)
  · obtain ⟨u, p, rfl, heq⟩ := ir_c2 n l r d e1 e
    rw [heq]
    refine fetch1P_spec hok' pLb wr u p gLb hr gFl gDir (fun Γ' M' nh f hp gbx hnd => ?_)
    refine specR_congr (m' := pure (ConLeche.Level.byCases n p l (.imax u (.param p)) d) >>= fun o => pure o) (by simp) ?_
    refine callOB_spec (C := ctxH C H) lV fByC bcParams [vv pFu, vv lBx, vv pLa, vv pLb, vv pD] (bcBody C)
      [BitVec.ofNat 64 n, Enc.idxW nh, wl, wr, iW d] (by decide) rfl (by decide) hcB
      ⟨by simp only [sev_vv]; rw [hp _ (by decide)]; exact gFu, by simp [gbx], by simp only [sev_vv]; rw [hp _ (by decide)]; exact gLa, by simp only [sev_vv]; rw [hp _ (by decide)]; exact gLb, by simp only [sev_vv]; rw [hp _ (by decide)]; exact gD, trivial⟩ _
      (bc_spec C hok hcS hcN hcM hcC B hcL n hn ih H nh f p _ _ wl wr d s hnd hl hr hd) ?_
    exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifEq lTb (innerCode l) 3 (by omega) (by decide) gTl (fun e => ?_) (fun e3 => ?_)
  · obtain ⟨a, x, y, rfl, heq⟩ := ir_c3 n l r d e e2
    rw [heq]
    refine fetch2_spec hok' pLa wl a _ x y (Or.inl rfl) gLa hl gFl gDir (fun Γ' M' wa wx wy hp ga ra gx rx gy ry => ?_)
    refine mkMI_spec C hok lA0 lBy lBx lBy (by decide) a y x y wa wy wx wy ga gy gx gy ra ry rx ry (fun H3 w Γ3 hp3 hw g3 hp3' => ?_)
    have gg : ∀ z, z ∉ fScr → z ≠ lW → z ≠ lW1 → z ≠ lW2 → Env.get Γ3 z = Env.get G z :=
      fun z h1 h2 h3 h4 => by rw [hp3' z h2 h3 h4, hp z h1]
    refine specR_congr (m' := pure (ConLeche.Level.leqCore n (.max (.imax a y) (.imax x y)) r d) >>= fun o => pure o) (by simp) ?_
    refine callOB_spec (C := ctxH C H3) lV fLeq leqParams [vv pFu, vv lW, vv pLb, vv pD] B [BitVec.ofNat 64 n, w, wr, iW d] (by decide) rfl (by decide) hcL
      ⟨by simp only [sev_vv]; rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact gFu, by simp [g3], by simp only [sev_vv]; rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact gLb, by simp only [sev_vv]; rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact gD, trivial⟩ _ (ih H3 _ _ w wr d s hw (lrep_mono hp3 _ wr hr) hd) ?_
    exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H3)
      (sr_of_eq ht.sr rfl rfl rfl rfl) hp3⟩)
  refine specR_ifEq lTb (innerCode l) 2 (by omega) (by decide) gTl (fun e => ?_) (fun e4 => ?_)
  · obtain ⟨a, x, y, rfl, heq⟩ := ir_c4 n l r d e e2
    rw [heq]
    refine fetch2_spec hok' pLa wl a _ x y (Or.inr rfl) gLa hl gFl gDir (fun Γ' M' wa wx wy hp ga ra gx rx gy ry => ?_)
    refine mkMI_spec C hok lA0 lBx lA0 lBy (by decide) a x a y wa wx wa wy ga gx ga gy ra rx ra ry (fun H3 w Γ3 hp3 hw g3 hp3' => ?_)
    have gg : ∀ z, z ∉ fScr → z ≠ lW → z ≠ lW1 → z ≠ lW2 → Env.get Γ3 z = Env.get G z :=
      fun z h1 h2 h3 h4 => by rw [hp3' z h2 h3 h4, hp z h1]
    refine specR_congr (m' := pure (ConLeche.Level.simplify (.max (.imax a x) (.imax a y))) >>= (fun F => pure (ConLeche.Level.leqCore n F r d) >>= fun o => pure o)) (by simp) ?_
    unfold simpW
    refine callLv_spec (C := ctxH C H3) lW fSimp [pLa] [vv lW] (simpBody C) [w] (by decide) rfl (by decide) hcM
      ⟨by simp [g3], trivial⟩ _ (simp_spec C hok hcM hcC _ H3 w s hw) (fun H4 w4 hp4 hr4 => ?_)
    refine callOB_spec (C := ctxH C H4) lV fLeq leqParams [vv pFu, vv lW, vv pLb, vv pD] B [BitVec.ofNat 64 n, w4, wr, iW d] (by decide) rfl (by decide) hcL
      ⟨by simp only [sev_vv, Env.get_cons]; rw [ite_eq_right (by decide), gg _ (by decide) (by decide) (by decide) (by decide)]; exact gFu, by simp, by simp only [sev_vv, Env.get_cons]; rw [ite_eq_right (by decide), gg _ (by decide) (by decide) (by decide) (by decide)]; exact gLb, by simp only [sev_vv, Env.get_cons]; rw [ite_eq_right (by decide), gg _ (by decide) (by decide) (by decide) (by decide)]; exact gD, trivial⟩ _ (ih H4 _ _ w4 wr d s hr4 (lrep_mono (hp3.trans hp4) _ wr hr) hd) ?_
    exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H4)
      (sr_of_eq ht.sr rfl rfl rfl rfl) (hp3.trans hp4)⟩)
  refine specR_ifEq lPb (innerCode r) 3 (by omega) (by decide) gTr (fun e => ?_) (fun e5 => ?_)
  · obtain ⟨a, x, y, rfl, heq⟩ := ir_c5 n l r d e1 e3 e4 e
    rw [heq]
    refine fetch2_spec hok' pLb wr a _ x y (Or.inl rfl) gLb hr gFl gDir (fun Γ' M' wa wx wy hp ga ra gx rx gy ry => ?_)
    refine mkMI_spec C hok lA0 lBy lBx lBy (by decide) a y x y wa wy wx wy ga gy gx gy ra ry rx ry (fun H3 w Γ3 hp3 hw g3 hp3' => ?_)
    have gg : ∀ z, z ∉ fScr → z ≠ lW → z ≠ lW1 → z ≠ lW2 → Env.get Γ3 z = Env.get G z :=
      fun z h1 h2 h3 h4 => by rw [hp3' z h2 h3 h4, hp z h1]
    refine specR_congr (m' := pure (ConLeche.Level.leqCore n l (.max (.imax a y) (.imax x y)) d) >>= fun o => pure o) (by simp) ?_
    refine callOB_spec (C := ctxH C H3) lV fLeq leqParams [vv pFu, vv pLa, vv lW, vv pD] B [BitVec.ofNat 64 n, wl, w, iW d] (by decide) rfl (by decide) hcL
      ⟨by simp only [sev_vv]; rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact gFu, by simp only [sev_vv]; rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact gLa, by simp [g3], by simp only [sev_vv]; rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact gD, trivial⟩ _ (ih H3 _ _ wl w d s (lrep_mono hp3 _ wl hl) hw hd) ?_
    exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H3)
      (sr_of_eq ht.sr rfl rfl rfl rfl) hp3⟩)
  refine specR_ifEq lPb (innerCode r) 2 (by omega) (by decide) gTr (fun e => ?_) (fun e6 => ?_)
  · obtain ⟨a, x, y, rfl, heq⟩ := ir_c6 n l r d e1 e3 e4 e
    rw [heq]
    refine fetch2_spec hok' pLb wr a _ x y (Or.inr rfl) gLb hr gFl gDir (fun Γ' M' wa wx wy hp ga ra gx rx gy ry => ?_)
    refine mkMI_spec C hok lA0 lBx lA0 lBy (by decide) a x a y wa wx wa wy ga gx ga gy ra rx ra ry (fun H3 w Γ3 hp3 hw g3 hp3' => ?_)
    have gg : ∀ z, z ∉ fScr → z ≠ lW → z ≠ lW1 → z ≠ lW2 → Env.get Γ3 z = Env.get G z :=
      fun z h1 h2 h3 h4 => by rw [hp3' z h2 h3 h4, hp z h1]
    refine specR_congr (m' := pure (ConLeche.Level.simplify (.max (.imax a x) (.imax a y))) >>= (fun F => pure (ConLeche.Level.leqCore n l F d) >>= fun o => pure o)) (by simp) ?_
    unfold simpW
    refine callLv_spec (C := ctxH C H3) lW fSimp [pLa] [vv lW] (simpBody C) [w] (by decide) rfl (by decide) hcM
      ⟨by simp [g3], trivial⟩ _ (simp_spec C hok hcM hcC _ H3 w s hw) (fun H4 w4 hp4 hr4 => ?_)
    refine callOB_spec (C := ctxH C H4) lV fLeq leqParams [vv pFu, vv pLa, vv lW, vv pD] B [BitVec.ofNat 64 n, wl, w4, iW d] (by decide) rfl (by decide) hcL
      ⟨by simp only [sev_vv, Env.get_cons]; rw [ite_eq_right (by decide), gg _ (by decide) (by decide) (by decide) (by decide)]; exact gFu, by simp only [sev_vv, Env.get_cons]; rw [ite_eq_right (by decide), gg _ (by decide) (by decide) (by decide) (by decide)]; exact gLa, by simp, by simp only [sev_vv, Env.get_cons]; rw [ite_eq_right (by decide), gg _ (by decide) (by decide) (by decide) (by decide)]; exact gD, trivial⟩ _ (ih H4 _ _ wl w4 d s (lrep_mono (hp3.trans hp4) _ wl hl) hr4 hd) ?_
    exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H4)
      (sr_of_eq ht.sr rfl rfl rfl rfl) (hp3.trans hp4)⟩)
  rw [ir_c7 n l r d e1 e3 e4 e2 e5 e6]
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.LLeq
