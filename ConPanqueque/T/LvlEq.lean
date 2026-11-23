import ConPanqueque.T.LvlView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Level equality by structure

`lvlEq(a, b)` decides `la = lb` (con-leche's `l == r`, lawful) for the trees the two words represent:
both views, the tags, then the children (names by `nameEq`).
-/

namespace ConPanqueque.T.LEq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.NEq

def fLvlEq := ofString "levelEq"
def pLa := ofString "la"
def pLb := ofString "lb"

def lvlLocals : List MlS := inst1Locals ++ [lQ]
abbrev DL : List MlS := ctxLocals ++ lvlLocals

def lvlTail : ProgHOL 64 :=
  .ite (.cmp .notEqual (vv lA2) (vv lX)) (.return (.const 0))
  (.ite (.cmp .equal (vv lX) (.const 0)) (.return (.const 1))
  (.seq (.assign .local lD1 (.load .one (vv lA3))) (.seq (.assign .local lB (.load .one (vv lY)))
  (.ite (.cmp .equal (vv lX) (.const 4))
    (.seq (.call (some (some (.local, lZ), none)) fNeq [vv lD1, vv lB]) (.return (vv lZ)))
  (.ite (.cmp .equal (vv lX) (.const 1))
    (.seq (.call (some (some (.local, lZ), none)) fLvlEq [vv lD1, vv lB]) (.return (vv lZ)))
  (.seq (.assign .local lW (.load .one (.op .add [vv lA3, .const 8])))
  (.seq (.assign .local lA1 (.load .one (.op .add [vv lY, .const 8])))
  (.seq (.call (some (some (.local, lZ), none)) fLvlEq [vv lD1, vv lB])
  (.ite (.cmp .equal (vv lZ) (.const 0)) (.return (.const 0))
    (.seq (.call (some (some (.local, lZ), none)) fLvlEq [vv lW, vv lA1]) (.return (vv lZ))))))))))))

def lvlEqCore : ProgHOL 64 :=
  .seq (.assign .local lQ (vv pLa)) (lvViewP
    (.seq (.assign .local lA2 (vv lX)) (.seq (.assign .local lA3 (vv lY))
      (.seq (.assign .local lQ (vv pLb)) (lvViewP lvlTail)))))

def lvlEqBody : ProgHOL 64 := prologue lvlLocals lvlEqCore

section
variable {σ : Type}

def KidOf (u : ConLeche.Level) : ConLeche.Level → Prop
  | .succ x => u = x
  | .max x y => u = x ∨ u = y
  | .imax x y => u = x ∨ u = y
  | _ => False

/-- The twin's level equality, a recursive call to `lvlEq`, as the tail needs it. -/
def RecEq (C : Ctx) (s : AState) (la : ConLeche.Level) : Prop :=
  ∀ u wu u' wu', KidOf u la → LRep C.HB C.H s.store.ls wu u → LRep C.HB C.H s.store.ls wu' u' →
    SpecR (Pre (σ := σ) C s [(pLa, wu), (pLb, wu')]) lvlEqBody s (pure (decide (u = u'))) (PostB C)

theorem callEq_spec {β : Type} (C : Ctx)
    (hcL : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Bool → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x e1 e2 : MlS) (u u' : ConLeche.Level) (wu wu' : BitVec 64)
    (hx : x ∈ D) (h1 : Γ.get e1 = some wu) (h2 : Γ.get e2 = some wu')
    (hspec : SpecR (Pre (σ := σ) C s [(pLa, wu), (pLb, wu')]) lvlEqBody s (pure (decide (u = u'))) (PostB C))
    (hk : SpecR (Inv C s ((x, if decide (u = u') then 1 else 0) :: Γ) [] D) rest s (k (decide (u = u'))) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fLvlEq [vv e1, vv e2]) rest) s
      (pure (decide (u = u')) >>= k) R := by
  refine specR_call2IM x fLvlEq pLa pLb (by decide) _ _ lvlEqBody wu wu' hx hcL (by simp [h1]) (by simp [h2])
    (fun a w s' st => s' = s ∧ a = decide (u = u') ∧ PostB C a w s' st) (fun _ _ _ _ hp => hp.2.2.2)
    (fun u0 hu _ hl1 hl2 => by
      have H0 : SpecR (· = u0) lvlEqBody s (pure (decide (u = u')) : AM Bool) (PostB C) :=
        fun w hw => by subst hw; exact hspec _ (pre2 hu _ _ _ _ hl1 hl2)
      refine specR_mono (specR_run H0) (fun _ h => h) (fun a w s' st hp => ?_)
      obtain ⟨hrun, hp⟩ := hp
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨hrun.2.symm, hrun.1.symm, hp⟩)
    (fun a w s' st ⟨hs, ha, hw, _⟩ => by subst hs ha hw; exact hk)

end

section
variable {σ : Type}

theorem callNeq_spec {β : Type} (C : Ctx)
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Bool → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x e1 e2 : MlS) (na nb : NIdx) (xa xb : ConLeche.Name)
    (fa fb : Nat) (hda : denoteNAux s.store.ns fa na = some xa) (hdb : denoteNAux s.store.ns fb nb = some xb)
    (hx : x ∈ D) (h1 : Γ.get e1 = some (Enc.idxW na)) (h2 : Γ.get e2 = some (Enc.idxW nb))
    (hk : SpecR (Inv C s ((x, if decide (xa = xb) then 1 else 0) :: Γ) [] D) rest s (k (decide (xa = xb))) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fNeq [vv e1, vv e2]) rest) s
      (pure (decide (xa = xb)) >>= k) R := by
  refine specR_call2IM x fNeq pNa pNb (by decide) _ _ neqBody (Enc.idxW na) (Enc.idxW nb) hx hcN (by simp [h1])
    (by simp [h2]) (fun a w s' st => s' = s ∧ a = decide (xa = xb) ∧ PostB C a w s' st) (fun _ _ _ _ hp => hp.2.2.2)
    (fun u0 hu _ hl1 hl2 => by
      have H0 : SpecR (· = u0) neqBody s (pure (decide (xa = xb)) : AM Bool) (PostB C) :=
        fun w hw => by subst hw; exact neq_spec C hcN xa na nb xb fa fb s hda hdb _ (pre2 hu _ _ _ _ hl1 hl2)
      refine specR_mono (specR_run H0) (fun _ h => h) (fun a w s' st hp => ?_)
      obtain ⟨hrun, hp⟩ := hp
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨hrun.2.symm, hrun.1.symm, hp⟩)
    (fun a w s' st ⟨hs, ha, hw, _⟩ => by subst hs ha hw; exact hk)

theorem ofNat_tag_ne (a b : Nat) (ha : a < 8) (hb : b < 8) (h : a ≠ b) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b :=
  fun e => h ((word_eq_iff a b (by omega) (by omega)).mp e)

theorem ltag_lt (l : ConLeche.Level) : ltag l < 5 := by cases l <;> simp [ltag]

theorem lvlTail_diff (C : Ctx) {s : AState} {Γ : Env} {M : Mem} (la lb : ConLeche.Level) (ht : ltag la ≠ ltag lb)
    (ha2 : Γ.get lA2 = some (BitVec.ofNat 64 (ltag la))) (hx : Γ.get lX = some (BitVec.ofNat 64 (ltag lb))) :
    SpecR (Inv (σ := σ) C s Γ M DL) lvlTail s (pure (decide (la = lb))) (PostB C) := by
  unfold lvlTail
  have hne := ofNat_tag_ne _ _ (by have := ltag_lt la; omega) (by have := ltag_lt lb; omega) ht
  refine specR_ifI _ 1 (by simp +decide [sev, ha2, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
    (fun _ => ?_) (fun hw => absurd hw (by decide))
  refine specR_congr (m' := pure false) (by have : la ≠ lb := fun e => ht (by rw [e]); simp [this]) ?_
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem lvlTail_zero (C : Ctx) {s : AState} {Γ : Env} {M : Mem}
    (ha2 : Γ.get lA2 = some (BitVec.ofNat 64 0)) (hx : Γ.get lX = some (BitVec.ofNat 64 0)) :
    SpecR (Inv (σ := σ) C s Γ M DL) lvlTail s (pure (decide (ConLeche.Level.zero = .zero))) (PostB C) := by
  unfold lvlTail
  refine specR_ifI _ 0 (by simp +decide [sev, ha2, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 1 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
  exact specR_returnI (.const 1) 1 rfl (fun t ht => ⟨by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem lvlTail_param (C : Ctx) (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    {s : AState} {Γ : Env} {M : Mem} (xa xb : ConLeche.Name) (na nb : NIdx) (fa fb : Nat) (Pa Pb : BitVec 64)
    (ha2 : Γ.get lA2 = some (BitVec.ofNat 64 4)) (ha3 : Γ.get lA3 = some Pa)
    (hx : Γ.get lX = some (BitVec.ofNat 64 4)) (hy : Γ.get lY = some Pb)
    (hm1 : (Pa + BitVec.ofNat 64 (8 * 0), Enc.idxW na) ∈ M) (hm3 : (Pb + BitVec.ofNat 64 (8 * 0), Enc.idxW nb) ∈ M)
    (hda : denoteNAux s.store.ns fa na = some xa) (hdb : denoteNAux s.store.ns fb nb = some xb) :
    SpecR (Inv (σ := σ) C s Γ M DL) lvlTail s (pure (decide (ConLeche.Level.param xa = .param xb))) (PostB C) := by
  unfold lvlTail
  refine specR_ifI _ 0 (by simp +decide [sev, ha2, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_loadI' lD1 (vv lA3) Pa (Pa + BitVec.ofNat 64 (8 * 0)) _ (by decide) (by simp +decide [ha3]) (by simp)
    hm1 ?_
  refine specR_loadI' lB (vv lY) Pb (Pb + BitVec.ofNat 64 (8 * 0)) _ (by decide) (by simp +decide [hy]) (by simp)
    hm3 ?_
  refine specR_ifI _ 1 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
  refine specR_congr (m' := pure (decide (xa = xb)) >>= fun b => pure b) (by simp) ?_
  refine callNeq_spec C hcN lZ lD1 lB na nb xa xb fa fb hda hdb (by decide) (by simp +decide) (by simp +decide) ?_
  exact specR_returnI (vv lZ) _ (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem lvlTail_succ (C : Ctx) (hcL : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    {s : AState} {Γ : Env} {M : Mem} (u u' : ConLeche.Level) (wu wu' Pa Pb : BitVec 64)
    (ha2 : Γ.get lA2 = some (BitVec.ofNat 64 1)) (ha3 : Γ.get lA3 = some Pa)
    (hx : Γ.get lX = some (BitVec.ofNat 64 1)) (hy : Γ.get lY = some Pb)
    (hm1 : (Pa + BitVec.ofNat 64 (8 * 0), wu) ∈ M) (hm3 : (Pb + BitVec.ofNat 64 (8 * 0), wu') ∈ M)
    (hu : LRep C.HB C.H s.store.ls wu u) (hu' : LRep C.HB C.H s.store.ls wu' u')
    (hrec : RecEq (σ := σ) C s (.succ u)) :
    SpecR (Inv (σ := σ) C s Γ M DL) lvlTail s (pure (decide (ConLeche.Level.succ u = .succ u'))) (PostB C) := by
  unfold lvlTail
  refine specR_ifI _ 0 (by simp +decide [sev, ha2, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_loadI' lD1 (vv lA3) Pa (Pa + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [ha3]) (by simp)
    hm1 ?_
  refine specR_loadI' lB (vv lY) Pb (Pb + BitVec.ofNat 64 (8 * 0)) wu' (by decide) (by simp +decide [hy]) (by simp)
    hm3 ?_
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 1 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
  refine specR_congr (m' := pure (decide (u = u')) >>= fun b => pure b) (by simp) ?_
  refine callEq_spec C hcL lZ lD1 lB u u' wu wu' (by decide) (by simp +decide) (by simp +decide)
    (hrec u wu u' wu' rfl hu hu') ?_
  exact specR_returnI (vv lZ) _ (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem lvlTail_max (C : Ctx) (hcL : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    {s : AState} {Γ : Env} {M : Mem} (u v u' v' : ConLeche.Level) (wu wv wu' wv' Pa Pb : BitVec 64)
    (ha2 : Γ.get lA2 = some (BitVec.ofNat 64 2)) (ha3 : Γ.get lA3 = some Pa)
    (hx : Γ.get lX = some (BitVec.ofNat 64 2)) (hy : Γ.get lY = some Pb)
    (hm1 : (Pa + BitVec.ofNat 64 (8 * 0), wu) ∈ M) (hm2 : (Pa + BitVec.ofNat 64 (8 * 1), wv) ∈ M)
    (hm3 : (Pb + BitVec.ofNat 64 (8 * 0), wu') ∈ M) (hm4 : (Pb + BitVec.ofNat 64 (8 * 1), wv') ∈ M)
    (hu : LRep C.HB C.H s.store.ls wu u) (hv : LRep C.HB C.H s.store.ls wv v)
    (hu' : LRep C.HB C.H s.store.ls wu' u') (hv' : LRep C.HB C.H s.store.ls wv' v')
    (hrec : RecEq (σ := σ) C s (.max u v)) :
    SpecR (Inv (σ := σ) C s Γ M DL) lvlTail s (pure (decide (ConLeche.Level.max u v = .max u' v'))) (PostB C) := by
  unfold lvlTail
  refine specR_ifI _ 0 (by simp +decide [sev, ha2, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_loadI' lD1 (vv lA3) Pa (Pa + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [ha3]) (by simp)
    hm1 ?_
  refine specR_loadI' lB (vv lY) Pb (Pb + BitVec.ofNat 64 (8 * 0)) wu' (by decide) (by simp +decide [hy]) (by simp)
    hm3 ?_
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_loadI' lW _ (Pa + 8) (Pa + BitVec.ofNat 64 (8 * 1)) wv (by decide) (by simp +decide [sev, ha3])
    (by simp) hm2 ?_
  refine specR_loadI' lA1 _ (Pb + 8) (Pb + BitVec.ofNat 64 (8 * 1)) wv' (by decide) (by simp +decide [sev, hy])
    (by simp) hm4 ?_
  refine specR_congr (m' := pure (decide (u = u')) >>= fun b =>
    if b = true then (pure (decide (v = v')) >>= fun c => pure c) else pure false) (by by_cases e : u = u' <;> simp [e]) ?_
  refine callEq_spec C hcL lZ lD1 lB u u' wu wu' (by decide) (by simp +decide) (by simp +decide)
    (hrec u wu u' wu' (Or.inl rfl) hu hu') ?_
  by_cases e : u = u'
  · refine specR_ifI _ 0 (by simp +decide [sev, e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_congr (m' := pure (decide (v = v')) >>= fun c => pure c) (by simp [e]) ?_
    refine callEq_spec C hcL lZ lW lA1 v v' wv wv' (by decide) (by simp +decide) (by simp +decide)
      (hrec v wv v' wv' (Or.inr rfl) hv hv') ?_
    exact specR_returnI (vv lZ) _ (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp +decide [sev, e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure false) (by simp [e]) ?_
    exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem lvlTail_imax (C : Ctx) (hcL : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    {s : AState} {Γ : Env} {M : Mem} (u v u' v' : ConLeche.Level) (wu wv wu' wv' Pa Pb : BitVec 64)
    (ha2 : Γ.get lA2 = some (BitVec.ofNat 64 3)) (ha3 : Γ.get lA3 = some Pa)
    (hx : Γ.get lX = some (BitVec.ofNat 64 3)) (hy : Γ.get lY = some Pb)
    (hm1 : (Pa + BitVec.ofNat 64 (8 * 0), wu) ∈ M) (hm2 : (Pa + BitVec.ofNat 64 (8 * 1), wv) ∈ M)
    (hm3 : (Pb + BitVec.ofNat 64 (8 * 0), wu') ∈ M) (hm4 : (Pb + BitVec.ofNat 64 (8 * 1), wv') ∈ M)
    (hu : LRep C.HB C.H s.store.ls wu u) (hv : LRep C.HB C.H s.store.ls wv v)
    (hu' : LRep C.HB C.H s.store.ls wu' u') (hv' : LRep C.HB C.H s.store.ls wv' v')
    (hrec : RecEq (σ := σ) C s (.imax u v)) :
    SpecR (Inv (σ := σ) C s Γ M DL) lvlTail s (pure (decide (ConLeche.Level.imax u v = .imax u' v'))) (PostB C) := by
  unfold lvlTail
  refine specR_ifI _ 0 (by simp +decide [sev, ha2, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_loadI' lD1 (vv lA3) Pa (Pa + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [ha3]) (by simp)
    hm1 ?_
  refine specR_loadI' lB (vv lY) Pb (Pb + BitVec.ofNat 64 (8 * 0)) wu' (by decide) (by simp +decide [hy]) (by simp)
    hm3 ?_
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_loadI' lW _ (Pa + 8) (Pa + BitVec.ofNat 64 (8 * 1)) wv (by decide) (by simp +decide [sev, ha3])
    (by simp) hm2 ?_
  refine specR_loadI' lA1 _ (Pb + 8) (Pb + BitVec.ofNat 64 (8 * 1)) wv' (by decide) (by simp +decide [sev, hy])
    (by simp) hm4 ?_
  refine specR_congr (m' := pure (decide (u = u')) >>= fun b =>
    if b = true then (pure (decide (v = v')) >>= fun c => pure c) else pure false) (by by_cases e : u = u' <;> simp [e]) ?_
  refine callEq_spec C hcL lZ lD1 lB u u' wu wu' (by decide) (by simp +decide) (by simp +decide)
    (hrec u wu u' wu' (Or.inl rfl) hu hu') ?_
  by_cases e : u = u'
  · refine specR_ifI _ 0 (by simp +decide [sev, e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_congr (m' := pure (decide (v = v')) >>= fun c => pure c) (by simp [e]) ?_
    refine callEq_spec C hcL lZ lW lA1 v v' wv wv' (by decide) (by simp +decide) (by simp +decide)
      (hrec v wv v' wv' (Or.inr rfl) hv hv') ?_
    exact specR_returnI (vv lZ) _ (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp +decide [sev, e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure false) (by simp [e]) ?_
    exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem params_noneLE (va vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ lvlLocals → (ctxEnv C ++ [(pLa, va), (pLb, vb)]).get x = none := by
  intro x hx
  simp only [lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem lvScratch_DL : ∀ z, z ∈ lvScratch → z ∈ DL := by
  intro z hz
  simp only [lvScratch, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem lvlEq_views (C : Ctx) (hok : CtxOK C) (la lb : ConLeche.Level) (a b : BitVec 64) (s : AState)
    (ha : LRep C.HB C.H s.store.ls a la) (hb : LRep C.HB C.H s.store.ls b lb)
    (hk : ∀ (Γ : Env) (M : Mem) (Pa Pb : BitVec 64), Γ.get lA2 = some (BitVec.ofNat 64 (ltag la)) →
      Γ.get lA3 = some Pa → Γ.get lX = some (BitVec.ofNat 64 (ltag lb)) → Γ.get lY = some Pb →
      LKids C.HB C.H s.store.ls Pa M la → LKids C.HB C.H s.store.ls Pb M lb →
      SpecR (Inv (σ := σ) C s Γ M DL) lvlTail s (pure (decide (la = lb))) (PostB C)) :
    SpecR (Pre (σ := σ) C s [(pLa, a), (pLb, b)]) lvlEqBody s (pure (decide (la = lb))) (PostB C) := by
  refine specR_prologue (postB_locals C) (params_noneLE _ _ C) ?_
  unfold lvlEqCore
  refine specR_assignI lQ (vv pLa) a (by decide) (by simp +decide [ctxEnv]) ?_
  refine specR_lvViewI hok a la (by simp) ha (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) lvScratch_DL
    (fun Γ1 M1 Pa hp1 hx1 hy1 _ hk1 => ?_)
  refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 (ltag la)) (by decide) (by simp [hx1]) ?_
  refine specR_assignI lA3 (vv lY) Pa (by decide) (by simp +decide [hy1]) ?_
  refine specR_assignI lQ (vv pLb) b (by decide)
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv]) ?_
  refine specR_lvViewI hok b lb (by simp) hb (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv])
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv]) lvScratch_DL
    (fun Γ2 M2 Pb hp2 hx2 hy2 hmm2 hk2 => ?_)
  refine hk Γ2 M2 Pa Pb (by rw [hp2 _ (by decide)]; simp +decide) (by rw [hp2 _ (by decide)]; simp +decide)
    hx2 hy2 ?_ hk2
  cases la with
  | zero => trivial
  | succ u => obtain ⟨wu, h1, h2⟩ := hk1; exact ⟨wu, hmm2 _ h1, h2⟩
  | max u v => obtain ⟨wu, wv, h1, h2, h3, h4⟩ := hk1; exact ⟨wu, wv, hmm2 _ h1, hmm2 _ h2, h3, h4⟩
  | imax u v => obtain ⟨wu, wv, h1, h2, h3, h4⟩ := hk1; exact ⟨wu, wv, hmm2 _ h1, hmm2 _ h2, h3, h4⟩
  | param n => obtain ⟨nh, f, h1, h2⟩ := hk1; exact ⟨nh, f, hmm2 _ h1, h2⟩

end

section
variable {σ : Type}

/-- `levelEq` decides the equality of the represented trees. -/
theorem lvlEq_spec (C : Ctx) (hok : CtxOK C)
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcL : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one)) :
    ∀ (la : ConLeche.Level) (a b : BitVec 64) (lb : ConLeche.Level) (s : AState),
      LRep C.HB C.H s.store.ls a la → LRep C.HB C.H s.store.ls b lb →
      SpecR (Pre (σ := σ) C s [(pLa, a), (pLb, b)]) lvlEqBody s (pure (decide (la = lb))) (PostB C) := by
  intro la
  induction la with
  | zero =>
    intro a b lb s ha hb
    refine lvlEq_views C hok _ lb a b s ha hb (fun Γ M Pa Pb h1 h2 h3 h4 hka hkb => ?_)
    by_cases ht : ltag .zero = ltag lb
    · cases lb <;> simp [ltag] at ht
      exact lvlTail_zero C h1 h3
    · exact lvlTail_diff C _ lb ht h1 h3
  | succ u ih =>
    intro a b lb s ha hb
    refine lvlEq_views C hok _ lb a b s ha hb (fun Γ M Pa Pb h1 h2 h3 h4 hka hkb => ?_)
    by_cases ht : ltag (.succ u) = ltag lb
    · cases lb <;> simp [ltag] at ht
      rename_i u'
      obtain ⟨wu, m1, r1⟩ := hka
      obtain ⟨wu', m3, r3⟩ := hkb
      exact lvlTail_succ C hcL u u' wu wu' Pa Pb h1 h2 h3 h4 m1 m3 r1 r3
        (fun u0 w0 u1 w1 hk r r' => by cases hk; exact ih w0 w1 u1 s r r')
    · exact lvlTail_diff C _ lb ht h1 h3
  | max u v ihu ihv =>
    intro a b lb s ha hb
    refine lvlEq_views C hok _ lb a b s ha hb (fun Γ M Pa Pb h1 h2 h3 h4 hka hkb => ?_)
    by_cases ht : ltag (.max u v) = ltag lb
    · cases lb <;> simp [ltag] at ht
      rename_i u' v'
      obtain ⟨wu, wv, m1, m2, r1, r2⟩ := hka
      obtain ⟨wu', wv', m3, m4, r3, r4⟩ := hkb
      exact lvlTail_max C hcL u v u' v' wu wv wu' wv' Pa Pb h1 h2 h3 h4 m1 m2 m3 m4 r1 r2 r3 r4
        (fun u0 w0 u1 w1 hk r r' => by
          rcases hk with rfl | rfl
          · exact ihu w0 w1 u1 s r r'
          · exact ihv w0 w1 u1 s r r')
    · exact lvlTail_diff C _ lb ht h1 h3
  | imax u v ihu ihv =>
    intro a b lb s ha hb
    refine lvlEq_views C hok _ lb a b s ha hb (fun Γ M Pa Pb h1 h2 h3 h4 hka hkb => ?_)
    by_cases ht : ltag (.imax u v) = ltag lb
    · cases lb <;> simp [ltag] at ht
      rename_i u' v'
      obtain ⟨wu, wv, m1, m2, r1, r2⟩ := hka
      obtain ⟨wu', wv', m3, m4, r3, r4⟩ := hkb
      exact lvlTail_imax C hcL u v u' v' wu wv wu' wv' Pa Pb h1 h2 h3 h4 m1 m2 m3 m4 r1 r2 r3 r4
        (fun u0 w0 u1 w1 hk r r' => by
          rcases hk with rfl | rfl
          · exact ihu w0 w1 u1 s r r'
          · exact ihv w0 w1 u1 s r r')
    · exact lvlTail_diff C _ lb ht h1 h3
  | param n =>
    intro a b lb s ha hb
    refine lvlEq_views C hok _ lb a b s ha hb (fun Γ M Pa Pb h1 h2 h3 h4 hka hkb => ?_)
    by_cases ht : ltag (.param n) = ltag lb
    · cases lb <;> simp [ltag] at ht
      rename_i n'
      obtain ⟨nha, fa, m1, d1⟩ := hka
      obtain ⟨nhb, fb, m3, d3⟩ := hkb
      exact lvlTail_param C hcN n n' nha nhb fa fb Pa Pb h1 h2 h3 h4 m1 m3 d1 d3
    · exact lvlTail_diff C _ lb ht h1 h3

end

end ConPanqueque.T.LEq
