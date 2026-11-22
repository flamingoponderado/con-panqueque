import ConPanqueque.T.LvlLeqBase
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `leqCore` and its mutual block

Four Pancake functions mirror con-leche's `leqCore`, `rest`, `imaxRules`, `byCases`; only `leqCore`
consumes fuel. This file: `byCases`.
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub

def fLeq := ofString "leqCore"
def fRest := ofString "leqRest"
def fImax := ofString "imaxRules"
def fByC := ofString "byCases"

def lV := ofString "lv"
def lE0 := ofString "e0"

def leqParams : List MlS := [pFu, pLa, pLb, pD]
def bcParams : List MlS := [pFu, pSp, pLa, pLb, pD]
def leqLocals : List MlS := lvlLocals ++ [lV, lE0]
abbrev DQ : List MlS := ctxLocals ++ leqLocals

def callLeqP (x a b : MlS) (dE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fLeq [vv pFu, vv a, vv b, dE]

/-- `l` and `r` with `p := v` (the value in `v`), simplified, into `a1` and `z`. -/
def substBoth (v : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, lA1), none)) fSubst [vv pLa, vv pSp, vv v])
  (.seq (.call (some (some (.local, lA1), none)) fSimp [vv lA1])
  (.seq (.call (some (some (.local, lZ), none)) fSubst [vv pLb, vv pSp, vv v])
  (.seq (.call (some (some (.local, lZ), none)) fSimp [vv lZ]) rest)))

def bcBody (C : Ctx) : ProgHOL 64 :=
  prologue leqLocals
   (alloc1 C lW (.const 0)
   (substBoth lW
   (.seq (callLeqP lV lA1 lZ (vv pD))
   (.ite (.cmp .equal (vv lV) (.const 0)) (.return (.const 0))
   (.ite (.cmp .equal (vv lV) (.const 1)) (.return (.const 1))
   (alloc2 C lW (.const 4) (vv pSp)
   (alloc2 C lE0 (.const 1) (vv lW)
   (substBoth lE0
   (.seq (callLeqP lV lA1 lZ (vv pD)) (.return (vv lV)))))))))))

section
variable {σ : Type}

/-- `substBoth v`: the two simplified substitutions land in `a1` and `z` at a bigger image. -/
theorem substBoth_spec {α : Type} (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (v : MlS) (hv : v ≠ lA1 ∧ v ≠ lZ)
    (l r vl : ConLeche.Level) (wl wr wv : BitVec 64) (nh : NIdx) (f : Nat) (pn : ConLeche.Name)
    (hl : LRep C.HB H s.store.ls wl l) (hr : LRep C.HB H s.store.ls wr r) (hvl : LRep C.HB H s.store.ls wv vl)
    (hn : denoteNAux s.store.ns f nh = some pn)
    (ha : Γ.get pLa = some wl) (hb : Γ.get pLb = some wr) (hs : Γ.get pSp = some (Enc.idxW nh))
    (hw : Γ.get v = some wv)
    (hk : ∀ (H2 : List (BitVec 64)) (c1 c2 : BitVec 64) (Γ' : Env), H <+: H2 →
      LRep C.HB H2 s.store.ls c1 (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [vl] l)) →
      LRep C.HB H2 s.store.ls c2 (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [vl] r)) →
      Γ'.get lA1 = some c1 → Γ'.get lZ = some c2 → (∀ y, y ≠ lA1 → y ≠ lZ → Γ'.get y = Γ.get y) →
      SpecR (Inv (σ := σ) (ctxH C H2) s Γ' [] DQ) rest s m R) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DQ) (substBoth v rest) s m R := by
  unfold substBoth
  refine specR_congr (m' := pure (ConLeche.Level.subst [pn] [vl] l) >>= fun _ => m) (by simp) ?_
  refine callLv_spec (C := ctxH C H) lA1 fSubst substParams [vv pLa, vv pSp, vv v] (substBody C) [wl, Enc.idxW nh, wv]
    (by decide) rfl (by decide) hcS ⟨by simp [ha], by simp [hs], by simp [hw], trivial⟩ _
    (subst_spec C hok hcS hcN l H wl nh f pn vl wv s hl hn hvl) (fun H1 c0 hp1 hc0 => ?_)
  refine specR_congr (m' := pure (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [vl] l)) >>= fun _ => m)
    (by simp) ?_
  refine callLv_spec (C := ctxH C H1) lA1 fSimp [pLa] [vv lA1] (simpBody C) [c0] (by decide) rfl (by decide) hcM
    ⟨by simp, trivial⟩ _ (simp_spec C hok hcM hcC _ H1 c0 s hc0) (fun H2 c1 hp2 hc1 => ?_)
  refine specR_congr (m' := pure (ConLeche.Level.subst [pn] [vl] r) >>= fun _ => m) (by simp) ?_
  refine callLv_spec (C := ctxH C H2) lZ fSubst substParams [vv pLb, vv pSp, vv v] (substBody C) [wr, Enc.idxW nh, wv]
    (by decide) rfl (by decide) hcS
    ⟨by simp +decide [hb], by simp +decide [hs], by simp [Env.get, hv.1, hv.2, hw], trivial⟩ _
    (subst_spec C hok hcS hcN r H2 wr nh f pn vl wv s (lrep_mono (hp1.trans hp2) r wr hr) hn
      (lrep_mono (hp1.trans hp2) vl wv hvl)) (fun H3 c2' hp3 hc2' => ?_)
  refine specR_congr (m' := pure (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [vl] r)) >>= fun _ => m)
    (by simp) ?_
  refine callLv_spec (C := ctxH C H3) lZ fSimp [pLa] [vv lZ] (simpBody C) [c2'] (by decide) rfl (by decide) hcM
    ⟨by simp, trivial⟩ _ (simp_spec C hok hcM hcC _ H3 c2' s hc2') (fun H4 c2 hp4 hc2 => ?_)
  refine hk H4 c1 c2 _ (hp1.trans (hp2.trans (hp3.trans hp4))) (lrep_mono (hp3.trans hp4) _ c1 hc1) hc2
    (by simp +decide) (by simp) (fun y h1 h2 => ?_)
  simp [Env.get, h1, h2]

end

theorem bc_eq (n : Nat) (pn : ConLeche.Name) (l r : ConLeche.Level) (d : Int) :
    ConLeche.Level.byCases n pn l r d =
      match ConLeche.Level.leqCore n (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.zero] l))
          (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.zero] r)) d with
      | none => none
      | some false => some false
      | some true => ConLeche.Level.leqCore n
          (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.succ (.param pn)] l))
          (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.succ (.param pn)] r)) d := by
  rw [ConLeche.Level.byCases]
  cases ConLeche.Level.leqCore n _ _ d with
  | none => rfl
  | some b => cases b <;> rfl

section
variable {σ : Type}

/-- The `leqCore` spec at fuel `n`, for a given body. -/
def RecLeq (C : Ctx) (B : ProgHOL 64) (n : Nat) : Prop :=
  ∀ (H : List (BitVec 64)) (l r : ConLeche.Level) (wl wr : BitVec 64) (d : Int) (s : AState),
    LRep C.HB H s.store.ls wl l → LRep C.HB H s.store.ls wr r → d.natAbs + n < 2 ^ 62 →
    SpecR (Pre (σ := σ) (ctxH C H) s (leqParams.zip [BitVec.ofNat 64 n, wl, wr, iW d])) B s
      (pure (ConLeche.Level.leqCore n l r d)) (PostOB (ctxH C H))

theorem params_noneBC (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ leqLocals → (ctxEnv C ++ bcParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ bcParams := by
    simp only [leqLocals, lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [leqLocals, lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
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

theorem bc_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (B : ProgHOL 64) (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), B, .one))
    (n : Nat) (hn : n < 2 ^ 64) (ih : RecLeq (σ := σ) C B n) :
    ∀ (H : List (BitVec 64)) (nh : NIdx) (f : Nat) (pn : ConLeche.Name) (l r : ConLeche.Level)
      (wl wr : BitVec 64) (d : Int) (s : AState),
      denoteNAux s.store.ns f nh = some pn → LRep C.HB H s.store.ls wl l → LRep C.HB H s.store.ls wr r →
      d.natAbs + n < 2 ^ 62 →
      SpecR (Pre (σ := σ) (ctxH C H) s (bcParams.zip [BitVec.ofNat 64 n, Enc.idxW nh, wl, wr, iW d])) (bcBody C) s
        (pure (ConLeche.Level.byCases n pn l r d)) (PostOB (ctxH C H)) := by
  intro H nh f pn l r wl wr d s hnd hl hr hd
  refine specR_prologue (postOB_locals _) (params_noneBC _ _) ?_
  refine specR_alloc1I (C := ctxH C H) (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl)
    (fun I1 ws hp1 hws => ?_)
  have hz := lrep_mkZero (ctxH C H) s.store.ls I1 ws hws
  refine substBoth_spec C hok hcS hcN hcM hcC (H := (I1 ++ ws).set I1.length (BitVec.ofNat 64 0)) lW (by decide)
    l r .zero wl wr (cellA C I1.length) nh f pn
    (lrep_mono (hp1.trans (img1_prefix I1 ws _ hws)) l wl hl) (lrep_mono (hp1.trans (img1_prefix I1 ws _ hws)) r wr hr)
    hz hnd (by simp +decide [ctxEnv, bcParams]) (by simp +decide [ctxEnv, bcParams])
    (by simp +decide [ctxEnv, bcParams]) (by simp +decide <;> rfl) (fun H2 c1 c2 Γ' hp2 hc1 hc2 g1 g2 gfr => ?_)
  have gFu : Γ'.get pFu = some (BitVec.ofNat 64 n) := by rw [gfr _ (by decide) (by decide)]; simp +decide [ctxEnv, bcParams]
  have gD : Γ'.get pD = some (iW d) := by rw [gfr _ (by decide) (by decide)]; simp +decide [ctxEnv, bcParams]
  have gLa : Γ'.get pLa = some wl := by rw [gfr _ (by decide) (by decide)]; simp +decide [ctxEnv, bcParams]
  have gLb : Γ'.get pLb = some wr := by rw [gfr _ (by decide) (by decide)]; simp +decide [ctxEnv, bcParams]
  have gSp : Γ'.get pSp = some (Enc.idxW nh) := by
    rw [gfr _ (by decide) (by decide)]; simp +decide [ctxEnv, bcParams]
  rw [bc_eq]
  generalize hl0 : ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.zero] l) = l0 at hc1
  generalize hr0 : ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.zero] r) = r0 at hc2
  refine specR_congr (m' := pure (ConLeche.Level.leqCore n l0 r0 d) >>= fun o => pure (match o with
      | none => none
      | some false => some false
      | some true => ConLeche.Level.leqCore n
          (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.succ (.param pn)] l))
          (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.succ (.param pn)] r)) d)) (by simp) ?_
  refine callOB_spec (C := ctxH C H2) lV fLeq leqParams [vv pFu, vv lA1, vv lZ, vv pD] B [BitVec.ofNat 64 n, c1, c2, iW d]
    (by decide) rfl (by decide) hcL ⟨by simp [gFu], by simp [g1], by simp [g2], by simp [gD], trivial⟩ _
    (ih H2 l0 r0 c1 c2 d s hc1 hc2 hd) ?_
  rcases ho : ConLeche.Level.leqCore n l0 r0 d with _ | b
  · refine specR_ifI _ 1 (by simp +decide [sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H2) (sr_of_eq ht.sr rfl rfl rfl rfl)
      (hp1.trans ((img1_prefix I1 ws _ hws).trans hp2))⟩)
  cases b
  · refine specR_ifI _ 0 (by simp +decide [sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    exact specR_returnI (.const 1) 1 rfl (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H2) (sr_of_eq ht.sr rfl rfl rfl rfl)
      (hp1.trans ((img1_prefix I1 ws _ hws).trans hp2))⟩)
  refine specR_ifI _ 0 (by simp +decide [sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_alloc2I (C := ctxH C H2) (ctxOK_H hok H2) lW (.const 4) (vv pSp) 4 (Enc.idxW nh) (by decide)
    (fun _ => rfl) (fun _ => by simp +decide [gSp]) (fun I3 ws3 hp3 hws3 => ?_)
  have hpar := lrep_mkParam (ctxH C H2) s.store.ls I3 ws3 nh f pn hws3 hnd
  refine specR_alloc2I (C := ctxH C (((I3 ++ ws3).set I3.length (BitVec.ofNat 64 4)).set (I3.length + 1) (Enc.idxW nh)))
    (ctxOK_H hok _) lE0 (.const 1) (vv lW) 1 (cellA C I3.length) (by decide) (fun _ => rfl)
    (fun _ => by simp +decide <;> rfl) (fun I4 ws4 hp4 hws4 => ?_)
  have hsuc := lrep_mkSucc (ctxH C (((I3 ++ ws3).set I3.length (BitVec.ofNat 64 4)).set (I3.length + 1) (Enc.idxW nh)))
    s.store.ls I4 ws4 (cellA C I3.length) (.param pn) hws4 hp4 hpar
  have hpre : H2 <+: ((I4 ++ ws4).set I4.length (BitVec.ofNat 64 1)).set (I4.length + 1) (cellA C I3.length) :=
    hp3.trans ((img2_prefix I3 ws3 _ _ hws3).trans (hp4.trans (img2_prefix I4 ws4 _ _ hws4)))
  have hpre0 : H <+: H2 := hp1.trans ((img1_prefix I1 ws _ hws).trans hp2)
  refine substBoth_spec C hok hcS hcN hcM hcC lE0 (by decide) l r (.succ (.param pn)) wl wr (cellA C I4.length) nh f pn
    (lrep_mono (hpre0.trans hpre) l wl hl) (lrep_mono (hpre0.trans hpre) r wr hr) hsuc hnd
    (by simp +decide [gLa]) (by simp +decide [gLb]) (by simp +decide [gSp]) (by simp +decide <;> rfl)
    (fun H5 c3 c4 Γ5 hp5 hc3 hc4 g3 g4 gfr5 => ?_)
  refine specR_congr (m' := pure (ConLeche.Level.leqCore n
      (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.succ (.param pn)] l))
      (ConLeche.Level.simplify (ConLeche.Level.subst [pn] [.succ (.param pn)] r)) d) >>= fun o => pure o) (by simp) ?_
  refine callOB_spec (C := ctxH C H5) lV fLeq leqParams [vv pFu, vv lA1, vv lZ, vv pD] B
    [BitVec.ofNat 64 n, c3, c4, iW d] (by decide) rfl (by decide) hcL
    ⟨by rw [show (vv pFu : ExpHOL 64) = vv pFu from rfl]; simp only [sev_vv]; rw [gfr5 _ (by decide) (by decide)]; simp +decide [gFu],
      by simp [g3], by simp [g4],
      by simp only [sev_vv]; rw [gfr5 _ (by decide) (by decide)]; simp +decide [gD], trivial⟩ _
    (ih H5 _ _ c3 c4 d s hc3 hc4 hd) ?_
  exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H5) (sr_of_eq ht.sr rfl rfl rfl rfl)
    (hpre0.trans (hpre.trans hp5))⟩)

end

/-! ## `imaxRules` -/

def lPb := ofString "kpb"
def lA0 := ofString "ka"
def lBx := ofString "kbx"
def lBy := ofString "kby"
def lRx := ofString "krx"
def lPy := ofString "kpy"
def lTb := ofString "ktb"
def lW1 := ofString "kw1"
def lW2 := ofString "kw2"

def imLocals : List MlS := leqLocals ++ [lPb, lA0, lBx, lBy, lRx, lPy, lTb, lW1, lW2]
abbrev DM : List MlS := ctxLocals ++ imLocals

/-- `w := max (imax u₁ v₁) (imax u₂ v₂)`. -/
def mkMI (C : Ctx) (u1 v1 u2 v2 : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  alloc3 C lW1 (.const 3) (vv u1) (vv v1) (alloc3 C lW2 (.const 3) (vv u2) (vv v2)
    (alloc3 C lW (.const 2) (vv lW1) (vv lW2) rest))

section
variable {σ : Type}

theorem mkMI_spec {α : Type} (C : Ctx) (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (u1 v1 u2 v2 : MlS) (hn : u1 ≠ lW1 ∧ v1 ≠ lW1 ∧ u2 ≠ lW1 ∧ v2 ≠ lW1 ∧ u2 ≠ lW2 ∧ v2 ≠ lW2)
    (a1 b1 a2 b2 : ConLeche.Level) (x1 y1 x2 y2 : BitVec 64)
    (h1 : Γ.get u1 = some x1) (h2 : Γ.get v1 = some y1) (h3 : Γ.get u2 = some x2) (h4 : Γ.get v2 = some y2)
    (r1 : LRep C.HB H s.store.ls x1 a1) (r2 : LRep C.HB H s.store.ls y1 b1)
    (r3 : LRep C.HB H s.store.ls x2 a2) (r4 : LRep C.HB H s.store.ls y2 b2)
    (hk : ∀ (H3 : List (BitVec 64)) (w : BitVec 64) (Γ' : Env), H <+: H3 →
      LRep C.HB H3 s.store.ls w (.max (.imax a1 b1) (.imax a2 b2)) → Γ'.get lW = some w →
      (∀ y, y ≠ lW → y ≠ lW1 → y ≠ lW2 → Γ'.get y = Γ.get y) →
      SpecR (Inv (σ := σ) (ctxH C H3) s Γ' [] DM) rest s m R) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DM) (mkMI C u1 v1 u2 v2 rest) s m R := by
  unfold mkMI
  refine specR_alloc3I (C := ctxH C H) (ctxOK_H hok H) lW1 (.const 3) (vv u1) (vv v1) 3 x1 y1 (by decide)
    (fun _ => rfl) (fun _ => by simp [Env.get, hn.1, h1]) (fun _ => by simp [Env.get, hn.2.1, h2])
    (fun I1 ws1 hp1 hws1 => ?_)
  have hm1 := lrep_mkImax (ctxH C H) s.store.ls I1 ws1 x1 y1 a1 b1 hws1 hp1 r1 r2
  have q1 : H <+: (((I1 ++ ws1).set I1.length (BitVec.ofNat 64 3)).set (I1.length + 1) x1).set (I1.length + 2) y1 :=
    hp1.trans (img3_prefix I1 ws1 _ x1 y1 hws1)
  refine specR_alloc3I (C := ctxH C _) (ctxOK_H hok _) lW2 (.const 3) (vv u2) (vv v2) 3 x2 y2 (by decide)
    (fun _ => rfl) (fun _ => by simp [Env.get, show u2 ≠ lW2 from hn.2.2.2.2.1, show u2 ≠ lW1 from hn.2.2.1, h3])
    (fun _ => by simp [Env.get, show v2 ≠ lW2 from hn.2.2.2.2.2, show v2 ≠ lW1 from hn.2.2.2.1, h4])
    (fun I2 ws2 hp2 hws2 => ?_)
  have hm2 := lrep_mkImax (ctxH C _) s.store.ls I2 ws2 x2 y2 a2 b2 hws2 hp2
    (lrep_mono q1 a2 x2 r3) (lrep_mono q1 b2 y2 r4)
  have q2 := hp2.trans (img3_prefix I2 ws2 (BitVec.ofNat 64 3) x2 y2 hws2)
  refine specR_alloc3I (C := ctxH C _) (ctxOK_H hok _) lW (.const 2) (vv lW1) (vv lW2) 2 (cellA C I1.length)
    (cellA C I2.length) (by decide) (fun _ => rfl) (fun _ => by simp +decide <;> rfl)
    (fun _ => by simp +decide <;> rfl) (fun I3 ws3 hp3 hws3 => ?_)
  have hm3 := lrep_mkMax (ctxH C _) s.store.ls I3 ws3 (cellA C I1.length) (cellA C I2.length) _ _ hws3 hp3
    (lrep_mono q2 _ _ hm1) hm2 2 rfl
  refine hk _ (cellA C I3.length) _ (q1.trans (q2.trans (hp3.trans (img3_prefix I3 ws3 (BitVec.ofNat 64 2) _ _ hws3)))) hm3
    (by simp +decide <;> rfl) (fun y e1 e2 e3 => by simp [Env.get, e1, e2, e3])

end

end ConPanqueque.T.LLeq
