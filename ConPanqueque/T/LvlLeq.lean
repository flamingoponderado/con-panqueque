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

end ConPanqueque.T.LLeq
