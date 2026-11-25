import ConPanqueque.T.LvlEqQ
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `Level.leq`

`leq l r = leqCore defaultFuel (simplify l) (simplify r) 0`, over level words; and the handle form the
direct-sum field check runs (both readbacks, then the comparison).
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub

def fLeqTop := ofString "lvlLeqTop"

def leqTopBody : ProgHOL 64 :=
  prologue leqLocals
  (.seq (.call (some (some (.local, lA1), none)) fSimp [vv pLa])
  (.seq (.call (some (some (.local, lZ), none)) fSimp [vv pLb])
  (.seq (callLeqC lA1 lZ) (.return (vv lV)))))

section
variable {σ : Type}

theorem leq_unfold (l r : ConLeche.Level) :
    ConLeche.Level.leq l r = ConLeche.Level.leqCore 10000 (ConLeche.Level.simplify l) (ConLeche.Level.simplify r) 0 :=
  rfl

theorem leqTop_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (hcB : C.code.lookup fByC = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody C, .one))
    (hcI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one))
    (hcR : C.code.lookup fImax = some (leqParams.map (fun p => (p, ShapeHOL.one)), imBody C, .one))
    (hcE : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    (hcT : C.code.lookup fRest = some (leqParams.map (fun p => (p, ShapeHOL.one)), restBody, .one))
    (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), leqBody, .one)) :
    ∀ (H : List (BitVec 64)) (l r : ConLeche.Level) (wl wr : BitVec 64) (s : AState),
      LRep C.HB H s.store.ls wl l → LRep C.HB H s.store.ls wr r →
      SpecR (Pre (σ := σ) (ctxH C H) s [(pLa, wl), (pLb, wr)]) leqTopBody s
        (pure (ConLeche.Level.leq l r)) (PostOB (ctxH C H)) := by
  intro H l r wl wr s hl hr
  have RL := leq_all (σ := σ) C hok hcS hcN hcM hcC hcB hcI hcR hcE hcT hcL 10000 (by decide)
  refine specR_prologue (postOB_locals _) (params_noneE _ _ _) ?_
  rw [leq_unfold]
  generalize hsl : ConLeche.Level.simplify l = sl
  generalize hsr : ConLeche.Level.simplify r = sr
  refine specR_congr (m' := pure sl >>= fun _ => pure sr >>= fun _ => pure (ConLeche.Level.leqCore 10000 sl sr 0))
    (by simp) ?_
  refine callLv_spec (C := ctxH C H) lA1 fSimp [pLa] [vv pLa] (simpBody C) [wl] (by decide) rfl (by decide) hcM
    ⟨by simp +decide [ctxEnv], trivial⟩ _ (hsl ▸ simp_spec C hok hcM hcC l H wl s hl) (fun H1 c1 hp1 hc1 => ?_)
  refine callLv_spec (C := ctxH C H1) lZ fSimp [pLa] [vv pLb] (simpBody C) [wr] (by decide) rfl (by decide) hcM
    ⟨by simp +decide [ctxEnv], trivial⟩ _ (hsr ▸ simp_spec C hok hcM hcC r H1 wr s (lrep_mono hp1 r wr hr))
    (fun H2 c2 hp2 hc2 => ?_)
  have hc1' := lrep_mono hp2 sl c1 hc1
  have hpre : H <+: H2 := hp1.trans hp2
  refine specR_congr (m' := pure (ConLeche.Level.leqCore 10000 sl sr 0) >>= fun o => pure o) (by simp) ?_
  refine callOB_spec (C := ctxH C H2) lV fLeq leqParams [.const (BitVec.ofNat 64 10000), vv lA1, vv lZ, .const 0] leqBody
    [BitVec.ofNat 64 10000, c1, c2, iW 0]
    (by decide) rfl (by decide) hcL ⟨rfl, by simp +decide, by simp +decide, by rw [iW_zero]; rfl, trivial⟩ _
    (RL H2 sl sr c1 c2 0 s hc1' hc2 (by decide)) ?_
  exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H2)
    (sr_of_eq ht.sr rfl rfl rfl rfl) hpre⟩)

end

end ConPanqueque.T.LLeq
