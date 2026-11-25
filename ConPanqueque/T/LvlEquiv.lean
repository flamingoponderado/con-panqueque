import ConPanqueque.T.LvlLeqCore
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `isEquiv`

The `l == r` disjunct of con-leche's `isEquiv` is verdict-neutral (`isEquiv_noPtr`), so the port starts
at the simplified comparison.
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub

def fEqv := ofString "lvlIsEquiv"

theorem isEquiv_noPtr (l r : ConLeche.Level) :
    ConLeche.Level.isEquiv l r =
      if ConLeche.Level.simplify l = ConLeche.Level.simplify r then some true
      else match ConLeche.Level.leqCore 10000 (ConLeche.Level.simplify l) (ConLeche.Level.simplify r) 0 with
        | none => none
        | some false => some false
        | some true => ConLeche.Level.leqCore 10000 (ConLeche.Level.simplify r) (ConLeche.Level.simplify l) 0 := by
  unfold ConLeche.Level.isEquiv
  by_cases h : (l == r) = true
  · have e : l = r := eq_of_beq h
    subst e; simp
  · simp only [h, Bool.false_eq_true, ite_false]
    by_cases hs : ConLeche.Level.simplify l = ConLeche.Level.simplify r
    · simp [hs]
    · simp only [hs, ite_false, ConLeche.Level.leq, ConLeche.Level.defaultFuel]
      rcases ConLeche.Level.leqCore 10000 (ConLeche.Level.simplify l) (ConLeche.Level.simplify r) 0 with _ | _ | _ <;> rfl

def callLeqC (a b : MlS) : ProgHOL 64 :=
  .call (some (some (.local, lV), none)) fLeq [.const (BitVec.ofNat 64 10000), vv a, vv b, .const 0]

def eqvBody : ProgHOL 64 :=
  prologue leqLocals
  (.seq (.call (some (some (.local, lA1), none)) fSimp [vv pLa])
  (.seq (.call (some (some (.local, lZ), none)) fSimp [vv pLb])
  (.seq (.call (some (some (.local, lE0), none)) fLvlEq [vv lA1, vv lZ])
  (.ite (eqC lE0 0)
    (.seq (callLeqC lA1 lZ)
     (.ite (eqC lV 0) (retK 0) (.ite (eqC lV 1) (retK 1)
       (.seq (callLeqC lZ lA1) (.return (vv lV))))))
    (retK 2)))))

section
variable {σ : Type}

theorem params_noneE (va vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ leqLocals → (ctxEnv C ++ [(pLa, va), (pLb, vb)]).get x = none := by
  intro x hx
  simp only [leqLocals, lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem iW_zero : iW 0 = 0 := by decide

theorem eqv_spec (C : Ctx) (hok : CtxOK C)
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
      SpecR (Pre (σ := σ) (ctxH C H) s [(pLa, wl), (pLb, wr)]) eqvBody s
        (pure (ConLeche.Level.isEquiv l r)) (PostOB (ctxH C H)) := by
  intro H l r wl wr s hl hr
  have RL := leq_all (σ := σ) C hok hcS hcN hcM hcC hcB hcI hcR hcE hcT hcL 10000 (by decide)
  refine specR_prologue (postOB_locals _) (params_noneE _ _ _) ?_
  rw [isEquiv_noPtr]
  generalize hsl : ConLeche.Level.simplify l = sl
  generalize hsr : ConLeche.Level.simplify r = sr
  refine specR_congr (m' := pure sl >>= fun _ => pure sr >>= fun _ => pure (decide (sl = sr)) >>= fun _ =>
    pure (if sl = sr then some true else match ConLeche.Level.leqCore 10000 sl sr 0 with
        | none => none
        | some false => some false
        | some true => ConLeche.Level.leqCore 10000 sr sl 0)) (by simp) ?_
  refine callLv_spec (C := ctxH C H) lA1 fSimp [pLa] [vv pLa] (simpBody C) [wl] (by decide) rfl (by decide) hcM
    ⟨by simp +decide [ctxEnv], trivial⟩ _ (hsl ▸ simp_spec C hok hcM hcC l H wl s hl) (fun H1 c1 hp1 hc1 => ?_)
  refine callLv_spec (C := ctxH C H1) lZ fSimp [pLa] [vv pLb] (simpBody C) [wr] (by decide) rfl (by decide) hcM
    ⟨by simp +decide [ctxEnv], trivial⟩ _ (hsr ▸ simp_spec C hok hcM hcC r H1 wr s (lrep_mono hp1 r wr hr))
    (fun H2 c2 hp2 hc2 => ?_)
  have hc1' := lrep_mono hp2 sl c1 hc1
  refine callEq_spec (C := ctxH C H2) hcE lE0 lA1 lZ sl sr c1 c2 (by decide) (by simp +decide) (by simp)
    (lvlEq_spec (ctxH C H2) (ctxOK_H hok H2) hcN hcE sl c1 c2 sr s hc1' hc2) ?_
  have hpre : H <+: H2 := hp1.trans hp2
  by_cases he : sl = sr
  · simp only [he, decide_true, ite_true]
    refine specR_ifI _ 0 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ _ rfl (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H2)
      (sr_of_eq ht.sr rfl rfl rfl rfl) hpre⟩)
  simp only [he, decide_false, ite_false]
  refine specR_ifI _ 1 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_congr (m' := pure (ConLeche.Level.leqCore 10000 sl sr 0) >>= fun o => pure (match o with
      | none => none | some false => some false | some true => ConLeche.Level.leqCore 10000 sr sl 0)) (by simp) ?_
  refine callOB_spec (C := ctxH C H2) lV fLeq leqParams [.const (BitVec.ofNat 64 10000), vv lA1, vv lZ, .const 0] leqBody
    [BitVec.ofNat 64 10000, c1, c2, iW 0]
    (by decide) rfl (by decide) hcL ⟨rfl, by simp +decide, by simp +decide, by rw [iW_zero]; rfl, trivial⟩ _
    (RL H2 sl sr c1 c2 0 s hc1' hc2 (by decide)) ?_
  rcases ho : ConLeche.Level.leqCore 10000 sl sr 0 with _ | b0
  · refine specR_ifI _ 1 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ _ rfl (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H2)
      (sr_of_eq ht.sr rfl rfl rfl rfl) hpre⟩)
  cases b0
  · refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ _ rfl (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H2)
      (sr_of_eq ht.sr rfl rfl rfl rfl) hpre⟩)
  refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_congr (m' := pure (ConLeche.Level.leqCore 10000 sr sl 0) >>= fun o => pure o) (by simp) ?_
  refine callOB_spec (C := ctxH C H2) lV fLeq leqParams [.const (BitVec.ofNat 64 10000), vv lZ, vv lA1, .const 0] leqBody
    [BitVec.ofNat 64 10000, c2, c1, iW 0]
    (by decide) rfl (by decide) hcL ⟨rfl, by simp +decide, by simp +decide, by rw [iW_zero]; rfl, trivial⟩ _
    (RL H2 sr sl c2 c1 0 s hc2 hc1' (by decide)) ?_
  exact specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_weakenH (C := ctxH C H) (H := H2)
    (sr_of_eq ht.sr rfl rfl rfl rfl) hpre⟩)

end

end ConPanqueque.T.LLeq
