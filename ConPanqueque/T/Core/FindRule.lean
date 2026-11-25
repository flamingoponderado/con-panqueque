import ConPanqueque.T.Core.IotaTwin
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `findRule`: a recursor's rule for a constructor

A recursive function over the rules block (`RulesE`): the rule record whose constructor is `c`, as its
environment pointer plus one, or `0`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Str
open ConPanqueque.V.Enc

def frR := ofString "frr"
def frJ := ofString "frj"
def frN := ofString "frn"
def frC := ofString "frc"
def frQ := ofString "frq"
def frK := ofString "frk"
def frX := ofString "frx"
def fFr := ofString "findRule"

@[simp] theorem fr_frR_ne_frJ : frR ≠ frJ := by decide
@[simp] theorem fr_frR_ne_frN : frR ≠ frN := by decide
@[simp] theorem fr_frR_ne_frC : frR ≠ frC := by decide
@[simp] theorem fr_frR_ne_frQ : frR ≠ frQ := by decide
@[simp] theorem fr_frR_ne_frK : frR ≠ frK := by decide
@[simp] theorem fr_frR_ne_frX : frR ≠ frX := by decide
@[simp] theorem fr_frJ_ne_frR : frJ ≠ frR := by decide
@[simp] theorem fr_frJ_ne_frN : frJ ≠ frN := by decide
@[simp] theorem fr_frJ_ne_frC : frJ ≠ frC := by decide
@[simp] theorem fr_frJ_ne_frQ : frJ ≠ frQ := by decide
@[simp] theorem fr_frJ_ne_frK : frJ ≠ frK := by decide
@[simp] theorem fr_frJ_ne_frX : frJ ≠ frX := by decide
@[simp] theorem fr_frN_ne_frR : frN ≠ frR := by decide
@[simp] theorem fr_frN_ne_frJ : frN ≠ frJ := by decide
@[simp] theorem fr_frN_ne_frC : frN ≠ frC := by decide
@[simp] theorem fr_frN_ne_frQ : frN ≠ frQ := by decide
@[simp] theorem fr_frN_ne_frK : frN ≠ frK := by decide
@[simp] theorem fr_frN_ne_frX : frN ≠ frX := by decide
@[simp] theorem fr_frC_ne_frR : frC ≠ frR := by decide
@[simp] theorem fr_frC_ne_frJ : frC ≠ frJ := by decide
@[simp] theorem fr_frC_ne_frN : frC ≠ frN := by decide
@[simp] theorem fr_frC_ne_frQ : frC ≠ frQ := by decide
@[simp] theorem fr_frC_ne_frK : frC ≠ frK := by decide
@[simp] theorem fr_frC_ne_frX : frC ≠ frX := by decide
@[simp] theorem fr_frQ_ne_frR : frQ ≠ frR := by decide
@[simp] theorem fr_frQ_ne_frJ : frQ ≠ frJ := by decide
@[simp] theorem fr_frQ_ne_frN : frQ ≠ frN := by decide
@[simp] theorem fr_frQ_ne_frC : frQ ≠ frC := by decide
@[simp] theorem fr_frQ_ne_frK : frQ ≠ frK := by decide
@[simp] theorem fr_frQ_ne_frX : frQ ≠ frX := by decide
@[simp] theorem fr_frK_ne_frR : frK ≠ frR := by decide
@[simp] theorem fr_frK_ne_frJ : frK ≠ frJ := by decide
@[simp] theorem fr_frK_ne_frN : frK ≠ frN := by decide
@[simp] theorem fr_frK_ne_frC : frK ≠ frC := by decide
@[simp] theorem fr_frK_ne_frQ : frK ≠ frQ := by decide
@[simp] theorem fr_frK_ne_frX : frK ≠ frX := by decide
@[simp] theorem fr_frX_ne_frR : frX ≠ frR := by decide
@[simp] theorem fr_frX_ne_frJ : frX ≠ frJ := by decide
@[simp] theorem fr_frX_ne_frN : frX ≠ frN := by decide
@[simp] theorem fr_frX_ne_frC : frX ≠ frC := by decide
@[simp] theorem fr_frX_ne_frQ : frX ≠ frQ := by decide
@[simp] theorem fr_frX_ne_frK : frX ≠ frK := by decide

def frParams : List MlS := [frR, frJ, frN, frC]
def frLocals : List MlS := [frQ, frK, frX]

def frCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv frJ) (vv frN)) (.return (.const 0))
  (.seq (.assign .local frQ (.load .one (.op .add [vv frR, .shift .lsl (.op .add [vv frJ, .const 1]) (.const 3)])))
  (.seq (.assign .local frK (.load .one (vv frQ)))
  (.ite (.cmp .equal (vv frK) (vv frC)) (.return (.op .add [vv frQ, .const 1]))
  (.seq (.call (some (some (.local, frX), none)) fFr [vv frR, .op .add [vv frJ, .const 1], vv frN, vv frC])
    (.return (vv frX))))))

def frBody : ProgHOL 64 := prologue frLocals frCore

section
variable {σ : Type}

theorem fr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ frLocals → (ctxEnv C ++ frParams.zip vals).get x = none :=
  Knot.params_none C frLocals frParams vals (by decide) (by decide)

/-- The answer of `findRule`: a rule's record pointer plus one, or `0` (state and heap unchanged). -/
def PostFR (C : Ctx) (s : AState) (r : Option IRecRule) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ SR C s st ∧ match r with
    | none => w = 0
    | some rl => ∃ q, w = ecell C q + 1 ∧ q < C.EN ∧ RuleE C.EB C.EH q rl

theorem postFR_locals (C : Ctx) (s : AState) : ∀ (a : Option IRecRule) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostFR C s a w s' st → PostFR C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl, h3⟩

theorem ecell_shl (C : Ctx) (o j : Nat) (hj : j + 1 < 2 ^ 61) :
    ecell C o + (BitVec.ofNat 64 j + 1) <<< (3 : Nat) = ecell C (o + 1 + j) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat, w_shl _ _ (by omega),
    show (j + 1) * 2 ^ 3 = 8 * (1 + j) by omega, ecell_add, Nat.add_assoc]

theorem ecell_shl' (C : Ctx) (o j : Nat) (hj : j + 1 < 2 ^ 61) :
    ecell C o + (BitVec.ofNat 64 j <<< (3 : Nat) + 8#64) = ecell C (o + 1 + j) := by
  rw [w_shl _ _ (by omega), show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat,
    show j * 2 ^ 3 + 8 = 8 * (1 + j) by omega, ecell_add, Nat.add_assoc]

theorem fr_spec (C : Ctx) (hok : CtxOK C)
    (hcf : C.code.lookup fFr = some (frParams.map (fun p => (p, ShapeHOL.one)), frBody, .one))
    (rules : List IRecRule) (o : Nat) (hrl : C.EH[o]? = some (BitVec.ofNat 64 rules.length))
    (hrs : ∀ i (hi : i < rules.length), ∃ q, C.EH[o + 1 + i]? = some (C.EB + BitVec.ofNat 64 (8 * q)) ∧
      RuleE C.EB C.EH q rules[i]) (c : NIdx) (s : AState) :
    ∀ k j, rules.length - j = k → j ≤ rules.length →
      SpecR (σ := σ) (Pre C s (frParams.zip [ecell C o, BitVec.ofNat 64 j, BitVec.ofNat 64 rules.length,
        Enc.idxW c])) frBody s (pure (findRule (rules.drop j) c) : AM (Option IRecRule)) (PostFR C s) := by
  intro k
  induction k with
  | zero =>
    intro j hk hj
    have hj' : j = rules.length := by omega
    subst hj'
    refine specR_prologue (postFR_locals C s) (fr_none C _) ?_
    unfold frCore
    rw [List.drop_length]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, frParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, rfl⟩)
  | succ k ih =>
    intro j hk hj
    have hjl : j < rules.length := by omega
    refine specR_prologue (postFR_locals C s) (fr_none C _) ?_
    unfold frCore
    refine specR_atEntry fun t0 ht0 => ?_
    have hEN := ht0.sr.env.1.len
    have hlay := hok.envLay
    have hol : o < C.EH.length := (List.getElem?_eq_some_iff.mp hrl).1
    have hj61 : j + 1 < 2 ^ 61 := by
      obtain ⟨q, hq, _⟩ := hrs j hjl
      have := (List.getElem?_eq_some_iff.mp hq).1; omega
    have hrlen : rules.length < 2 ^ 62 := by
      obtain ⟨q, hq, _⟩ := hrs (rules.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hq).1; omega
    have hne : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 rules.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, frParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    obtain ⟨q, hq, hrule⟩ := hrs j hjl
    refine specR_envLoadI frQ _ (o + 1 + j) _ (by decide)
      (by simp +decide [sev, Env.get, frParams, ctxEnv]; first | exact ecell_shl' C o j hj61 | exact ecell_shl C o j hj61)
      hq ?_
    have hqE : q < C.EN := by have := (List.getElem?_eq_some_iff.mp hrule.1).1; omega
    refine specR_envLoadI frK (vv frQ) q _ (by decide) (by simp; rfl) hrule.1 ?_
    rw [List.drop_eq_getElem_cons hjl]
    simp only [findRule]
    by_cases hc : rules[j].ctor = c
    · rw [ite_eq_left (by simp [hc])]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, frParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hc])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (ecell C q + 1) (by simp [sev]; rfl)
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, q, rfl, hqE, hrule⟩)
    · rw [ite_eq_right (by simp [hc])]
      have hne2 : Enc.idxW rules[j].ctor ≠ Enc.idxW c := fun e => hc (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, frParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne2])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_congr (m' := (pure (findRule (rules.drop (j + 1)) c) : AM (Option IRecRule)) >>= fun r => pure r)
        (by simp) ?_
      refine specR_callNIH frX fFr frParams [vv frR, .op .add [vv frJ, .const 1], vv frN, vv frC] frBody
        [ecell C o, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 rules.length, Enc.idxW c] (by decide) rfl (by decide) hcf
        ⟨by simp +decide [Env.get, frParams, ctxEnv], by simp +decide [sev, Env.get, frParams, ctxEnv]; exact word_add1_eq j,
          by simp +decide [Env.get, frParams, ctxEnv], by simp +decide [Env.get, frParams, ctxEnv], trivial⟩
        (PostFR C s) (fun r w s' H' => H' = C.H ∧ s' = s ∧ match r with
          | none => w = 0
          | some rl => ∃ q, w = ecell C q + 1 ∧ q < C.EN ∧ RuleE C.EB C.EH q rl)
        (fun r w s' st ⟨hs, hsr, hr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hs, hr⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu frParams _ rfl hlk) (ih (j + 1) (by omega) (by omega)))
        (fun r w s' H' hp ⟨eH, hs, hr⟩ => ?_)
      subst eH hs
      exact specR_returnI _ w (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, hr⟩)

end

end ConPanqueque.T.WC
