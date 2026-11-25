import ConPanqueque.T.Ex.StripPis

/-!
# `piSortTeleLen?`

The first function of the inductive-block check (`indParamsOk` reads it off a member's type): the number
of leading `∀` binders before a `Sort`, or `none` when the telescope ends in anything else.

`pst(k, h)`: fuel `k`, expression `h`; returns `0` for `none` and `n + 1` for `some n`.  Out of fuel it
halts (the twin fails).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG ConPanqueque.T.ExPre
open ConPanqueque.T.ExA ConPanqueque.T.ExSP

def fPiSortTele := ofString "piSortTeleLen"

def pstBody (fn : MlS) : ProgHOL 64 :=
  prologue gaaLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.ite (.cmp .equal (vv lDg) (.const 6))
        (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
          (.seq (.call (some (some (.local, lY), none)) fn [.op .sub [vv pFu, .const 1], vv lA2])
            (.ite (.cmp .equal (vv lY) (.const 0)) (.return (.const 0)) (.return (.op .add [vv lY, .const 1])))))
        (.ite (.cmp .equal (vv lDg) (.const 2)) (.return (.const 1)) (.return (.const 0))))))))

/-- An optional count as a word: `0` for `none`, `n + 1` for `some n`. -/
def optW : Option Nat → BitVec 64
  | none => 0
  | some n => BitVec.ofNat 64 (n + 1)

section
variable {σ : Type}

/-- The post at fuel `K`: the word encodes the answer, and a count is below the fuel. -/
def PostPST (C : Ctx) (K : Nat) (o : Option Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ w = optW o ∧ ∀ n, o = some n → n < K

theorem postPST_locals (C : Ctx) (K : Nat) : ∀ (a : Option Nat) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostPST C K a w s' st → PostPST C K a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem ofNat_eq_c_iff (n c : Nat) (hn : n < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 n = BitVec.ofNat 64 c) ↔ n = c := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp at this; omega
  · intro e; rw [e]

theorem pst_spec (C : Ctx) (hcode : C.code.lookup fPiSortTele = some ([(pFu, .one), (pH, .one)], pstBody fPiSortTele, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) (pstBody fPiSortTele) s
        (piSortTeleLen? k h) (PostPST (ctxH C H) k) := by
  intro k
  induction k with
  | zero =>
    intro _ H s h
    refine specR_prologue (postPST_locals _ _) (params_noneSP _ _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    exact specR_hangI
  | succ k ih =>
    intro hk H s h
    have ih' := ih (by omega)
    refine specR_prologue (postPST_locals _ _) (params_noneSP _ _ _) ?_
    rw [piSortTeleLen?]
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (k + 1) (by omega) hk
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ctxEnv] at hw; exact absurd hw this
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
    refine specR_viewI h (by simp +decide) (by simp +decide <;> rfl) (by simp +decide [ctxEnv] <;> rfl)
      (by decide) (fun vw P htg hsh => ?_)
    have htl : vw.tagN < 2 ^ 64 := by cases vw <;> simp [ENodeView.tagN]
    refine specR_ifI _ (if vw.tagN = 6 then 1 else 0)
      (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        ofNat_eq_c_iff _ 6 htl (by decide)]) (fun hw6 => ?_) (fun hw6 => ?_)
    · -- a `∀`: recurse on the body
      have h6 : vw.tagN = 6 := by by_cases c : vw.tagN = 6; exact c; simp [c] at hw6
      cases vw with
      | forallE ty b =>
        simp only
        refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide)
          (by simp +decide [sev]) rfl (by exact wordsAt_mem1 _ _ _ _ _) ?_
        refine specR_callNIH lY fPiSortTele [pFu, pH] [.op .sub [vv pFu, .const 1], vv lA2] (pstBody fPiSortTele)
          [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcode
          ⟨by simp +decide [sev, ctxEnv]; exact ofNat_succ_sub_one k, by simp +decide, trivial⟩
          (PostPST (ctxH C H) k) (fun o w _ _ => w = optW o ∧ ∀ n, o = some n → n < k)
          (fun o w s' st ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, ⟨h1, h2⟩, hs⟩)
          (fun u hu _ hlk => fun w hw => by subst hw; exact ih' H s b _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
          (fun o wy s1 H1 hp1 ⟨hwy, hbd⟩ => ?_)
        rcases o with _ | n
        · subst hwy
          refine specR_ifI _ 1 (by simp +decide [sev, optW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun hw => absurd hw (by decide))
          exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨H1, hp1, sr_of_eq ht'.sr rfl rfl rfl rfl, rfl,
            fun _ e => by simp at e⟩)
        · subst hwy
          have hnk := hbd n rfl
          refine specR_ifI _ (if BitVec.ofNat 64 (n + 1) = 0 then 1 else 0)
            (by simp +decide [sev, optW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hz => ?_) (fun _ => ?_)
          · -- `n + 1 ≡ 0 (mod 2⁶⁴)` cannot happen: `n < k < 2⁶⁴`
            exfalso; have : BitVec.ofNat 64 (n + 1) = 0 := by split at hz <;> simp_all
            have := congrArg BitVec.toNat this; simp at this; omega
          · exact specR_returnI (.op .add [vv lY, .const 1]) (BitVec.ofNat 64 (n + 1) + 1)
              (by simp +decide [sev, optW]) (fun t ht' => ⟨H1, hp1, sr_of_eq ht'.sr rfl rfl rfl rfl, by
                simp only [optW]; apply BitVec.eq_of_toNat_eq; simp, fun m e => by
                  cases e; exact Nat.succ_lt_succ hnk⟩)
      | _ => revert h6; simp [ENodeView.tagN]
    · -- not a `∀`
      have h6 : vw.tagN ≠ 6 := by intro c; simp [c] at hw6
      refine specR_ifI _ (if vw.tagN = 2 then 1 else 0)
        (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
          ofNat_eq_c_iff _ 2 htl (by decide)]) (fun hw2 => ?_) (fun hw2 => ?_)
      · have h2 : vw.tagN = 2 := by by_cases c : vw.tagN = 2; exact c; simp [c] at hw2
        cases vw with
        | sort u => exact specR_returnI (.const 1) 1 rfl (fun t ht' => ⟨H, List.prefix_refl _,
            sr_of_eq ht'.sr rfl rfl rfl rfl, rfl, fun m e => by simp only [Option.some.injEq] at e; omega⟩)
        | _ => revert h2; simp [ENodeView.tagN]
      · have h2 : vw.tagN ≠ 2 := by intro c; simp [c] at hw2
        cases vw with
        | forallE _ _ => revert h6; simp [ENodeView.tagN]
        | sort _ => revert h2; simp [ENodeView.tagN]
        | _ => exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨H, List.prefix_refl _,
            sr_of_eq ht'.sr rfl rfl rfl rfl, rfl, fun _ e => by simp at e⟩)

end

end ConPanqueque.T.Ind
