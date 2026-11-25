import ConPanqueque.T.Ind.PiSortTele
import ConRon.Arena.Inductives.FieldTele

/-!
# `piBinders`, then the body's view: is the telescope a sort's, and how long

`blockCounts` reads a member's type off `piBinders` (all leading `∀`s, by the handle's own tag) and then views
the body: a sort gives the binder count.  `pbc(k, h)` computes that composite, `pbcT k h`: `0` when the body is
no sort, `n + 1` for `n` binders before a sort.  Out of fuel it halts (the twin fails).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG ConPanqueque.T.ExPre
open ConPanqueque.T.ExA ConPanqueque.T.ExSP

theorem fail_bind' {α β : Type} (e : CheckError) (k : α → AM β) : ((fail e : AM α) >>= k) = fail e := by
  funext st; rfl

/-- The twin composite: `piBinders`, then the body's view. -/
def pbcT (fuel : Nat) (h : EIdx) : AM (Option Nat) := do
  let (bs, res) ← piBinders fuel h
  match ← view res with
  | .sort _ => pure (some bs.length)
  | _ => pure none

theorem pbcT_zero (h : EIdx) : pbcT 0 h = (fail (.internal "fuel exhausted: piBinders") : AM (Option Nat)) := by
  simp only [pbcT, piBinders, fail_bind']

theorem pbcT_succ (fuel : Nat) (h : EIdx) : pbcT (fuel + 1) h =
    if h.tag == ETag.forallE then (do
      match ← viewBind h with
      | none => failDanglingE
      | some (_, b) => do
        let r ← pbcT fuel b
        pure (r.map (· + 1)))
    else (do
      match ← view h with
      | .sort _ => pure (some 0)
      | _ => pure none) := by
  unfold pbcT
  rw [piBinders]
  split
  · simp only [bind_assoc]
    congr 1; funext vb
    cases vb with
    | none => simp only [failDanglingE, fail_bind']
    | some p =>
      obtain ⟨ty, b⟩ := p
      simp only [bind_assoc, pure_bind]
      congr 1; funext q
      obtain ⟨bs, e⟩ := q
      simp only [pure_bind]
      congr 1; funext v
      cases v <;> simp
  · simp only [pure_bind, List.length_nil]

def fPbc := ofString "piBindersSort"

def pbcBody (fn : MlS) : ProgHOL 64 :=
  prologue gaaLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
    (.ite (tagIsE pH 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, lY), none)) fn [.op .sub [vv pFu, .const 1], vv lA2])
        (.ite (.cmp .equal (vv lY) (.const 0)) (.return (.const 0)) (.return (.op .add [vv lY, .const 1]))))))))
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
        (.ite (.cmp .equal (vv lDg) (.const 2)) (.return (.const 1)) (.return (.const 0))))))))

section
variable {σ : Type}

theorem pbc_spec (C : Ctx) (hcode : C.code.lookup fPbc = some ([(pFu, .one), (pH, .one)], pbcBody fPbc, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) (pbcBody fPbc) s
        (pbcT k h) (PostPST (ctxH C H) k) := by
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
    rw [pbcT_succ]
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (k + 1) (by omega) hk
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ctxEnv] at hw; exact absurd hw this
    obtain ⟨w, hw, hiff⟩ := sev_tagIs (ctxEnv (ctxH C H) ++ [(pFu, BitVec.ofNat 64 (k + 1)), (pH, Enc.idxW h)])
      pH h (by simp +decide [ctxEnv]) 6 (by omega) (by omega)
    by_cases ht : h.tag = UInt32.ofNat 6
    case pos =>
      have hb : (h.tag == ETag.forallE) = true := by simp [ht]; rfl
      rw [hb]; simp only [ite_true]
      refine specR_ifI _ w hw (fun _ => ?_) (fun e => absurd (hiff.mpr ht) (by simp [e]))
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h (Or.inr ht) s vw hvw)
        (by simp) (by simp +decide <;> rfl) (by simp +decide [ctxEnv] <;> rfl) (by decide) (fun vw P htg hsh => ?_)
      obtain ⟨ty, b, hpb, hwv⟩ : ∃ ty b, projBind vw = some (ty, b) ∧ encEView vw = [Enc.idxW ty, Enc.idxW b] := by
        have htT : h.tag.toNat = 6 := by rw [ht]; simp
        rw [htT] at htg
        cases vw with
        | lam ty b => exact ⟨ty, b, rfl, rfl⟩
        | forallE ty b => exact ⟨ty, b, rfl, rfl⟩
        | _ => simp [ENodeView.tagN] at htg <;> omega
      rw [hpb]; simp only
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by rw [hwv]; exact wordsAt_mem1 _ _ _ _ _) ?_
      refine specR_callNIH lY fPbc [pFu, pH] [.op .sub [vv pFu, .const 1], vv lA2] (pbcBody fPbc)
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
        · exfalso; have : BitVec.ofNat 64 (n + 1) = 0 := by split at hz <;> simp_all
          have := congrArg BitVec.toNat this; simp at this; omega
        · exact specR_returnI (.op .add [vv lY, .const 1]) (BitVec.ofNat 64 (n + 1) + 1)
            (by simp +decide [sev, optW]) (fun t ht' => ⟨H1, hp1, sr_of_eq ht'.sr rfl rfl rfl rfl, by
              simp only [optW, Option.map_some]; apply BitVec.eq_of_toNat_eq; simp, fun m e => by
                cases e; exact Nat.succ_lt_succ hnk⟩)
    case neg =>
      have hb : (h.tag == ETag.forallE) = false := by simp; intro e; exact ht e
      rw [hb]; simp only [Bool.false_eq_true, ite_false]
      refine specR_ifI _ w hw (fun e => absurd (hiff.mp e) ht) (fun _ => ?_)
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_viewI h (by simp +decide) (by simp +decide <;> rfl) (by simp +decide [ctxEnv] <;> rfl)
        (by decide) (fun vw P htg hsh => ?_)
      have htl : vw.tagN < 2 ^ 64 := by cases vw <;> simp [ENodeView.tagN]
      refine specR_ifI _ (if vw.tagN = 2 then 1 else 0)
        (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
          ofNat_eq_c_iff _ 2 htl (by decide)]) (fun hw2 => ?_) (fun hw2 => ?_)
      · have h2 : vw.tagN = 2 := by split at hw2 <;> simp_all
        cases vw with
        | sort u => exact specR_returnI (.const 1) 1 rfl (fun t ht' => ⟨H, List.prefix_refl _,
            sr_of_eq ht'.sr rfl rfl rfl rfl, rfl, fun m e => by cases e; omega⟩)
        | _ => revert h2; simp [ENodeView.tagN]
      · have h2 : vw.tagN ≠ 2 := by intro c; simp [c] at hw2
        cases vw with
        | sort _ => revert h2; simp [ENodeView.tagN]
        | _ => exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨H, List.prefix_refl _,
            sr_of_eq ht'.sr rfl rfl rfl rfl, rfl, fun _ e => by simp at e⟩)

end

end ConPanqueque.T.Ind
