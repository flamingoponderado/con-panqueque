import ConPanqueque.T.Ind.PiBinders

/-!
# `piBinders`, its binder count

`pbn(k, h)`: the number of leading `∀` binders of `h` (by the handle's tag), the twin's `(piBinders k h).1.length`.
Out of fuel it halts (the twin fails).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG ConPanqueque.T.ExPre
open ConPanqueque.T.ExA ConPanqueque.T.ExSP

def fPbn := ofString "piBindersCount"

def pbnBody : ProgHOL 64 :=
  prologue gaaLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
    (.ite (tagIsE pH 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, lY), none)) fPbn [.op .sub [vv pFu, .const 1], vv lA2])
        (.return (.op .add [vv lY, .const 1])))))))
      (.return (.const 0))))

section
variable {σ : Type}

/-- The count's post: the binder count, at most the fuel. -/
def PostPBN (C : Ctx) (K : Nat) (r : List EIdx × EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ w = BitVec.ofNat 64 r.1.length ∧ r.1.length ≤ K

theorem postPBN_locals (C : Ctx) (K : Nat) : ∀ (a : List EIdx × EIdx) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostPBN C K a w s' st → PostPBN C K a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem pbn_spec (C : Ctx) (hcode : C.code.lookup fPbn = some ([(pFu, .one), (pH, .one)], pbnBody, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) pbnBody s
        (piBinders k h) (PostPBN (ctxH C H) k) := by
  intro k
  induction k with
  | zero =>
    intro _ H s h
    refine specR_prologue (postPBN_locals _ _) (params_noneSP _ _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    exact specR_hangI
  | succ k ih =>
    intro hk H s h
    have ih' := ih (by omega)
    refine specR_prologue (postPBN_locals _ _) (params_noneSP _ _ _) ?_
    rw [piBinders]
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
      refine specR_callNIH lY fPbn [pFu, pH] [.op .sub [vv pFu, .const 1], vv lA2] pbnBody
        [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcode
        ⟨by simp +decide [sev, ctxEnv]; exact ofNat_succ_sub_one k, by simp +decide, trivial⟩
        (PostPBN (ctxH C H) k) (fun r w _ _ => w = BitVec.ofNat 64 r.1.length ∧ r.1.length ≤ k)
        (fun r w s' st ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, ⟨h1, h2⟩, hs⟩)
        (fun u hu _ hlk => fun w hw => by subst hw; exact ih' H s b _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
        (fun r wy s1 H1 hp1 ⟨hwy, hbd⟩ => ?_)
      subst hwy
      obtain ⟨bs, e⟩ := r
      exact specR_returnI (.op .add [vv lY, .const 1]) (BitVec.ofNat 64 bs.length + 1)
        (by simp +decide [sev]) (fun t ht' => ⟨H1, hp1, sr_of_eq ht'.sr rfl rfl rfl rfl, by
          apply BitVec.eq_of_toNat_eq; simp, by simp at hbd ⊢; omega⟩)
    case neg =>
      have hb : (h.tag == ETag.forallE) = false := by simp; intro e; exact ht e
      rw [hb]; simp only [Bool.false_eq_true, ite_false]
      refine specR_ifI _ w hw (fun e => absurd (hiff.mp e) ht) (fun _ => ?_)
      exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨H, List.prefix_refl _,
        sr_of_eq ht'.sr rfl rfl rfl rfl, rfl, by simp⟩)

end

end ConPanqueque.T.Ind
