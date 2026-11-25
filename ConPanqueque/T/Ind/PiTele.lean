import ConPanqueque.T.Ind.PiBinders
import ConPanqueque.T.LvlMk
import ConPanqueque.T.Core.Unfold
import ConRon.Arena.Inductives.IotaRead

/-!
# `piTele`: a `∀`-telescope's binder count and body

`piTele(k, h)` returns a block `[n, body]`; out of fuel it halts (the twin fails).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG ConPanqueque.T.ExPre
open ConPanqueque.T.ExA ConPanqueque.T.ExSP

def fPiTele := ofString "piTele"

def ptBody (C : Ctx) (fn : MlS) : ProgHOL 64 :=
  prologue gaaLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
    (.ite (tagIsE pH 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, lY), none)) fn [.op .sub [vv pFu, .const 1], vv lA2])
      (.seq (.assign .local lA1 (.load .one (vv lY)))
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lY, .const 8])))
        (alloc2 C lW (.op .add [vv lA1, .const 1]) (vv lA2) (.return (vv lW))))))))))
      (alloc2 C lW (.const 0) (vv pH) (.return (vv lW)))))

section
variable {σ : Type}

/-- The telescope's post: a block `[n, body]` of a bigger heap, `n` below the fuel. -/
def PostPT (C : Ctx) (k : Nat) (a : Nat × EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ a.1 < k ∧
    ∃ ob, w = cellA C ob ∧ H'[ob]? = some (BitVec.ofNat 64 a.1) ∧ H'[ob + 1]? = some (Enc.idxW a.2)

theorem postPT_locals (C : Ctx) (k : Nat) : ∀ (a : Nat × EIdx) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostPT C k a w s' st → PostPT C k a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem pt_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fPiTele = some ([(pFu, .one), (pH, .one)], ptBody C fPiTele, .one)) :
    ∀ k, k < 2 ^ 63 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) (ptBody C fPiTele) s
        (piTele k h) (PostPT (ctxH C H) k) := by
  intro k
  induction k with
  | zero =>
    intro _ H s h
    refine specR_prologue (postPT_locals _ _) (params_noneSP _ _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    exact specR_hangI
  | succ k ih =>
    intro hk H s h
    have ih' := ih (by omega)
    refine specR_prologue (postPT_locals _ _) (params_noneSP _ _ _) ?_
    rw [piTele]
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (k + 1) (by omega) (by omega)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ctxEnv] at hw; exact absurd hw this
    obtain ⟨w, hw, hiff⟩ := sev_tagIs (ctxEnv (ctxH C H) ++ [(pFu, BitVec.ofNat 64 (k + 1)), (pH, Enc.idxW h)])
      pH h (by simp +decide [ctxEnv]) 6 (by omega) (by omega)
    by_cases ht : h.tag = UInt32.ofNat 6
    case neg =>
      have hb : (h.tag == ETag.forallE) = false := by simp; intro e; exact ht e
      rw [hb]; simp only [Bool.false_eq_true, ite_false]
      refine specR_ifI _ w hw (fun e => absurd (hiff.mp e) ht) (fun _ => ?_)
      refine specR_alloc2I (ctxOK_H hok H) lW (.const 0) (vv pH) 0 (Enc.idxW h) (by decide) (fun _ => rfl)
        (fun _ => by simp +decide [sev, ctxEnv]) (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (0 : BitVec 64) (Enc.idxW h) hws
      exact specR_returnI _ _ (by simp +decide [sev] <;> rfl) (fun t ht' => ⟨_, hp2.trans (img2_prefix _ _ _ _ hws),
        sr_of_eq ht'.sr rfl rfl rfl rfl, by simp, H2.length, rfl, by simpa using g0, g1⟩)
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
    refine specR_callNIH lY fPiTele [pFu, pH] [.op .sub [vv pFu, .const 1], vv lA2] (ptBody C fPiTele)
      [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, ctxEnv]; exact ofNat_succ_sub_one k, by simp +decide, trivial⟩
      (PostPT (ctxH C H) k) (fun r w _ H' => r.1 < k ∧
        ∃ ob, w = cellA C ob ∧ H'[ob]? = some (BitVec.ofNat 64 r.1) ∧ H'[ob + 1]? = some (Enc.idxW r.2))
      (fun r w s' st ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, ⟨h1, h2⟩, hs⟩)
      (fun u hu _ hlk => fun w hw => by subst hw; exact ih' H s b _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
      (fun r wy s1 H1 hp1 ⟨hrk, ob, hwy, hc0, hc1⟩ => ?_)
    subst hwy
    refine UD.specR_heapLoadI' (C := ctxH C H1) lA1 (vv lY) ob _ hc0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) lA2 _ (ob + 1) _ hc1 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ob) ?_
    refine specR_alloc2I (ctxOK_H hok H1) lW _ _ (BitVec.ofNat 64 (r.1 + 1)) (Enc.idxW r.2) (by decide)
      (fun _ => by simp +decide [sev, Env.get_cons]; exact word_add1_eq r.1)
      (fun _ => by simp +decide [sev, Env.get_cons]) (fun H2 ws hp2 hws => ?_)
    obtain ⟨g0, g1⟩ := img2_get H2 ws (BitVec.ofNat 64 (r.1 + 1)) (Enc.idxW r.2) hws
    exact specR_returnI _ _ (by simp +decide [sev] <;> rfl) (fun t ht' => ⟨_, (hp1.trans hp2).trans (img2_prefix _ _ _ _ hws),
      sr_of_eq ht'.sr rfl rfl rfl rfl, by simp; omega, H2.length, rfl, g0, g1⟩)

end

end ConPanqueque.T.Ind
