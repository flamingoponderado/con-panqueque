import ConPanqueque.T.Inv
import ConPanqueque.T.Ex.GetAppFn
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `getAppFn` again, in the symbolic-environment style

The same function as `T/Ex/GetAppFn.lean`, behind the uniform prologue, proved with the `Inv`
combinators: side conditions are `rfl`/`decide`, the local-variable bookkeeping is gone.
-/

namespace ConPanqueque.T.Ex2
open ConPanqueque.T ConPanqueque.T.Ex

def locals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, lX]
def body : ProgHOL 64 := prologue locals getAppFnCore

section
variable {σ : Type}

theorem sev_isApp (Γ : Env) (x : MlS) (w : BitVec 64) (hx : Γ.get x = some w) :
    sev Γ (isAppE (vv x)) = some (isAppW w) := by
  simp only [isAppE, isAppW, sev, vv, hx, bw]
  by_cases h : (w >>> (26 : BitVec 64).toNat) &&& 31 = 4
  · simp [h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem post_locals' (C : Ctx) (s : AState) : ∀ (a : EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    Post C s a w s' st → Post C s a w s' { st with locals := L } := post_locals C s

theorem getAppFn_spec (C : Ctx) (hcode : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], body, .one)) :
    ∀ fuel (h : EIdx) (s : AState), fuel < 2 ^ 64 →
      SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pH, Enc.idxW h)]) body s (getAppFn fuel h) (Post C s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h s _
    refine specR_prologue (post_locals' C s) (by intro x hx; simp [locals] at hx; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro h s hf
    refine specR_prologue (post_locals' C s) (by intro x hx; simp [locals] at hx; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (m' := if h.tag == ETag.app then (do
        match ← ConRon.Arena.viewApp h with
        | none => failDanglingE
        | some (f, _) => getAppFn n f) else pure h) (by rw [getAppFn]; rfl) ?_
    refine specR_iteI _ _ (sev_isApp _ pH _ rfl) (by rw [isApp_iff]; simp [ETag.app]) (fun hb => ?_) (fun _ => ?_)
    · have h4 : h.tag = 4 := by simpa [ETag.app] using hb
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
      refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) rfl ?_
      refine specR_viewAppI h h4 rfl rfl rfl (by decide) (fun f a P => ?_)
      refine specR_congr (m' := getAppFn n f) rfl ?_
      refine specR_loadI lX (vv lRp) P (Enc.idxW f) (by decide) rfl (List.mem_cons_self ..) ?_
      refine specR_congr (m' := getAppFn n f >>= fun a => pure a) (by simp) ?_
      refine specR_call2I lX fGetAppFn pFu pH (by decide) (.op .sub [vv pFu, .const 1]) (vv lX) body
        (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW f) (by decide) hcode rfl rfl (Post C s)
        (fun _ _ _ _ hp => by rw [hp.2.1]; exact hp.2.2)
        (fun u hu h1 h2 v hv => by
          subst hv
          exact ih f s (by omega) _ ⟨hu, fun x v hx => by
          simp only [Env.get] at hx
          split at hx
          · rename_i e; subst e; simp at hx; subst hx; rw [h1, ofNat_succ_sub_one]
          · split at hx
            · rename_i e; subst e; simp at hx; subst hx; exact h2
            · simp at hx⟩)
        (fun a w s' st hp => ?_)
      obtain ⟨hw, hs, _⟩ := hp
      subst hw hs
      exact specR_returnI (vv lX) (Enc.idxW a) rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · exact specR_returnI (vv pH) (Enc.idxW h) rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ex2
