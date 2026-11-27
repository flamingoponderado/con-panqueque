import ConPanqueque.T.Quot.RecSpec

/-! # `checkDecl` at a quotient record: every kind -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Decl

section
variable {σ : Type}

set_option maxHeartbeats 4000000 in
/-- **`checkDecl` at a quotient record**: every kind. -/
theorem kq_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hs : C.side = false) (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (k : ConLeche.QuotKind) (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (s : AState) :
    SpecR (σ := σ) (Pre C s (kdParams.zip [cellA C q, BitVec.ofNat 64 (qkN k), 0])) (kqBody C) s
      (checkDecl mode pins C.fe (.quotDecl k cv)) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (kq_none C _) ?_
  have hB0 : Base C q (ctxEnv C ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (qkN k), 0]) :=
    ⟨by simp +decide [Env.get, kdParams, ctxEnv], by simp +decide [Env.get, kdParams, ctxEnv]⟩
  have hV : (ctxEnv C ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (qkN k), 0]).get kdV =
      some (BitVec.ofNat 64 (qkN k)) := by simp +decide [Env.get, kdParams, ctxEnv]
  rw [checkDecl_quot]
  have hT : ∀ (fe : IFEnv) (s' : AState), s'.pins = C.pins → (pure fe : AM IFEnv) s' = .ok (fe, s') :=
    fun _ _ _ => rfl
  cases k with
  | type =>
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .type 0 (Or.inl ⟨rfl, rfl⟩) cv q hrc C.H
      (List.prefix_refl _) s _ hB0 pure hT (fun ol H4 s3 Γ' hb hp hB hRL =>
        restNR_spec ra mode C hok hc hpl hg hF hL hf hA .type 0 (Or.inl ⟨rfl, rfl⟩) cv q hrc ol hb pure hT H4 hp s3 Γ'
          hB hRL)
  | ctor =>
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .ctor 1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) cv q hrc C.H
      (List.prefix_refl _) s _ hB0 pure hT (fun ol H4 s3 Γ' hb hp hB hRL =>
        restNR_spec ra mode C hok hc hpl hg hF hL hf hA .ctor 1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) cv q hrc ol hb pure hT
          H4 hp s3 Γ' hB hRL)
  | sound =>
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .sound 4 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) cv q
      hrc C.H (List.prefix_refl _) s _ hB0 pure hT (fun ol H4 s3 Γ' hb hp hB hRL =>
        restNR_spec ra mode C hok hc hpl hg hF hL hf hA .sound 4 (Or.inr (Or.inr ⟨rfl, rfl⟩)) cv q hrc ol hb pure hT
          H4 hp s3 Γ' hB hRL)
  | lift =>
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .lift 2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      cv q hrc C.H (List.prefix_refl _) s _ hB0 pure hT (fun ol H4 s3 Γ' hb hp hB hRL =>
        restR_spec ra mode C hok hc hpl hg hF hL hf hA .lift 2 (Or.inl ⟨rfl, rfl⟩) cv q hrc ol hb pure hT H4 hp s3 Γ'
          hB hRL)
  | ind =>
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .ind 3 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      cv q hrc C.H (List.prefix_refl _) s _ hB0 pure hT (fun ol H4 s3 Γ' hb hp hB hRL =>
        restR_spec ra mode C hok hc hpl hg hF hL hf hA .ind 3 (Or.inr ⟨rfl, rfl⟩) cv q hrc ol hb pure hT H4 hp s3 Γ'
          hB hRL)

end

end ConPanqueque.T.Quot
