import ConPanqueque.T.Decl.EnvUndo

/-!
# Constant-table inserts of rule-less recursors, and contexts back after an undo

`specR_idxInsI'`: `specR_idxInsI` for any constant whose recursor form (if any) carries no rules — the
rule-less generated recursors `classFeR` pushes.  `ctxOK_insEq`: a context whose environment and constant table
answer as `C`'s (the state after the pushes are undone) is well formed.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- `envDen_push` for a constant that is a recursor only with no rules. -/
theorem envDen_push' {fe fe' : IFEnv} {p : Pins} {st : EStore} {ci : IConstantInfo}
    (hf : ∀ n, fe'.find? n = if (ci.name == n) = true then some ci else fe.find? n)
    (ht : ∀ n, fe'.findTable? n = fe.findTable? n) (h : EnvDen fe p st) (hnew : NewDen ci st)
    (hrec : ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → rules = []) : EnvDen fe' p st := by
  obtain ⟨hc, htb, hp, hr⟩ := h
  refine ⟨fun c ci' hci => ?_, fun T tbl h' => htb T tbl (by rw [← ht]; exact h'), hp,
    fun c cv mI rP isK rules hci => ?_⟩
  · rw [hf] at hci
    split at hci
    · cases hci; exact hnew
    · exact hc c ci' hci
  · rw [hf] at hci
    split at hci
    · cases hci
      have := hrec cv mI rP isK rules rfl
      subst this
      intro rl hrl; cases hrl
    · exact hr c cv mI rP isK rules hci

/-- A context with an environment and constant table answering as `C`'s, over a grown environment image. -/
theorem ctxOK_insEq {C : Ctx} (hok : CtxOK C) {fe : IFEnv} {EH : List (BitVec 64)}
    {envM : Std.HashMap NIdx (BitVec 64)} (hp : C.EH <+: EH) (hf : ∀ n, fe.find? n = C.fe.find? n)
    (ht : ∀ n, fe.findTable? n = C.fe.findTable? n) (hm : ∀ n : NIdx, envM[n]? = C.envM[n]?) :
    CtxOK (ctxIns C fe EH envM) := by
  have h1 : EnvRel (ctxIns C fe EH envM) := by
    refine ⟨fun n => ?_, fun n => ?_⟩
    · show match fe.find? n with
        | none => envM[n]? = none
        | some ci => ∃ o, envM[n]? = some (ecell C o) ∧ CIE C.EB EH o ci
      rw [hf, hm]
      have := hok.envRel.1 n
      revert this
      cases C.fe.find? n with
      | none => exact id
      | some ci => exact fun ⟨o, h1, h2⟩ => ⟨o, h1, cie_mono hp h2⟩
    · show match fe.findTable? n with
        | none => C.tblM[n]? = none
        | some tb => ∃ o, C.tblM[n]? = some (ecell C o) ∧ TblE C.EB EH o tb
      rw [ht]
      have := hok.envRel.2 n
      revert this
      cases C.fe.findTable? n with
      | none => exact id
      | some tb => exact fun ⟨o, h1, h2⟩ => ⟨o, h1, tblE_mono hp h2⟩
  have h2 : PinsE (ctxIns C fe EH envM) := pinsE_E hok.pinsRel hp
  cases hok; constructor <;> first | assumption | exact h1 | exact h2

section
variable {σ : Type}

/-- **`specR_idxInsI` for a constant that is a recursor only with no rules.** -/
theorem specR_idxInsI' {α : Type} {C : Ctx} (hok : CtxOK C)
    (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (hg : TblGate C.fe) (ci : IConstantInfo) (hnew : C.fe.find? ci.name = none)
    (hrec : ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → rules = [])
    (EH : List (BitVec 64)) (ox : Nat) (hpE : C.EH <+: EH) {s : AState} (hden : NewDen ci s.store)
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (eN eX : ExpHOL 64) (r : MlS) (hr : r ∈ D) (heN : sev Γ eN = some (Enc.idxW ci.name))
    (heX' : sev Γ eX = some (ecell C ox))
    (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv (ctxIns C ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH
      (C.envM.insert ci.name (ecell C ox))) s ((r, w) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxE C EH) s Γ M D) (idxInsP C eN eX r rest) s m R := by
  unfold idxInsP
  refine specR_storeKBI (ctxOK_E hok hpE) 0 (by decide) eN (Enc.idxW ci.name) heN hkb ?_
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => m) (by simp) ?_
  refine specR_memoSetGIC (C := ctxE C EH)
    (C' := ctxIns C ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH (C.envM.insert ci.name (ecell C ox)))
    (D := D) (K := NIdx) (V := BitVec 64) encNI_inj (C.mG .env) (C.mg .env) C.envM ci.name (ecell C ox) (pure ()) rfl
    (fun u hu => hu.env.2.1) (fun i hi => hok.kbMemo .env i (by simp [encNI] at hi; omega))
    (fun j hj => hok.mdescMemo .env .env j hj)
    (fun u u' hsr hmem hfr hd hg' hc => sr_envIns (ctxOK_E hok hpE) hsr hfr hd hg' hc hmem rfl
      (envDen_push' (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew) hsr.envd hden hrec))
    hcS hcI r (.const (C.mG .env)) (.const 1) eX hr rfl rfl heX'
    (by simp [encNI]) (fun u hM j hj => by
      have e : j = 0 := by simp [encNI] at hj; omega
      subst e; exact hM _ (Enc.idxW ci.name) (by simp)) (fun w => ?_)
  exact hk w

end

end ConPanqueque.T.Decl
