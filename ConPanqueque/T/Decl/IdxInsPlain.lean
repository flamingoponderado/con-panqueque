import ConPanqueque.T.Decl.IdxInsRec

/-!
# Constant-table inserts of recursors whose rules fire plainly

`specR_idxInsIP`: `specR_idxInsI'` for a recursor whose every rule fires `.plain` (no firing data to denote).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- `envDen_push` for a constant that is a recursor only with no rules. -/
theorem envDen_pushP {fe fe' : IFEnv} {p : Pins} {st : EStore} {ci : IConstantInfo}
    (hf : ∀ n, fe'.find? n = if (ci.name == n) = true then some ci else fe.find? n)
    (ht : ∀ n, fe'.findTable? n = fe.findTable? n) (h : EnvDen fe p st) (hnew : NewDen ci st)
    (hrec : ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ rl ∈ rules, rl.fire = .plain) : EnvDen fe' p st := by
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
      intro rl hrl
      have hpl := hrec cv mI rP isK rules rfl rl hrl
      refine ⟨fun lv h => ?_, fun lv pins h => ?_⟩
      · rcases h with ⟨pins, h⟩ | h <;> rw [hpl] at h <;> cases h
      · rw [hpl] at h; cases h
    · exact hr c cv mI rP isK rules hci

section
variable {σ : Type}

/-- **`specR_idxInsI` for a constant that is a recursor only with no rules.** -/
theorem specR_idxInsIP {α : Type} {C : Ctx} (hok : CtxOK C)
    (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (hg : TblGate C.fe) (ci : IConstantInfo) (hnew : C.fe.find? ci.name = none)
    (hrec : ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ rl ∈ rules, rl.fire = .plain)
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
      (envDen_pushP (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew) hsr.envd hden hrec))
    hcS hcI r (.const (C.mG .env)) (.const 1) eX hr rfl rfl heX'
    (by simp [encNI]) (fun u hM j hj => by
      have e : j = 0 := by simp [encNI] at hj; omega
      subst e; exact hM _ (Enc.idxW ci.name) (by simp)) (fun w => ?_)
  exact hk w

end

end ConPanqueque.T.Decl
