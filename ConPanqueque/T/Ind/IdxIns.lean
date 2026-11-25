import ConPanqueque.T.Ind.CheckBlock

/-!
# A constant record into the environment index

`idxInsP`: the record already in the environment heap at `ox`; its name into the key buffer, then the constant
table's insert (`memoSet`) — `inst_spec`'s tail, for any record (a former's ten words among them).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

def idxInsP (C : Ctx) (eN eX : ExpHOL 64) (r : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eN)
  (.seq (.call (some (some (.local, r), none)) fMemoSet [.const (C.mG .env), .const 1, eX]) rest)

section
variable {σ : Type}

theorem specR_idxInsI {α : Type} {C : Ctx} (hok : CtxOK C)
    (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (hg : TblGate C.fe) (ci : IConstantInfo) (hnew : C.fe.find? ci.name = none)
    (hrec : ∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules)
    (EH : List (BitVec 64)) (ox : Nat) (hpE : C.EH <+: EH) {s : AState} (hden : NewDen ci s.store)
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (eN eX : ExpHOL 64) (r : MlS) (hr : r ∈ D) (heN : sev Γ eN = some (Enc.idxW ci.name))
    (heX : ∀ v, sev Γ eX = some v → v = ecell C ox) (heX' : sev Γ eX = some (ecell C ox))
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
      (envDen_push (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew) hsr.envd hden hrec))
    hcS hcI r (.const (C.mG .env)) (.const 1) eX hr rfl rfl heX'
    (by simp [encNI]) (fun u hM j hj => by
      have e : j = 0 := by simp [encNI] at hj; omega
      subst e; exact hM _ (Enc.idxW ci.name) (by simp)) (fun w => ?_)
  exact hk w

end

end ConPanqueque.T.Decl
