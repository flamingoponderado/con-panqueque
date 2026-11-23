import ConPanqueque.T.Big.NatBin
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `rawNatLit?` as a heap block

`rawNat(h)`: `0` for `none`; for a `Nat` literal its limbs copied to a fresh block; for `Nat.zero` (at the empty
level list) a block for `0`. The handle is viewed first, as the twin does, so a dangling handle halts.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def qH := ofString "qrh"
def qW := ofString "qrw"
def qC := ofString "qrc"
def qU := ofString "qru"
def qE := ofString "qre"
def qZ := ofString "qrz"
def qX := ofString "qrx"
def fRaw := ofString "rawNat"

@[simp] theorem rn_qH_ne_qW : qH ≠ qW := by decide
@[simp] theorem rn_qH_ne_qC : qH ≠ qC := by decide
@[simp] theorem rn_qH_ne_qU : qH ≠ qU := by decide
@[simp] theorem rn_qH_ne_qE : qH ≠ qE := by decide
@[simp] theorem rn_qH_ne_qZ : qH ≠ qZ := by decide
@[simp] theorem rn_qH_ne_qX : qH ≠ qX := by decide
@[simp] theorem rn_qH_ne_lFl : qH ≠ lFl := by decide
@[simp] theorem rn_lFl_ne_qH : lFl ≠ qH := by decide
@[simp] theorem rn_qH_ne_lDh : qH ≠ lDh := by decide
@[simp] theorem rn_lDh_ne_qH : lDh ≠ qH := by decide
@[simp] theorem rn_qH_ne_lDt : qH ≠ lDt := by decide
@[simp] theorem rn_lDt_ne_qH : lDt ≠ qH := by decide
@[simp] theorem rn_qH_ne_lDg : qH ≠ lDg := by decide
@[simp] theorem rn_lDg_ne_qH : lDg ≠ qH := by decide
@[simp] theorem rn_qH_ne_lDi : qH ≠ lDi := by decide
@[simp] theorem rn_lDi_ne_qH : lDi ≠ qH := by decide
@[simp] theorem rn_qH_ne_lRp : qH ≠ lRp := by decide
@[simp] theorem rn_lRp_ne_qH : lRp ≠ qH := by decide
@[simp] theorem rn_qH_ne_lRn : qH ≠ lRn := by decide
@[simp] theorem rn_lRn_ne_qH : lRn ≠ qH := by decide
@[simp] theorem rn_qH_ne_rZ : qH ≠ rZ := by decide
@[simp] theorem rn_rZ_ne_qH : rZ ≠ qH := by decide
@[simp] theorem rn_qH_ne_lFle : qH ≠ lFle := by decide
@[simp] theorem rn_lFle_ne_qH : lFle ≠ qH := by decide
@[simp] theorem rn_qH_ne_lDir : qH ≠ lDir := by decide
@[simp] theorem rn_lDir_ne_qH : lDir ≠ qH := by decide
@[simp] theorem rn_qH_ne_lKb : qH ≠ lKb := by decide
@[simp] theorem rn_lKb_ne_qH : lKb ≠ qH := by decide
@[simp] theorem rn_qH_ne_cH : qH ≠ cH := by decide
@[simp] theorem rn_cH_ne_qH : cH ≠ qH := by decide
@[simp] theorem rn_qW_ne_qH : qW ≠ qH := by decide
@[simp] theorem rn_qW_ne_qC : qW ≠ qC := by decide
@[simp] theorem rn_qW_ne_qU : qW ≠ qU := by decide
@[simp] theorem rn_qW_ne_qE : qW ≠ qE := by decide
@[simp] theorem rn_qW_ne_qZ : qW ≠ qZ := by decide
@[simp] theorem rn_qW_ne_qX : qW ≠ qX := by decide
@[simp] theorem rn_qW_ne_lFl : qW ≠ lFl := by decide
@[simp] theorem rn_lFl_ne_qW : lFl ≠ qW := by decide
@[simp] theorem rn_qW_ne_lDh : qW ≠ lDh := by decide
@[simp] theorem rn_lDh_ne_qW : lDh ≠ qW := by decide
@[simp] theorem rn_qW_ne_lDt : qW ≠ lDt := by decide
@[simp] theorem rn_lDt_ne_qW : lDt ≠ qW := by decide
@[simp] theorem rn_qW_ne_lDg : qW ≠ lDg := by decide
@[simp] theorem rn_lDg_ne_qW : lDg ≠ qW := by decide
@[simp] theorem rn_qW_ne_lDi : qW ≠ lDi := by decide
@[simp] theorem rn_lDi_ne_qW : lDi ≠ qW := by decide
@[simp] theorem rn_qW_ne_lRp : qW ≠ lRp := by decide
@[simp] theorem rn_lRp_ne_qW : lRp ≠ qW := by decide
@[simp] theorem rn_qW_ne_lRn : qW ≠ lRn := by decide
@[simp] theorem rn_lRn_ne_qW : lRn ≠ qW := by decide
@[simp] theorem rn_qW_ne_rZ : qW ≠ rZ := by decide
@[simp] theorem rn_rZ_ne_qW : rZ ≠ qW := by decide
@[simp] theorem rn_qW_ne_lFle : qW ≠ lFle := by decide
@[simp] theorem rn_lFle_ne_qW : lFle ≠ qW := by decide
@[simp] theorem rn_qW_ne_lDir : qW ≠ lDir := by decide
@[simp] theorem rn_lDir_ne_qW : lDir ≠ qW := by decide
@[simp] theorem rn_qW_ne_lKb : qW ≠ lKb := by decide
@[simp] theorem rn_lKb_ne_qW : lKb ≠ qW := by decide
@[simp] theorem rn_qW_ne_cH : qW ≠ cH := by decide
@[simp] theorem rn_cH_ne_qW : cH ≠ qW := by decide
@[simp] theorem rn_qC_ne_qH : qC ≠ qH := by decide
@[simp] theorem rn_qC_ne_qW : qC ≠ qW := by decide
@[simp] theorem rn_qC_ne_qU : qC ≠ qU := by decide
@[simp] theorem rn_qC_ne_qE : qC ≠ qE := by decide
@[simp] theorem rn_qC_ne_qZ : qC ≠ qZ := by decide
@[simp] theorem rn_qC_ne_qX : qC ≠ qX := by decide
@[simp] theorem rn_qC_ne_lFl : qC ≠ lFl := by decide
@[simp] theorem rn_lFl_ne_qC : lFl ≠ qC := by decide
@[simp] theorem rn_qC_ne_lDh : qC ≠ lDh := by decide
@[simp] theorem rn_lDh_ne_qC : lDh ≠ qC := by decide
@[simp] theorem rn_qC_ne_lDt : qC ≠ lDt := by decide
@[simp] theorem rn_lDt_ne_qC : lDt ≠ qC := by decide
@[simp] theorem rn_qC_ne_lDg : qC ≠ lDg := by decide
@[simp] theorem rn_lDg_ne_qC : lDg ≠ qC := by decide
@[simp] theorem rn_qC_ne_lDi : qC ≠ lDi := by decide
@[simp] theorem rn_lDi_ne_qC : lDi ≠ qC := by decide
@[simp] theorem rn_qC_ne_lRp : qC ≠ lRp := by decide
@[simp] theorem rn_lRp_ne_qC : lRp ≠ qC := by decide
@[simp] theorem rn_qC_ne_lRn : qC ≠ lRn := by decide
@[simp] theorem rn_lRn_ne_qC : lRn ≠ qC := by decide
@[simp] theorem rn_qC_ne_rZ : qC ≠ rZ := by decide
@[simp] theorem rn_rZ_ne_qC : rZ ≠ qC := by decide
@[simp] theorem rn_qC_ne_lFle : qC ≠ lFle := by decide
@[simp] theorem rn_lFle_ne_qC : lFle ≠ qC := by decide
@[simp] theorem rn_qC_ne_lDir : qC ≠ lDir := by decide
@[simp] theorem rn_lDir_ne_qC : lDir ≠ qC := by decide
@[simp] theorem rn_qC_ne_lKb : qC ≠ lKb := by decide
@[simp] theorem rn_lKb_ne_qC : lKb ≠ qC := by decide
@[simp] theorem rn_qC_ne_cH : qC ≠ cH := by decide
@[simp] theorem rn_cH_ne_qC : cH ≠ qC := by decide
@[simp] theorem rn_qU_ne_qH : qU ≠ qH := by decide
@[simp] theorem rn_qU_ne_qW : qU ≠ qW := by decide
@[simp] theorem rn_qU_ne_qC : qU ≠ qC := by decide
@[simp] theorem rn_qU_ne_qE : qU ≠ qE := by decide
@[simp] theorem rn_qU_ne_qZ : qU ≠ qZ := by decide
@[simp] theorem rn_qU_ne_qX : qU ≠ qX := by decide
@[simp] theorem rn_qU_ne_lFl : qU ≠ lFl := by decide
@[simp] theorem rn_lFl_ne_qU : lFl ≠ qU := by decide
@[simp] theorem rn_qU_ne_lDh : qU ≠ lDh := by decide
@[simp] theorem rn_lDh_ne_qU : lDh ≠ qU := by decide
@[simp] theorem rn_qU_ne_lDt : qU ≠ lDt := by decide
@[simp] theorem rn_lDt_ne_qU : lDt ≠ qU := by decide
@[simp] theorem rn_qU_ne_lDg : qU ≠ lDg := by decide
@[simp] theorem rn_lDg_ne_qU : lDg ≠ qU := by decide
@[simp] theorem rn_qU_ne_lDi : qU ≠ lDi := by decide
@[simp] theorem rn_lDi_ne_qU : lDi ≠ qU := by decide
@[simp] theorem rn_qU_ne_lRp : qU ≠ lRp := by decide
@[simp] theorem rn_lRp_ne_qU : lRp ≠ qU := by decide
@[simp] theorem rn_qU_ne_lRn : qU ≠ lRn := by decide
@[simp] theorem rn_lRn_ne_qU : lRn ≠ qU := by decide
@[simp] theorem rn_qU_ne_rZ : qU ≠ rZ := by decide
@[simp] theorem rn_rZ_ne_qU : rZ ≠ qU := by decide
@[simp] theorem rn_qU_ne_lFle : qU ≠ lFle := by decide
@[simp] theorem rn_lFle_ne_qU : lFle ≠ qU := by decide
@[simp] theorem rn_qU_ne_lDir : qU ≠ lDir := by decide
@[simp] theorem rn_lDir_ne_qU : lDir ≠ qU := by decide
@[simp] theorem rn_qU_ne_lKb : qU ≠ lKb := by decide
@[simp] theorem rn_lKb_ne_qU : lKb ≠ qU := by decide
@[simp] theorem rn_qU_ne_cH : qU ≠ cH := by decide
@[simp] theorem rn_cH_ne_qU : cH ≠ qU := by decide
@[simp] theorem rn_qE_ne_qH : qE ≠ qH := by decide
@[simp] theorem rn_qE_ne_qW : qE ≠ qW := by decide
@[simp] theorem rn_qE_ne_qC : qE ≠ qC := by decide
@[simp] theorem rn_qE_ne_qU : qE ≠ qU := by decide
@[simp] theorem rn_qE_ne_qZ : qE ≠ qZ := by decide
@[simp] theorem rn_qE_ne_qX : qE ≠ qX := by decide
@[simp] theorem rn_qE_ne_lFl : qE ≠ lFl := by decide
@[simp] theorem rn_lFl_ne_qE : lFl ≠ qE := by decide
@[simp] theorem rn_qE_ne_lDh : qE ≠ lDh := by decide
@[simp] theorem rn_lDh_ne_qE : lDh ≠ qE := by decide
@[simp] theorem rn_qE_ne_lDt : qE ≠ lDt := by decide
@[simp] theorem rn_lDt_ne_qE : lDt ≠ qE := by decide
@[simp] theorem rn_qE_ne_lDg : qE ≠ lDg := by decide
@[simp] theorem rn_lDg_ne_qE : lDg ≠ qE := by decide
@[simp] theorem rn_qE_ne_lDi : qE ≠ lDi := by decide
@[simp] theorem rn_lDi_ne_qE : lDi ≠ qE := by decide
@[simp] theorem rn_qE_ne_lRp : qE ≠ lRp := by decide
@[simp] theorem rn_lRp_ne_qE : lRp ≠ qE := by decide
@[simp] theorem rn_qE_ne_lRn : qE ≠ lRn := by decide
@[simp] theorem rn_lRn_ne_qE : lRn ≠ qE := by decide
@[simp] theorem rn_qE_ne_rZ : qE ≠ rZ := by decide
@[simp] theorem rn_rZ_ne_qE : rZ ≠ qE := by decide
@[simp] theorem rn_qE_ne_lFle : qE ≠ lFle := by decide
@[simp] theorem rn_lFle_ne_qE : lFle ≠ qE := by decide
@[simp] theorem rn_qE_ne_lDir : qE ≠ lDir := by decide
@[simp] theorem rn_lDir_ne_qE : lDir ≠ qE := by decide
@[simp] theorem rn_qE_ne_lKb : qE ≠ lKb := by decide
@[simp] theorem rn_lKb_ne_qE : lKb ≠ qE := by decide
@[simp] theorem rn_qE_ne_cH : qE ≠ cH := by decide
@[simp] theorem rn_cH_ne_qE : cH ≠ qE := by decide
@[simp] theorem rn_qZ_ne_qH : qZ ≠ qH := by decide
@[simp] theorem rn_qZ_ne_qW : qZ ≠ qW := by decide
@[simp] theorem rn_qZ_ne_qC : qZ ≠ qC := by decide
@[simp] theorem rn_qZ_ne_qU : qZ ≠ qU := by decide
@[simp] theorem rn_qZ_ne_qE : qZ ≠ qE := by decide
@[simp] theorem rn_qZ_ne_qX : qZ ≠ qX := by decide
@[simp] theorem rn_qZ_ne_lFl : qZ ≠ lFl := by decide
@[simp] theorem rn_lFl_ne_qZ : lFl ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lDh : qZ ≠ lDh := by decide
@[simp] theorem rn_lDh_ne_qZ : lDh ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lDt : qZ ≠ lDt := by decide
@[simp] theorem rn_lDt_ne_qZ : lDt ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lDg : qZ ≠ lDg := by decide
@[simp] theorem rn_lDg_ne_qZ : lDg ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lDi : qZ ≠ lDi := by decide
@[simp] theorem rn_lDi_ne_qZ : lDi ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lRp : qZ ≠ lRp := by decide
@[simp] theorem rn_lRp_ne_qZ : lRp ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lRn : qZ ≠ lRn := by decide
@[simp] theorem rn_lRn_ne_qZ : lRn ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_rZ : qZ ≠ rZ := by decide
@[simp] theorem rn_rZ_ne_qZ : rZ ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lFle : qZ ≠ lFle := by decide
@[simp] theorem rn_lFle_ne_qZ : lFle ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lDir : qZ ≠ lDir := by decide
@[simp] theorem rn_lDir_ne_qZ : lDir ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_lKb : qZ ≠ lKb := by decide
@[simp] theorem rn_lKb_ne_qZ : lKb ≠ qZ := by decide
@[simp] theorem rn_qZ_ne_cH : qZ ≠ cH := by decide
@[simp] theorem rn_cH_ne_qZ : cH ≠ qZ := by decide
@[simp] theorem rn_qX_ne_qH : qX ≠ qH := by decide
@[simp] theorem rn_qX_ne_qW : qX ≠ qW := by decide
@[simp] theorem rn_qX_ne_qC : qX ≠ qC := by decide
@[simp] theorem rn_qX_ne_qU : qX ≠ qU := by decide
@[simp] theorem rn_qX_ne_qE : qX ≠ qE := by decide
@[simp] theorem rn_qX_ne_qZ : qX ≠ qZ := by decide
@[simp] theorem rn_qX_ne_lFl : qX ≠ lFl := by decide
@[simp] theorem rn_lFl_ne_qX : lFl ≠ qX := by decide
@[simp] theorem rn_qX_ne_lDh : qX ≠ lDh := by decide
@[simp] theorem rn_lDh_ne_qX : lDh ≠ qX := by decide
@[simp] theorem rn_qX_ne_lDt : qX ≠ lDt := by decide
@[simp] theorem rn_lDt_ne_qX : lDt ≠ qX := by decide
@[simp] theorem rn_qX_ne_lDg : qX ≠ lDg := by decide
@[simp] theorem rn_lDg_ne_qX : lDg ≠ qX := by decide
@[simp] theorem rn_qX_ne_lDi : qX ≠ lDi := by decide
@[simp] theorem rn_lDi_ne_qX : lDi ≠ qX := by decide
@[simp] theorem rn_qX_ne_lRp : qX ≠ lRp := by decide
@[simp] theorem rn_lRp_ne_qX : lRp ≠ qX := by decide
@[simp] theorem rn_qX_ne_lRn : qX ≠ lRn := by decide
@[simp] theorem rn_lRn_ne_qX : lRn ≠ qX := by decide
@[simp] theorem rn_qX_ne_rZ : qX ≠ rZ := by decide
@[simp] theorem rn_rZ_ne_qX : rZ ≠ qX := by decide
@[simp] theorem rn_qX_ne_lFle : qX ≠ lFle := by decide
@[simp] theorem rn_lFle_ne_qX : lFle ≠ qX := by decide
@[simp] theorem rn_qX_ne_lDir : qX ≠ lDir := by decide
@[simp] theorem rn_lDir_ne_qX : lDir ≠ qX := by decide
@[simp] theorem rn_qX_ne_lKb : qX ≠ lKb := by decide
@[simp] theorem rn_lKb_ne_qX : lKb ≠ qX := by decide
@[simp] theorem rn_qX_ne_cH : qX ≠ cH := by decide
@[simp] theorem rn_cH_ne_qX : cH ≠ qX := by decide

def rnLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, qW, qC, qU, qE, qZ, qX, rZ]

def rnCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 8))
    (.seq (.assign .local qW (.load .one (vv lRp)))
      (.ite (.cmp .equal (vv qW) (.const 0))
        (.seq (.call (some (some (.local, qX), none)) fLitH [vv qH]) (.return (vv qX)))
        (.return (.const 0))))
  (.ite (.cmp .equal (vv lDg) (.const 3))
    (.seq (.assign .local qC (.load .one (vv lRp)))
    (.seq (.assign .local qU (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local qE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
    (.seq (.assign .local qZ (.load .one (.const (ecell C (C.PO + PIN_NAT_ZERO)))))
    (.ite (.cmp .equal (vv qC) (vv qZ))
      (.ite (.cmp .equal (vv qU) (vv qE)) (zeroBlk C) (.return (.const 0)))
      (.return (.const 0)))))))
    (.return (.const 0))))))

def rnBody (C : Ctx) : ProgHOL 64 := prologue rnLocals (rnCore C)

section
variable {σ : Type}

/-- The post: the state unchanged, the heap grown, and `0` or a block for the number. -/
def PostRN (C : Ctx) (s : AState) (o : Option Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s st ∧
    match o with
    | none => w = 0
    | some n => ∃ ob, w = cellA C ob ∧ BlkAt H' ob (limbs n)

theorem postRN_locals (C : Ctx) (s : AState) : ∀ (a : Option Nat) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostRN C s a w s' st → PostRN C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', h2, h3, h4⟩ => ⟨h1, H', h2, sr_of_eq h3 rfl rfl rfl rfl, h4⟩

theorem rn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rnLocals → (ctxEnv C ++ [qH].zip vals).get x = none :=
  Knot.params_none C rnLocals [qH] vals (by decide) (by decide)

theorem specR_dropM {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (h : SpecR (Inv C s Γ [] D) c s m R) :
    SpecR (Inv C s Γ M D) c s m R :=
  fun t ht => h t ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩

theorem specR_pureMap {α β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {a : α} {b : β}
    {R : α → BitVec 64 → AState → PState σ → Prop} {R' : β → BitVec 64 → AState → PState σ → Prop}
    (h : SpecR P c s (pure a) R) (hR : ∀ w s' st, R a w s' st → R' b w s' st) : SpecR P c s (pure b) R' := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a', s', hm, hq⟩
  · exact Or.inl hs
  · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact Or.inr ⟨w, hr, b, _, rfl, hR _ _ _ hq⟩

theorem tagN_lit {v : ENodeView} (h : v.tagN = 8) : ∃ l, v = .lit l := by
  cases v <;> simp [ENodeView.tagN] at h ⊢

theorem rn_spec (C : Ctx) (hok : CtxOK C) (hc : BigCodes C) (s : AState) (h : EIdx) :
    SpecR (σ := σ) (Pre C s ([qH].zip [Enc.idxW h])) (rnBody C) s (rawNatLit? h) (PostRN C s) := by
  refine specR_prologue (postRN_locals C s) (rn_none C _) ?_
  unfold rnCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv qH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine ILP.specR_viewIv h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  by_cases h8 : v.tagN = 8
  · refine specR_ifI _ 1 (by simp [sev, h8, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    obtain ⟨l, rfl⟩ := tagN_lit h8
    cases l with
    | natVal n =>
      refine specR_loadI' qW (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (limbs n) []) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine specR_dropM ?_
      show SpecR _ _ s (pure (some n)) _
      refine specR_callPH (k := fun r => pure (some r)) qX fLitH [cH] [vv qH] (litBody C) [Enc.idxW h] n
        (by decide) rfl (by decide) hc.lit ⟨by simp +decide [sev, Env.get, ctxEnv], trivial⟩ (lit_spec C hok s h n hv)
        (fun H o hp hb => ?_)
      refine specR_returnI _ (cellA C o) (by simp) (fun t ht => ?_)
      exact ⟨rfl, H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, o, rfl, hb⟩
    | strVal str =>
      refine specR_loadI' qW (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 _ []) ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      show SpecR _ _ s (pure none) _
      refine specR_returnI _ 0 rfl (fun t ht => ?_)
      exact ⟨rfl, C.H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl, rfl⟩
  have h8w : BitVec.ofNat 64 v.tagN ≠ 8#64 := by
    have : v.tagN < 16 := by cases v <;> simp [ENodeView.tagN]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h8w]) (fun h => absurd rfl h)
    (fun _ => ?_)
  by_cases h3 : v.tagN = 3
  · refine specR_ifI _ 1 (by simp [sev, h3, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
    refine specR_loadI' qC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
    refine specR_loadI' qU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
    refine specR_dropM ?_
    show SpecR _ _ s (emptyLevels >>= fun e => pinNatZero >>= fun nz =>
      pure (if c == nz && us == e then some 0 else none)) _
    refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
      (pin_emptyLevels_cell hok) qE (by decide) ?_
    refine specR_pinAtI hok PIN_NAT_ZERO (by decide) qZ (by decide) ?_
    by_cases hcz : c = C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide)
    · refine specR_ifI _ 1 (by simp [sev, hcz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      by_cases hue : us = C.pins.emptyLevels
      · refine specR_ifI _ 1 (by simp [sev, hue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        have e1 : (c == C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide) && us == C.pins.emptyLevels) =
            true := by simp [hcz, hue]
        rw [e1]
        exact specR_pureMap (zeroBlk_spec hok (by decide))
          (fun w s' st ⟨H', o, hp, hw, hb, hs, hsr⟩ => ⟨hs, H', hp, hs ▸ hsr, o, hw, hb⟩)
      · have hne : Enc.idxW us ≠ Enc.idxW C.pins.emptyLevels := fun e => hue (Enc.idxW_inj e)
        refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h)
          (fun _ => ?_)
        have e1 : (c == C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide) && us == C.pins.emptyLevels) =
            false := by simp [hue]
        rw [e1]
        refine specR_returnI _ 0 rfl (fun t ht => ?_)
        exact ⟨rfl, C.H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl, rfl⟩
    · have hne : Enc.idxW c ≠ Enc.idxW (C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide)) :=
        fun e => hcz (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h)
        (fun _ => ?_)
      have e1 : (c == C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide) && us == C.pins.emptyLevels) =
          false := by simp [hcz]
      rw [e1]
      refine specR_returnI _ 0 rfl (fun t ht => ?_)
      exact ⟨rfl, C.H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl, rfl⟩
  have h3w : BitVec.ofNat 64 v.tagN ≠ 3#64 := by
    have : v.tagN < 16 := by cases v <;> simp [ENodeView.tagN]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h3w]) (fun h => absurd rfl h)
    (fun _ => ?_)
  cases v <;> (try simp [ENodeView.tagN] at h8 h3) <;>
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, C.H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl, rfl⟩)

end

end ConPanqueque.T.Big
