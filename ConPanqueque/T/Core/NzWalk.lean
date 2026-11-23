import ConPanqueque.T.Core.NeverZero
import ConPanqueque.T.LvlView
import ConRon.Bridge.Checker.Canon
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `nz` over a level handle

A recursive function on the level DAG: `succ` is never zero, `zero` and `param` may be, `max` is never zero if
either side is, `imax` if its right side is. Read-only.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def nzU := ofString "nzu"
def nzA := ofString "nza"
def nzB := ofString "nzb"
def nzX := ofString "nzx"
def nzY := ofString "nzy"
def fNz0 := ofString "neverZero"

@[simp] theorem nz_nzU_ne_nzA : nzU ≠ nzA := by decide
@[simp] theorem nz_nzU_ne_nzB : nzU ≠ nzB := by decide
@[simp] theorem nz_nzU_ne_nzX : nzU ≠ nzX := by decide
@[simp] theorem nz_nzU_ne_nzY : nzU ≠ nzY := by decide
@[simp] theorem nz_nzU_ne_lFl : nzU ≠ lFl := by decide
@[simp] theorem nz_lFl_ne_nzU : lFl ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lDh : nzU ≠ lDh := by decide
@[simp] theorem nz_lDh_ne_nzU : lDh ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lDt : nzU ≠ lDt := by decide
@[simp] theorem nz_lDt_ne_nzU : lDt ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lDg : nzU ≠ lDg := by decide
@[simp] theorem nz_lDg_ne_nzU : lDg ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lDi : nzU ≠ lDi := by decide
@[simp] theorem nz_lDi_ne_nzU : lDi ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lRp : nzU ≠ lRp := by decide
@[simp] theorem nz_lRp_ne_nzU : lRp ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lRn : nzU ≠ lRn := by decide
@[simp] theorem nz_lRn_ne_nzU : lRn ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lFll : nzU ≠ lFll := by decide
@[simp] theorem nz_lFll_ne_nzU : lFll ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lDir : nzU ≠ lDir := by decide
@[simp] theorem nz_lDir_ne_nzU : lDir ≠ nzU := by decide
@[simp] theorem nz_nzU_ne_lKb : nzU ≠ lKb := by decide
@[simp] theorem nz_lKb_ne_nzU : lKb ≠ nzU := by decide
@[simp] theorem nz_nzA_ne_nzU : nzA ≠ nzU := by decide
@[simp] theorem nz_nzA_ne_nzB : nzA ≠ nzB := by decide
@[simp] theorem nz_nzA_ne_nzX : nzA ≠ nzX := by decide
@[simp] theorem nz_nzA_ne_nzY : nzA ≠ nzY := by decide
@[simp] theorem nz_nzA_ne_lFl : nzA ≠ lFl := by decide
@[simp] theorem nz_lFl_ne_nzA : lFl ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lDh : nzA ≠ lDh := by decide
@[simp] theorem nz_lDh_ne_nzA : lDh ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lDt : nzA ≠ lDt := by decide
@[simp] theorem nz_lDt_ne_nzA : lDt ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lDg : nzA ≠ lDg := by decide
@[simp] theorem nz_lDg_ne_nzA : lDg ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lDi : nzA ≠ lDi := by decide
@[simp] theorem nz_lDi_ne_nzA : lDi ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lRp : nzA ≠ lRp := by decide
@[simp] theorem nz_lRp_ne_nzA : lRp ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lRn : nzA ≠ lRn := by decide
@[simp] theorem nz_lRn_ne_nzA : lRn ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lFll : nzA ≠ lFll := by decide
@[simp] theorem nz_lFll_ne_nzA : lFll ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lDir : nzA ≠ lDir := by decide
@[simp] theorem nz_lDir_ne_nzA : lDir ≠ nzA := by decide
@[simp] theorem nz_nzA_ne_lKb : nzA ≠ lKb := by decide
@[simp] theorem nz_lKb_ne_nzA : lKb ≠ nzA := by decide
@[simp] theorem nz_nzB_ne_nzU : nzB ≠ nzU := by decide
@[simp] theorem nz_nzB_ne_nzA : nzB ≠ nzA := by decide
@[simp] theorem nz_nzB_ne_nzX : nzB ≠ nzX := by decide
@[simp] theorem nz_nzB_ne_nzY : nzB ≠ nzY := by decide
@[simp] theorem nz_nzB_ne_lFl : nzB ≠ lFl := by decide
@[simp] theorem nz_lFl_ne_nzB : lFl ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lDh : nzB ≠ lDh := by decide
@[simp] theorem nz_lDh_ne_nzB : lDh ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lDt : nzB ≠ lDt := by decide
@[simp] theorem nz_lDt_ne_nzB : lDt ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lDg : nzB ≠ lDg := by decide
@[simp] theorem nz_lDg_ne_nzB : lDg ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lDi : nzB ≠ lDi := by decide
@[simp] theorem nz_lDi_ne_nzB : lDi ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lRp : nzB ≠ lRp := by decide
@[simp] theorem nz_lRp_ne_nzB : lRp ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lRn : nzB ≠ lRn := by decide
@[simp] theorem nz_lRn_ne_nzB : lRn ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lFll : nzB ≠ lFll := by decide
@[simp] theorem nz_lFll_ne_nzB : lFll ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lDir : nzB ≠ lDir := by decide
@[simp] theorem nz_lDir_ne_nzB : lDir ≠ nzB := by decide
@[simp] theorem nz_nzB_ne_lKb : nzB ≠ lKb := by decide
@[simp] theorem nz_lKb_ne_nzB : lKb ≠ nzB := by decide
@[simp] theorem nz_nzX_ne_nzU : nzX ≠ nzU := by decide
@[simp] theorem nz_nzX_ne_nzA : nzX ≠ nzA := by decide
@[simp] theorem nz_nzX_ne_nzB : nzX ≠ nzB := by decide
@[simp] theorem nz_nzX_ne_nzY : nzX ≠ nzY := by decide
@[simp] theorem nz_nzX_ne_lFl : nzX ≠ lFl := by decide
@[simp] theorem nz_lFl_ne_nzX : lFl ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lDh : nzX ≠ lDh := by decide
@[simp] theorem nz_lDh_ne_nzX : lDh ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lDt : nzX ≠ lDt := by decide
@[simp] theorem nz_lDt_ne_nzX : lDt ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lDg : nzX ≠ lDg := by decide
@[simp] theorem nz_lDg_ne_nzX : lDg ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lDi : nzX ≠ lDi := by decide
@[simp] theorem nz_lDi_ne_nzX : lDi ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lRp : nzX ≠ lRp := by decide
@[simp] theorem nz_lRp_ne_nzX : lRp ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lRn : nzX ≠ lRn := by decide
@[simp] theorem nz_lRn_ne_nzX : lRn ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lFll : nzX ≠ lFll := by decide
@[simp] theorem nz_lFll_ne_nzX : lFll ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lDir : nzX ≠ lDir := by decide
@[simp] theorem nz_lDir_ne_nzX : lDir ≠ nzX := by decide
@[simp] theorem nz_nzX_ne_lKb : nzX ≠ lKb := by decide
@[simp] theorem nz_lKb_ne_nzX : lKb ≠ nzX := by decide
@[simp] theorem nz_nzY_ne_nzU : nzY ≠ nzU := by decide
@[simp] theorem nz_nzY_ne_nzA : nzY ≠ nzA := by decide
@[simp] theorem nz_nzY_ne_nzB : nzY ≠ nzB := by decide
@[simp] theorem nz_nzY_ne_nzX : nzY ≠ nzX := by decide
@[simp] theorem nz_nzY_ne_lFl : nzY ≠ lFl := by decide
@[simp] theorem nz_lFl_ne_nzY : lFl ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lDh : nzY ≠ lDh := by decide
@[simp] theorem nz_lDh_ne_nzY : lDh ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lDt : nzY ≠ lDt := by decide
@[simp] theorem nz_lDt_ne_nzY : lDt ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lDg : nzY ≠ lDg := by decide
@[simp] theorem nz_lDg_ne_nzY : lDg ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lDi : nzY ≠ lDi := by decide
@[simp] theorem nz_lDi_ne_nzY : lDi ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lRp : nzY ≠ lRp := by decide
@[simp] theorem nz_lRp_ne_nzY : lRp ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lRn : nzY ≠ lRn := by decide
@[simp] theorem nz_lRn_ne_nzY : lRn ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lFll : nzY ≠ lFll := by decide
@[simp] theorem nz_lFll_ne_nzY : lFll ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lDir : nzY ≠ lDir := by decide
@[simp] theorem nz_lDir_ne_nzY : lDir ≠ nzY := by decide
@[simp] theorem nz_nzY_ne_lKb : nzY ≠ lKb := by decide
@[simp] theorem nz_lKb_ne_nzY : lKb ≠ nzY := by decide

def nzLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, nzA, nzB, nzX, nzY]

def nzBody : ProgHOL 64 := prologue nzLocals
  (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv nzU)) (.seq lViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 0))
  (.ite (.cmp .equal (vv lDg) (.const 1)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 4)) (.return (.const 0))
  (.seq (.assign .local nzA (.load .one (vv lRp)))
  (.seq (.assign .local nzB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, nzY), none)) fNz0 [vv nzB])
  (.ite (.cmp .equal (vv lDg) (.const 3)) (.return (vv nzY))
  (.ite (vv nzY) (.return (.const 1))
  (.seq (.call (some (some (.local, nzX), none)) fNz0 [vv nzA]) (.return (vv nzX))))))))))))))

section
variable {σ : Type}

theorem nz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nzLocals → (ctxEnv C ++ [nzU].zip vals).get x = none :=
  Knot.params_none C nzLocals [nzU] vals (by decide) (by decide)

/-- A read-only Boolean answer at the given state. -/
def PostBS (C : Ctx) (s : AState) (b : Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = boolW b ∧ SR C s st

theorem postBS_locals (C : Ctx) (s : AState) : ∀ (a : Bool) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostBS C s a w s' st → PostBS C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem nz0_spec (C : Ctx) (hcf : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)) (s : AState)
    (hwf : LStoreWF s.store.ls) :
    ∀ (l : ConLeche.Level) (u : LIdx), denoteL s.store.ls u = some l →
      SpecR (σ := σ) (Pre C s [(nzU, Enc.idxW u)]) nzBody s (pure (nz l) : AM Bool) (PostBS C s) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u hd
    refine specR_prologue (postBS_locals C s) (nz_none C [Enc.idxW u]) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv nzU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_lviewPI u (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- succ
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- max
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 2
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' nzA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' nzB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure nzY fNz0 [nzU] [vv nzB] nzBody [Enc.idxW _] (nz _) (by decide) rfl (by decide) hcf
        ⟨by simp, trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nzU] _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      cases hq : nz q
      · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_callPure nzX fNz0 [nzU] [vv nzA] nzBody [Enc.idxW _] (nz _) (by decide) rfl (by decide) hcf
          ⟨by simp, trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
          (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nzU] _ rfl hlk) (ihp _ hda))
          (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
        subst eH2 hw
        exact specR_returnI _ (boolW (nz p)) (by simp)
          (fun t ht => ⟨rfl, by simp [nz, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
          (fun t ht => ⟨rfl, by simp [nz, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- imax
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 3
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' nzA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' nzB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure nzY fNz0 [nzU] [vv nzB] nzBody [Enc.idxW _] (nz _) (by decide) rfl (by decide) hcf
        ⟨by simp, trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nzU] _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW (nz q)) (by simp)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- param
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 4
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)

end

end ConPanqueque.T.WC
