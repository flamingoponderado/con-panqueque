import ConPanqueque.T.Core.NzWalk
import ConPanqueque.T.Core.LvlZero
import ConPanqueque.T.LvlView
import ConRon.Bridge.Checker.Canon
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `ze` over a level handle: is the zero-ness datum's parameter list empty

`ze l ↔ zps l = []`: `zero` and `succ` name no parameter, `param` does, `max` both sides, `imax` its right side.
A recursive function on the level DAG, read-only (as `nz`).
-/

namespace ConPanqueque.T.WC

/-- Is the zero-ness datum's parameter list empty (`zps l = []`). -/
def ze : ConLeche.Level → Bool
  | .zero => true
  | .succ _ => true
  | .param _ => false
  | .max a b => ze a && ze b
  | .imax _ b => ze b

theorem ze_iff : ∀ l : ConLeche.Level, ze l = true ↔ zps l = []
  | .zero => by simp [ze, zps]
  | .succ _ => by simp [ze, zps]
  | .param _ => by simp [ze, zps]
  | .max a b => by simp [ze, zps, ze_iff a, ze_iff b]
  | .imax _ b => by simp [ze, zps, ze_iff b]

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def zeU := ofString "zeu"
def zeA := ofString "zea"
def zeB := ofString "zeb"
def zeX := ofString "zex"
def zeY := ofString "zey"
def fZe0 := ofString "zpsEmpty"

@[simp] theorem ze_nzU_ne_nzA : zeU ≠ zeA := by decide
@[simp] theorem ze_nzU_ne_nzB : zeU ≠ zeB := by decide
@[simp] theorem ze_nzU_ne_nzX : zeU ≠ zeX := by decide
@[simp] theorem ze_nzU_ne_nzY : zeU ≠ zeY := by decide
@[simp] theorem ze_nzU_ne_lFl : zeU ≠ lFl := by decide
@[simp] theorem ze_lFl_ne_nzU : lFl ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lDh : zeU ≠ lDh := by decide
@[simp] theorem ze_lDh_ne_nzU : lDh ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lDt : zeU ≠ lDt := by decide
@[simp] theorem ze_lDt_ne_nzU : lDt ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lDg : zeU ≠ lDg := by decide
@[simp] theorem ze_lDg_ne_nzU : lDg ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lDi : zeU ≠ lDi := by decide
@[simp] theorem ze_lDi_ne_nzU : lDi ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lRp : zeU ≠ lRp := by decide
@[simp] theorem ze_lRp_ne_nzU : lRp ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lRn : zeU ≠ lRn := by decide
@[simp] theorem ze_lRn_ne_nzU : lRn ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lFll : zeU ≠ lFll := by decide
@[simp] theorem ze_lFll_ne_nzU : lFll ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lDir : zeU ≠ lDir := by decide
@[simp] theorem ze_lDir_ne_nzU : lDir ≠ zeU := by decide
@[simp] theorem ze_nzU_ne_lKb : zeU ≠ lKb := by decide
@[simp] theorem ze_lKb_ne_nzU : lKb ≠ zeU := by decide
@[simp] theorem ze_nzA_ne_nzU : zeA ≠ zeU := by decide
@[simp] theorem ze_nzA_ne_nzB : zeA ≠ zeB := by decide
@[simp] theorem ze_nzA_ne_nzX : zeA ≠ zeX := by decide
@[simp] theorem ze_nzA_ne_nzY : zeA ≠ zeY := by decide
@[simp] theorem ze_nzA_ne_lFl : zeA ≠ lFl := by decide
@[simp] theorem ze_lFl_ne_nzA : lFl ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lDh : zeA ≠ lDh := by decide
@[simp] theorem ze_lDh_ne_nzA : lDh ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lDt : zeA ≠ lDt := by decide
@[simp] theorem ze_lDt_ne_nzA : lDt ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lDg : zeA ≠ lDg := by decide
@[simp] theorem ze_lDg_ne_nzA : lDg ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lDi : zeA ≠ lDi := by decide
@[simp] theorem ze_lDi_ne_nzA : lDi ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lRp : zeA ≠ lRp := by decide
@[simp] theorem ze_lRp_ne_nzA : lRp ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lRn : zeA ≠ lRn := by decide
@[simp] theorem ze_lRn_ne_nzA : lRn ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lFll : zeA ≠ lFll := by decide
@[simp] theorem ze_lFll_ne_nzA : lFll ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lDir : zeA ≠ lDir := by decide
@[simp] theorem ze_lDir_ne_nzA : lDir ≠ zeA := by decide
@[simp] theorem ze_nzA_ne_lKb : zeA ≠ lKb := by decide
@[simp] theorem ze_lKb_ne_nzA : lKb ≠ zeA := by decide
@[simp] theorem ze_nzB_ne_nzU : zeB ≠ zeU := by decide
@[simp] theorem ze_nzB_ne_nzA : zeB ≠ zeA := by decide
@[simp] theorem ze_nzB_ne_nzX : zeB ≠ zeX := by decide
@[simp] theorem ze_nzB_ne_nzY : zeB ≠ zeY := by decide
@[simp] theorem ze_nzB_ne_lFl : zeB ≠ lFl := by decide
@[simp] theorem ze_lFl_ne_nzB : lFl ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lDh : zeB ≠ lDh := by decide
@[simp] theorem ze_lDh_ne_nzB : lDh ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lDt : zeB ≠ lDt := by decide
@[simp] theorem ze_lDt_ne_nzB : lDt ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lDg : zeB ≠ lDg := by decide
@[simp] theorem ze_lDg_ne_nzB : lDg ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lDi : zeB ≠ lDi := by decide
@[simp] theorem ze_lDi_ne_nzB : lDi ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lRp : zeB ≠ lRp := by decide
@[simp] theorem ze_lRp_ne_nzB : lRp ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lRn : zeB ≠ lRn := by decide
@[simp] theorem ze_lRn_ne_nzB : lRn ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lFll : zeB ≠ lFll := by decide
@[simp] theorem ze_lFll_ne_nzB : lFll ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lDir : zeB ≠ lDir := by decide
@[simp] theorem ze_lDir_ne_nzB : lDir ≠ zeB := by decide
@[simp] theorem ze_nzB_ne_lKb : zeB ≠ lKb := by decide
@[simp] theorem ze_lKb_ne_nzB : lKb ≠ zeB := by decide
@[simp] theorem ze_nzX_ne_nzU : zeX ≠ zeU := by decide
@[simp] theorem ze_nzX_ne_nzA : zeX ≠ zeA := by decide
@[simp] theorem ze_nzX_ne_nzB : zeX ≠ zeB := by decide
@[simp] theorem ze_nzX_ne_nzY : zeX ≠ zeY := by decide
@[simp] theorem ze_nzX_ne_lFl : zeX ≠ lFl := by decide
@[simp] theorem ze_lFl_ne_nzX : lFl ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lDh : zeX ≠ lDh := by decide
@[simp] theorem ze_lDh_ne_nzX : lDh ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lDt : zeX ≠ lDt := by decide
@[simp] theorem ze_lDt_ne_nzX : lDt ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lDg : zeX ≠ lDg := by decide
@[simp] theorem ze_lDg_ne_nzX : lDg ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lDi : zeX ≠ lDi := by decide
@[simp] theorem ze_lDi_ne_nzX : lDi ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lRp : zeX ≠ lRp := by decide
@[simp] theorem ze_lRp_ne_nzX : lRp ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lRn : zeX ≠ lRn := by decide
@[simp] theorem ze_lRn_ne_nzX : lRn ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lFll : zeX ≠ lFll := by decide
@[simp] theorem ze_lFll_ne_nzX : lFll ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lDir : zeX ≠ lDir := by decide
@[simp] theorem ze_lDir_ne_nzX : lDir ≠ zeX := by decide
@[simp] theorem ze_nzX_ne_lKb : zeX ≠ lKb := by decide
@[simp] theorem ze_lKb_ne_nzX : lKb ≠ zeX := by decide
@[simp] theorem ze_nzY_ne_nzU : zeY ≠ zeU := by decide
@[simp] theorem ze_nzY_ne_nzA : zeY ≠ zeA := by decide
@[simp] theorem ze_nzY_ne_nzB : zeY ≠ zeB := by decide
@[simp] theorem ze_nzY_ne_nzX : zeY ≠ zeX := by decide
@[simp] theorem ze_nzY_ne_lFl : zeY ≠ lFl := by decide
@[simp] theorem ze_lFl_ne_nzY : lFl ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lDh : zeY ≠ lDh := by decide
@[simp] theorem ze_lDh_ne_nzY : lDh ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lDt : zeY ≠ lDt := by decide
@[simp] theorem ze_lDt_ne_nzY : lDt ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lDg : zeY ≠ lDg := by decide
@[simp] theorem ze_lDg_ne_nzY : lDg ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lDi : zeY ≠ lDi := by decide
@[simp] theorem ze_lDi_ne_nzY : lDi ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lRp : zeY ≠ lRp := by decide
@[simp] theorem ze_lRp_ne_nzY : lRp ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lRn : zeY ≠ lRn := by decide
@[simp] theorem ze_lRn_ne_nzY : lRn ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lFll : zeY ≠ lFll := by decide
@[simp] theorem ze_lFll_ne_nzY : lFll ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lDir : zeY ≠ lDir := by decide
@[simp] theorem ze_lDir_ne_nzY : lDir ≠ zeY := by decide
@[simp] theorem ze_nzY_ne_lKb : zeY ≠ lKb := by decide
@[simp] theorem ze_lKb_ne_nzY : lKb ≠ zeY := by decide

def zeLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zeA, zeB, zeX, zeY]

def zeBody : ProgHOL 64 := prologue zeLocals
  (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv zeU)) (.seq lViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 1)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 4)) (.return (.const 0))
  (.seq (.assign .local zeA (.load .one (vv lRp)))
  (.seq (.assign .local zeB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, zeY), none)) fZe0 [vv zeB])
  (.ite (.cmp .equal (vv lDg) (.const 3)) (.return (vv zeY))
  (.ite (vv zeY) (.seq (.call (some (some (.local, zeX), none)) fZe0 [vv zeA]) (.return (vv zeX)))
  (.return (.const 0)))))))))))))

section
variable {σ : Type}

theorem ze_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zeLocals → (ctxEnv C ++ [zeU].zip vals).get x = none :=
  Knot.params_none C zeLocals [zeU] vals (by decide) (by decide)

theorem ze0_spec (C : Ctx) (hcf : C.code.lookup fZe0 = some ([(zeU, ShapeHOL.one)], zeBody, .one)) (s : AState)
    (hwf : LStoreWF s.store.ls) :
    ∀ (l : ConLeche.Level) (u : LIdx), denoteL s.store.ls u = some l →
      SpecR (σ := σ) (Pre C s [(zeU, Enc.idxW u)]) zeBody s (pure (ze l) : AM Bool) (PostBS C s) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u hd
    refine specR_prologue (postBS_locals C s) (ze_none C [Enc.idxW u]) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv zeU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_lviewPI u (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
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
      refine specR_loadI' zeA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zeB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zeY fZe0 [zeU] [vv zeB] zeBody [Enc.idxW _] (ze _) (by decide) rfl (by decide) hcf
        ⟨by simp, trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [zeU] _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      cases hq : ze q
      · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
          (fun t ht => ⟨rfl, by simp [ze, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_callPure zeX fZe0 [zeU] [vv zeA] zeBody [Enc.idxW _] (ze _) (by decide) rfl (by decide) hcf
          ⟨by simp, trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
          (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [zeU] _ rfl hlk) (ihp _ hda))
          (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
        subst eH2 hw
        exact specR_returnI _ (boolW (ze p)) (by simp)
          (fun t ht => ⟨rfl, by simp [ze, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_loadI' zeA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zeB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zeY fZe0 [zeU] [vv zeB] zeBody [Enc.idxW _] (ze _) (by decide) rfl (by decide) hcf
        ⟨by simp, trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [zeU] _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW (ze q)) (by simp)
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
