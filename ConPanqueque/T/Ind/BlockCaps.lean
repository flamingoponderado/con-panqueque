import ConPanqueque.T.Ind.BlockIsRec
import ConPanqueque.T.Core.FamilyNZ

/-!
# A former's capabilities (`blockCapsAt`)

`memberNeverZero`: the member's declared sort (`formerResSort`), its zero-ness datum never satisfiable
(`neverZero` on the level). The capability record itself is written into the environment heap with the former's
record (`blockFormers`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.WC

def mvD := ofString "mv_d"
def mvT := ofString "mv_t"
def mvR := ofString "mv_r"
def mvX := ofString "mv_x"
def fMemberNZ := ofString "memberNeverZero"

def mvParams : List MlS := [mvD]
def mvLocals : List MlS := [mvT, mvR, mvX]

/-- `mvD` points at the member's declared constant (a value-heap `CVE`). -/
def mvBody : ProgHOL 64 := prologue mvLocals
  (.seq (.assign .local mvT (.load .one (.op .add [vv mvD, .const 16])))
  (.seq (.call (some (some (.local, mvR), none)) fFs [vv mvT])
  (.ite (.cmp .equal (vv mvR) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, mvX), none)) fNz0 [.op .sub [vv mvR, .const 1]])
    (.return (vv mvX))))))

structure MVCodes (C : Ctx) : Prop where
  fs : C.code.lookup fFs = some ([(fsT, ShapeHOL.one)], fsBody, .one)
  pir : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one)
  nz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)

section
variable {σ : Type}

theorem mv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mvLocals → (ctxEnv C ++ mvParams.zip vals).get x = none :=
  Knot.params_none C mvLocals mvParams vals (by decide) (by decide)

/-- **A declared former's sort is never zero** (`memberNeverZero` at a member). -/
theorem mv_spec (C : Ctx) (hc : MVCodes C) (cv : IConstantVal) (od : Nat) (H : List (BitVec 64))
    (hp : C.H <+: H) (hcv : CVRep C H od cv) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (mvParams.zip [cellA C od])) mvBody s
      (formerZ cv >>= fun z => pure z.isNever) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (mv_none _ _) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsd : ∀ u, formerResSort cv.type s = .ok (some u, s) → ∃ l, denoteL s.store.ls u = some l :=
    fun u hrun => by
      obtain ⟨w0, hw0⟩ := Comp.formerResSort_sort _ _ _ _ hrun
      exact sr_sortDen ht0.sr w0 u hw0
  have hwf := sr_lwf ht0.sr
  have hrl := ht0.sr.cok.rl
  refine UD.specR_heapLoadI' (C := ctxH C H) mvT _ (od + 2) _ hcv.2.2 (by decide)
    (by simp +decide [sev, Env.get, mvParams, ctxEnv]; exact cellA_plus C od 2) ?_
  refine specR_congr (m' := formerResSort cv.type >>= fun r =>
      (match r with
        | some s => readLevelM s >>= fun l => pure (ConLeche.Level.zeronessOf l)
        | none => pure (ConLeche.PropWhen.ifAllZero [])) >>= fun z => pure z.isNever)
    (by simp only [formerZ, bind_assoc] <;> rfl) ?_
  refine specR_callNIH (C := ctxH C H) mvR fFs [fsT] [vv mvT] fsBody [Enc.idxW cv.type] (by decide) rfl (by decide) hc.fs
    ⟨by simp +decide [sev, Env.get], trivial⟩
    (fun a w s' st => formerResSort cv.type s = .ok (a, s') ∧ PostOL (ctxH C H) s a w s' st)
    (fun a w s' _ => formerResSort cv.type s = .ok (a, s') ∧ s' = s ∧ w = optWG Enc.idxW a)
    (fun a w s' st ⟨hrun, h1, h2, H', hp', h3⟩ => ⟨H', hp', ⟨hrun, h1, h2⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [fsT] _ rfl hlk)
      (fs_spec (ctxH C H) hc.pir s cv.type)))
    (fun r w s1 H1 hp1 ⟨hrun, hs1, hw⟩ => ?_)
  subst s1 hw
  have hp1' : H <+: H1 := hp1
  rcases r with _ | u
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · obtain ⟨l, hl⟩ := hsd u hrun
    obtain ⟨X, hx, hX⟩ := readLevelM_runC u s l hrl hl
    simp only [bind_assoc, pure_bind]
    refine LLeq.specR_ofRun (R' := PostB (ctxH C H)) (am_run_bind hx rfl) ?_
      (fun w st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, LLeq.sr_congrS hsr rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
        (cachesOK_readLC hsr.cok X hX)⟩)
    have hne : ¬ Enc.idxW u + 1 = 0 := lidxW_add_one_ne u
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [isNever_zeronessOf]
    refine specR_bindPure ?_
    refine specR_callNIH (C := ctxH C H1) mvX fNz0 [nzU] [.op .sub [vv mvR, .const 1]] nzBody [Enc.idxW u]
      (by decide) rfl (by decide) hc.nz
      ⟨by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
      (PostBS (ctxH C H1) s) (fun a w s' _ => s' = s ∧ w = boolW a)
      (fun a w s' st ⟨h1, h2, h3⟩ => ⟨H1, List.prefix_refl _, ⟨h1, h2⟩, by subst h1; exact h3⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [nzU] _ rfl hlk)
        (nz0_spec (ctxH C H1) hc.nz s hwf l u hl))
      (fun b w s4 H4 hp4 ⟨hs4, hw⟩ => ?_)
    subst hs4 hw
    exact specR_returnI _ (boolW b) (by simp [Env.get])
      (fun t ht => ⟨H4, hp1'.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
