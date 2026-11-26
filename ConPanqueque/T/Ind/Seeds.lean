import ConPanqueque.T.Ind.CheckPos

/-!
# `classSeeds` (unnested blocks): every class targets a block member, so there are no seeds

A class over an outside inductive (a nested block) hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def cseA := ofString "cse_a"
def cseJ := ofString "cse_j"
def cseL := ofString "cse_l"
def cseP := ofString "cse_p"
def cseX := ofString "cse_x"
def cseR := ofString "cse_r"
def fSd := ofString "classSeedsNone"

def cseParams : List MlS := [cseA, cseJ]
def cseLocals : List MlS := [cseL, cseP, cseX, cseR]

def cseBody : ProgHOL 64 := prologue cseLocals
  (.seq (.assign .local cseL (.load .one (vv cseA)))
  (.ite (.cmp .lower (vv cseJ) (vv cseL))
    (.seq (.assign .local cseP (.load .one (.op .add [.op .add [vv cseA, .const 8], .shift .lsl (vv cseJ) (.const 3)])))
    (.seq (.assign .local cseX (.load .one (.op .add [vv cseP, .const 16])))
    (.ite (.cmp .equal (vv cseX) (.const 0)) hang
      (.seq (.call (some (some (.local, cseR), none)) fSd [vv cseA, .op .add [vv cseJ, .const 1]]) (.return (vv cseR))))))
    (.return (.const 0))))

section
variable {σ : Type}

theorem cse_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cseLocals → (ctxEnv C ++ cseParams.zip vals).get x = none :=
  Knot.params_none C cseLocals cseParams vals (by decide) (by decide)

/-- No seeds, the heap kept. -/
def PostCse (C : Ctx) (r : List (NestKey × Nat)) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  r = [] ∧ SR C s' st

theorem postCse_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCse C a w s' st → PostCse C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

/-- **`classSeeds`** from major `j` on (a class without a member hangs). -/
theorem cse_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fSd = some (cseParams.map (fun p => (p, ShapeHOL.one)), cseBody, .one))
    (ctx : NestCtx) (holes : List EIdx) (pfvs : List EIdx) (ms : List TargetMajor) (o : Nat) (H : List (BitVec 64))
    (hb : TMBlk C H o pfvs ms) (hml : ms.length < 2 ^ 58) :
    ∀ f j (s : AState), ms.length - j = f → j ≤ ms.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cseParams.zip [cellA C o, BitVec.ofNat 64 j])) cseBody s
        (classSeeds ctx holes (ms.drop j)) (PostCse (ctxH C H)) := by
  obtain ⟨ps, hpl, hpb, hpr⟩ := hb
  intro f
  induction f with
  | zero =>
    intro j s hf hj
    have hjl : j = ms.length := by omega
    subst hjl
    refine specR_prologue (postCse_locals _) (cse_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cseL (vv cseA) o _ hpb.1 (by decide)
      (by simp +decide [sev, Env.get, cseParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cseParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hpl]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, classSeeds]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j s hf hj
    have hjl : j < ms.length := by omega
    refine specR_prologue (postCse_locals _) (cse_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cseL (vv cseA) o _ hpb.1 (by decide)
      (by simp +decide [sev, Env.get, cseParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cseParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hpl, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hrep, -, -⟩ := hpr j hjl
    have hjp : j < ps.length := by omega
    have h1 := hpb.2 j (by simpa using hjp)
    rw [List.getElem_map, List.getElem?_eq_getElem hjp] at *
    simp only [Option.some.injEq] at hop
    subst hop
    obtain ⟨-, -, -, -, -, -, -, -, hmem, hmb⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxH C H) cseP _ (o + 1 + j) _ h1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cseParams, ctxEnv]; show _ = cellA C (o + 1 + j)
          rw [← cellA_shl C (o + 1) j (by omega), ← cellA_add8]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cseX _ (ps[j] + 2) _ hmem (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ps[j] 2) ?_
    rw [List.drop_eq_getElem_cons hjl, classSeeds]
    rcases hm : ms[j].member with _ | t
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hm, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    have ht := hmb t hm
    have hnt : BitVec.ofNat 64 (t + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hm, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnt)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only
    refine specR_congr (m' := classSeeds ctx holes (ms.drop (j + 1)) >>= fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNIM cseR fSd cseParams [vv cseA, .op .add [vv cseJ, .const 1]] cseBody
      [cellA C o, BitVec.ofNat 64 (j + 1)] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cseParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cseParams, ctxEnv]; exact e_succ j, trivial⟩
      (PostCse (ctxH C H)) (fun _ _ _ _ h => h.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cseParams _ rfl hlk) (ih (j + 1) s (by omega) (by omega)))
      (fun r w s1 st ⟨hr, _⟩ => ?_)
    subst hr
    exact specR_returnI _ w (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
