import ConPanqueque.T.Ind.CheckAbs

/-!
# `checkBlockPositivity` (unnested blocks): the walk's context, uniformity, the root frame, the sorts

`blockNestCtx`, then `nestUniform`, `nestRoot` from an empty state, the block's `Prop`-ness, and
`checkAbsCtorSortsAll`.  The parameters and holes are concatenated into one block for `nestCrest`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## Appending a block's words to another (fresh blocks) -/

def catA := ofString "cat_a"
def catB := ofString "cat_b"
def catJ := ofString "cat_j"
def catL := ofString "cat_l"
def catX := ofString "cat_x"
def catA2 := ofString "cat_a2"
def catR := ofString "cat_r"
def fCat := ofString "appendBlock"

def catParams : List MlS := [catA, catB, catJ]
def catLocals : List MlS := [catL, catX, catA2, catR]

def catBody : ProgHOL 64 := prologue catLocals
  (.seq (.assign .local catL (.load .one (vv catB)))
  (.ite (.cmp .lower (vv catJ) (vv catL))
    (.seq (.assign .local catX (.load .one (.op .add [.op .add [vv catB, .const 8], .shift .lsl (vv catJ) (.const 3)])))
    (.seq (.call (some (some (.local, catA2), none)) ExPre.fAppend [vv catA, vv catX])
    (.seq (.call (some (some (.local, catR), none)) fCat [vv catA2, vv catB, .op .add [vv catJ, .const 1]])
      (.return (vv catR)))))
    (.return (vv catA))))

structure CatCodes (C : Ctx) : Prop where
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fCat = some (catParams.map (fun p => (p, ShapeHOL.one)), catBody, .one)

section
variable {σ : Type}

theorem cat_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ catLocals → (ctxEnv C ++ catParams.zip vals).get x = none :=
  Knot.params_none C catLocals catParams vals (by decide) (by decide)

/-- **`xs ++ ys.drop j`** as a fresh block (the state kept). -/
theorem cat_spec (C : Ctx) (hok : CtxOK C) (hc : CatCodes C) (ys : List (BitVec 64)) (ob : Nat)
    (hyl : ys.length < 2 ^ 58) :
    ∀ f j (xs : List (BitVec 64)) (oa : Nat) (H : List (BitVec 64)) (s : AState), ys.length - j = f → j ≤ ys.length →
      BlkAt H oa xs → BlkAt H ob ys →
      SpecR (σ := σ) (Pre (ctxH C H) s (catParams.zip [cellA C oa, cellA C ob, BitVec.ofNat 64 j])) catBody s
        (pure (xs ++ ys.drop j) : AM (List (BitVec 64)))
        (fun r w s' st => ∃ H' o, H <+: H' ∧ s' = s ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st) := by
  intro f
  induction f with
  | zero =>
    intro j xs oa H s hf hj ha hb
    have hjl : j = ys.length := by omega
    subst hjl
    refine specR_prologue (fun a w s' st L ⟨H', o, h1, h2, h3, h4, hsr⟩ => ⟨H', o, h1, h2, h3, h4,
      sr_of_eq hsr rfl rfl rfl rfl⟩) (cat_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) catL (vv catB) ob _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, catParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.append_nil]
    exact specR_returnI _ (cellA C oa) (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv])
      (fun t ht => ⟨H, oa, List.prefix_refl _, rfl, rfl, ha, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j xs oa H s hf hj ha hb
    have hjl : j < ys.length := by omega
    refine specR_prologue (fun a w s' st L ⟨H', o, h1, h2, h3, h4, hsr⟩ => ⟨H', o, h1, h2, h3, h4,
      sr_of_eq hsr rfl rfl rfl rfl⟩) (cat_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) catL (vv catB) ob _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, catParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j ys.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, catParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := ctxH C H) catX _ (ob + 1 + j) ys[j] (hb.2 j hjl) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv]; show _ = cellA C (ob + 1 + j)
          rw [← cellA_shl C (ob + 1) j (by omega), ← cellA_add8]; rfl) ?_
    have heq : xs ++ ys.drop j = (xs ++ [ys[j]]) ++ ys.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjl]; simp
    rw [heq]
    refine specR_appendI hok hc.app H catA2 (vv catA) (vv catX) xs ys[j] oa ha (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv]) (by simp [sev, Env.get_cons])
      (fun H2 oa2 hp2 ha2 => ?_)
    refine specR_congr (m' := (pure ((xs ++ [ys[j]]) ++ ys.drop (j + 1)) : AM (List (BitVec 64))) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H2) catR fCat catParams [vv catA2, vv catB, .op .add [vv catJ, .const 1]] catBody
      [cellA C oa2, cellA C ob, BitVec.ofNat 64 (j + 1)] (by decide) rfl (by decide) hc.self
      ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv]; exact e_succ j, trivial⟩
      (fun r w s' st => ∃ H' o, H2 <+: H' ∧ s' = s ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
      (fun r w s' H' => s' = s ∧ ∃ o, w = cellA C o ∧ BlkAt H' o r)
      (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨hs', o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
        (ih (j + 1) (xs ++ [ys[j]]) oa2 H2 s (by omega) (by omega) ha2 (blkAt_mono hb hp2)))
      (fun r w s1 H3 hp3 ⟨hs1, o3, hw3, hb3⟩ => ?_)
    subst hs1; subst hw3
    exact specR_returnI _ (cellA C o3) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H3, o3, hp2.trans hp3, rfl, rfl, hb3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
