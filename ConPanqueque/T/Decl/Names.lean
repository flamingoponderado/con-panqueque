import ConPanqueque.T.Decl.Flush
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The record's name tests

`andPinOk` at a one-constant record (the name is none of the pinned `And` names) and `basisNamesOk` there (the
name is not reserved: not in the pin table's reserved-name block, an environment block).
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def rmN := ofString "rm_n"
def rmP := ofString "rm_p"
def rmJ := ofString "rm_j"
def rmL := ofString "rm_l"
def rmY := ofString "rm_y"
def rmR := ofString "rm_r"
def fRsm := ofString "envBlockMem"
def rmParams : List MlS := [rmN, rmP, rmJ, rmL]
def rmLocals : List MlS := [rmY, rmR]

/-- Is the handle `rmN` among the environment block's handles from index `rmJ` on. -/
def rsmBody : ProgHOL 64 := prologue rmLocals
  (.ite (.cmp .lower (vv rmJ) (vv rmL))
    (.seq (.assign .local rmY (.load .one (.op .add [vv rmP, .op .add [.panop .mul [vv rmJ, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv rmY) (vv rmN)) (.return (.const 1))
      (.seq (.call (some (some (.local, rmR), none)) fRsm [vv rmN, vv rmP, .op .add [vv rmJ, .const 1], vv rmL])
        (.return (vv rmR)))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem rm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rmLocals → (ctxEnv C ++ rmParams.zip vals).get x = none :=
  Knot.params_none C rmLocals rmParams vals (by decide) (by decide)

/-- **`rsm`**: membership in an environment block of handles. -/
theorem rsm_spec (C : Ctx)
    (hc : C.code.lookup fRsm = some (rmParams.map (fun p => (p, ShapeHOL.one)), rsmBody, .one))
    (xs : List NIdx) (o : Nat) (hb : EBlk C.EH o (xs.map Enc.idxW)) (hlen : xs.length < 2 ^ 62) (x : NIdx) (s : AState) :
    ∀ k j (H : List (BitVec 64)), C.H <+: H → xs.length - j = k → j ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (rmParams.zip [Enc.idxW x, ecell C o, BitVec.ofNat 64 j,
        BitVec.ofNat 64 xs.length])) rsmBody s (pure ((xs.drop j).contains x)) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro j H hp hk hj
    have hjl : j = xs.length := by omega
    subst hjl
    refine specR_prologue (postB_locals _) (rm_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, List.contains_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j H hp hk hj
    have hjl : j < xs.length := by omega
    refine specR_prologue (postB_locals _) (rm_none _ _) ?_
    have hlw := nd_lt_iff j xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).EH[o + 1 + j]? = some (Enc.idxW xs[j]) := by
      have := hb.2 j (by simp; omega); simp only [List.getElem_map] at this; exact this
    refine specR_envLoadI (C := ctxH C H) rmY _ (o + 1 + j) _ (by decide)
      (by simp +decide [sev, Env.get, rmParams, ctxEnv]; exact ecell_idx C o j) hw ?_
    rw [contains_drop hjl]
    by_cases he : xs[j] = x
    · subst he
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, Bool.true_or]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : Enc.idxW xs[j] ≠ Enc.idxW x := fun h => he (idxW_inj h)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
        (fun h => absurd rfl h) (fun _ => ?_)
      have hb' : (xs[j] == x) = false := by simpa using he
      rw [hb', Bool.false_or]
      refine specR_callPure (C := ctxH C H) rmR fRsm rmParams [vv rmN, vv rmP, .op .add [vv rmJ, .const 1], vv rmL]
        rsmBody [Enc.idxW x, ecell C o, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 xs.length]
        ((xs.drop (j + 1)).contains x) (by decide) rfl (by decide) hc
        ⟨by simp +decide [Env.get, rmParams, ctxEnv], by simp +decide [Env.get, rmParams, ctxEnv] <;> rfl,
          by simp +decide [sev, Env.get, rmParams, ctxEnv]; exact word_add1_eq j, by simp +decide [Env.get, rmParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk) (ih (j + 1) H hp (by omega) (by omega)))
        (fun w H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp +decide [Env.get]) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
