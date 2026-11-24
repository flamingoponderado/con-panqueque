import ConPanqueque.T.Decl.ConstsResolveF
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `nameNodup`: the universe parameters are distinct

Over a block of name handles: `ndHas` (is a handle among those from index `j` on) and `ndGo` (no handle repeats
from index `i` on), both by self-recursion along the block.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def ndP := ofString "nd_p"
def ndJ := ofString "nd_j"
def ndN := ofString "nd_n"
def ndX := ofString "nd_x"
def ndY := ofString "nd_y"
def ndR := ofString "nd_r"
def fNdh := ofString "nameHas"
def fNdg := ofString "nameNodupGo"

def ndhParams : List MlS := [ndP, ndJ, ndN, ndX]
def ndgParams : List MlS := [ndP, ndJ, ndN]
def ndLocals : List MlS := [ndY, ndR]

/-- Is `x` among the block's handles from index `j` on. -/
def ndhBody : ProgHOL 64 := prologue ndLocals
  (.ite (.cmp .lower (vv ndJ) (vv ndN))
    (.seq (.assign .local ndY (.load .one (.op .add [vv ndP, .op .add [.panop .mul [vv ndJ, .const 8], .const 8]])))
      (.ite (.cmp .equal (vv ndY) (vv ndX)) (.return (.const 1))
        (.seq (.call (some (some (.local, ndR), none)) fNdh [vv ndP, .op .add [vv ndJ, .const 1], vv ndN, vv ndX])
          (.return (vv ndR)))))
    (.return (.const 0)))

/-- No handle repeats from index `j` on. -/
def ndgBody : ProgHOL 64 := prologue ndLocals
  (.ite (.cmp .lower (vv ndJ) (vv ndN))
    (.seq (.assign .local ndY (.load .one (.op .add [vv ndP, .op .add [.panop .mul [vv ndJ, .const 8], .const 8]])))
      (.seq (.call (some (some (.local, ndR), none)) fNdh [vv ndP, .op .add [vv ndJ, .const 1], vv ndN, vv ndY])
        (.ite (.cmp .notEqual (vv ndR) (.const 0)) (.return (.const 0))
          (.seq (.call (some (some (.local, ndR), none)) fNdg [vv ndP, .op .add [vv ndJ, .const 1], vv ndN])
            (.return (vv ndR))))))
    (.return (.const 1)))


section
variable {σ : Type}

theorem nd_lt_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a < BitVec.ofNat 64 b ↔ a < b := by
  rw [BitVec.lt_def]; simp; omega

theorem ndh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ndLocals → (ctxEnv C ++ ndhParams.zip vals).get x = none :=
  Knot.params_none C ndLocals ndhParams vals (by decide) (by decide)

theorem ndg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ndLocals → (ctxEnv C ++ ndgParams.zip vals).get x = none :=
  Knot.params_none C ndLocals ndgParams vals (by decide) (by decide)

theorem contains_drop {xs : List NIdx} {j : Nat} (hj : j < xs.length) (x : NIdx) :
    (xs.drop j).contains x = ((xs[j] == x) || (xs.drop (j + 1)).contains x) := by
  rw [List.drop_eq_getElem_cons hj, List.contains_cons]
  cases h : (xs[j] == x) <;> cases h' : (x == xs[j]) <;> simp_all

/-- **`ndHas`**: is `x` among the block's handles from index `j` on. -/
theorem ndh_spec (C : Ctx) (hc : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one))
    (xs : List NIdx) (o : Nat) (x : NIdx) (hlen : xs.length < 2 ^ 62) :
    ∀ k j (H : List (BitVec 64)) (s : AState), C.H <+: H → BlkAt H o (xs.map Enc.idxW) → xs.length - j = k →
      j ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ndhParams.zip [cellA C o, BitVec.ofNat 64 j, BitVec.ofNat 64 xs.length,
        Enc.idxW x])) ndhBody s (pure ((xs.drop j).contains x)) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro j H s hp hb hk hj
    have hjl : j = xs.length := by omega
    subst hjl
    refine specR_prologue (postB_locals _) (ndh_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ndhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, List.contains_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j H s hp hb hk hj
    have hjl : j < xs.length := by omega
    refine specR_prologue (postB_locals _) (ndh_none _ _) ?_
    have hlw := nd_lt_iff j xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ndhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[o + 1 + j]? = some (Enc.idxW xs[j]) := by
      show H[o + 1 + j]? = _
      have := hb.2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) ndY _ (o + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, ndhParams, ctxEnv]; exact cellA_idx C o j) ?_
    rw [contains_drop hjl]
    by_cases he : xs[j] = x
    · subst he
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ndhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, Bool.true_or]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : Enc.idxW xs[j] ≠ Enc.idxW x := fun h => he (idxW_inj h)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ndhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
        (fun h => absurd rfl h) (fun _ => ?_)
      have hb' : (xs[j] == x) = false := by simpa using he
      rw [hb', Bool.false_or]
      refine specR_congr (m' := (pure ((xs.drop (j + 1)).contains x) : AM Bool) >>= fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) ndR fNdh ndhParams [vv ndP, .op .add [vv ndJ, .const 1], vv ndN, vv ndX]
        ndhBody [cellA C o, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 xs.length, Enc.idxW x] (by decide) rfl (by decide) hc
        ⟨by simp +decide [Env.get, ndhParams, ctxEnv], by simp +decide [sev, Env.get, ndhParams, ctxEnv]; exact word_add1_eq j,
          by simp +decide [Env.get, ndhParams, ctxEnv], by simp +decide [Env.get, ndhParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndhParams _ rfl hlk)
          (ih (j + 1) H s hp hb (by omega) (by omega)))
        (fun b w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW b) (by simp +decide [Env.get])
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


theorem nameNodup_drop {xs : List NIdx} {j : Nat} (hj : j < xs.length) :
    nameNodup (xs.drop j) = (!(xs.drop (j + 1)).contains xs[j] && nameNodup (xs.drop (j + 1))) := by
  rw [List.drop_eq_getElem_cons hj]; rfl

/-- **`ndGo`**: no handle of the block repeats from index `j` on. -/
theorem ndg_spec (C : Ctx) (hch : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one))
    (hcg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one))
    (xs : List NIdx) (o : Nat) (hlen : xs.length < 2 ^ 62) :
    ∀ k j (H : List (BitVec 64)) (s : AState), C.H <+: H → BlkAt H o (xs.map Enc.idxW) → xs.length - j = k →
      j ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ndgParams.zip [cellA C o, BitVec.ofNat 64 j, BitVec.ofNat 64 xs.length]))
        ndgBody s (pure (nameNodup (xs.drop j))) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro j H s hp hb hk hj
    have hjl : j = xs.length := by omega
    subst hjl
    refine specR_prologue (postB_locals _) (ndg_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ndgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW, nameNodup], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j H s hp hb hk hj
    have hjl : j < xs.length := by omega
    refine specR_prologue (postB_locals _) (ndg_none _ _) ?_
    have hlw := nd_lt_iff j xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ndgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[o + 1 + j]? = some (Enc.idxW xs[j]) := by
      show H[o + 1 + j]? = _
      have := hb.2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) ndY _ (o + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, ndgParams, ctxEnv]; exact cellA_idx C o j) ?_
    rw [nameNodup_drop hjl]
    refine specR_congr (m' := (pure ((xs.drop (j + 1)).contains xs[j]) : AM Bool) >>= fun c =>
      bif c then pure false else ((pure (nameNodup (xs.drop (j + 1))) : AM Bool) >>= fun b => pure b))
      (by cases (xs.drop (j + 1)).contains xs[j] <;> simp) ?_
    refine specR_callNIH (C := ctxH C H) ndR fNdh ndhParams [vv ndP, .op .add [vv ndJ, .const 1], vv ndN, vv ndY]
      ndhBody [cellA C o, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 xs.length, Enc.idxW xs[j]] (by decide) rfl (by decide) hch
      ⟨by simp +decide [Env.get, ndgParams, ctxEnv], by simp +decide [sev, Env.get, ndgParams, ctxEnv]; exact word_add1_eq j,
        by simp +decide [Env.get, ndgParams, ctxEnv], by simp +decide [Env.get, ndgParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndhParams _ rfl hlk)
        (ndh_spec C hch xs o xs[j] hlen _ (j + 1) H s hp hb rfl (by omega)))
      (fun c w s1 H1 hp1 hw => ?_)
    subst hw
    cases c with
    | true =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | false =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      have hp01 : C.H <+: H1 := hp.trans hp1
      have hb1 : BlkAt H1 o (xs.map Enc.idxW) := blkAt_mono hb hp1
      refine specR_callNIH (C := ctxH C H1) ndR fNdg ndgParams [vv ndP, .op .add [vv ndJ, .const 1], vv ndN]
        ndgBody [cellA C o, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hcg
        ⟨by simp +decide [Env.get, ndgParams, ctxEnv], by simp +decide [sev, Env.get, ndgParams, ctxEnv]; exact word_add1_eq j,
          by simp +decide [Env.get, ndgParams, ctxEnv], trivial⟩
        (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
          (ih (j + 1) H1 s1 hp01 hb1 (by omega) (by omega)))
        (fun b w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW b) (by simp +decide [Env.get])
        (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
