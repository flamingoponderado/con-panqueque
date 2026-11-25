import ConPanqueque.T.Ind.Split

/-!
# Equal level-parameter lists

`readBlock` checks that every member and constructor declares the block's universe parameters
(`c.levelParams == lps`).  A list is a heap block of name handles (`EBlk`, reached by an `ENList` pointer);
`lpsEq(a, b)` compares the lengths, then `lpsEqGo(a, b, i, n)` the handles from index `i`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

def leA := ofString "le_a"
def leB := ofString "le_b"
def leI := ofString "le_i"
def leN := ofString "le_n"
def leX := ofString "le_x"
def leY := ofString "le_y"
def leR := ofString "le_r"
def fLpsEqGo := ofString "lpsEqGo"
def fLpsEq := ofString "lpsEq"

def legParams : List MlS := [leA, leB, leI, leN]
def leParams : List MlS := [leA, leB]
def leLocals : List MlS := [leX, leY, leR]

def legBody : ProgHOL 64 := prologue leLocals
  (.ite (.cmp .lower (vv leI) (vv leN))
    (.seq (.assign .local leX (.load .one (.op .add [vv leA, .op .add [.panop .mul [vv leI, .const 8], .const 8]])))
    (.seq (.assign .local leY (.load .one (.op .add [vv leB, .op .add [.panop .mul [vv leI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv leX) (vv leY))
      (.seq (.call (some (some (.local, leR), none)) fLpsEqGo [vv leA, vv leB, .op .add [vv leI, .const 1], vv leN])
        (.return (vv leR)))
      (.return (.const 0)))))
    (.return (.const 1)))

def leBody : ProgHOL 64 := prologue leLocals
  (.seq (.assign .local leX (.load .one (vv leA)))
  (.seq (.assign .local leY (.load .one (vv leB)))
  (.ite (.cmp .equal (vv leX) (vv leY))
    (.seq (.call (some (some (.local, leR), none)) fLpsEqGo [vv leA, vv leB, .const 0, vv leX]) (.return (vv leR)))
    (.return (.const 0)))))

section
variable {σ : Type}

theorem leg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ leLocals → (ctxEnv C ++ legParams.zip vals).get x = none :=
  Knot.params_none C leLocals legParams vals (by decide) (by decide)

theorem le_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ leLocals → (ctxEnv C ++ leParams.zip vals).get x = none :=
  Knot.params_none C leLocals leParams vals (by decide) (by decide)

/-- The handles of a list from cell `o + 1` (an `EBlk`'s elements, the count cell not needed). -/
def Elems (H : List (BitVec 64)) (o : Nat) (xs : List NIdx) : Prop :=
  ∀ j (hj : j < xs.length), H[o + 1 + j]? = some (Enc.idxW xs[j])

theorem elems_of_eblk {H : List (BitVec 64)} {o : Nat} {xs : List NIdx} (h : EBlk H o (xs.map Enc.idxW)) :
    Elems H o xs := fun j hj => by have := h.2 j (by simp; omega); simpa using this

/-- Equal suffixes from index `i`. -/
theorem drop_beq_succ {xs ys : List NIdx} {i : Nat} (hx : i < xs.length) (hy : i < ys.length) :
    (xs.drop i == ys.drop i) = (xs[i] == ys[i] && xs.drop (i + 1) == ys.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy, List.cons_beq_cons]

/-- **`lpsEqGo`**: the handles from index `i` agree. -/
theorem leg_spec (C : Ctx) (hc : C.code.lookup fLpsEqGo = some (legParams.map (fun p => (p, ShapeHOL.one)), legBody, .one))
    (xs ys : List NIdx) (oa ob : Nat) (hlen : xs.length = ys.length) (hl : xs.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → Elems H oa xs → Elems H ob ys →
      xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (legParams.zip [cellA C oa, cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length]))
        legBody s (pure (xs.drop i == ys.drop i)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hp ha hb hf hi
    have hil : i = xs.length := by omega
    subst hil
    refine specR_prologue (postB_locals _) (leg_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, legParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, hlen, List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hp ha hb hf hi
    have hix : i < xs.length := by omega
    have hiy : i < ys.length := by omega
    refine specR_prologue (postB_locals _) (leg_none _ _) ?_
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, legParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hix])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hwa : (ctxH C H).H[oa + 1 + i]? = some (Enc.idxW xs[i]) := by
      show H[oa + 1 + i]? = _; exact ha i hix
    have hwb : (ctxH C H).H[ob + 1 + i]? = some (Enc.idxW ys[i]) := by
      show H[ob + 1 + i]? = _; exact hb i hiy
    refine UD.specR_heapLoadI' (C := ctxH C H) leX _ (oa + 1 + i) _ hwa (by decide)
      (by simp +decide [sev, Env.get, legParams, ctxEnv]; exact cellA_mulIdx C oa i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) leY _ (ob + 1 + i) _ hwb (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, legParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    rw [drop_beq_succ hix hiy]
    by_cases he : xs[i] = ys[i]
    · refine specR_ifI _ 1 (by simp [sev, Env.get_cons, he, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [he, beq_self_eq_true, Bool.true_and]
      refine specR_congr (m' := (pure (xs.drop (i + 1) == ys.drop (i + 1)) : AM Bool) >>= fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) leR fLpsEqGo legParams [vv leA, vv leB, .op .add [vv leI, .const 1], vv leN]
        legBody [cellA C oa, cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl
        (by simp +decide [ctxLocals, leLocals]) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, legParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, legParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, legParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, legParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu legParams _ rfl hlk)
          (ih (i + 1) H s hp ha hb (by omega) (by omega)))
        (fun b w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW b) (by simp +decide [Env.get])
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : Enc.idxW xs[i] ≠ Enc.idxW ys[i] := fun h => he (ConPanqueque.V.Enc.idxW_inj h)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hne, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      have hb' : (xs[i] == ys[i]) = false := by simpa using he
      simp only [hb', Bool.false_and]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem beq_of_length_ne {xs ys : List NIdx} (h : xs.length ≠ ys.length) : (xs == ys) = false := by
  cases e : (xs == ys)
  · rfl
  · have := List.length_eq_of_beq e; exact absurd this h

/-- **`lpsEq`**: the two lists are equal. -/
theorem le_spec (C : Ctx) (hcg : C.code.lookup fLpsEqGo = some (legParams.map (fun p => (p, ShapeHOL.one)), legBody, .one))
    (hc : C.code.lookup fLpsEq = some (leParams.map (fun p => (p, ShapeHOL.one)), leBody, .one))
    (xs ys : List NIdx) (oa ob : Nat) (hx : xs.length < 2 ^ 59) (hy : ys.length < 2 ^ 59)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (ha : EBlk H oa (xs.map Enc.idxW)) (hb : EBlk H ob (ys.map Enc.idxW)) :
    SpecR (σ := σ) (Pre (ctxH C H) s (leParams.zip [cellA C oa, cellA C ob])) leBody s (pure (xs == ys))
      (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (le_none _ _) ?_
  have hla : (ctxH C H).H[oa]? = some (BitVec.ofNat 64 xs.length) := by show H[oa]? = _; rw [ha.1]; simp
  have hlb : (ctxH C H).H[ob]? = some (BitVec.ofNat 64 ys.length) := by show H[ob]? = _; rw [hb.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) leX (vv leA) oa _ hla (by decide)
    (by simp +decide [sev, Env.get, leParams, ctxEnv]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) leY (vv leB) ob _ hlb (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, leParams, ctxEnv]; rfl) ?_
  refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (x := xs.length) (y := ys.length) (by omega) (by omega)
    (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons])) (fun h => ?_) (fun h => ?_)
  · have hl : xs.length = ys.length := by
      by_cases c : xs.length = ys.length; exact c; simp [boolW, c] at h
    have hd : (xs == ys) = (xs.drop 0 == ys.drop 0) := by simp
    rw [hd]
    refine specR_congr (m' := (pure (xs.drop 0 == ys.drop 0) : AM Bool) >>= fun b => pure b) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) leR fLpsEqGo legParams [vv leA, vv leB, .const 0, vv leX]
      legBody [cellA C oa, cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 xs.length] (by decide) rfl
      (by simp +decide [ctxLocals, leLocals]) hcg
      ⟨by simp +decide [sev, Env.get_cons, Env.get, leParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, leParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu legParams _ rfl hlk)
        (leg_spec C hcg xs ys oa ob hl hx xs.length 0 H s hp (elems_of_eblk ha) (elems_of_eblk hb) (by omega)
          (by omega)))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp +decide [Env.get])
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hl : xs.length ≠ ys.length := by intro c; simp [boolW, c] at h
    rw [beq_of_length_ne hl]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
