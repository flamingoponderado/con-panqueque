import ConPanqueque.T.Ind.Shape

/-!
# Splitting a block: runs of record kinds

A block's records are its inductive types, then its constructors, then its recursors (`blockSplit`).  In the
heap the three lists are slices of the one block, so the split is two boundaries: `tagRun(p, j, n, t)` is the
first index from `j` whose record's kind word is not `t` (`runEnd`), and the block splits when the runs of
kinds `3`, `4`, `5` from `0` reach its end.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- A record's kind word (`CIE`'s first word). -/
def kindOf : IConstantInfo → Nat
  | .axiomInfo _ => 0 | .defnInfo .. => 1 | .thmInfo _ => 2 | .indInfo .. => 3 | .ctorInfo .. => 4
  | .recInfo .. => 5

theorem cie_kind {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) :
    H[o]? = some (BitVec.ofNat 64 (kindOf ci)) := by
  obtain ⟨-, h⟩ := h
  cases ci <;> simp only [kindOf] at h ⊢
  all_goals first | exact h | exact h.1

/-- The first index from `j` whose record is not of kind `t` (the block's length if none). -/
def runEnd (blk : List IConstantInfo) (t : Nat) : Nat → Nat → Nat
  | 0, j => j
  | fuel + 1, j => match blk[j]? with
    | some ci => if kindOf ci = t then runEnd blk t fuel (j + 1) else j
    | none => j

def trP := ofString "tr_p"
def trJ := ofString "tr_j"
def trN := ofString "tr_n"
def trT := ofString "tr_t"
def trQ := ofString "tr_q"
def trW := ofString "tr_w"
def trR := ofString "tr_r"
def fTagRun := ofString "tagRun"

def trParams : List MlS := [trP, trJ, trN, trT]
def trLocals : List MlS := [trQ, trW, trR]

def trBody : ProgHOL 64 := prologue trLocals
  (.ite (.cmp .lower (vv trJ) (vv trN))
    (.seq (.assign .local trQ (.load .one (.op .add [vv trP, .op .add [.panop .mul [vv trJ, .const 8], .const 8]])))
    (.seq (.assign .local trW (.load .one (vv trQ)))
    (.ite (.cmp .equal (vv trW) (vv trT))
      (.seq (.call (some (some (.local, trR), none)) fTagRun [vv trP, .op .add [vv trJ, .const 1], vv trN, vv trT])
        (.return (vv trR)))
      (.return (vv trJ)))))
    (.return (vv trJ)))

section
variable {σ : Type}

/-- The post: the word is the run's end. -/
def PostN (C : Ctx) (n : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = BitVec.ofNat 64 n ∧ SR (ctxH C H') s' st

theorem postN_locals (C : Ctx) : ∀ (a : Nat) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostN C a w s' st → PostN C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hs⟩ => ⟨H', hp, hw, sr_of_eq hs rfl rfl rfl rfl⟩

theorem tr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ trLocals → (ctxEnv C ++ trParams.zip vals).get x = none :=
  Knot.params_none C trLocals trParams vals (by decide) (by decide)

theorem runEnd_succ {blk : List IConstantInfo} {t fuel j : Nat} (hj : j < blk.length) :
    runEnd blk t (fuel + 1) j = if kindOf blk[j] = t then runEnd blk t fuel (j + 1) else j := by
  simp [runEnd, List.getElem?_eq_getElem hj]

theorem runEnd_zero_len {blk : List IConstantInfo} {t fuel j : Nat} (hj : blk.length ≤ j) :
    runEnd blk t fuel j = j := by
  cases fuel with
  | zero => rfl
  | succ f => simp [runEnd, List.getElem?_eq_none hj]

theorem kindOf_lt (ci : IConstantInfo) : kindOf ci < 6 := by cases ci <;> simp [kindOf]

/-- **`tagRun`**: the run of kind `t` from index `j`. -/
theorem tr_spec (C : Ctx) (hc : C.code.lookup fTagRun = some (trParams.map (fun p => (p, ShapeHOL.one)), trBody, .one))
    (blk : List IConstantInfo) (ob t : Nat) (ht : t < 6) (hlen : blk.length < 2 ^ 59) :
    ∀ k j (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → blk.length - j = k →
      j ≤ blk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (trParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 blk.length,
        BitVec.ofNat 64 t])) trBody s (pure (runEnd blk t k j)) (PostN (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro j H s hp hb hk hj
    have hjl : j = blk.length := by omega
    subst hjl
    refine specR_prologue (postN_locals _) (tr_none _ _) ?_
    have hlw := nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, trParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ (BitVec.ofNat 64 blk.length) (by simp +decide [sev, Env.get, trParams, ctxEnv])
      (fun t' ht' => ⟨H, List.prefix_refl _, by simp [runEnd], sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j H s hp hb hk hj
    have hjl : j < blk.length := by omega
    obtain ⟨os, hosl, hblk, hcie⟩ := id hb
    have hoj : j < os.length := by omega
    refine specR_prologue (postN_locals _) (tr_none _ _) ?_
    have hlw := nd_lt_iff j blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, trParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[ob + 1 + j]? = some (cellA C os[j]) := by
      show H[ob + 1 + j]? = _
      have := hblk.2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) trQ _ (ob + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, trParams, ctxEnv]; exact cellA_mulIdx C ob j (by omega)) ?_
    have hkd := cie_kind (hcie j hjl hoj)
    refine UD.specR_heapLoadI' (C := ctxH C H) trW (vv trQ) os[j] _ hkd (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    rw [runEnd_succ hjl]
    have hk6 := kindOf_lt blk[j]
    have hcmp : sev ((trW, BitVec.ofNat 64 (kindOf blk[j])) :: (trQ, cellA C os[j]) :: (ctxEnv (ctxH C H) ++
        trParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 blk.length, BitVec.ofNat 64 t]))
        (.cmp .equal (vv trW) (vv trT)) = some (if kindOf blk[j] = t then 1 else 0) := by
      simp +decide [sev, Env.get, trParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        ofNat_eq_small (kindOf blk[j]) t (by omega) (by omega)]
    by_cases hkt : kindOf blk[j] = t
    · refine specR_ifI _ _ hcmp (fun _ => ?_) (fun h => by simp [hkt] at h)
      rw [ite_eq_left hkt]
      refine specR_congr (m' := (pure (runEnd blk t k (j + 1)) : AM Nat) >>= fun n => pure n) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) trR fTagRun trParams [vv trP, .op .add [vv trJ, .const 1], vv trN, vv trT]
        trBody [cellA C ob, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 blk.length, BitVec.ofNat 64 t] (by decide) rfl
        (by simp +decide [ctxLocals, trLocals]) hc
        ⟨by simp +decide [sev, Env.get, trParams, ctxEnv], by simp +decide [sev, Env.get, trParams, ctxEnv]; exact word_add1_eq j,
          by simp +decide [sev, Env.get, trParams, ctxEnv], by simp +decide [sev, Env.get, trParams, ctxEnv], trivial⟩
        (PostN (ctxH C H)) (fun n w _ _ => w = BitVec.ofNat 64 n) (fun n w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu trParams _ rfl hlk)
          (ih (j + 1) H s hp hb (by omega) (by omega)))
        (fun n w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp +decide [Env.get])
        (fun t' ht' => ⟨H1, hp1, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ _ hcmp (fun h => by simp [hkt] at h) (fun _ => ?_)
      rw [ite_eq_right hkt]
      exact specR_returnI _ (BitVec.ofNat 64 j) (by simp +decide [sev, Env.get, trParams, ctxEnv])
        (fun t' ht' => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
