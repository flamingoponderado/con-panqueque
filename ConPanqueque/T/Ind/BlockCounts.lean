import ConPanqueque.T.Ind.PiBinders
import ConPanqueque.T.Ind.RecTarget
import ConPanqueque.Front.Tbl
import ConPanqueque.T.Core.AndRescue

/-!
# `blockCounts`: one member's index count

Read off the member's own telescope when it ends in a sort (`pbcT`), else off the argument counts `(mI, rP)` of
a recursor whose major names the member.  The twin returns `Except`; the port halts on every error (any error
rejects the block), so it refines `unwrapE (blockCounts …)`, the error turned into a failure.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP

/-- An `Except`-valued step, its error a failure. -/
def unwrapE {α : Type} (m : AM (Except CheckError α)) : AM α := do
  match ← m with
  | .ok v => pure v
  | .error e => fail e

/-- The counts once the telescope's reading is known. -/
def bcTail (nPd k nC nR : Nat) (r : Option (Nat × Nat)) : Option Nat → AM (Except CheckError (Nat × Nat))
  | some n =>
    if nPd ≤ n then pure (.ok (nPd, n - nPd))
    else pure (.error (.invalid "inductive type declares more parameters than its type has binders"))
  | none =>
    match r with
    | none => pure (.error (.invalid "no recursor of the block eliminates the inductive type"))
    | some (mI, rP) =>
      if rP < nC + k || mI < rP then pure (.error recCountsError)
      else if rP - (nC + k) == nPd then pure (.ok (nPd, mI - rP))
      else if k < nR && nPd + nR + nC ≤ rP then pure (.ok (nPd, mI - rP))
      else pure (.error recCountsError)

theorem blockCounts_eq (nPd k nC nR : Nat) (cvT : IConstantVal) (r : Option (Nat × Nat)) :
    blockCounts nPd k nC nR cvT r = (pbcT coreWalkFuel cvT.type >>= bcTail nPd k nC nR r) := by
  unfold blockCounts pbcT
  simp only [bind_assoc]
  congr 1; funext q
  obtain ⟨bs, res⟩ := q
  simp only []
  congr 1; funext v
  cases v <;> cases r <;> rfl

def bcNP := ofString "bc_np"
def bcK := ofString "bc_k"
def bcNC := ofString "bc_nc"
def bcNR := ofString "bc_nr"
def bcT := ofString "bc_t"
def bcHas := ofString "bc_has"
def bcMI := ofString "bc_mi"
def bcRP := ofString "bc_rp"
def bcV := ofString "bc_v"
def bcN := ofString "bc_n"
def fBlockCounts := ofString "blockCounts"

def bcParams : List MlS := [bcNP, bcK, bcNC, bcNR, bcT, bcHas, bcMI, bcRP]
def bcLocals : List MlS := [bcV, bcN]

def bcBody : ProgHOL 64 := prologue bcLocals
  (.seq (.call (some (some (.local, bcV), none)) fPbc [.const (BitVec.ofNat 64 coreWalkFuel), vv bcT])
  (.ite (.cmp .notEqual (vv bcV) (.const 0))
    (.seq (.assign .local bcN (.op .sub [vv bcV, .const 1]))
      (.ite (.cmp .lower (vv bcN) (vv bcNP)) hang (.return (.op .sub [vv bcN, vv bcNP]))))
    (.ite (.cmp .equal (vv bcHas) (.const 0)) hang
    (.ite (.cmp .lower (vv bcRP) (.op .add [vv bcNC, vv bcK])) hang
    (.ite (.cmp .lower (vv bcMI) (vv bcRP)) hang
    (.ite (.cmp .equal (.op .sub [vv bcRP, .op .add [vv bcNC, vv bcK]]) (vv bcNP)) (.return (.op .sub [vv bcMI, vv bcRP]))
    (.ite (.cmp .lower (vv bcK) (vv bcNR))
      (.ite (.cmp .lower (vv bcRP) (.op .add [vv bcNP, .op .add [vv bcNR, vv bcNC]])) hang
        (.return (.op .sub [vv bcMI, vv bcRP])))
      hang)))))))

/-- The recursor counts as three words: present, `mI`, `rP`. -/
def rWords : Option (Nat × Nat) → List (BitVec 64)
  | none => [0, 0, 0]
  | some (mI, rP) => [1, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP]

section
variable {σ : Type}

/-- The post: the word is the index count. -/
def PostBC (C : Ctx) (a : Nat × Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = BitVec.ofNat 64 a.2 ∧ SR (ctxH C H') s' st ∧ a.2 < 2 ^ 63

theorem postBC_locals (C : Ctx) : ∀ (a : Nat × Nat) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBC C a w s' st → PostBC C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hs, hb⟩ => ⟨H', hp, hw, sr_of_eq hs rfl rfl rfl rfl, hb⟩

theorem bc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bcLocals → (ctxEnv C ++ bcParams.zip vals).get x = none :=
  Knot.params_none C bcLocals bcParams vals (by decide) (by decide)

theorem unwrapE_bind {α β : Type} (m : AM α) (f : α → AM (Except CheckError β)) :
    unwrapE (m >>= f) = (m >>= fun a => unwrapE (f a)) := by
  simp [unwrapE, bind_assoc]

end

section
variable {σ : Type}

theorem ofNat_sub_small (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem ofNat_add_small (a b : Nat) (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega

/-- **`blockCounts`**, errors halting. -/
theorem bc_spec (C : Ctx) (hcp : C.code.lookup fPbc = some ([(pFu, .one), (pH, .one)], pbcBody fPbc, .one))
    (nPd k nC nR : Nat) (cvT : IConstantVal) (r : Option (Nat × Nat))
    (hb : nPd < 2 ^ 60 ∧ k < 2 ^ 60 ∧ nC < 2 ^ 60 ∧ nR < 2 ^ 60)
    (hr : ∀ mI rP, r = some (mI, rP) → mI < 2 ^ 63 ∧ rP < 2 ^ 63)
    (H : List (BitVec 64)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (bcParams.zip ([BitVec.ofNat 64 nPd, BitVec.ofNat 64 k, BitVec.ofNat 64 nC,
        BitVec.ofNat 64 nR, Enc.idxW cvT.type] ++ rWords r))) bcBody s
      (unwrapE (blockCounts nPd k nC nR cvT r)) (PostBC (ctxH C H)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  refine specR_prologue (postBC_locals _) (bc_none _ _) ?_
  rw [blockCounts_eq, unwrapE_bind]
  refine specR_callNIH (C := ctxH C H) bcV fPbc [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv bcT]
    (pbcBody fPbc) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cvT.type] (by decide) rfl
    (by simp +decide [ctxLocals, bcLocals]) hcp
    ⟨rfl, by cases r <;> simp +decide [sev, Env.get, bcParams, ctxEnv, rWords], trivial⟩
    (PostPST (ctxH C H) coreWalkFuel) (fun o w _ _ => w = optW o ∧ ∀ n, o = some n → n < coreWalkFuel)
    (fun o w s' st ⟨H', hp', hs', h1', h2'⟩ => ⟨H', hp', ⟨h1', h2'⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (pbc_spec C hcp coreWalkFuel (by decide) H s cvT.type))
    (fun o w s1 H1 hp1 ⟨hw, hbd⟩ => ?_)
  have hcw : coreWalkFuel < 2 ^ 63 := by decide
  have hpH : H <+: H1 := hp1
  let Γ0 : Env := ctxEnv (ctxH C H) ++ bcParams.zip ([BitVec.ofNat 64 nPd, BitVec.ofNat 64 k, BitVec.ofNat 64 nC,
    BitVec.ofNat 64 nR, Enc.idxW cvT.type] ++ rWords r)
  have gNP : Γ0.get bcNP = some (BitVec.ofNat 64 nPd) := by cases r <;> simp +decide [Γ0, Env.get, bcParams, ctxEnv, rWords]
  have gK : Γ0.get bcK = some (BitVec.ofNat 64 k) := by cases r <;> simp +decide [Γ0, Env.get, bcParams, ctxEnv, rWords]
  have gNC : Γ0.get bcNC = some (BitVec.ofNat 64 nC) := by cases r <;> simp +decide [Γ0, Env.get, bcParams, ctxEnv, rWords]
  have gNR : Γ0.get bcNR = some (BitVec.ofNat 64 nR) := by cases r <;> simp +decide [Γ0, Env.get, bcParams, ctxEnv, rWords]
  rcases o with _ | n
  · -- the telescope ends in no sort: the recursor's counts
    subst hw
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    rcases r with _ | ⟨mI, rP⟩
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Γ0, Env.get, bcParams, ctxEnv, rWords,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨hmI, hrP⟩ := hr mI rP rfl
    have gHas : Γ0.get bcHas = some 1 := by simp +decide [Γ0, Env.get, bcParams, ctxEnv, rWords]
    have gMI : Γ0.get bcMI = some (BitVec.ofNat 64 mI) := by simp +decide [Γ0, Env.get, bcParams, ctxEnv, rWords]
    have gRP : Γ0.get bcRP = some (BitVec.ofNat 64 rP) := by simp +decide [Γ0, Env.get, bcParams, ctxEnv, rWords]
    let Γ1 : Env := (bcV, (0 : BitVec 64)) :: Γ0
    have L : ∀ y, y ≠ bcV → Env.get Γ1 y = Env.get Γ0 y := fun y h => by
      simp only [Γ1, Env.get_cons, ite_eq_right h]
    have sv : ∀ (x : MlS) (v : Nat), x ≠ bcV → Env.get Γ0 x = some (BitVec.ofNat 64 v) →
        sev Γ1 (vv x) = some (BitVec.ofNat 64 v) := fun x v hx hg => by simp only [sev, sev_vv, L x hx, hg]
    refine specR_ifI _ (boolW (1 == 0)) (ConPanqueque.T.WC.sev_eqNatB (by decide) (by decide)
        (sv bcHas 1 (by decide) gHas) rfl) (fun h => absurd rfl h) (fun _ => ?_)
    have hsum : sev Γ1 (.op .add [vv bcNC, vv bcK]) = some (BitVec.ofNat 64 (nC + k)) := by
      simp only [sev, sev_vv, L bcNC (by decide), L bcK (by decide), gNC, gK, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, ofNat_add_small nC k (by omega)]
    simp only [unwrapE, bcTail, bind_pure_comp]
    refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ1 (vv bcRP) _ rP (nC + k) (sv bcRP rP (by decide) gRP) hsum
      (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
    · exact specR_hangI
    have c1 : ¬ rP < nC + k := by intro c; simp [bw, c] at h
    refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ1 (vv bcMI) (vv bcRP) mI rP (sv bcMI mI (by decide) gMI)
      (sv bcRP rP (by decide) gRP) (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
    · exact specR_hangI
    have c2 : ¬ mI < rP := by intro c; simp [bw, c] at h
    have hc12 : (decide (rP < nC + k) || decide (mI < rP)) = false := by simp [c1, c2]
    simp only [hc12, Bool.false_eq_true, ite_false]
    have hsub : sev Γ1 (.op .sub [vv bcRP, .op .add [vv bcNC, vv bcK]]) = some (BitVec.ofNat 64 (rP - (nC + k))) := by
      simp only [sev, sev_vv, L bcRP (by decide), gRP] at hsum ⊢; rw [hsum]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, ofNat_sub_small rP (nC + k) (by omega) (by omega)]
    have hmr : sev Γ1 (.op .sub [vv bcMI, vv bcRP]) = some (BitVec.ofNat 64 (mI - rP)) := by
      simp only [sev, sev_vv, L bcRP (by decide), gRP, L bcMI (by decide), gMI, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, ofNat_sub_small mI rP (by omega) (by omega)]
    have retOk : SpecR (σ := σ) (Inv (ctxH (ctxH C H) H1) s1 Γ1 [] (ctxLocals ++ bcLocals))
        (.return (.op .sub [vv bcMI, vv bcRP])) s1 (pure (nPd, mI - rP)) (PostBC (ctxH C H)) :=
      specR_returnI _ _ hmr (fun t ht => ⟨H1, hpH, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, by omega⟩)
    refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (by omega) (by omega) hsub (sv bcNP nPd (by decide) gNP))
      (fun h => ?_) (fun h => ?_)
    · have c3 : rP - (nC + k) = nPd := by by_cases c : rP - (nC + k) = nPd; exact c; simp [boolW, c] at h
      simp only [c3, beq_self_eq_true, ite_true]
      exact retOk
    have c3 : ¬ rP - (nC + k) = nPd := by intro c; simp [boolW, c] at h
    have hb3 : (rP - (nC + k) == nPd) = false := by simpa using c3
    simp only [hb3, Bool.false_eq_true, ite_false]
    refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ1 (vv bcK) (vv bcNR) k nR (sv bcK k (by decide) gK)
      (sv bcNR nR (by decide) gNR) (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
    · have c4 : k < nR := by by_cases c : k < nR; exact c; simp [bw, c] at h
      have hsum2 : sev Γ1 (.op .add [vv bcNP, .op .add [vv bcNR, vv bcNC]]) = some (BitVec.ofNat 64 (nPd + (nR + nC))) := by
        simp only [sev, sev_vv, L bcNP (by decide), L bcNR (by decide), L bcNC (by decide), gNP, gNR, gNC,
          Option.bind_eq_bind, Option.bind_some, Option.pure_def, ofNat_add_small nR nC (by omega),
          ofNat_add_small nPd (nR + nC) (by omega)]
      refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ1 (vv bcRP) _ rP (nPd + (nR + nC)) (sv bcRP rP (by decide) gRP)
        hsum2 (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
      · exact specR_hangI
      have c5 : ¬ rP < nPd + (nR + nC) := by intro c; simp [bw, c] at h
      have hb45 : (decide (k < nR) && decide (nPd + nR + nC ≤ rP)) = true := by simp [c4]; omega
      simp only [hb45, ite_true]
      exact retOk
    · exact specR_hangI
  · -- the telescope ends in a sort after `n` binders
    subst hw
    have hn := hbd n rfl
    have hne : optW (some n) ≠ 0 := by
      simp only [optW]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 1 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI bcN (.op .sub [vv bcV, .const 1]) (BitVec.ofNat 64 n) (by simp +decide [ctxLocals, bcLocals])
      (by simp [sev, Env.get_cons, optW]; exact ofNat_succ_sub_one n) ?_
    let Γ2 : Env := (bcN, BitVec.ofNat 64 n) :: (bcV, optW (some n)) :: Γ0
    have gNP2 : sev Γ2 (vv bcNP) = some (BitVec.ofNat 64 nPd) := by
      show sev ((bcN, BitVec.ofNat 64 n) :: (bcV, optW (some n)) :: Γ0) (vv bcNP) = _
      rw [sev_vv, Env.get_cons, ite_eq_right (show bcNP ≠ bcN by decide), Env.get_cons,
        ite_eq_right (show bcNP ≠ bcV by decide)]; exact gNP
    have gN2 : sev Γ2 (vv bcN) = some (BitVec.ofNat 64 n) := by simp [Γ2, sev, sev_vv, Env.get_cons]
    simp only [unwrapE, bcTail]
    refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ2 (vv bcN) (vv bcNP) n nPd gN2 gNP2 (by omega) (by omega))
      (fun h => ?_) (fun h => ?_)
    · exact specR_hangI
    have c : nPd ≤ n := by by_cases c : n < nPd; simp [bw, c] at h; omega
    simp only [c, ite_true, bind_pure_comp, pure_bind]
    refine specR_returnI _ (BitVec.ofNat 64 (n - nPd)) (by
        show sev Γ2 (.op .sub [vv bcN, vv bcNP]) = _
        simp only [sev] at gN2 gNP2 ⊢; simp only [gN2, gNP2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          ofNat_sub_small n nPd c (by omega)])
      (fun t ht => ⟨H1, hpH, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, by omega⟩)

end

end ConPanqueque.T.Ind
