import ConPanqueque.T.Ind.RecTarget
import ConPanqueque.T.Ind.SplitLemma

/-!
# The recursor whose major names a member

`blockMemberCounts` hands `blockCounts` the first recursor (in the stream's order) whose major premise names
member `m` (`rs.findM? (recTargetOf … == m)`).  `findRec(p, j, n, k, m)` walks the recursor records from index
`j` below `n` and returns the first such index, `n` when none.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP

/-- The twin's test on one recursor tuple. -/
def recNames (blk : List IConstantInfo) (k : Nat) : List NIdx := (blk.take k).map (fun (c : IConstantInfo) => c.name)

def recIs (names : List NIdx) (m : Nat) (q : IConstantVal × Nat × Nat × Bool × List IRecRule) : AM Bool := do
  pure ((← recTargetOf names q.2.1 q.1.type) == m)

def frP := ofString "fr_p"
def frJ := ofString "fr_j"
def frN := ofString "fr_n"
def frK := ofString "fr_k"
def frM := ofString "fr_m"
def frQ := ofString "fr_q"
def frI := ofString "fr_i"
def frT := ofString "fr_t"
def frR := ofString "fr_r"
def fFindRec := ofString "findRec"

def frParams : List MlS := [frP, frJ, frN, frK, frM]
def frLocals : List MlS := [frQ, frI, frT, frR]

def frBody : ProgHOL 64 := prologue frLocals
  (.ite (.cmp .lower (vv frJ) (vv frN))
    (.seq (.assign .local frQ (.load .one (.op .add [vv frP, .op .add [.panop .mul [vv frJ, .const 8], .const 8]])))
    (.seq (.assign .local frI (.load .one (.op .add [vv frQ, .const (BitVec.ofNat 64 (8 * 4))])))
    (.seq (.assign .local frT (.load .one (.op .add [vv frQ, .const (BitVec.ofNat 64 (8 * 3))])))
    (.seq (.call (some (some (.local, frR), none)) fRecTarget [vv frP, vv frK, vv frI, vv frT])
    (.ite (.cmp .equal (vv frR) (vv frM)) (.return (vv frJ))
      (.seq (.call (some (some (.local, frR), none)) fFindRec [vv frP, .op .add [vv frJ, .const 1], vv frN, vv frK, vv frM])
        (.return (vv frR))))))))
    (.return (vv frN)))

section
variable {σ : Type}

/-- The post: the word is the index of the found recursor (`n` when none), the twin's answer its tuple. -/
def PostFR (C : Ctx) (blk : List IConstantInfo) (j0 n : Nat) (a : Option (IConstantVal × Nat × Nat × Bool × List IRecRule))
    (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧
    ((a = none ∧ w = BitVec.ofNat 64 n) ∨
      ∃ r, ∃ hr : r < blk.length, j0 ≤ r ∧ r < n ∧ a = some (recT blk[r]) ∧ w = BitVec.ofNat 64 r)

theorem postFR_locals (C : Ctx) (blk : List IConstantInfo) (j0 n : Nat) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostFR C blk j0 n a w s' st → PostFR C blk j0 n a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem fr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ frLocals → (ctxEnv C ++ frParams.zip vals).get x = none :=
  Knot.params_none C frLocals frParams vals (by decide) (by decide)

theorem findM_cons {α : Type} (p : α → AM Bool) (a : α) (as : List α) :
    List.findM? p (a :: as) = (do if ← p a then pure (some a) else List.findM? p as) := by
  simp only [List.findM?]; congr 1; funext b; cases b <;> rfl

theorem recT_rec {cvR : IConstantVal} {mI rP : Nat} {isK : Bool} {rules : List IRecRule} :
    recT (.recInfo cvR mI rP isK rules) = (cvR, mI, rP, isK, rules) := rfl

/-- **`findRec`** over the recursor records from index `j` (all of kind `5`). -/
theorem fr_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fFindRec = some (frParams.map (fun p => (p, ShapeHOL.one)), frBody, .one))
    (hcr : C.code.lookup fRecTarget = some (rtParams.map (fun p => (p, ShapeHOL.one)), rtBody C, .one))
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k m : Nat) (hk : k ≤ blk.length) (hlen : blk.length < 2 ^ 59) (hm : m < 2 ^ 63) :
    ∀ f j (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → blk.length - j = f →
      j ≤ blk.length → (∀ i, j ≤ i → i < blk.length → kindAt blk i = some 5) →
      SpecR (σ := σ) (Pre (ctxH C H) s (frParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 blk.length,
        BitVec.ofNat 64 k, BitVec.ofNat 64 m])) frBody s
        (List.findM? (recIs (recNames blk k) m) ((blk.drop j).map recT)) (PostFR (ctxH C H) blk j blk.length) := by
  intro f
  induction f with
  | zero =>
    intro j H s hp hb hf hj hkd
    have hjl : j = blk.length := by omega
    subst hjl
    refine specR_prologue (postFR_locals _ _ _ _) (fr_none _ _) ?_
    have hlw := nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, frParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, List.map_nil]
    exact specR_returnI _ (BitVec.ofNat 64 blk.length) (by simp +decide [sev, Env.get, frParams, ctxEnv])
      (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl, Or.inl ⟨by simp [List.findM?], rfl⟩⟩)
  | succ f ih =>
    intro j H s hp hb hf hj hkd
    have hjl : j < blk.length := by omega
    obtain ⟨os, hosl, hblk, hcie⟩ := id hb
    have hoj : j < os.length := by omega
    refine specR_prologue (postFR_locals _ _ _ _) (fr_none _ _) ?_
    have hlw := nd_lt_iff j blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, frParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[ob + 1 + j]? = some (cellA C os[j]) := by
      show H[ob + 1 + j]? = _
      have := hblk.2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) frQ _ (ob + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, frParams, ctxEnv]; exact cellA_mulIdx C ob j (by omega)) ?_
    have hk5 := hkd j (le_refl _) hjl
    have hci := hcie j hjl hoj
    generalize hcj : blk[j] = ci at hci hk5
    cases ci with
    | recInfo cvR mI rP isK rules =>
      obtain ⟨hcv, -, ⟨hmi, hmi63⟩, -, -, -⟩ := hci
      have hsQ : ∀ (Γ : Env), Γ.get frQ = some (cellA C os[j]) → ∀ q, sev Γ (.op .add [vv frQ, .const (BitVec.ofNat 64 (8 * q))]) =
          some (cellA C (os[j] + q)) := by
        intro Γ hq q; simp only [sev, sev_vv, hq]; simp; exact cellA_plus C _ q
      refine UD.specR_heapLoadI' (C := ctxH C H) frI _ (os[j] + 4) _ hmi (by decide)
        (hsQ _ (by simp [Env.get_cons]) 4) ?_
      have hty : (ctxH C H).H[os[j] + 3]? = some (Enc.idxW cvR.type) := by
        have := hcv.2.2; rw [show os[j] + 1 + 2 = os[j] + 3 by omega] at this; exact this
      refine UD.specR_heapLoadI' (C := ctxH C H) frT _ (os[j] + 3) _ hty (by decide)
        (hsQ _ (by simp +decide [Env.get_cons]) 3) ?_
      rw [List.drop_eq_getElem_cons hjl, hcj, List.map_cons, findM_cons, recT_rec]
      refine specR_congr (m' := recTargetOf (recNames blk k) mI cvR.type >>= fun t =>
          if (t == m) = true then pure (some (cvR, mI, rP, isK, rules))
          else List.findM? (recIs (recNames blk k) m) ((blk.drop (j + 1)).map recT))
        (by simp only [recIs, bind_assoc, pure_bind]) ?_
      refine specR_callNIH (C := ctxH C H) frR fRecTarget rtParams [vv frP, vv frK, vv frI, vv frT] (rtBody C)
        [cellA C ob, BitVec.ofNat 64 k, BitVec.ofNat 64 mI, Enc.idxW cvR.type] (by decide) rfl
        (by simp +decide [ctxLocals, frLocals]) hcr
        ⟨by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv],
          by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
        (fun a w s' st => PostN (ctxH C H) a w s' st ∧ a ≤ k) (fun t w _ _ => w = BitVec.ofNat 64 t ∧ t ≤ k)
        (fun t w s' st ⟨⟨H', hp', hw', hsr⟩, htk⟩ => ⟨H', hp', ⟨hw', htk⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rtParams _ rfl hlk)
          (rt_spec C hok hcs hcg hcn blk ob k mI cvR.type hk hlen (by omega) H s hp hb))
        (fun t w s1 H1 hp1 ⟨hw', htk⟩ => ?_)
      subst hw'
      have hpH : H <+: H1 := hp1
      refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (x := t) (y := m) (by omega) (by omega)
          (by simp [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv]))
        (fun h => ?_) (fun h => ?_)
      · have htm : t = m := by by_cases c : t = m; exact c; simp [boolW, c] at h
        simp only [htm, beq_self_eq_true, ite_true]
        exact specR_returnI _ (BitVec.ofNat 64 j) (by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv])
          (fun t' ht' => ⟨H1, hpH, sr_of_eq ht'.sr rfl rfl rfl rfl,
            Or.inr ⟨j, hjl, le_refl _, hjl, by rw [hcj, recT_rec], rfl⟩⟩)
      · have htm : t ≠ m := by intro c; simp [boolW, c] at h
        have hbt : (t == m) = false := by simpa using htm
        simp only [hbt, Bool.false_eq_true, ite_false]
        refine specR_congr (m' := List.findM? (recIs (recNames blk k) m) ((blk.drop (j + 1)).map recT) >>= fun r => pure r)
          (by simp) ?_
        refine specR_callNIH (C := ctxH C H1) frR fFindRec frParams
          [vv frP, .op .add [vv frJ, .const 1], vv frN, vv frK, vv frM] frBody
          [cellA C ob, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 blk.length, BitVec.ofNat 64 k, BitVec.ofNat 64 m]
          (by decide) rfl (by simp +decide [ctxLocals, frLocals]) hc
          ⟨by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv],
            by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv]; exact word_add1_eq j,
            by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv],
            by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv],
            by simp +decide [sev, Env.get_cons, Env.get, frParams, ctxEnv], trivial⟩
          (PostFR (ctxH C H1) blk (j + 1) blk.length) (fun a w _ _ => (a = none ∧ w = BitVec.ofNat 64 blk.length) ∨
            ∃ r, ∃ hr : r < blk.length, j ≤ r ∧ r < blk.length ∧ a = some (recT blk[r]) ∧ w = BitVec.ofNat 64 r)
          (fun a w s' st ⟨H', hp', hs', h'⟩ => ⟨H', hp', by
            rcases h' with h1 | ⟨r, hr, h1, h2, h3, h4⟩
            · exact Or.inl h1
            · exact Or.inr ⟨r, hr, by omega, h2, h3, h4⟩, hs'⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu frParams _ rfl hlk)
            (ih (j + 1) H1 s1 (hp.trans hpH) (indBlk_mono hb hpH) (by omega) (by omega)
              (fun i hi hl => hkd i (by omega) hl)))
          (fun a w s2 H2 hp2 hq => ?_)
        exact specR_returnI _ w (by simp [sev, Env.get_cons])
          (fun t' ht' => ⟨H2, hpH.trans hp2, sr_of_eq ht'.sr rfl rfl rfl rfl, hq⟩)
    | _ => simp [kindAt, List.getElem?_eq_getElem hjl, hcj, kindOf] at hk5

end

end ConPanqueque.T.Ind
