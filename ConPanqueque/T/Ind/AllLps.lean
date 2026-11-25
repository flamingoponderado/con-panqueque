import ConPanqueque.T.Ind.LpsEq
import ConPanqueque.T.Ind.SplitLemma

/-!
# Every record declares the block's universe parameters (and parameter count)

`readBlock` checks that every inductive type declares the first type's universe parameters, and that every
constructor declares the block's parameter count and the same universe parameters.  `allLps(p, j, n, l0, c, nP)`
walks the records `j … n - 1`: each one's universe parameters equal the list at `l0` (`lpsEq`), and when `c ≠ 0`
its parameter count (a constructor record's field) is `nP`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- One record's test. -/
def lpsOk (lps0 : List NIdx) (chk : Bool) (nP : Nat) (c : IConstantInfo) : Bool :=
  (c.toConstantVal.levelParams == lps0) && (!chk || (ctorT c).2.1 == nP)

def alP := ofString "al_p"
def alJ := ofString "al_j"
def alN := ofString "al_n"
def alL := ofString "al_l"
def alC := ofString "al_c"
def alNP := ofString "al_np"
def alQ := ofString "al_q"
def alW := ofString "al_w"
def alR := ofString "al_r"
def fAllLps := ofString "allLps"

def alParams : List MlS := [alP, alJ, alN, alL, alC, alNP]
def alLocals : List MlS := [alQ, alW, alR]

def alCont : ProgHOL 64 :=
  .seq (.call (some (some (.local, alR), none)) fAllLps [vv alP, .op .add [vv alJ, .const 1], vv alN, vv alL, vv alC, vv alNP])
    (.return (vv alR))

def alBody : ProgHOL 64 := prologue alLocals
  (.ite (.cmp .lower (vv alJ) (vv alN))
    (.seq (.assign .local alQ (.load .one (.op .add [vv alP, .op .add [.panop .mul [vv alJ, .const 8], .const 8]])))
    (.seq (.assign .local alW (.load .one (.op .add [vv alQ, .const (BitVec.ofNat 64 (8 * 2))])))
    (.seq (.call (some (some (.local, alR), none)) fLpsEq [vv alW, vv alL])
    (.ite (.cmp .equal (vv alR) (.const 0)) (.return (.const 0))
      (.ite (.cmp .equal (vv alC) (.const 0)) alCont
        (.seq (.assign .local alW (.load .one (.op .add [vv alQ, .const (BitVec.ofNat 64 (8 * 4))])))
          (.ite (.cmp .equal (vv alW) (vv alNP)) alCont (.return (.const 0)))))))))
    (.return (.const 1)))

section
variable {σ : Type}

theorem al_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ alLocals → (ctxEnv C ++ alParams.zip vals).get x = none :=
  Knot.params_none C alLocals alParams vals (by decide) (by decide)

theorem all_drop_succ {f : IConstantInfo → Bool} {l : List IConstantInfo} {j n : Nat} (hj : j < n) (hn : n ≤ l.length) :
    ((l.drop j).take (n - j)).all f = (f (l[j]'(by omega)) && ((l.drop (j + 1)).take (n - (j + 1))).all f) := by
  rw [List.drop_eq_getElem_cons (by omega), show n - j = (n - (j + 1)) + 1 by omega, List.take_succ_cons,
    List.all_cons]

theorem enlist_cell {C : Ctx} {H : List (BitVec 64)} {w : BitVec 64} {xs : List NIdx} (h : ENList C.HB H w xs) :
    ∃ o, w = cellA C o ∧ EBlk H o (xs.map Enc.idxW) := h

/-- **`allLps`** over records `j … n - 1`. -/
theorem al_spec (C : Ctx) (hc : C.code.lookup fAllLps = some (alParams.map (fun p => (p, ShapeHOL.one)), alBody, .one))
    (hce : C.code.lookup fLpsEq = some (leParams.map (fun p => (p, ShapeHOL.one)), leBody, .one))
    (hcg : C.code.lookup fLpsEqGo = some (legParams.map (fun p => (p, ShapeHOL.one)), legBody, .one))
    (blk : List IConstantInfo) (ob ol n nP : Nat) (lps0 : List NIdx) (chk : Bool) (hn : n ≤ blk.length)
    (hlen : blk.length < 2 ^ 59) (hl0 : lps0.length < 2 ^ 59) (hnP : nP < 2 ^ 63)
    (hlp : ∀ i (hi : i < blk.length), blk[i].toConstantVal.levelParams.length < 2 ^ 59) :
    ∀ f j (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → EBlk H ol (lps0.map Enc.idxW) →
      n - j = f → j ≤ n → (chk = true → ∀ i, j ≤ i → i < n → kindAt blk i = some 4) →
      SpecR (σ := σ) (Pre (ctxH C H) s (alParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 n, cellA C ol,
        (if chk then 1 else 0), BitVec.ofNat 64 nP])) alBody s (pure (((blk.drop j).take (n - j)).all (lpsOk lps0 chk nP)))
        (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j H s hp hb hl hf hj hk4
    have hjn : j = n := by omega
    subst hjn
    refine specR_prologue (postB_locals _) (al_none _ _) ?_
    have hlw := nd_lt_iff j j (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, alParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Nat.sub_self, List.take_zero, List.all_nil]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hp hb hl hf hj hk4
    have hjn : j < n := by omega
    have hjl : j < blk.length := by omega
    obtain ⟨os, hosl, hblk, hcie⟩ := id hb
    have hoj : j < os.length := by omega
    refine specR_prologue (postB_locals _) (al_none _ _) ?_
    have hlw := nd_lt_iff j n (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, alParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjn])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[ob + 1 + j]? = some (cellA C os[j]) := by
      show H[ob + 1 + j]? = _
      have := hblk.2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) alQ _ (ob + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, alParams, ctxEnv]; exact cellA_mulIdx C ob j (by omega)) ?_
    have hci := hcie j hjl hoj
    obtain ⟨wl, hwl, hen⟩ := hci.1.2.1
    obtain ⟨olj, rfl, heb⟩ := enlist_cell hen
    have hwl' : (ctxH C H).H[os[j] + 2]? = some (cellA C olj) := by
      show H[os[j] + 2]? = _; rw [show os[j] + 2 = os[j] + 1 + 1 by omega]; exact hwl
    refine UD.specR_heapLoadI' (C := ctxH C H) alW _ (os[j] + 2) _ hwl' (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp; exact cellA_plus C _ 2) ?_
    rw [all_drop_succ hjn hn]
    let Γ0 : Env := ctxEnv (ctxH C H) ++ alParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 n, cellA C ol,
      (if chk then 1 else 0), BitVec.ofNat 64 nP]
    have cont : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env), H <+: H1 →
        (∀ y, y ∈ alParams → Env.get Γ y = Env.get Γ0 y) →
        SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ alLocals)) alCont s1
          (pure (((blk.drop (j + 1)).take (n - (j + 1))).all (lpsOk lps0 chk nP))) (PostB (ctxH C H)) := by
      intro H1 s1 Γ hp1 hΓ
      have g : ∀ y v, y ∈ alParams → Env.get Γ0 y = some v → sev Γ (vv y) = some v := fun y v hy h => by
        simp only [sev, sev_vv, hΓ y hy, h]
      refine specR_congr (m' := (pure (((blk.drop (j + 1)).take (n - (j + 1))).all (lpsOk lps0 chk nP)) : AM Bool) >>=
        fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) alR fAllLps alParams
        [vv alP, .op .add [vv alJ, .const 1], vv alN, vv alL, vv alC, vv alNP] alBody
        [cellA C ob, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 n, cellA C ol, (if chk then 1 else 0), BitVec.ofNat 64 nP]
        (by decide) rfl (by simp +decide [ctxLocals, alLocals]) hc
        ⟨g alP _ (by decide) (by simp +decide [Γ0, Env.get, alParams, ctxEnv]),
          by have := g alJ (BitVec.ofNat 64 j) (by decide) (by simp +decide [Γ0, Env.get, alParams, ctxEnv])
             simp only [sev] at this ⊢; rw [this]; simp; exact word_add1_eq j,
          g alN _ (by decide) (by simp +decide [Γ0, Env.get, alParams, ctxEnv]),
          g alL _ (by decide) (by simp +decide [Γ0, Env.get, alParams, ctxEnv]),
          g alC _ (by decide) (by simp +decide [Γ0, Env.get, alParams, ctxEnv]),
          g alNP _ (by decide) (by simp +decide [Γ0, Env.get, alParams, ctxEnv]), trivial⟩
        (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw', hsr⟩ => ⟨H', hp', hw', hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu alParams _ rfl hlk)
          (ih (j + 1) H1 s1 (hp.trans hp1) (indBlk_mono hb hp1) (Decl.eblk_mono hp1 hl) (by omega) (by omega)
            (fun hc i h1 h2 => hk4 hc i (by omega) h2)))
        (fun b w s2 H2 hp2 hw' => ?_)
      subst hw'
      exact specR_returnI _ (boolW b) (by simp +decide [Env.get])
        (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_congr (m' := (pure (blk[j].toConstantVal.levelParams == lps0) : AM Bool) >>= fun r =>
        if r then pure ((!chk || (ctorT blk[j]).2.1 == nP) && ((blk.drop (j + 1)).take (n - (j + 1))).all (lpsOk lps0 chk nP))
        else pure false)
      (by cases h : (blk[j].toConstantVal.levelParams == lps0) <;> simp [lpsOk, h]) ?_
    refine specR_callNIH (C := ctxH C H) alR fLpsEq leParams [vv alW, vv alL] leBody [cellA C olj, cellA C ol]
      (by decide) rfl (by simp +decide [ctxLocals, alLocals]) hce
      ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, alParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw', hsr⟩ => ⟨H', hp', hw', hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu leParams _ rfl hlk)
        (le_spec C hcg hce _ lps0 olj ol (hlp j hjl) hl0 H s hp heb hl))
      (fun b w s1 H1 hp1 hw' => ?_)
    subst hw'
    have hpH : H <+: H1 := hp1
    let Γb : Env := (alR, boolW b) :: (alW, cellA C olj) :: (alQ, cellA C os[j]) :: Γ0
    have hΓb : ∀ y, y ∈ alParams → Env.get Γb y = Env.get Γ0 y := by
      intro y hy
      simp only [alParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      have h1 : y ≠ alR := by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      have h2 : y ≠ alW := by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      have h3 : y ≠ alQ := by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simp only [Γb, Env.get_cons, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
    cases b with
    | false =>
      refine specR_ifI _ 1 (by simp [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hpH, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | true =>
      refine specR_ifI _ 0 (by simp [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [ite_true]
      have gC : sev Γb (vv alC) = some (if chk then 1 else 0) := by
        simp only [sev, sev_vv, hΓb alC (by decide)]; simp +decide [Γ0, Env.get, alParams, ctxEnv]
      cases chk with
      | false =>
        refine specR_ifI _ 1 (by
            show sev Γb (.cmp .equal (vv alC) (.const 0)) = _
            simp only [sev] at gC ⊢; rw [gC]; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [Bool.not_false, Bool.true_or, Bool.true_and]
        exact cont H1 s1 Γb hpH hΓb
      | true =>
        refine specR_ifI _ 0 (by
            show sev Γb (.cmp .equal (vv alC) (.const 0)) = _
            simp only [sev] at gC ⊢; rw [gC]; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        have hk := hk4 rfl j (le_refl _) hjn
        have hci1 := hcie j hjl hoj
        generalize hcj : blk[j] = ci at hci1 hk
        cases ci with
        | ctorInfo cvC np nf ind =>
          obtain ⟨-, -, ⟨hnp, hnp63⟩, -⟩ := hci1
          have hnp' : (ctxH C H1).H[os[j] + 4]? = some (BitVec.ofNat 64 np) := get_prefix hnp hpH
          refine UD.specR_heapLoadI' (C := ctxH C H1) alW _ (os[j] + 4) _ hnp' (by decide)
            (by simp +decide only [sev, sev_vv, Env.get_cons, Γb]; simp; exact cellA_plus C _ 4) ?_
          have gNP : sev ((alW, BitVec.ofNat 64 np) :: Γb) (vv alNP) = some (BitVec.ofNat 64 nP) := by
            simp only [sev, sev_vv, Env.get_cons, ite_eq_right (show alNP ≠ alW by decide), hΓb alNP (by decide)]
            simp +decide [Γ0, Env.get, alParams, ctxEnv]
          refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (x := np) (y := nP) (by omega) (by omega)
            (by simp [sev, Env.get_cons]) gNP) (fun h => ?_) (fun h => ?_)
          · have he : np = nP := by by_cases c : np = nP; exact c; simp [boolW, c] at h
            simp only [ctorT, he, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.true_and]
            exact cont H1 s1 _ hpH (fun y hy => by
              have h1 : y ≠ alW := by
                simp only [alParams, List.mem_cons, List.not_mem_nil, or_false] at hy
                rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
              rw [Env.get_cons, ite_eq_right h1]; exact hΓb y hy)
          · have he : np ≠ nP := by intro c; simp [boolW, c] at h
            have hb' : (np == nP) = false := by simpa using he
            simp only [ctorT, hb', Bool.not_true, Bool.false_or, Bool.false_and]
            exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hpH, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        | _ => simp [kindAt, List.getElem?_eq_getElem hjl, hcj, kindOf] at hk

end

end ConPanqueque.T.Ind
