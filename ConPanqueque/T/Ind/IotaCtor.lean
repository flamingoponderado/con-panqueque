import ConPanqueque.T.Ind.IotaParts

/-!
# A rule's parts, read through its constructor (the parameters)

`iotaBVars rP n i`: the prefix variables `bvar (rP - 1 - j)` for `j` from `i` below `n`, as a block.
`iotaParamsAt rl rP cnP`: a nested rule's recorded parameters, else the prefix's first `min cnP rP` variables.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.Decl
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.ExSP

def ibR := ofString "ib_r"
def ibN := ofString "ib_n"
def ibI := ofString "ib_i"
def fIotaBVars := ofString "iotaBVars"

def ibParams : List MlS := [ibR, ibN, ibI]

def ibBody (C : Ctx) : ProgHOL 64 := prologue gaaLocals
  (.ite (.cmp .lower (vv ibI) (vv ibN))
    (.seq (.call (some (some (.local, lA1), none)) fInternBVar [.op .sub [.op .sub [vv ibR, .const 1], vv ibI]])
    (.seq (.call (some (some (.local, ExS.lY), none)) fIotaBVars [vv ibR, vv ibN, .op .add [vv ibI, .const 1]])
      (prependP C lA1)))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem ib_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ ibParams.zip vals).get x = none :=
  Knot.params_none C gaaLocals ibParams vals (by decide) (by decide)

/-- **`iotaBVars`** from `i`. -/
theorem ib_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fIotaBVars = some (ibParams.map (fun p => (p, ShapeHOL.one)), ibBody C, .one))
    (hcb : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (rP n : Nat) (hn : n ≤ rP) (hr : rP < 2 ^ 62) :
    ∀ f i (H : List (BitVec 64)) (s : AState), n - i = f → i ≤ n →
      SpecR (σ := σ) (Pre (ctxH C H) s (ibParams.zip [BitVec.ofNat 64 rP, BitVec.ofNat 64 n, BitVec.ofNat 64 i]))
        (ibBody C) s (iotaBVars rP n i) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi
    have hin : i = n := by omega
    subst hin
    refine specR_prologue (postA_locals _) (ib_none _ _) ?_
    rw [iotaBVars, if_neg (by omega)]
    have hlw := nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ibParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by simp +decide [ctxLocals, gaaLocals, inst1Locals])
      (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    exact specR_returnI _ _ (by simp [sev] <;> rfl) (fun t ht => ⟨_, H2.length, hp2.trans (img1_prefix _ _ _ hws), rfl,
      ⟨by simpa using img1_get H2 ws (0 : BitVec 64) hws, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi
    have hin : i < n := by omega
    refine specR_prologue (postA_locals _) (ib_none _ _) ?_
    rw [iotaBVars, if_pos hin]
    have hlw := nd_lt_iff i n (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ibParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_internBVarI ra (ctxOK_H hok H) hcb lA1 _ (rP - 1 - i) (by omega)
      (by simp +decide [ctxLocals, gaaLocals, inst1Locals])
      (by simp +decide [sev, Env.get, ibParams, ctxEnv]
          rw [ConPanqueque.T.ExP.word_sub_eq rP 1 (by omega) (by omega), ConPanqueque.T.ExP.word_sub_eq _ i (by omega) (by omega)])
      (fun b s1 => ?_)
    refine specR_congr (m' := iotaBVars rP n (i + 1) >>= fun rest => pure (b :: rest)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fIotaBVars ibParams [vv ibR, vv ibN, .op .add [vv ibI, .const 1]]
      (ibBody C) [BitVec.ofNat 64 rP, BitVec.ofNat 64 n, BitVec.ofNat 64 (i + 1)] (by decide) rfl
      (by simp +decide [ctxLocals, gaaLocals, inst1Locals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ibParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ibParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ibParams, ctxEnv]; exact word_add1_eq i, trivial⟩
      (PostA (ctxH C H)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibParams _ rfl hlk)
        (ih (i + 1) H s1 (by omega) (by omega)))
      (fun ys wr s2 H2 hp2 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    exact prepend_spec C hok lA1 (Enc.idxW b) oy _ (by simp +decide [ctxLocals, gaaLocals, inst1Locals])
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hblk (by decide)
      (by simp +decide [Env.get_cons, Env.get, ibParams, ctxEnv]) (by decide)
      (fun H' o t hpH hbk hsr => ⟨H', o, hp2.trans hpH, rfl, by simpa using hbk, hsr⟩)

end

def paQ := ofString "pa_q"
def paR := ofString "pa_r"
def paC := ofString "pa_c"
def paT := ofString "pa_t"
def paM1 := ofString "pa_m1"
def paM := ofString "pa_m"
def paX := ofString "pa_x"
def fIotaParams := ofString "iotaParamsAt"

def paParams : List MlS := [paQ, paR, paC]
def paLocals : List MlS := [paT, paM1, paM, paX]

def paBody : ProgHOL 64 := prologue paLocals
  (.seq (.assign .local paT (.load .one (.op .add [vv paQ, .const 16])))
  (.ite (.cmp .equal (vv paT) (.const 1))
    (.seq (.assign .local paX (.load .one (.op .add [vv paQ, .const 32]))) (.return (vv paX)))
    (.seq (.call (some (some (.local, paM1), none)) fTSub [vv paC, vv paR])
    (.seq (.call (some (some (.local, paM), none)) fTSub [vv paC, vv paM1])
    (.seq (.call (some (some (.local, paX), none)) fIotaBVars [vv paR, vv paM, .const 0])
      (.return (vv paX)))))))

section
variable {σ : Type}

theorem pa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ paLocals → (ctxEnv C ++ paParams.zip vals).get x = none :=
  Knot.params_none C paLocals paParams vals (by decide) (by decide)

/-- **`iotaParamsAt`**, the rule a record at `oq`. -/
theorem pa_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fIotaParams = some (paParams.map (fun p => (p, ShapeHOL.one)), paBody, .one))
    (hcs : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one))
    (hci : C.code.lookup fIotaBVars = some (ibParams.map (fun p => (p, ShapeHOL.one)), ibBody C, .one))
    (hcb : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (rl : IRecRule) (oq rP cnP : Nat) (hr : rP < 2 ^ 62) (hc' : cnP < 2 ^ 62)
    (H : List (BitVec 64)) (hq : RuleE C.HB H oq rl) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (paParams.zip [cellA C oq, BitVec.ofNat 64 rP, BitVec.ofNat 64 cnP])) paBody s
      (iotaParamsAt rl rP cnP) (PostA (ctxH C H)) := by
  refine specR_prologue (postA_locals _) (pa_none _ _) ?_
  unfold iotaParamsAt
  obtain ⟨-, -, hf, -⟩ := hq
  let Γ0 : Env := ctxEnv (ctxH C H) ++ paParams.zip [cellA C oq, BitVec.ofNat 64 rP, BitVec.ofNat 64 cnP]
  have hsQ : ∀ k, sev Γ0 (.op .add [vv paQ, .const (BitVec.ofNat 64 (8 * k))]) = some (cellA C (oq + k)) := by
    intro k; simp +decide [Γ0, sev, Env.get, paParams, ctxEnv]; exact cellA_plus C oq k
  have rest : ∀ (tw : BitVec 64), tw ≠ 1 → (∀ M, SpecR (σ := σ) (Inv (ctxH C H) s ((paT, tw) :: Γ0) M
      (ctxLocals ++ paLocals)) (.ite (.cmp .equal (vv paT) (.const 1))
        (.seq (.assign .local paX (.load .one (.op .add [vv paQ, .const 32]))) (.return (vv paX)))
        (.seq (.call (some (some (.local, paM1), none)) fTSub [vv paC, vv paR])
        (.seq (.call (some (some (.local, paM), none)) fTSub [vv paC, vv paM1])
        (.seq (.call (some (some (.local, paX), none)) fIotaBVars [vv paR, vv paM, .const 0])
          (.return (vv paX)))))) s (iotaBVars rP (min cnP rP) 0) (PostA (ctxH C H))) := by
    intro tw htw M
    refine specR_ifI _ 0 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact htw)
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [show min cnP rP = cnP - (cnP - rP) by omega]
    refine specR_pureBind (cnP - rP) ?_
    refine rb_tsub (D := ctxLocals ++ paLocals) C hcs cnP rP (by omega) (by omega) H s paM1 (vv paC) (vv paR)
      (by simp +decide [ctxLocals, paLocals]) (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv])
      (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv]) (fun H1 hp1 => ?_)
    refine specR_pureBind (cnP - (cnP - rP)) ?_
    refine rb_tsub (D := ctxLocals ++ paLocals) C hcs cnP (cnP - rP) (by omega) (by omega) H1 s paM (vv paC) (vv paM1)
      (by simp +decide [ctxLocals, paLocals]) (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv])
      (by simp +decide [sev, Env.get_cons]) (fun H2 hp2 => ?_)
    refine specR_congr (m' := iotaBVars rP (cnP - (cnP - rP)) 0 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H2) paX fIotaBVars ibParams [vv paR, vv paM, .const 0] (ibBody C)
      [BitVec.ofNat 64 rP, BitVec.ofNat 64 (cnP - (cnP - rP)), BitVec.ofNat 64 0] (by decide) rfl
      (by simp +decide [ctxLocals, paLocals]) hci
      ⟨by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (PostA (ctxH C H2)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibParams _ rfl hlk)
        (ib_spec ra C hok hci hcb rP (cnP - (cnP - rP)) (by omega) hr _ 0 H2 s rfl (by omega)))
      (fun ys wr s2 H3 hp3 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    exact specR_returnI _ _ (by simp [sev, Env.get_cons] <;> rfl) (fun t ht => ⟨H3, oy, (hp1.trans hp2).trans hp3, rfl, hblk,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rcases hrf : rl.fire with _ | ⟨lv, pins⟩ | lv <;> rw [hrf] at hf <;> simp only []
  · -- plain
    refine UD.specR_heapLoadI' (C := ctxH C H) paT _ (oq + 2) _ hf (by simp +decide [ctxLocals, paLocals]) (hsQ 2) ?_
    exact rest 0 (by decide) _
  · -- nested: the recorded parameters
    obtain ⟨h1, -, ⟨w, hw, hpins⟩⟩ := hf
    refine UD.specR_heapLoadI' (C := ctxH C H) paT _ (oq + 2) _ h1 (by simp +decide [ctxLocals, paLocals]) (hsQ 2) ?_
    refine specR_ifI _ 1 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    obtain ⟨op, hwo, hpb⟩ := hpins
    have hw4 : (ctxH C H).H[oq + 4]? = some (cellA C op) := by
      show H[oq + 4]? = _; rw [show oq + 4 = oq + 2 + 2 by omega, hw, hwo]; rfl
    refine UD.specR_heapLoadI' (C := ctxH C H) paX _ (oq + 4) _ hw4 (by simp +decide [ctxLocals, paLocals])
      (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv]; exact cellA_plus C oq 4) ?_
    exact specR_returnI _ _ (by simp [sev, Env.get_cons] <;> rfl) (fun t ht => ⟨H, op, List.prefix_refl _, rfl, hpb,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · -- recorded levels
    obtain ⟨h1, -⟩ := hf
    refine UD.specR_heapLoadI' (C := ctxH C H) paT _ (oq + 2) _ h1 (by simp +decide [ctxLocals, paLocals]) (hsQ 2) ?_
    exact rest 2 (by decide) _

end

end ConPanqueque.T.Ind
