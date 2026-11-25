import ConPanqueque.T.Ind.BlockTele

/-!
# `openPisAtFvarsF`, the opened variables kept

`openPisRawGo` from an empty accumulator hands back the opened variables as its accumulator; the wrapper
returns them with the residual instantiated at them.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl ConPanqueque.T.WC

theorem openPisRawGo_acc : ∀ (n : Nat) (acc : Array EIdx) (h : EIdx) (i : Nat) (s s' : AState)
    (fvs : List EIdx) (acc' : Array EIdx) (e : EIdx),
    openPisRawGo acc n h i s = .ok (some (fvs, acc', e), s') → acc'.toList = acc.toList ++ fvs
  | 0, acc, h, i, s, s', fvs, acc', e, hr => by
    rw [openPisRawGo] at hr
    obtain ⟨he, -⟩ := AM.pure_ok hr
    cases he; simp
  | n + 1, acc, h, i, s, s', fvs, acc', e, hr => by
    rw [openPisRawGo] at hr
    split at hr
    · obtain ⟨v, s1, hv, hr1⟩ := AM.bind_ok hr
      split at hr1
      · obtain ⟨d, s2, hd, hr2⟩ := AM.bind_ok hr1
        obtain ⟨fv, s3, hfv, hr3⟩ := AM.bind_ok hr2
        obtain ⟨o, s4, ho, hr4⟩ := AM.bind_ok hr3
        rcases o with _ | ⟨fvs', acc'', e'⟩
        · obtain ⟨he, -⟩ := AM.pure_ok hr4; cases he
        · obtain ⟨he, -⟩ := AM.pure_ok hr4
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          have := openPisRawGo_acc n (acc.push fv) _ (i + 1) s3 s4 fvs' acc' e ho
          rw [this]; simp
      · obtain ⟨he, -⟩ := AM.pure_ok hr1; cases he
    · obtain ⟨he, -⟩ := AM.pure_ok hr; cases he

def ofN := ofString "of_n"
def ofE := ofString "of_e"
def ofI := ofString "of_i"
def ofA0 := ofString "of_a0"
def ofP := ofString "of_p"
def ofAcc := ofString "of_acc"
def ofR := ofString "of_r"
def ofL := ofString "of_l"
def ofX := ofString "of_x"
def ofO := ofString "of_o"
def fOpenFvars := ofString "openPisAtFvarsF"

def ofParams : List MlS := [ofN, ofE, ofI]
def ofLocals : List MlS := [ofA0, ofP, ofAcc, ofR, ofL, ofX, ofO]

/-- `openPisAtFvarsF n e i`: `0`, or a pair block `[variables block, instantiated residual]`. -/
def ofBody (C : Ctx) : ProgHOL 64 := prologue ofLocals
  (allocP C ofA0 (.const 8)
  (.seq (.store (vv ofA0) (.const 0))
  (.seq (.call (some (some (.local, ofP), none)) fOp [vv ofA0, vv ofN, vv ofE, vv ofI])
  (.ite (.cmp .equal (vv ofP) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ofAcc (.load .one (vv ofP)))
  (.seq (.assign .local ofR (.load .one (.op .add [vv ofP, .const 8])))
  (.seq (.assign .local ofL (.load .one (vv ofAcc)))
  (.seq (.call (some (some (.local, ofX), none)) ExQ.fIrr
    [vv ofAcc, .const 0, vv ofL, .const (BitVec.ofNat 64 coreWalkFuel), vv ofR, .const 0])
  (alloc6 C ofO (vv ofAcc) (vv ofX) (.const 0) (.const 0) (.const 0) (.const 0) (.return (vv ofO)))))))))))

section
variable {σ : Type}

def PostOF (C : Ctx) (o : Option (List EIdx × EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ fvs e', o = some (fvs, e') → ∃ ob oa, w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧
      H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW)

theorem postOF_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOF C a w s' st → PostOF C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem of_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ofLocals → (ctxEnv C ++ ofParams.zip vals).get x = none :=
  Knot.params_none C ofLocals ofParams vals (by decide) (by decide)

/-- **`openPisAtFvarsF`**. -/
theorem of_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : OpCodes C)
    (n : Nat) (e : EIdx) (i : Nat) (hn : n < 2 ^ 57) (hi : i + n < 2 ^ 63) (H : List (BitVec 64)) (hp : C.H <+: H)
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ofParams.zip [BitVec.ofNat 64 n, Enc.idxW e, BitVec.ofNat 64 i])) (ofBody C) s
      (openPisAtFvarsF n e i) (PostOF (ctxH C H)) := by
  refine specR_prologue (postOF_locals _) (of_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) ofA0 (.const 8) 1 (by omega) (by decide) (fun _ => rfl)
    (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hq : H1.length < (ctxH (ctxH C H) (H1 ++ ws)).H.length := by show H1.length < (H1 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv ofA0) (.const 0) H1.length hq 0 (by simp +decide [Env.get] <;> rfl) rfl ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length 0)) _ _ _ _) _ _ _ _
  generalize hB : (H1 ++ ws).set H1.length 0 = B
  have hpB : H1 <+: B := by
    refine prefix_of_get? (by rw [← hB]; simp) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  have hb0 : BlkAt B H1.length (([] : List EIdx).map Enc.idxW) :=
    ⟨by rw [← hB, List.getElem?_set_self (by simp; omega)]; rfl, fun j hj => by simp at hj⟩
  unfold openPisAtFvarsF
  refine specR_callNIH (C := ctxH C B) ofP fOp opParams [vv ofA0, vv ofN, vv ofE, vv ofI] (opBody C)
    [cellA C H1.length, BitVec.ofNat 64 n, Enc.idxW e, BitVec.ofNat 64 i] (by decide) rfl (by decide) hc.self
    ⟨by simp +decide [Env.get] <;> rfl, by simp +decide [sev, Env.get, ofParams, ctxEnv],
      by simp +decide [sev, Env.get, ofParams, ctxEnv], by simp +decide [sev, Env.get, ofParams, ctxEnv], trivial⟩
    (fun o w s' st => openPisRawGo #[] n e i s = .ok (o, s') ∧ PostOp (ctxH C B) o w s' st)
    (fun o w s' H' => openPisRawGo #[] n e i s = .ok (o, s') ∧ (o = none → w = 0) ∧ ∀ fvs acc r, o = some (fvs, acc, r) → ∃ ob oa, w = cellA C ob ∧
      H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW r) ∧ BlkAt H' oa (acc.toList.map Enc.idxW) ∧
      acc.size < 2 ^ 58)
    (fun o w s' st ⟨hr, H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨hr, h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu opParams _ rfl hlk)
      (op_spec ra C hok hc n [] e i H1.length B s (hp.trans (hp1'.trans hpB)) hb0 (by simp; omega) hi)))
    (fun o w s1 H2 hp2 ⟨hr1, hn2, hs2⟩ => ?_)
  have hp2' : B <+: H2 := hp2
  have hpH2 : H <+: H2 := hp1'.trans (hpB.trans hp2')
  rcases o with _ | ⟨fvs, acc, r⟩
  · rw [hn2 rfl]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hpH2, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl,
      fun _ _ h => by cases h⟩)
  obtain ⟨ob, oa, hw, hob, hob1, hba, hasz⟩ := hs2 fvs acc r rfl
  subst hw
  have hfv : acc.toList = fvs := by have := openPisRawGo_acc n #[] e i s s1 fvs acc r hr1; simpa using this
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN2 => ?_)
  have hHN2' : H2.length ≤ C.HN := hHN2
  have hol : ob < H2.length := (List.getElem?_eq_some_iff.mp hob).1
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H2) ofAcc (vv ofP) ob _ hob (by decide) (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) ofR _ (ob + 1) _ hob1 (by decide)
    (by simp +decide [sev, Env.get]; exact cellA_add8 C ob) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) ofL (vv ofAcc) oa _ hba.1 (by decide) (by simp +decide [Env.get]; rfl) ?_
  dsimp only
  simp only [instantiateListFast, bind_assoc]
  refine ILP.callE_spec (C := ctxH C H2) ofX ExQ.fIrr ExQ.irrParams
    [vv ofAcc, .const 0, vv ofL, .const (BitVec.ofNat 64 coreWalkFuel), vv ofR, .const 0] (ExQ.irrBody C)
    [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.size, BitVec.ofNat 64 coreWalkFuel,
      Enc.idxW r, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
    ⟨by simp +decide [Env.get] <;> rfl, rfl, by simp +decide [Env.get], rfl, by simp +decide [Env.get], rfl, trivial⟩
    (ExQ.irr_spec (σ := σ) ra (ctxH C H2) (ctxOK_H hok H2) (codesQ_H hc.q H2) acc oa hba (by omega) s1
        coreWalkFuel 0 acc.size 0 r CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun x s2 => ?_)
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN3 => ?_)
  refine specR_alloc6I (ctxOK_H hok H2) ofO _ _ _ _ _ _ (cellA C oa) (Enc.idxW x) 0 0 0 0 (by decide)
    (fun _ => by simp +decide [Env.get] <;> rfl) (fun _ => by simp +decide [Env.get]) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun H3 ws3 hp3 hws3 hroom3 => ?_)
  obtain ⟨g0, g1, -⟩ := img6_get H3 ws3 (cellA C oa) (Enc.idxW x) 0 0 0 0 hws3
  have hpre3 : H3 <+: img6 H3 ws3 (cellA C oa) (Enc.idxW x) 0 0 0 0 := img6_prefix _ _ _ _ _ _ _ _ hws3
  have hp3' : H2 <+: H3 := hp3
  exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨_, hpH2.trans (hp3'.trans hpre3), sr_of_eq ht.sr rfl rfl rfl rfl, (fun h => by cases h),
      (fun fvs' e' h => by
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨H3.length, oa, rfl, g0, g1, by rw [← hfv]; exact blkAt_mono hba (hp3'.trans hpre3)⟩)⟩)

end

end ConPanqueque.T.Ind
