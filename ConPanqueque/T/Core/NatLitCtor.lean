import ConPanqueque.T.Core.RuleBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `natLitToConstructor`: a `Nat` literal one layer in constructor form

`Nat.zero` for `0`; `Nat.succ (lit (n - 1))` otherwise. The literal's limbs are copied to the heap, decremented
by the block subtraction, and the pieces interned in the twin's order (the constant, then the literal, then the
application).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def nlH := ofString "nlh"
def nlB := ofString "nlb"
def nlL := ofString "nll"
def nlZ := ofString "nlz"
def nlE := ofString "nle"
def nlR := ofString "nlr"
def nlS := ofString "nls"
def nlC := ofString "nlc"
def nlO := ofString "nlo"
def nlD := ofString "nld"
def nlT := ofString "nlt"
def fNl := ofString "natLitToCtor"

@[simp] theorem nl_nlH_ne_nlB : nlH ≠ nlB := by decide
@[simp] theorem nl_nlH_ne_nlL : nlH ≠ nlL := by decide
@[simp] theorem nl_nlH_ne_nlZ : nlH ≠ nlZ := by decide
@[simp] theorem nl_nlH_ne_nlE : nlH ≠ nlE := by decide
@[simp] theorem nl_nlH_ne_nlR : nlH ≠ nlR := by decide
@[simp] theorem nl_nlH_ne_nlS : nlH ≠ nlS := by decide
@[simp] theorem nl_nlH_ne_nlC : nlH ≠ nlC := by decide
@[simp] theorem nl_nlH_ne_nlO : nlH ≠ nlO := by decide
@[simp] theorem nl_nlH_ne_nlD : nlH ≠ nlD := by decide
@[simp] theorem nl_nlH_ne_nlT : nlH ≠ nlT := by decide
@[simp] theorem nl_nlH_ne_lKb : nlH ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlH : lKb ≠ nlH := by decide
@[simp] theorem nl_nlB_ne_nlH : nlB ≠ nlH := by decide
@[simp] theorem nl_nlB_ne_nlL : nlB ≠ nlL := by decide
@[simp] theorem nl_nlB_ne_nlZ : nlB ≠ nlZ := by decide
@[simp] theorem nl_nlB_ne_nlE : nlB ≠ nlE := by decide
@[simp] theorem nl_nlB_ne_nlR : nlB ≠ nlR := by decide
@[simp] theorem nl_nlB_ne_nlS : nlB ≠ nlS := by decide
@[simp] theorem nl_nlB_ne_nlC : nlB ≠ nlC := by decide
@[simp] theorem nl_nlB_ne_nlO : nlB ≠ nlO := by decide
@[simp] theorem nl_nlB_ne_nlD : nlB ≠ nlD := by decide
@[simp] theorem nl_nlB_ne_nlT : nlB ≠ nlT := by decide
@[simp] theorem nl_nlB_ne_lKb : nlB ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlB : lKb ≠ nlB := by decide
@[simp] theorem nl_nlL_ne_nlH : nlL ≠ nlH := by decide
@[simp] theorem nl_nlL_ne_nlB : nlL ≠ nlB := by decide
@[simp] theorem nl_nlL_ne_nlZ : nlL ≠ nlZ := by decide
@[simp] theorem nl_nlL_ne_nlE : nlL ≠ nlE := by decide
@[simp] theorem nl_nlL_ne_nlR : nlL ≠ nlR := by decide
@[simp] theorem nl_nlL_ne_nlS : nlL ≠ nlS := by decide
@[simp] theorem nl_nlL_ne_nlC : nlL ≠ nlC := by decide
@[simp] theorem nl_nlL_ne_nlO : nlL ≠ nlO := by decide
@[simp] theorem nl_nlL_ne_nlD : nlL ≠ nlD := by decide
@[simp] theorem nl_nlL_ne_nlT : nlL ≠ nlT := by decide
@[simp] theorem nl_nlL_ne_lKb : nlL ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlL : lKb ≠ nlL := by decide
@[simp] theorem nl_nlZ_ne_nlH : nlZ ≠ nlH := by decide
@[simp] theorem nl_nlZ_ne_nlB : nlZ ≠ nlB := by decide
@[simp] theorem nl_nlZ_ne_nlL : nlZ ≠ nlL := by decide
@[simp] theorem nl_nlZ_ne_nlE : nlZ ≠ nlE := by decide
@[simp] theorem nl_nlZ_ne_nlR : nlZ ≠ nlR := by decide
@[simp] theorem nl_nlZ_ne_nlS : nlZ ≠ nlS := by decide
@[simp] theorem nl_nlZ_ne_nlC : nlZ ≠ nlC := by decide
@[simp] theorem nl_nlZ_ne_nlO : nlZ ≠ nlO := by decide
@[simp] theorem nl_nlZ_ne_nlD : nlZ ≠ nlD := by decide
@[simp] theorem nl_nlZ_ne_nlT : nlZ ≠ nlT := by decide
@[simp] theorem nl_nlZ_ne_lKb : nlZ ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlZ : lKb ≠ nlZ := by decide
@[simp] theorem nl_nlE_ne_nlH : nlE ≠ nlH := by decide
@[simp] theorem nl_nlE_ne_nlB : nlE ≠ nlB := by decide
@[simp] theorem nl_nlE_ne_nlL : nlE ≠ nlL := by decide
@[simp] theorem nl_nlE_ne_nlZ : nlE ≠ nlZ := by decide
@[simp] theorem nl_nlE_ne_nlR : nlE ≠ nlR := by decide
@[simp] theorem nl_nlE_ne_nlS : nlE ≠ nlS := by decide
@[simp] theorem nl_nlE_ne_nlC : nlE ≠ nlC := by decide
@[simp] theorem nl_nlE_ne_nlO : nlE ≠ nlO := by decide
@[simp] theorem nl_nlE_ne_nlD : nlE ≠ nlD := by decide
@[simp] theorem nl_nlE_ne_nlT : nlE ≠ nlT := by decide
@[simp] theorem nl_nlE_ne_lKb : nlE ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlE : lKb ≠ nlE := by decide
@[simp] theorem nl_nlR_ne_nlH : nlR ≠ nlH := by decide
@[simp] theorem nl_nlR_ne_nlB : nlR ≠ nlB := by decide
@[simp] theorem nl_nlR_ne_nlL : nlR ≠ nlL := by decide
@[simp] theorem nl_nlR_ne_nlZ : nlR ≠ nlZ := by decide
@[simp] theorem nl_nlR_ne_nlE : nlR ≠ nlE := by decide
@[simp] theorem nl_nlR_ne_nlS : nlR ≠ nlS := by decide
@[simp] theorem nl_nlR_ne_nlC : nlR ≠ nlC := by decide
@[simp] theorem nl_nlR_ne_nlO : nlR ≠ nlO := by decide
@[simp] theorem nl_nlR_ne_nlD : nlR ≠ nlD := by decide
@[simp] theorem nl_nlR_ne_nlT : nlR ≠ nlT := by decide
@[simp] theorem nl_nlR_ne_lKb : nlR ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlR : lKb ≠ nlR := by decide
@[simp] theorem nl_nlS_ne_nlH : nlS ≠ nlH := by decide
@[simp] theorem nl_nlS_ne_nlB : nlS ≠ nlB := by decide
@[simp] theorem nl_nlS_ne_nlL : nlS ≠ nlL := by decide
@[simp] theorem nl_nlS_ne_nlZ : nlS ≠ nlZ := by decide
@[simp] theorem nl_nlS_ne_nlE : nlS ≠ nlE := by decide
@[simp] theorem nl_nlS_ne_nlR : nlS ≠ nlR := by decide
@[simp] theorem nl_nlS_ne_nlC : nlS ≠ nlC := by decide
@[simp] theorem nl_nlS_ne_nlO : nlS ≠ nlO := by decide
@[simp] theorem nl_nlS_ne_nlD : nlS ≠ nlD := by decide
@[simp] theorem nl_nlS_ne_nlT : nlS ≠ nlT := by decide
@[simp] theorem nl_nlS_ne_lKb : nlS ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlS : lKb ≠ nlS := by decide
@[simp] theorem nl_nlC_ne_nlH : nlC ≠ nlH := by decide
@[simp] theorem nl_nlC_ne_nlB : nlC ≠ nlB := by decide
@[simp] theorem nl_nlC_ne_nlL : nlC ≠ nlL := by decide
@[simp] theorem nl_nlC_ne_nlZ : nlC ≠ nlZ := by decide
@[simp] theorem nl_nlC_ne_nlE : nlC ≠ nlE := by decide
@[simp] theorem nl_nlC_ne_nlR : nlC ≠ nlR := by decide
@[simp] theorem nl_nlC_ne_nlS : nlC ≠ nlS := by decide
@[simp] theorem nl_nlC_ne_nlO : nlC ≠ nlO := by decide
@[simp] theorem nl_nlC_ne_nlD : nlC ≠ nlD := by decide
@[simp] theorem nl_nlC_ne_nlT : nlC ≠ nlT := by decide
@[simp] theorem nl_nlC_ne_lKb : nlC ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlC : lKb ≠ nlC := by decide
@[simp] theorem nl_nlO_ne_nlH : nlO ≠ nlH := by decide
@[simp] theorem nl_nlO_ne_nlB : nlO ≠ nlB := by decide
@[simp] theorem nl_nlO_ne_nlL : nlO ≠ nlL := by decide
@[simp] theorem nl_nlO_ne_nlZ : nlO ≠ nlZ := by decide
@[simp] theorem nl_nlO_ne_nlE : nlO ≠ nlE := by decide
@[simp] theorem nl_nlO_ne_nlR : nlO ≠ nlR := by decide
@[simp] theorem nl_nlO_ne_nlS : nlO ≠ nlS := by decide
@[simp] theorem nl_nlO_ne_nlC : nlO ≠ nlC := by decide
@[simp] theorem nl_nlO_ne_nlD : nlO ≠ nlD := by decide
@[simp] theorem nl_nlO_ne_nlT : nlO ≠ nlT := by decide
@[simp] theorem nl_nlO_ne_lKb : nlO ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlO : lKb ≠ nlO := by decide
@[simp] theorem nl_nlD_ne_nlH : nlD ≠ nlH := by decide
@[simp] theorem nl_nlD_ne_nlB : nlD ≠ nlB := by decide
@[simp] theorem nl_nlD_ne_nlL : nlD ≠ nlL := by decide
@[simp] theorem nl_nlD_ne_nlZ : nlD ≠ nlZ := by decide
@[simp] theorem nl_nlD_ne_nlE : nlD ≠ nlE := by decide
@[simp] theorem nl_nlD_ne_nlR : nlD ≠ nlR := by decide
@[simp] theorem nl_nlD_ne_nlS : nlD ≠ nlS := by decide
@[simp] theorem nl_nlD_ne_nlC : nlD ≠ nlC := by decide
@[simp] theorem nl_nlD_ne_nlO : nlD ≠ nlO := by decide
@[simp] theorem nl_nlD_ne_nlT : nlD ≠ nlT := by decide
@[simp] theorem nl_nlD_ne_lKb : nlD ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlD : lKb ≠ nlD := by decide
@[simp] theorem nl_nlT_ne_nlH : nlT ≠ nlH := by decide
@[simp] theorem nl_nlT_ne_nlB : nlT ≠ nlB := by decide
@[simp] theorem nl_nlT_ne_nlL : nlT ≠ nlL := by decide
@[simp] theorem nl_nlT_ne_nlZ : nlT ≠ nlZ := by decide
@[simp] theorem nl_nlT_ne_nlE : nlT ≠ nlE := by decide
@[simp] theorem nl_nlT_ne_nlR : nlT ≠ nlR := by decide
@[simp] theorem nl_nlT_ne_nlS : nlT ≠ nlS := by decide
@[simp] theorem nl_nlT_ne_nlC : nlT ≠ nlC := by decide
@[simp] theorem nl_nlT_ne_nlO : nlT ≠ nlO := by decide
@[simp] theorem nl_nlT_ne_nlD : nlT ≠ nlD := by decide
@[simp] theorem nl_nlT_ne_lKb : nlT ≠ lKb := by decide
@[simp] theorem nl_lKb_ne_nlT : lKb ≠ nlT := by decide

def nlLocals : List MlS := [nlB, nlL, nlZ, nlE, nlR, nlS, nlC, nlO, nlD, nlT]

def nlCore (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, nlB), none)) fLitH [vv nlH])
  (.seq (.assign .local nlL (.load .one (vv nlB)))
  (.ite (.cmp .equal (vv nlL) (.const 0))
    (.seq (.assign .local nlZ (.load .one (.const (ecell C (C.PO + PIN_NAT_ZERO)))))
    (.seq (.assign .local nlE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
    (.seq (.call (some (some (.local, nlR), none)) fInternConst [vv nlZ, vv nlE]) (.return (vv nlR)))))
    (.seq (.assign .local nlS (.load .one (.const (ecell C (C.PO + PIN_NAT_SUCC)))))
    (.seq (.assign .local nlE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
    (.seq (.call (some (some (.local, nlC), none)) fInternConst [vv nlS, vv nlE])
    (allocP C nlO (.const 16) (.seq (.store (vv nlO) (.const 1))
    (.seq (.store (.op .add [vv nlO, .const 8]) (.const 1))
    (.seq (.call (some (some (.local, nlD), none)) fSub [vv nlB, vv nlO])
    (.seq (.call (some (some (.local, nlT), none)) fLitB [vv nlD])
    (.seq (.call (some (some (.local, nlR), none)) fInternApp [vv nlC, vv nlT]) (.return (vv nlR)))))))))))))

def nlBody (C : Ctx) : ProgHOL 64 := prologue nlLocals (nlCore C)

section
variable {σ : Type}

theorem specR_bindPure {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : SpecR P c s (m >>= fun r => pure r) R) : SpecR P c s m R := by
  simpa using h

theorem nl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nlLocals → (ctxEnv C ++ [nlH].zip vals).get x = none :=
  Knot.params_none C nlLocals [nlH] vals (by decide) (by decide)

structure NlCodes (C : Ctx) : Prop where
  lit : C.code.lookup fLitH = some ([Big.cH].map (fun p => (p, ShapeHOL.one)), litBody C, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  sub : C.code.lookup fSub = some (subParams.map (fun p => (p, ShapeHOL.one)), subBody C, .one)
  litb : C.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C, .one)
  ia : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)

theorem nl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NlCodes C)
    (s : AState) (h : EIdx) (n : Nat) (hv : s.store.view h = some (.lit (.natVal n))) :
    SpecR (σ := σ) (Pre C s [(nlH, Enc.idxW h)]) (nlBody C) s (natLitToConstructor n) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (nl_none C [Enc.idxW h]) ?_
  unfold nlCore
  refine specR_congr (m' := (pure n : AM Nat) >>= fun n => natLitToConstructor n) rfl ?_
  refine specR_callPH (C := C) (k := fun n => natLitToConstructor n) nlB fLitH [Big.cH] [vv nlH] (litBody C) [Enc.idxW h] n (by decide) rfl (by decide) hc.lit
    ⟨by simp +decide [Env.get, ctxEnv], trivial⟩ (lit_spec C hok s h n hv) (fun H1 o hp1 hb => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H1) nlL (vv nlB) o _ hb.1 (by decide) (by simp; rfl) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsl := blk_small0 (ctxOK_H hok H1) ht0.sr hb
  have hok1 := ctxOK_H hok H1
  cases n with
  | zero =>
    rw [limbs_zero] at hb hsl ⊢
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    show SpecR _ _ _ (pinAt PIN_NAT_ZERO >>= fun z => emptyLevels >>= fun us => internE (.const z us)) _
    refine specR_pinAtI (C := ctxH C H1) hok1 PIN_NAT_ZERO (by decide) nlZ (by decide) ?_
    refine specR_pinXI (C := ctxH C H1) hok1 pinEmptyLevels 0 C.pins.emptyLevels _
      (fun s hp => pinEmptyLevels_run (C := ctxH C H1) hok1 hp) (pin_emptyLevels_cell hok1) nlE (by decide) ?_
    refine specR_bindPure ?_
    refine ILP.callE_spec (C := ctxH C H1) nlR fInternConst [lEn, lEus] [vv nlZ, vv nlE] constBody
      [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hc.ic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra (ctxH C H1) hok1 s _ _) (fun r s1 => ?_)
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k =>
    have hpos : (limbs (k + 1)).length ≠ 0 := by rw [limbs_pos (by omega)]; simp
    have hne : BitVec.ofNat 64 (limbs (k + 1)).length ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    show SpecR _ _ _ (pinAt PIN_NAT_SUCC >>= fun sN => (emptyLevels >>= fun us => internE (.const sN us)) >>=
      fun sc => internE (.lit (.natVal k)) >>= fun l => internE (.app sc l)) _
    simp only [bind_assoc]
    refine specR_pinAtI (C := ctxH C H1) hok1 PIN_NAT_SUCC (by decide) nlS (by decide) ?_
    refine specR_pinXI (C := ctxH C H1) hok1 pinEmptyLevels 0 C.pins.emptyLevels _
      (fun s hp => pinEmptyLevels_run (C := ctxH C H1) hok1 hp) (pin_emptyLevels_cell hok1) nlE (by decide) ?_
    refine ILP.callE_spec (C := ctxH C H1) nlC fInternConst [lEn, lEus] [vv nlS, vv nlE] constBody
      [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hc.ic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra (ctxH C H1) hok1 s _ _) (fun sc s1 => ?_)
    refine specR_allocI (C := ctxH C H1) nlO (.const 16) 2 (by norm_num) (by decide) (fun v => by simp [sev])
      (fun H3 ws hpre hwl hcap => ?_)
    have hpl : H1.length ≤ H3.length := hpre.length_le
    have hj : H3.length < (ctxH (ctxH C H1) (H3 ++ ws)).H.length := by show _ < (H3 ++ ws).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv nlO) (.const 1) _ hj 1 (by simp; rfl) rfl ?_
    have hj2 : H3.length + 1 < (ctxH (ctxH C H1) ((H3 ++ ws).set H3.length 1)).H.length := by
      show _ < ((H3 ++ ws).set _ _).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) _ (.const 1) _ hj2 1 (by simp [sev]; exact cellA_add8 C _) rfl ?_
    let H4 := ((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1
    have hp1' := prefix_set_ge ((show H1 <+: H3 from hpre).trans (List.prefix_append _ ws)) _ hpl (1 : BitVec 64)
    have hp4 : H1 <+: H4 := prefix_set_ge hp1' (H3.length + 1) (by omega) (1 : BitVec 64)
    have hbo : BlkAt H4 H3.length (limbs 1) := by
      rw [show limbs 1 = [BitVec.ofNat 64 1] by rw [limbs_word 1 (by decide)]; rfl]
      refine ⟨?_, fun i hi => ?_⟩
      · show (((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1)[H3.length]? = _
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]; rfl
      · have : i = 0 := by simpa using hi
        subst this
        show (((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1)[H3.length + 1 + 0]? = _
        rw [List.getElem?_set_self (by simp; omega)]; rfl
    have hb4 : BlkAt H4 o (limbs (k + 1)) := blkAt_mono hb hp4
    have hok4 := ctxOK_H hok H4
    refine specR_callPH (C := ctxH C H4) (k := fun m => internE (.lit (.natVal m)) >>= fun l => internE (.app sc l))
      nlD fSub subParams [vv nlB, vv nlO] (subBody C) [cellA C o, cellA C H3.length] (k + 1 - 1) (by decide) rfl
      (by decide) hc.sub ⟨by simp, by simp; rfl, trivial⟩
      (sub_spec (ctxH C H4) hok4 s1 (k + 1) 1 o H3.length hb4 hbo (by omega)
        (by rw [show limbs 1 = [BitVec.ofNat 64 1] by rw [limbs_word 1 (by decide)]; rfl]; simp; omega)
        (by omega)) (fun H5 od hp5 hbd => ?_)
    have hok5 := ctxOK_H hok H5
    simp only [Nat.add_sub_cancel] at hbd ⊢
    refine specR_callKH (C := ctxH C H5) nlT fLitB [iLx] [vv nlD] (litBlkBody C) [cellA C od] (by decide) rfl
      (by decide) hc.litb ⟨by simp; rfl, trivial⟩ (litBlk_spec ra (ctxH C H5) hok5 s1 k od hbd)
      (fun l s2 H6 hp6 => ?_)
    refine specR_congr (m' := internAppE sc l >>= fun r => pure r) (by simp [internAppE]) ?_
    refine specR_internAppI (C := ctxH C H6) ra (ctxOK_H hok H6) hc.ia nlR (vv nlC) (vv nlT) sc l
      (by decide) (by simp) (by simp) (fun r s3 => ?_)
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H6, hp1.trans (hp4.trans (hp5.trans hp6)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
