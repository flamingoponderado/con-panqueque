import ConPanqueque.T.Core.InferArms
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The ∀ arm: `inferPis` and its pieces

`inferPisOut`: the outward `imax` fold over the stacked binder sorts (a heap block), innermost first.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def poS := ofString "pon_s"
def poN := ofString "pon_n"
def poV := ofString "pon_v"
def poJ := ofString "pon_j"
def poA := ofString "pon_a"
def poW := ofString "pon_w"
def poR := ofString "pon_r"
def fPo := ofString "inferPisOut"

@[simp] theorem po_poS_ne_poN : poS ≠ poN := by decide
@[simp] theorem po_poS_ne_poV : poS ≠ poV := by decide
@[simp] theorem po_poS_ne_poJ : poS ≠ poJ := by decide
@[simp] theorem po_poS_ne_poA : poS ≠ poA := by decide
@[simp] theorem po_poS_ne_poW : poS ≠ poW := by decide
@[simp] theorem po_poS_ne_poR : poS ≠ poR := by decide
@[simp] theorem po_poS_ne_lKb : poS ≠ lKb := by decide
@[simp] theorem po_poN_ne_poS : poN ≠ poS := by decide
@[simp] theorem po_poN_ne_poV : poN ≠ poV := by decide
@[simp] theorem po_poN_ne_poJ : poN ≠ poJ := by decide
@[simp] theorem po_poN_ne_poA : poN ≠ poA := by decide
@[simp] theorem po_poN_ne_poW : poN ≠ poW := by decide
@[simp] theorem po_poN_ne_poR : poN ≠ poR := by decide
@[simp] theorem po_poN_ne_lKb : poN ≠ lKb := by decide
@[simp] theorem po_poV_ne_poS : poV ≠ poS := by decide
@[simp] theorem po_poV_ne_poN : poV ≠ poN := by decide
@[simp] theorem po_poV_ne_poJ : poV ≠ poJ := by decide
@[simp] theorem po_poV_ne_poA : poV ≠ poA := by decide
@[simp] theorem po_poV_ne_poW : poV ≠ poW := by decide
@[simp] theorem po_poV_ne_poR : poV ≠ poR := by decide
@[simp] theorem po_poV_ne_lKb : poV ≠ lKb := by decide
@[simp] theorem po_poJ_ne_poS : poJ ≠ poS := by decide
@[simp] theorem po_poJ_ne_poN : poJ ≠ poN := by decide
@[simp] theorem po_poJ_ne_poV : poJ ≠ poV := by decide
@[simp] theorem po_poJ_ne_poA : poJ ≠ poA := by decide
@[simp] theorem po_poJ_ne_poW : poJ ≠ poW := by decide
@[simp] theorem po_poJ_ne_poR : poJ ≠ poR := by decide
@[simp] theorem po_poJ_ne_lKb : poJ ≠ lKb := by decide
@[simp] theorem po_poA_ne_poS : poA ≠ poS := by decide
@[simp] theorem po_poA_ne_poN : poA ≠ poN := by decide
@[simp] theorem po_poA_ne_poV : poA ≠ poV := by decide
@[simp] theorem po_poA_ne_poJ : poA ≠ poJ := by decide
@[simp] theorem po_poA_ne_poW : poA ≠ poW := by decide
@[simp] theorem po_poA_ne_poR : poA ≠ poR := by decide
@[simp] theorem po_poA_ne_lKb : poA ≠ lKb := by decide
@[simp] theorem po_poW_ne_poS : poW ≠ poS := by decide
@[simp] theorem po_poW_ne_poN : poW ≠ poN := by decide
@[simp] theorem po_poW_ne_poV : poW ≠ poV := by decide
@[simp] theorem po_poW_ne_poJ : poW ≠ poJ := by decide
@[simp] theorem po_poW_ne_poA : poW ≠ poA := by decide
@[simp] theorem po_poW_ne_poR : poW ≠ poR := by decide
@[simp] theorem po_poW_ne_lKb : poW ≠ lKb := by decide
@[simp] theorem po_poR_ne_poS : poR ≠ poS := by decide
@[simp] theorem po_poR_ne_poN : poR ≠ poN := by decide
@[simp] theorem po_poR_ne_poV : poR ≠ poV := by decide
@[simp] theorem po_poR_ne_poJ : poR ≠ poJ := by decide
@[simp] theorem po_poR_ne_poA : poR ≠ poA := by decide
@[simp] theorem po_poR_ne_poW : poR ≠ poW := by decide
@[simp] theorem po_poR_ne_lKb : poR ≠ lKb := by decide
@[simp] theorem po_lKb_ne_poS : lKb ≠ poS := by decide
@[simp] theorem po_lKb_ne_poN : lKb ≠ poN := by decide
@[simp] theorem po_lKb_ne_poV : lKb ≠ poV := by decide
@[simp] theorem po_lKb_ne_poJ : lKb ≠ poJ := by decide
@[simp] theorem po_lKb_ne_poA : lKb ≠ poA := by decide
@[simp] theorem po_lKb_ne_poW : lKb ≠ poW := by decide
@[simp] theorem po_lKb_ne_poR : lKb ≠ poR := by decide

def poParams : List MlS := [poS, poN, poV]
def poLocals : List MlS := [poJ, poA, poW, poR]

def poBody : ProgHOL 64 := prologue poLocals
  (.ite (.cmp .equal (vv poN) (.const 0)) (.return (vv poV))
  (.seq (.assign .local poJ (.op .sub [vv poN, .const 1]))
  (.seq (.assign .local poA (.load .one (.op .add [.op .add [vv poS, .const 8], .shift .lsl (vv poJ) (.const 3)])))
  (.seq (.call (some (some (.local, poW), none)) fInternLImax [vv poA, vv poV])
  (.seq (.call (some (some (.local, poR), none)) fPo [vv poS, vv poJ, vv poW]) (.return (vv poR)))))))

section
variable {σ : Type}

theorem po_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ poLocals → (ctxEnv C ++ poParams.zip vals).get x = none :=
  Knot.params_none C poLocals poParams vals (by decide) (by decide)

/-- A level handle, the heap extended, any final state. -/
def PostLX (C : Ctx) (r : LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW r ∧ SR (ctxH C H') s' st

theorem postLX_locals (C : Ctx) : ∀ (a : LIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLX C a w s' st → PostLX C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem po_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hci : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one))
    (hcp : C.code.lookup fPo = some (poParams.map (fun p => (p, ShapeHOL.one)), poBody, .one))
    (stk : List LIdx) (o : Nat) (hsl : stk.length < 2 ^ 58) :
    ∀ n (v : LIdx) (H : List (BitVec 64)) (s : AState), C.H <+: H → BlkAt H o (stk.map Enc.idxW) → n ≤ stk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (poParams.zip [cellA C o, BitVec.ofNat 64 n, Enc.idxW v])) poBody s
        (inferPisOut stk.toArray n v) (PostLX (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro v H s hp hb hn
    refine specR_prologue (postLX_locals _) (po_none _ _) ?_
    rw [inferPisOut]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, poParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ (Enc.idxW v) (by simp +decide [Env.get, poParams, ctxEnv])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ n ih =>
    intro v H s hp hb hn
    refine specR_prologue (postLX_locals _) (po_none _ _) ?_
    rw [inferPisOut]
    have hne := ofNat_succ_ne n (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, poParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [show ¬ (n + 1 = 0) from by omega, ↓reduceIte, Nat.add_sub_cancel]
    refine specR_assignI poJ _ (BitVec.ofNat 64 n) (by decide)
      (by simp +decide [sev, Env.get, poParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _) ?_
    have hn' : n < stk.length := by omega
    have h1 := hb.2 n (by simpa using hn')
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) poA _ (o + 1 + n) (Enc.idxW stk[n]) h1 (by decide)
      (by simp +decide [sev, Env.get, poParams, ctxEnv]; show _ = cellA C (o + 1 + n); rw [← cellA_shl C (o + 1) n (by omega), ← cellA_add8]; rfl) ?_
    have hgx : stk.toArray[n]! = stk[n] := by simp [hn']
    rw [hgx]
    refine callLN (C := ctxH C H) poW fInternLImax [lEu, lEv] [vv poA, vv poV] internLImaxBody
      [Enc.idxW stk[n], Enc.idxW v] (by decide) rfl (by decide) hci
      ⟨by simp, by simp +decide [Env.get, poParams, ctxEnv], trivial⟩ (.imax stk[n] v)
      (internLImax_body_spec ra (ctxH C H) (ctxOK_H hok H) s stk[n] v) (fun v2 s1 _ => ?_)
    refine specR_congr (m' := inferPisOut stk.toArray n v2 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) poR fPo poParams [vv poS, vv poJ, vv poW] poBody
      [cellA C o, BitVec.ofNat 64 n, Enc.idxW v2] (by decide) rfl (by decide) hcp
      ⟨by simp +decide [Env.get, poParams, ctxEnv] <;> rfl, by simp, by simp, trivial⟩
      (PostLX (ctxH C H)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu poParams _ rfl hlk) (ih v2 H s1 hp hb (by omega)))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
