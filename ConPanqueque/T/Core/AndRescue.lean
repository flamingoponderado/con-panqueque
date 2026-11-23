import ConPanqueque.T.Core.EtaProjs
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `andRescueSlots`: the pinned `And`'s projection slots

Both slots read the same table, so the test is one table lookup: its constructor, parameter count and the two
fields.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

theorem andRescueSlotsGo_eq (fe : IFEnv) (an ctor : NIdx) (nP : Nat) :
    andRescueSlotsGo fe an ctor nP 2 0 = match fe.findTable? an with
      | some t => (t.ctor == ctor && t.numParams == nP && t.numFields == 2)
      | none => false := by
  simp only [andRescueSlotsGo, IFEnv.findProj?]
  rcases fe.findTable? an with _ | t
  · rfl
  · simp only [IProjTable.entry]
    by_cases h2 : t.numFields = 2
    · simp [h2]
      by_cases hc : t.ctor = ctor <;> by_cases hp : t.numParams = nP <;> simp [hc, hp]
    · by_cases h0 : 0 < t.numFields
      · by_cases h1 : 1 < t.numFields
        · simp [h0, h1, h2]
        · simp [h0, h1, h2]
      · simp [h0, h2]

def arC := ofString "arc"
def arP := ofString "arp"
def arN := ofString "arn"
def arW := ofString "arw"
def arQ := ofString "arq"
def arT := ofString "art"
def arR := ofString "arr"
def arF := ofString "arf"
def fAr := ofString "andRescueSlots"

@[simp] theorem ar_arC_ne_arP : arC ≠ arP := by decide
@[simp] theorem ar_arC_ne_arN : arC ≠ arN := by decide
@[simp] theorem ar_arC_ne_arW : arC ≠ arW := by decide
@[simp] theorem ar_arC_ne_arQ : arC ≠ arQ := by decide
@[simp] theorem ar_arC_ne_arT : arC ≠ arT := by decide
@[simp] theorem ar_arC_ne_arR : arC ≠ arR := by decide
@[simp] theorem ar_arC_ne_arF : arC ≠ arF := by decide
@[simp] theorem ar_arC_ne_lKb : arC ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arC : lKb ≠ arC := by decide
@[simp] theorem ar_arP_ne_arC : arP ≠ arC := by decide
@[simp] theorem ar_arP_ne_arN : arP ≠ arN := by decide
@[simp] theorem ar_arP_ne_arW : arP ≠ arW := by decide
@[simp] theorem ar_arP_ne_arQ : arP ≠ arQ := by decide
@[simp] theorem ar_arP_ne_arT : arP ≠ arT := by decide
@[simp] theorem ar_arP_ne_arR : arP ≠ arR := by decide
@[simp] theorem ar_arP_ne_arF : arP ≠ arF := by decide
@[simp] theorem ar_arP_ne_lKb : arP ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arP : lKb ≠ arP := by decide
@[simp] theorem ar_arN_ne_arC : arN ≠ arC := by decide
@[simp] theorem ar_arN_ne_arP : arN ≠ arP := by decide
@[simp] theorem ar_arN_ne_arW : arN ≠ arW := by decide
@[simp] theorem ar_arN_ne_arQ : arN ≠ arQ := by decide
@[simp] theorem ar_arN_ne_arT : arN ≠ arT := by decide
@[simp] theorem ar_arN_ne_arR : arN ≠ arR := by decide
@[simp] theorem ar_arN_ne_arF : arN ≠ arF := by decide
@[simp] theorem ar_arN_ne_lKb : arN ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arN : lKb ≠ arN := by decide
@[simp] theorem ar_arW_ne_arC : arW ≠ arC := by decide
@[simp] theorem ar_arW_ne_arP : arW ≠ arP := by decide
@[simp] theorem ar_arW_ne_arN : arW ≠ arN := by decide
@[simp] theorem ar_arW_ne_arQ : arW ≠ arQ := by decide
@[simp] theorem ar_arW_ne_arT : arW ≠ arT := by decide
@[simp] theorem ar_arW_ne_arR : arW ≠ arR := by decide
@[simp] theorem ar_arW_ne_arF : arW ≠ arF := by decide
@[simp] theorem ar_arW_ne_lKb : arW ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arW : lKb ≠ arW := by decide
@[simp] theorem ar_arQ_ne_arC : arQ ≠ arC := by decide
@[simp] theorem ar_arQ_ne_arP : arQ ≠ arP := by decide
@[simp] theorem ar_arQ_ne_arN : arQ ≠ arN := by decide
@[simp] theorem ar_arQ_ne_arW : arQ ≠ arW := by decide
@[simp] theorem ar_arQ_ne_arT : arQ ≠ arT := by decide
@[simp] theorem ar_arQ_ne_arR : arQ ≠ arR := by decide
@[simp] theorem ar_arQ_ne_arF : arQ ≠ arF := by decide
@[simp] theorem ar_arQ_ne_lKb : arQ ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arQ : lKb ≠ arQ := by decide
@[simp] theorem ar_arT_ne_arC : arT ≠ arC := by decide
@[simp] theorem ar_arT_ne_arP : arT ≠ arP := by decide
@[simp] theorem ar_arT_ne_arN : arT ≠ arN := by decide
@[simp] theorem ar_arT_ne_arW : arT ≠ arW := by decide
@[simp] theorem ar_arT_ne_arQ : arT ≠ arQ := by decide
@[simp] theorem ar_arT_ne_arR : arT ≠ arR := by decide
@[simp] theorem ar_arT_ne_arF : arT ≠ arF := by decide
@[simp] theorem ar_arT_ne_lKb : arT ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arT : lKb ≠ arT := by decide
@[simp] theorem ar_arR_ne_arC : arR ≠ arC := by decide
@[simp] theorem ar_arR_ne_arP : arR ≠ arP := by decide
@[simp] theorem ar_arR_ne_arN : arR ≠ arN := by decide
@[simp] theorem ar_arR_ne_arW : arR ≠ arW := by decide
@[simp] theorem ar_arR_ne_arQ : arR ≠ arQ := by decide
@[simp] theorem ar_arR_ne_arT : arR ≠ arT := by decide
@[simp] theorem ar_arR_ne_arF : arR ≠ arF := by decide
@[simp] theorem ar_arR_ne_lKb : arR ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arR : lKb ≠ arR := by decide
@[simp] theorem ar_arF_ne_arC : arF ≠ arC := by decide
@[simp] theorem ar_arF_ne_arP : arF ≠ arP := by decide
@[simp] theorem ar_arF_ne_arN : arF ≠ arN := by decide
@[simp] theorem ar_arF_ne_arW : arF ≠ arW := by decide
@[simp] theorem ar_arF_ne_arQ : arF ≠ arQ := by decide
@[simp] theorem ar_arF_ne_arT : arF ≠ arT := by decide
@[simp] theorem ar_arF_ne_arR : arF ≠ arR := by decide
@[simp] theorem ar_arF_ne_lKb : arF ≠ lKb := by decide
@[simp] theorem ar_lKb_ne_arF : lKb ≠ arF := by decide

def arParams : List MlS := [arC, arP]
def arLocals : List MlS := [arN, arW, arQ, arT, arR, arF]

def arBody (C : Ctx) : ProgHOL 64 := prologue arLocals
  (.seq (.assign .local arN (.load .one (.const (ecell C (C.PO + PIN_AND)))))
  (tblFindP C arW (vv arN)
  (.ite (.cmp .equal (vv arW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local arQ (.op .sub [vv arW, .const 1]))
  (.seq (.assign .local arT (.load .one (.op .add [vv arQ, .const 24])))
  (.seq (.assign .local arR (.load .one (.op .add [vv arQ, .const 16])))
  (.seq (.assign .local arF (.load .one (.op .add [vv arQ, .const 32])))
    (.return (andE (andE (.cmp .equal (vv arT) (vv arC)) (.cmp .equal (vv arR) (vv arP)))
      (.cmp .equal (vv arF) (.const 2)))))))))))

section
variable {σ : Type}

theorem ar_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ arLocals → (ctxEnv C ++ arParams.zip vals).get x = none :=
  Knot.params_none C arLocals arParams vals (by decide) (by decide)

theorem sev_eqNatB {Γ : Env} {a b : ExpHOL 64} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (ha : sev Γ a = some (BitVec.ofNat 64 x)) (hb : sev Γ b = some (BitVec.ofNat 64 y)) :
    sev Γ (.cmp .equal a b) = some (boolW (x == y)) := by
  simp only [sev, ha, hb]
  by_cases he : x = y
  · subst he; simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, he]

theorem ar_spec (C : Ctx) (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (s : AState) (ctor : NIdx) (nP : Nat) (hnP : nP < 2 ^ 63) :
    SpecR (σ := σ) (Pre C s (arParams.zip [Enc.idxW ctor, BitVec.ofNat 64 nP])) (arBody C) s
      (andRescueSlots C.fe ctor nP) (Knot.PostB C) := by
  refine specR_prologue (Knot.postB_locals C) (ar_none C _) ?_
  unfold andRescueSlots
  show SpecR _ _ _ (pinAt PIN_AND >>= fun an => pure (andRescueSlotsGo C.fe an ctor nP 2 0)) _
  refine specR_pinAtI hok PIN_AND (by decide) arN (by decide) ?_
  refine specR_tblFindI hok hcodeG hcodeP arW (vv arN) (C.pins.names[PIN_AND]'(by rw [hok.pinsRel.1]; decide))
    (by decide) (by simp) (by simp +decide [Env.get, ctxEnv]) ?_
  rw [andRescueSlotsGo_eq]
  have hrel := tbl_rel hok (C.pins.names[PIN_AND]'(by rw [hok.pinsRel.1]; decide))
  revert hrel
  rcases hft : C.fe.findTable? (C.pins.names[PIN_AND]'(by rw [hok.pinsRel.1]; decide)) with _ | tb
  · intro hrel; simp only at hrel
    rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, htb⟩
  rw [hm]
  dsimp only
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI arQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  obtain ⟨_, _, hnp, hctor, hnf, _⟩ := htb
  refine specR_envLoadI arT (.op .add [vv arQ, .const 24]) (o + 3) _ (by decide)
    (by simp [sev, vv]; exact ecell_add24 C o) hctor ?_
  refine specR_envLoadI arR (.op .add [vv arQ, .const 16]) (o + 2) _ (by decide)
    (by simp [sev, vv]; exact UD.ecell_add16 C o) hnp.1 ?_
  refine specR_envLoadI arF (.op .add [vv arQ, .const 32]) (o + 4) _ (by decide)
    (by simp [sev, vv]; exact UD.ecell_add32 C o) hnf.1 ?_
  exact specR_returnI _ _
    (sev_andE (sev_andE (sev_eqIdxB (by simp) (by simp +decide [Env.get, arParams, ctxEnv]))
      (sev_eqNatB (by have := hnp.2; omega) (by omega) (by simp) (by simp +decide [Env.get, arParams, ctxEnv])))
      (sev_eqNatB (x := tb.numFields) (y := 2) (by have := hnf.2; omega) (by norm_num) (by simp) rfl))
    (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
