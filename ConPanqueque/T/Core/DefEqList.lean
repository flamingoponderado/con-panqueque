import ConPanqueque.T.Core.RescueEta
import ConPanqueque.T.Core.Unfold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `defEqList`: pairwise definitional equality of two spines

Two runs of heap cells (a start cell and a count each). Both empty answers `true`, one empty `false`; otherwise
the knot's `defeq` on the heads, then the rest.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def dlA := ofString "dla"
def dlNa := ofString "dlna"
def dlB := ofString "dlb"
def dlNb := ofString "dlnb"
def dlX := ofString "dlx"
def dlY := ofString "dly"
def dlR := ofString "dlr"
def dlS := ofString "dls"
def fDl := ofString "defEqList"

@[simp] theorem dl_dlA_ne_dlNa : dlA ≠ dlNa := by decide
@[simp] theorem dl_dlA_ne_dlB : dlA ≠ dlB := by decide
@[simp] theorem dl_dlA_ne_dlNb : dlA ≠ dlNb := by decide
@[simp] theorem dl_dlA_ne_dlX : dlA ≠ dlX := by decide
@[simp] theorem dl_dlA_ne_dlY : dlA ≠ dlY := by decide
@[simp] theorem dl_dlA_ne_dlR : dlA ≠ dlR := by decide
@[simp] theorem dl_dlA_ne_dlS : dlA ≠ dlS := by decide
@[simp] theorem dl_dlA_ne_kFu : dlA ≠ kFu := by decide
@[simp] theorem dl_dlA_ne_kD : dlA ≠ kD := by decide
@[simp] theorem dl_dlA_ne_lKb : dlA ≠ lKb := by decide
@[simp] theorem dl_dlNa_ne_dlA : dlNa ≠ dlA := by decide
@[simp] theorem dl_dlNa_ne_dlB : dlNa ≠ dlB := by decide
@[simp] theorem dl_dlNa_ne_dlNb : dlNa ≠ dlNb := by decide
@[simp] theorem dl_dlNa_ne_dlX : dlNa ≠ dlX := by decide
@[simp] theorem dl_dlNa_ne_dlY : dlNa ≠ dlY := by decide
@[simp] theorem dl_dlNa_ne_dlR : dlNa ≠ dlR := by decide
@[simp] theorem dl_dlNa_ne_dlS : dlNa ≠ dlS := by decide
@[simp] theorem dl_dlNa_ne_kFu : dlNa ≠ kFu := by decide
@[simp] theorem dl_dlNa_ne_kD : dlNa ≠ kD := by decide
@[simp] theorem dl_dlNa_ne_lKb : dlNa ≠ lKb := by decide
@[simp] theorem dl_dlB_ne_dlA : dlB ≠ dlA := by decide
@[simp] theorem dl_dlB_ne_dlNa : dlB ≠ dlNa := by decide
@[simp] theorem dl_dlB_ne_dlNb : dlB ≠ dlNb := by decide
@[simp] theorem dl_dlB_ne_dlX : dlB ≠ dlX := by decide
@[simp] theorem dl_dlB_ne_dlY : dlB ≠ dlY := by decide
@[simp] theorem dl_dlB_ne_dlR : dlB ≠ dlR := by decide
@[simp] theorem dl_dlB_ne_dlS : dlB ≠ dlS := by decide
@[simp] theorem dl_dlB_ne_kFu : dlB ≠ kFu := by decide
@[simp] theorem dl_dlB_ne_kD : dlB ≠ kD := by decide
@[simp] theorem dl_dlB_ne_lKb : dlB ≠ lKb := by decide
@[simp] theorem dl_dlNb_ne_dlA : dlNb ≠ dlA := by decide
@[simp] theorem dl_dlNb_ne_dlNa : dlNb ≠ dlNa := by decide
@[simp] theorem dl_dlNb_ne_dlB : dlNb ≠ dlB := by decide
@[simp] theorem dl_dlNb_ne_dlX : dlNb ≠ dlX := by decide
@[simp] theorem dl_dlNb_ne_dlY : dlNb ≠ dlY := by decide
@[simp] theorem dl_dlNb_ne_dlR : dlNb ≠ dlR := by decide
@[simp] theorem dl_dlNb_ne_dlS : dlNb ≠ dlS := by decide
@[simp] theorem dl_dlNb_ne_kFu : dlNb ≠ kFu := by decide
@[simp] theorem dl_dlNb_ne_kD : dlNb ≠ kD := by decide
@[simp] theorem dl_dlNb_ne_lKb : dlNb ≠ lKb := by decide
@[simp] theorem dl_dlX_ne_dlA : dlX ≠ dlA := by decide
@[simp] theorem dl_dlX_ne_dlNa : dlX ≠ dlNa := by decide
@[simp] theorem dl_dlX_ne_dlB : dlX ≠ dlB := by decide
@[simp] theorem dl_dlX_ne_dlNb : dlX ≠ dlNb := by decide
@[simp] theorem dl_dlX_ne_dlY : dlX ≠ dlY := by decide
@[simp] theorem dl_dlX_ne_dlR : dlX ≠ dlR := by decide
@[simp] theorem dl_dlX_ne_dlS : dlX ≠ dlS := by decide
@[simp] theorem dl_dlX_ne_kFu : dlX ≠ kFu := by decide
@[simp] theorem dl_dlX_ne_kD : dlX ≠ kD := by decide
@[simp] theorem dl_dlX_ne_lKb : dlX ≠ lKb := by decide
@[simp] theorem dl_dlY_ne_dlA : dlY ≠ dlA := by decide
@[simp] theorem dl_dlY_ne_dlNa : dlY ≠ dlNa := by decide
@[simp] theorem dl_dlY_ne_dlB : dlY ≠ dlB := by decide
@[simp] theorem dl_dlY_ne_dlNb : dlY ≠ dlNb := by decide
@[simp] theorem dl_dlY_ne_dlX : dlY ≠ dlX := by decide
@[simp] theorem dl_dlY_ne_dlR : dlY ≠ dlR := by decide
@[simp] theorem dl_dlY_ne_dlS : dlY ≠ dlS := by decide
@[simp] theorem dl_dlY_ne_kFu : dlY ≠ kFu := by decide
@[simp] theorem dl_dlY_ne_kD : dlY ≠ kD := by decide
@[simp] theorem dl_dlY_ne_lKb : dlY ≠ lKb := by decide
@[simp] theorem dl_dlR_ne_dlA : dlR ≠ dlA := by decide
@[simp] theorem dl_dlR_ne_dlNa : dlR ≠ dlNa := by decide
@[simp] theorem dl_dlR_ne_dlB : dlR ≠ dlB := by decide
@[simp] theorem dl_dlR_ne_dlNb : dlR ≠ dlNb := by decide
@[simp] theorem dl_dlR_ne_dlX : dlR ≠ dlX := by decide
@[simp] theorem dl_dlR_ne_dlY : dlR ≠ dlY := by decide
@[simp] theorem dl_dlR_ne_dlS : dlR ≠ dlS := by decide
@[simp] theorem dl_dlR_ne_kFu : dlR ≠ kFu := by decide
@[simp] theorem dl_dlR_ne_kD : dlR ≠ kD := by decide
@[simp] theorem dl_dlR_ne_lKb : dlR ≠ lKb := by decide
@[simp] theorem dl_dlS_ne_dlA : dlS ≠ dlA := by decide
@[simp] theorem dl_dlS_ne_dlNa : dlS ≠ dlNa := by decide
@[simp] theorem dl_dlS_ne_dlB : dlS ≠ dlB := by decide
@[simp] theorem dl_dlS_ne_dlNb : dlS ≠ dlNb := by decide
@[simp] theorem dl_dlS_ne_dlX : dlS ≠ dlX := by decide
@[simp] theorem dl_dlS_ne_dlY : dlS ≠ dlY := by decide
@[simp] theorem dl_dlS_ne_dlR : dlS ≠ dlR := by decide
@[simp] theorem dl_dlS_ne_kFu : dlS ≠ kFu := by decide
@[simp] theorem dl_dlS_ne_kD : dlS ≠ kD := by decide
@[simp] theorem dl_dlS_ne_lKb : dlS ≠ lKb := by decide
@[simp] theorem dl_kFu_ne_dlA : kFu ≠ dlA := by decide
@[simp] theorem dl_kFu_ne_dlNa : kFu ≠ dlNa := by decide
@[simp] theorem dl_kFu_ne_dlB : kFu ≠ dlB := by decide
@[simp] theorem dl_kFu_ne_dlNb : kFu ≠ dlNb := by decide
@[simp] theorem dl_kFu_ne_dlX : kFu ≠ dlX := by decide
@[simp] theorem dl_kFu_ne_dlY : kFu ≠ dlY := by decide
@[simp] theorem dl_kFu_ne_dlR : kFu ≠ dlR := by decide
@[simp] theorem dl_kFu_ne_dlS : kFu ≠ dlS := by decide
@[simp] theorem dl_kD_ne_dlA : kD ≠ dlA := by decide
@[simp] theorem dl_kD_ne_dlNa : kD ≠ dlNa := by decide
@[simp] theorem dl_kD_ne_dlB : kD ≠ dlB := by decide
@[simp] theorem dl_kD_ne_dlNb : kD ≠ dlNb := by decide
@[simp] theorem dl_kD_ne_dlX : kD ≠ dlX := by decide
@[simp] theorem dl_kD_ne_dlY : kD ≠ dlY := by decide
@[simp] theorem dl_kD_ne_dlR : kD ≠ dlR := by decide
@[simp] theorem dl_kD_ne_dlS : kD ≠ dlS := by decide
@[simp] theorem dl_lKb_ne_dlA : lKb ≠ dlA := by decide
@[simp] theorem dl_lKb_ne_dlNa : lKb ≠ dlNa := by decide
@[simp] theorem dl_lKb_ne_dlB : lKb ≠ dlB := by decide
@[simp] theorem dl_lKb_ne_dlNb : lKb ≠ dlNb := by decide
@[simp] theorem dl_lKb_ne_dlX : lKb ≠ dlX := by decide
@[simp] theorem dl_lKb_ne_dlY : lKb ≠ dlY := by decide
@[simp] theorem dl_lKb_ne_dlR : lKb ≠ dlR := by decide
@[simp] theorem dl_lKb_ne_dlS : lKb ≠ dlS := by decide

def dlParams : List MlS := [kFu, kD, dlA, dlNa, dlB, dlNb]
def dlLocals : List MlS := [dlX, dlY, dlR, dlS]

def dlCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv dlNa) (.const 0)) (.return (.cmp .equal (vv dlNb) (.const 0)))
  (.ite (.cmp .equal (vv dlNb) (.const 0)) (.return (.const 0))
  (.seq (.assign .local dlX (.load .one (vv dlA)))
  (.seq (.assign .local dlY (.load .one (vv dlB)))
  (.seq (.call (some (some (.local, dlR), none)) fD [vv kFu, vv kD, vv dlX, vv dlY])
  (.ite (.cmp .equal (vv dlR) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, dlS), none)) fDl
      [vv kFu, vv kD, .op .add [vv dlA, .const 8], .op .sub [vv dlNa, .const 1],
        .op .add [vv dlB, .const 8], .op .sub [vv dlNb, .const 1]])
    (.return (vv dlS))))))))

def dlBody : ProgHOL 64 := prologue dlLocals dlCore

structure DlCodes (C : Ctx) : Prop where
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  self : C.code.lookup fDl = some (dlParams.map (fun p => (p, ShapeHOL.one)), dlBody, .one)

section
variable {σ : Type}

theorem dl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dlLocals → (ctxEnv C ++ dlParams.zip vals).get x = none :=
  Knot.params_none C dlLocals dlParams vals (by decide) (by decide)

theorem pfx_get {H H1 : List (BitVec 64)} (hp : H <+: H1) {i : Nat} {v : BitVec 64} (h : H[i]? = some v) :
    H1[i]? = some v := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h

theorem ofNat_succ_ne (k : Nat) (hk : k + 1 < 2 ^ 64) : BitVec.ofNat 64 (k + 1) ≠ 0 := by
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

theorem dl_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hc : DlCodes C) (d : Nat)
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H))) :
    ∀ (as bs : List EIdx) (qa qb : Nat) (H : List (BitVec 64)) (s : AState), C.H <+: H →
      (∀ j (hj : j < as.length), H[qa + j]? = some (Enc.idxW as[j])) →
      (∀ j (hj : j < bs.length), H[qb + j]? = some (Enc.idxW bs[j])) →
      as.length < 2 ^ 63 → bs.length < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (dlParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C qa,
        BitVec.ofNat 64 as.length, cellA C qb, BitVec.ofNat 64 bs.length])) dlBody s
        (defEqList (knot mode C n) C.fe d as bs) (PostB (ctxH C H)) := by
  intro as
  induction as with
  | nil =>
    intro bs qa qb H s hp ha hb hla hlb
    refine specR_prologue (postB_locals _) (dl_none _ _) ?_
    unfold dlCore
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    cases bs with
    | nil =>
      exact specR_returnI _ 1 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | cons b bs =>
      have hne := ofNat_succ_ne bs.length (by simp at hlb; omega)
      exact specR_returnI _ 0 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons a as ih =>
    intro bs qa qb H s hp ha hb hla hlb
    refine specR_prologue (postB_locals _) (dl_none _ _) ?_
    unfold dlCore
    have hnea := ofNat_succ_ne as.length (by simp at hla; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnea)
      (fun h => absurd rfl h) (fun _ => ?_)
    cases bs with
    | nil =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | cons b bs =>
      have hneb := ofNat_succ_ne bs.length (by simp at hlb; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hneb)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' (C := ctxH C H) dlX (vv dlA) qa (Enc.idxW a) (ha 0 (by simp) : H[qa]? = some (Enc.idxW a)) (by decide)
        (by simp +decide [sev, Env.get, dlParams, ctxEnv]; rfl) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) dlY (vv dlB) qb (Enc.idxW b) (hb 0 (by simp) : H[qb]? = some (Enc.idxW b)) (by decide)
        (by simp +decide [sev, Env.get, dlParams, ctxEnv]; rfl) ?_
      rw [defEqList]
      refine specR_callNIH (C := ctxH C H) dlR fD dParams [vv kFu, vv kD, vv dlX, vv dlY] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, dlParams, ctxEnv], by simp +decide [Env.get, dlParams, ctxEnv], by simp, by simp,
          trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => hD H s hp a b u hu (fun i hi _ => hlk i (by omega)))
        (fun df w s1 H1 hp1 hw => ?_)
      subst hw
      cases df
      · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
          (fun _ => ?_)
        simp only [ite_true]
        refine specR_congr (m' := defEqList (knot mode C n) C.fe d as bs >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H1) dlS fDl dlParams
          [vv kFu, vv kD, .op .add [vv dlA, .const 8], .op .sub [vv dlNa, .const 1],
            .op .add [vv dlB, .const 8], .op .sub [vv dlNb, .const 1]] dlBody
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C (qa + 1), BitVec.ofNat 64 as.length, cellA C (qb + 1),
            BitVec.ofNat 64 bs.length] (by decide) rfl (by decide) hc.self
          ⟨by simp +decide [Env.get, dlParams, ctxEnv], by simp +decide [Env.get, dlParams, ctxEnv],
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact cellA_add8 C qa,
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact cellA_add8 C qb,
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, trivial⟩
          (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dlParams _ rfl hlk)
            (ih bs (qa + 1) (qb + 1) H1 s1 (hp.trans hp1)
              (fun j hj => by have h := ha (j + 1) (by simp; omega); rw [show qa + (j + 1) = qa + 1 + j by omega] at h; exact pfx_get (H := H) hp1 (by simpa using h))
              (fun j hj => by have h := hb (j + 1) (by simp; omega); rw [show qb + (j + 1) = qb + 1 + j by omega] at h; exact pfx_get (H := H) hp1 (by simpa using h))
              (by simp at hla; omega) (by simp at hlb; omega)))
          (fun r w s2 H2 hp2 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW r) (by simp)
          (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
