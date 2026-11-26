import ConPanqueque.T.Ind.DepthWalk
import ConPanqueque.T.Core.InferLams
import ConPanqueque.T.Core.HasLoose
import ConPanqueque.T.Core.ProjGuardFast

/-!
# `closeTelescope`: a telescope opened at free variables closed back into Π binders

Each domain abstracted over the variables outside it (before the rest is closed), then the body, the ∀ nodes
interned on the way out — the twin's order of effects.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def ctgI := ofString "ctg_i"
def ctgK := ofString "ctg_k"
def ctgS := ofString "ctg_s"
def ctgJ := ofString "ctg_j"
def ctgB := ofString "ctg_b"
def ctgL := ofString "ctg_l"
def ctgA := ofString "ctg_a"
def ctgD := ofString "ctg_d"
def ctgW := ofString "ctg_w"
def ctgR := ofString "ctg_r"
def fCtg := ofString "closeTelescopeGo"

def ctgParams : List MlS := [ctgI, ctgK, ctgS, ctgJ, ctgB]
def ctgLocals : List MlS := [ctgL, ctgA, ctgD, ctgW, ctgR]

def ctgBody : ProgHOL 64 := prologue ctgLocals
  (.seq (.assign .local ctgL (.load .one (vv ctgS)))
  (.ite (.cmp .lower (vv ctgJ) (vv ctgL))
    (.seq (.assign .local ctgA (.load .one (.op .add [.op .add [vv ctgS, .const 8], .shift .lsl (vv ctgJ) (.const 3)])))
    (.seq (.call (some (some (.local, ctgD), none)) fAbsRF
        [.const (BitVec.ofNat 64 coreWalkFuel), vv ctgI, vv ctgK, .const 0, vv ctgA])
    (.seq (.call (some (some (.local, ctgW), none)) fCtg
        [vv ctgI, .op .add [vv ctgK, .const 1], vv ctgS, .op .add [vv ctgJ, .const 1], vv ctgB])
    (.seq (.call (some (some (.local, ctgR), none)) fInternForallE [vv ctgD, vv ctgW]) (.return (vv ctgR))))))
    (.seq (.call (some (some (.local, ctgR), none)) fAbsRF
        [.const (BitVec.ofNat 64 coreWalkFuel), vv ctgI, vv ctgK, .const 0, vv ctgB]) (.return (vv ctgR)))))

structure CTGCodes (C : Ctx) : Prop where
  cR : ExR.CodesR C (ExR.bodyR C)
  absf : C.code.lookup fAbsRF = some (absRFParams.map (fun p => (p, ShapeHOL.one)), ExR.fastBodyR C, .one)
  self : C.code.lookup fCtg = some (ctgParams.map (fun p => (p, ShapeHOL.one)), ctgBody, .one)

section
variable {σ : Type}

theorem ctg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ctgLocals → (ctxEnv C ++ ctgParams.zip vals).get x = none :=
  Knot.params_none C ctgLocals ctgParams vals (by decide) (by decide)

theorem e_succ (n : Nat) : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

set_option maxHeartbeats 4000000 in
/-- **`closeTelescopeGo`** over the domains of a block from `j` on. -/
theorem ctg_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CTGCodes C)
    (i : Nat) (hi : i < 2 ^ 63) (bs : List EIdx) (o : Nat) (hbl : bs.length < 2 ^ 58) (body : EIdx) :
    ∀ f j k (H : List (BitVec 64)) (s : AState), bs.length - j = f → j ≤ bs.length → k + (bs.length - j) < 2 ^ 63 →
      C.H <+: H → BlkAt H o (bs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (ctgParams.zip [BitVec.ofNat 64 i, BitVec.ofNat 64 k, cellA C o,
        BitVec.ofNat 64 j, Enc.idxW body])) ctgBody s (closeTelescopeGo i k (bs.drop j) body) (PostK (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j k H s hf hj hk hp hb
    have hjl : j = bs.length := by omega
    subst hjl
    refine specR_prologue (postK_locals _) (ctg_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ctgL (vv ctgS) o _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, ctgParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, closeTelescopeGo]
    refine specR_congr (m' := abstractRangeFast coreWalkFuel body i k 0 >>= fun r => pure r) (by simp) ?_
    refine ILP.callE_spec (C := ctxH C H) ctgR fAbsRF absRFParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ctgI, vv ctgK, .const 0, vv ctgB] (ExR.fastBodyR C)
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 i, BitVec.ofNat 64 k, BitVec.ofNat 64 0, Enc.idxW body]
      (by decide) rfl (by decide) hc.absf
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv],
        rfl, by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv], trivial⟩
      (ExR.fastR_spec ra (ctxH C H) (ctxOK_H hok H) (codesR_H hc.cR H) s coreWalkFuel i k 0 body
        CV.coreWalkFuel_lt hi (by omega) (by decide)) (fun ta s1 => ?_)
    exact specR_returnI _ (Enc.idxW ta) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j k H s hf hj hk hp hb
    have hjl : j < bs.length := by omega
    refine specR_prologue (postK_locals _) (ctg_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ctgL (vv ctgS) o _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, ctgParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j bs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, ctgParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hjl, closeTelescopeGo]
    have h1 := hb.2 j (by simpa using hjl)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) ctgA _ (o + 1 + j) (Enc.idxW bs[j]) h1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv]; show _ = cellA C (o + 1 + j)
          rw [← cellA_shl C (o + 1) j (by omega), ← cellA_add8]; rfl) ?_
    refine ILP.callE_spec (C := ctxH C H) ctgD fAbsRF absRFParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ctgI, vv ctgK, .const 0, vv ctgA] (ExR.fastBodyR C)
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 i, BitVec.ofNat 64 k, BitVec.ofNat 64 0, Enc.idxW bs[j]]
      (by decide) rfl (by decide) hc.absf
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv],
        rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (ExR.fastR_spec ra (ctxH C H) (ctxOK_H hok H) (codesR_H hc.cR H) s coreWalkFuel i k 0 bs[j]
        CV.coreWalkFuel_lt hi (by omega) (by decide)) (fun ta s1 => ?_)
    refine specR_callNIH (C := ctxH C H) ctgW fCtg ctgParams
      [vv ctgI, .op .add [vv ctgK, .const 1], vv ctgS, .op .add [vv ctgJ, .const 1], vv ctgB] ctgBody
      [BitVec.ofNat 64 i, BitVec.ofNat 64 (k + 1), cellA C o, BitVec.ofNat 64 (j + 1), Enc.idxW body] (by decide) rfl
      (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv]; exact e_succ k,
        by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv]; exact e_succ j,
        by simp +decide [sev, Env.get_cons, Env.get, ctgParams, ctxEnv], trivial⟩
      (PostK (ctxH C H)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctgParams _ rfl hlk)
        (ih (j + 1) (k + 1) H s1 (by omega) (by omega) (by omega) hp hb))
      (fun r w s3 H3 hp3 hw => ?_)
    subst hw
    have hp3' : H <+: H3 := hp3
    refine specR_congr (m' := internForallEE ta r >>= fun x => pure x) (by simp) ?_
    refine specR_internForallEI ra (ctxOK_H (ctxOK_H hok H) H3) (codesR_H (codesR_H hc.cR H) H3).internForallE ctgR (vv ctgD) (vv ctgW) ta r
      (by decide) (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons]) (fun nd s4 => ?_)
    exact specR_returnI _ (Enc.idxW nd) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H3, hp3', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `structUsedLater`: does the rest of a constructor type use field `j` -/

def sulC := ofString "sul_c"
def sulP := ofString "sul_p"
def sulJ := ofString "sul_j"
def sulK := ofString "sul_k"
def sulW := ofString "sul_w"
def sulN := ofString "sul_n"
def sulR := ofString "sul_r"
def sulB := ofString "sul_b"
def fSul := ofString "structUsedLater"

def sulParams : List MlS := [sulC, sulP, sulJ]
def sulLocals : List MlS := [sulK, sulW, sulN, sulR, sulB]

def sulBody : ProgHOL 64 := prologue sulLocals
  (.seq (.assign .local sulK (.op .add [.op .add [vv sulP, vv sulJ], .const 1]))
  (.seq (.call (some (some (.local, sulW), none)) fStripPis [vv sulK, vv sulC])
  (.ite (.cmp .equal (vv sulW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local sulN (.load .one (vv sulW)))
  (.seq (.assign .local sulR (.load .one (.op .add [vv sulW, .shift .lsl (vv sulN) (.const 3)])))
  (.seq (.call (some (some (.local, sulB), none)) fHi [.const 0, .const 1, vv sulR]) (.return (vv sulB))))))))

structure SULCodes (C : Ctx) : Prop where
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  hv : HvCodes C
  hi : C.code.lookup fHi = some (hiParams.map (fun p => (p, ShapeHOL.one)), hiBody, .one)

section
variable {σ : Type}

theorem sul_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ sulLocals → (ctxEnv C ++ sulParams.zip vals).get x = none :=
  Knot.params_none C sulLocals sulParams vals (by decide) (by decide)

/-- **`structUsedLater`**. -/
theorem sul_spec (C : Ctx) (hok : CtxOK C) (hc : SULCodes C) (cty : EIdx) (nP j : Nat) (hk : nP + j + 1 < 2 ^ 64)
    (H : List (BitVec 64)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (sulParams.zip [Enc.idxW cty, BitVec.ofNat 64 nP, BitVec.ofNat 64 j])) sulBody s
      (structUsedLater cty nP j) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (sul_none _ _) ?_
  rw [structUsedLater]
  refine specR_assignI sulK _ (BitVec.ofNat 64 (nP + j + 1)) (by decide)
    (by simp +decide [sev, Env.get, sulParams, ctxEnv]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  refine specR_callNIH (C := ctxH C H) sulW fStripPis [pFu, pH] [vv sulK, vv sulC] (stripBody C fStripPis 6)
    [BitVec.ofNat 64 (nP + j + 1), Enc.idxW cty] (by decide) rfl (by decide) hc.sp
    ⟨by simp +decide [sev, Env.get_cons, Env.get, sulParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, sulParams, ctxEnv], trivial⟩
    (PostSP (ctxH C H)) (fun o w s' H' => (o = none → w = 0) ∧
      ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact stripPis_spec C hok hc.sp (nP + j + 1) hk H s cty _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
  have hpH : H <+: H1 := hp1
  rcases o with _ | ⟨tys, b⟩
  · have e0 := hn rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hpH, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  obtain ⟨ob', rfl, hblk⟩ := hsm tys b rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hblk
  have hHN' : H1.length ≤ C.HN := hHN
  have hne : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hl0 : (ctxH C H1).H[ob']? = some (BitVec.ofNat 64 (tys.length + 1)) := by
    show H1[ob']? = _; rw [hblk.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H1) sulN (vv sulW) ob' _ hl0 (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  have hbw : (ctxH C H1).H[ob' + 1 + tys.length]? = some (Enc.idxW b) := by
    show H1[ob' + 1 + tys.length]? = _
    have := hblk.2 tys.length (by simp); simpa using this
  refine UD.specR_heapLoadI' (C := ctxH C H1) sulR _ (ob' + 1 + tys.length) _ hbw (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C ob' + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  refine specR_congr (m' := hasLooseBVarBFast 0 b >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H1) sulB fHi hiParams [.const 0, .const 1, vv sulR] hiBody
    [BitVec.ofNat 64 0, BitVec.ofNat 64 1, Enc.idxW b] (by decide) rfl (by decide) hc.hi
    ⟨rfl, rfl, by simp [sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H1)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu hiParams _ rfl hlk)
      (hb_spec (ctxH C H1) (ctxOK_H hok H1) (hvCodes_H hc.hv H1) s1 0 b (by unfold coreWalkFuel; decide)))
    (fun r w s3 H3 hp3 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW r) (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H3, hpH.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
