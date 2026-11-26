import ConPanqueque.T.Ind.StreamChk
import ConPanqueque.T.Ind.NestFields
import ConPanqueque.T.Ind.AnnEq
import ConPanqueque.T.Ex.InstLift

/-!
# A structure's projection bodies (`structProjBodiesGo`)

`spgBody`: field `i`'s domain instantiated at the values so far (`instantiateLiftFast`), the field's own value
`.proj T i (bvar 0)` appended to the values, the rest of the telescope next; a binder that is not a `∀` hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC ConPanqueque.T.ExIL

def spgT := ofString "spg_t"
def spgVs := ofString "spg_vs"
def spgVn := ofString "spg_vn"
def spgK := ofString "spg_k"
def spgI := ofString "spg_i"
def spgH := ofString "spg_h"
def spgD := ofString "spg_d"
def spgB := ofString "spg_b"
def spgBb := ofString "spg_bb"
def spgZ := ofString "spg_z"
def spgA := ofString "spg_a"
def spgV2 := ofString "spg_v2"
def fSpg := ofString "structProjBodiesGo"

def spgParams : List MlS := [spgT, spgVs, spgVn, spgK, spgI, spgH]
def spgLocals : List MlS := gaaLocals ++ [spgD, spgB, spgBb, spgZ, spgA, spgV2]

def spgBody (C : Ctx) : ProgHOL 64 := prologue spgLocals
  (.ite (.cmp .equal (vv spgK) (.const 0))
    (alloc1 C lW (.const 0) (.return (vv lW)))
    (.ite (tagIsE spgH 6)
      (viewOf spgH
      (.seq (.assign .local spgD (.load .one (vv lRp)))
      (.seq (.assign .local spgB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, spgBb), none)) fInstLF
          [vv spgVs, vv spgVn, .const (BitVec.ofNat 64 coreWalkFuel), vv spgD, .const 0])
      (.seq (.call (some (some (.local, spgZ), none)) fInternBVar [.const 0])
      (.seq (.call (some (some (.local, spgA), none)) fInternProj [vv spgT, vv spgZ, vv spgI])
      (.seq (.call (some (some (.local, spgV2), none)) ExPre.fAppend [vv spgVs, vv spgA])
      (.seq (.call (some (some (.local, ExS.lY), none)) fSpg
          [vv spgT, vv spgV2, .op .add [vv spgVn, .const 1], .op .sub [vv spgK, .const 1], .op .add [vv spgI, .const 1],
            vv spgB])
        (prependP C spgBb)))))))))
      hang))

structure SPGCodes (C : Ctx) : Prop where
  ilf : C.code.lookup fInstLF = some (ilParams.map (fun p => (p, ShapeHOL.one)), fastBodyIL C, .one)
  il : CodesIL C
  bv : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  pj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fSpg = some (spgParams.map (fun p => (p, ShapeHOL.one)), spgBody C, .one)

section
variable {σ : Type}

theorem spg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ spgLocals → (ctxEnv C ++ spgParams.zip vals).get x = none :=
  Knot.params_none C spgLocals spgParams vals (by decide) (by decide)

set_option maxHeartbeats 32000000 in
/-- **`structProjBodiesGo`**, `k` binders from field `i` on at the values `vs`. -/
theorem spg_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : SPGCodes C)
    (T : NIdx) :
    ∀ k (vs : Array EIdx) (ov i : Nat) (H : List (BitVec 64)) (s : AState) (h : EIdx), C.H <+: H →
      BlkAt H ov (vs.toList.map Enc.idxW) → vs.size + k < 2 ^ 58 → i + k < 2 ^ 62 →
      SpecR (σ := σ) (Pre (ctxH C H) s (spgParams.zip [Enc.idxW T, cellA C ov, BitVec.ofNat 64 vs.size,
        BitVec.ofNat 64 k, BitVec.ofNat 64 i, Enc.idxW h])) (spgBody C) s (structProjBodiesGo T vs k i h)
        (PostSL (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro vs ov i H s h hp hvs hk hi
    refine specR_prologue (postSL_locals _) (spg_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, spgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [structProjBodiesGo]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨[], _, H2.length, rfl,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro vs ov i H s h hp hvs hk hi
    refine specR_prologue (postSL_locals _) (spg_none _ _) ?_
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0#64 := fun e => by have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, spgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [structProjBodiesGo]
    obtain ⟨w, hw, hiff⟩ := sev_tagIs (ctxEnv (ctxH C H) ++ spgParams.zip [Enc.idxW T, cellA C ov, BitVec.ofNat 64 vs.size,
      BitVec.ofNat 64 (k + 1), BitVec.ofNat 64 i, Enc.idxW h]) spgH h (by simp +decide [Env.get, spgParams, ctxEnv]) 6 (by omega) (by omega)
    by_cases ht : h.tag = UInt32.ofNat 6
    case neg =>
      exact specR_ifI _ w hw (fun e' => absurd (hiff.mp e') ht) (fun _ => specR_hangI)
    have hb : (h.tag == ETag.forallE) = true := by simp [ht]; rfl
    rw [hb]; simp only [ite_true]
    refine specR_ifI _ w hw (fun _ => ?_) (fun e' => absurd (hiff.mpr ht) (by simp [e']))
    unfold viewOf
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, spgParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv spgH) (Enc.idxW h) (by decide) (by simp +decide [Env.get_cons, Env.get, spgParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, spgParams, ctxEnv] <;> rfl) (by decide) (fun ve P hve htne hlene => ?_)
    have htT : h.tag.toNat = 6 := by rw [ht]; simp
    rcases ve with _ | _ | _ | _ | _ | _ | ⟨dom, bd⟩ | _ | _ | _ <;> simp [ENodeView.tagN, htT] at htne
    refine specR_runBind (show ConRon.Arena.view h s = .ok (.forallE dom bd, s) by rw [view_run, hve]) ?_
    simp only
    refine specR_loadI' spgD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp +decide [sev]) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW bd] []) ?_
    refine specR_loadI' spgB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp +decide [sev, Env.get_cons]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW bd) [] []) ?_
    have hvsz : vs.size < 2 ^ 59 := by omega
    have hVs : VsAt (ctxH C H) ov vs := ⟨hvsz, fun j hj => by
      have := hvs.2 j (by simp; omega); simp at this; exact this⟩
    refine ILP.callE_spec (C := ctxH C H) spgBb fInstLF ilParams
      [vv spgVs, vv spgVn, .const (BitVec.ofNat 64 coreWalkFuel), vv spgD, .const 0] (fastBodyIL C)
      [cellA C ov, BitVec.ofNat 64 vs.size, BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom, BitVec.ofNat 64 0] (by decide) rfl
      (by decide) hc.ilf
      ⟨by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv],
        rfl, by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (fastIL_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.il) ov vs hVs s coreWalkFuel dom 0 coreWalkFuel_lt63 (by decide))
      (fun b s1 => ?_)
    simp only [structProjArgP, bind_assoc]
    refine specR_internBVarI ra (ctxOK_H hok H) hc.bv spgZ (.const 0) 0 (by decide) (by decide) (by simp [sev]) (fun z s2 => ?_)
    refine specR_internProjI ra (ctxOK_H hok H) hc.pj spgA (vv spgT) (vv spgZ) (vv spgI) T i z (by omega) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv]) (by simp +decide [sev, Env.get_cons])
      (by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv]) (fun a s3 => ?_)
    refine specR_appendI (ctxOK_H hok H) hc.app H spgV2 (vv spgVs) (vv spgA) (vs.toList.map Enc.idxW) (Enc.idxW a) ov hvs
      (by decide) (by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv]; rfl) (by simp +decide [sev, Env.get_cons])
      (fun H4 ov' hp4 hb4 => ?_)
    have hb4' : BlkAt H4 ov' ((vs.push a).toList.map Enc.idxW) := by simpa using hb4
    have hpC4 : C.H <+: H4 := hp.trans hp4
    have hsub : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    refine specR_callNIH (C := ctxH C H4) ExS.lY fSpg spgParams
      [vv spgT, vv spgV2, .op .add [vv spgVn, .const 1], .op .sub [vv spgK, .const 1], .op .add [vv spgI, .const 1], vv spgB]
      (spgBody C) [Enc.idxW T, cellA C ov', BitVec.ofNat 64 (vs.push a).size, BitVec.ofNat 64 k, BitVec.ofNat 64 (i + 1),
        Enc.idxW bd] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv], by simp +decide [sev, Env.get_cons]; rfl,
        by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv]; exact word_add1_eq _,
        by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv]; exact hsub,
        by simp +decide [sev, Env.get_cons, Env.get, spgParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostSL (ctxH C H4)) (fun o w _ H' => ∃ ds ob, o = some ds ∧ w = cellA C ob ∧ BlkAt H' ob (ds.map Enc.idxW))
      (fun o w s' st ⟨ds, H', ob, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, ob, h0, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu spgParams _ rfl hlk)
        (ih (vs.push a) ov' (i + 1) H4 s3 bd hpC4 hb4' (by simp; omega) (by omega)))
      (fun o w s4 H5 hp5 ⟨ds, ob, ho, hw, hb⟩ => ?_)
    subst ho hw
    have hp5' : H4 <+: H5 := hp5
    simp only
    refine ExPre.prepend_spec C hok (H := H5) spgBb (Enc.idxW b) ob (ds.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hb (by decide)
      (by simp +decide [Env.get_cons, Env.get, spgParams, ctxEnv]) (by decide) (fun H' o t hp' hb' hsr => ?_)
    exact ⟨b :: ds, H', o, rfl, hp4.trans (hp5'.trans hp'), rfl, by simpa using hb', hsr⟩

end

end ConPanqueque.T.Ind
