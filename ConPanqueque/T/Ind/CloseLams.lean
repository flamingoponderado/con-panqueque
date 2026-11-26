import ConPanqueque.T.Ind.CloseTele

/-!
# `closeLams`: a telescope opened at free variables closed back into λ binders

`closeLamsGo`'s program with the λ intern in place of the ∀ intern (the generated rules' closing).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def clmI := ofString "clm_i"
def clmK := ofString "clm_k"
def clmS := ofString "clm_s"
def clmJ := ofString "clm_j"
def clmB := ofString "clm_b"
def clmL := ofString "clm_l"
def clmA := ofString "clm_a"
def clmD := ofString "clm_d"
def clmW := ofString "clm_w"
def clmR := ofString "clm_r"
def fClm := ofString "closeLamsGo"

def clmParams : List MlS := [clmI, clmK, clmS, clmJ, clmB]
def clmLocals : List MlS := [clmL, clmA, clmD, clmW, clmR]

def clmBody : ProgHOL 64 := prologue clmLocals
  (.seq (.assign .local clmL (.load .one (vv clmS)))
  (.ite (.cmp .lower (vv clmJ) (vv clmL))
    (.seq (.assign .local clmA (.load .one (.op .add [.op .add [vv clmS, .const 8], .shift .lsl (vv clmJ) (.const 3)])))
    (.seq (.call (some (some (.local, clmD), none)) fAbsRF
        [.const (BitVec.ofNat 64 coreWalkFuel), vv clmI, vv clmK, .const 0, vv clmA])
    (.seq (.call (some (some (.local, clmW), none)) fClm
        [vv clmI, .op .add [vv clmK, .const 1], vv clmS, .op .add [vv clmJ, .const 1], vv clmB])
    (.seq (.call (some (some (.local, clmR), none)) fInternLam [vv clmD, vv clmW]) (.return (vv clmR))))))
    (.seq (.call (some (some (.local, clmR), none)) fAbsRF
        [.const (BitVec.ofNat 64 coreWalkFuel), vv clmI, vv clmK, .const 0, vv clmB]) (.return (vv clmR)))))

structure CLMCodes (C : Ctx) : Prop where
  cR : ExR.CodesR C (ExR.bodyR C)
  absf : C.code.lookup fAbsRF = some (absRFParams.map (fun p => (p, ShapeHOL.one)), ExR.fastBodyR C, .one)
  self : C.code.lookup fClm = some (clmParams.map (fun p => (p, ShapeHOL.one)), clmBody, .one)

section
variable {σ : Type}

theorem clm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ clmLocals → (ctxEnv C ++ clmParams.zip vals).get x = none :=
  Knot.params_none C clmLocals clmParams vals (by decide) (by decide)

set_option maxHeartbeats 4000000 in
/-- **`closeLamsGo`** over the domains of a block from `j` on. -/
theorem clm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CLMCodes C)
    (i : Nat) (hi : i < 2 ^ 63) (bs : List EIdx) (o : Nat) (hbl : bs.length < 2 ^ 58) (body : EIdx) :
    ∀ f j k (H : List (BitVec 64)) (s : AState), bs.length - j = f → j ≤ bs.length → k + (bs.length - j) < 2 ^ 63 →
      C.H <+: H → BlkAt H o (bs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (clmParams.zip [BitVec.ofNat 64 i, BitVec.ofNat 64 k, cellA C o,
        BitVec.ofNat 64 j, Enc.idxW body])) clmBody s (closeLamsGo i k (bs.drop j) body) (PostK (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j k H s hf hj hk hp hb
    have hjl : j = bs.length := by omega
    subst hjl
    refine specR_prologue (postK_locals _) (clm_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) clmL (vv clmS) o _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, clmParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, closeLamsGo]
    refine specR_congr (m' := abstractRangeFast coreWalkFuel body i k 0 >>= fun r => pure r) (by simp) ?_
    refine ILP.callE_spec (C := ctxH C H) clmR fAbsRF absRFParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv clmI, vv clmK, .const 0, vv clmB] (ExR.fastBodyR C)
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 i, BitVec.ofNat 64 k, BitVec.ofNat 64 0, Enc.idxW body]
      (by decide) rfl (by decide) hc.absf
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv],
        rfl, by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv], trivial⟩
      (ExR.fastR_spec ra (ctxH C H) (ctxOK_H hok H) (codesR_H hc.cR H) s coreWalkFuel i k 0 body
        CV.coreWalkFuel_lt hi (by omega) (by decide)) (fun ta s1 => ?_)
    exact specR_returnI _ (Enc.idxW ta) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j k H s hf hj hk hp hb
    have hjl : j < bs.length := by omega
    refine specR_prologue (postK_locals _) (clm_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) clmL (vv clmS) o _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, clmParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j bs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, clmParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hjl, closeLamsGo]
    have h1 := hb.2 j (by simpa using hjl)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) clmA _ (o + 1 + j) (Enc.idxW bs[j]) h1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv]; show _ = cellA C (o + 1 + j)
          rw [← cellA_shl C (o + 1) j (by omega), ← cellA_add8]; rfl) ?_
    refine ILP.callE_spec (C := ctxH C H) clmD fAbsRF absRFParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv clmI, vv clmK, .const 0, vv clmA] (ExR.fastBodyR C)
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 i, BitVec.ofNat 64 k, BitVec.ofNat 64 0, Enc.idxW bs[j]]
      (by decide) rfl (by decide) hc.absf
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv],
        rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (ExR.fastR_spec ra (ctxH C H) (ctxOK_H hok H) (codesR_H hc.cR H) s coreWalkFuel i k 0 bs[j]
        CV.coreWalkFuel_lt hi (by omega) (by decide)) (fun ta s1 => ?_)
    refine specR_callNIH (C := ctxH C H) clmW fClm clmParams
      [vv clmI, .op .add [vv clmK, .const 1], vv clmS, .op .add [vv clmJ, .const 1], vv clmB] clmBody
      [BitVec.ofNat 64 i, BitVec.ofNat 64 (k + 1), cellA C o, BitVec.ofNat 64 (j + 1), Enc.idxW body] (by decide) rfl
      (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv]; exact e_succ k,
        by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv]; exact e_succ j,
        by simp +decide [sev, Env.get_cons, Env.get, clmParams, ctxEnv], trivial⟩
      (PostK (ctxH C H)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu clmParams _ rfl hlk)
        (ih (j + 1) (k + 1) H s1 (by omega) (by omega) (by omega) hp hb))
      (fun r w s3 H3 hp3 hw => ?_)
    subst hw
    have hp3' : H <+: H3 := hp3
    refine specR_congr (m' := internLamE ta r >>= fun x => pure x) (by simp [internE]) ?_
    refine specR_internLamI ra (ctxOK_H (ctxOK_H hok H) H3) (codesR_H (codesR_H hc.cR H) H3).internLam clmR (vv clmD) (vv clmW) ta r
      (by decide) (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons]) (fun nd s4 => ?_)
    exact specR_returnI _ (Enc.idxW nd) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H3, hp3', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
