import ConPanqueque.T.Ind.NameIdx
import ConPanqueque.T.Core.CtorView
import ConRon.Arena.Inductives.BlockShape

/-!
# `recTargetOf`: the member a recursor's major premise names

Strip the `mI` binders the record claims (`stripPis`); the next binder is the major premise, and its domain's
head constant is looked up among the block's member names (`nameIdx`); `k` (no member) otherwise.

`rt(p, k, mI, ty)`: the block at `p`, its first `k` records the members.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI

def rtP := ofString "rt_p"
def rtK := ofString "rt_k"
def rtM := ofString "rt_m"
def rtT := ofString "rt_t"
def rtR := ofString "rt_r"
def rtL := ofString "rt_l"
def rtB := ofString "rt_b"
def rtD := ofString "rt_d"
def rtN := ofString "rt_n"
def rtH := ofString "rt_h"
def fRecTarget := ofString "recTargetOf"

def rtParams : List MlS := [rtP, rtK, rtM, rtT]
def rtLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, rtR, rtL, rtB, rtD, rtN, rtH]

def rtBody (C : Ctx) : ProgHOL 64 := prologue rtLocals
  (.seq (.call (some (some (.local, rtR), none)) fStripPis [vv rtM, vv rtT])
  (.ite (.cmp .equal (vv rtR) (.const 0)) (.return (vv rtK))
  (.seq (.assign .local rtL (.load .one (vv rtR)))
  (.seq (.assign .local rtB (.load .one (.op .add [vv rtR, .shift .lsl (vv rtL) (.const 3)])))
  (.ite (tagIsE rtB 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv rtB)) (.seq eViewP
    (.seq (.assign .local rtD (.load .one (vv lRp)))
    (.seq (.call (some (some (.local, rtH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv rtD])
    (.ite (tagIsE rtH 3)
      (.seq (.assign .local lDh (vv rtH)) (.seq eViewP
      (.seq (.assign .local rtN (.load .one (vv lRp)))
      (.seq (.call (some (some (.local, rtR), none)) fNameIdx [vv rtP, .const 0, vv rtK, vv rtN])
        (.return (vv rtR))))))
      (.return (vv rtK))))))))
    (.return (vv rtK)))))))

section
variable {σ : Type}

theorem rt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rtLocals → (ctxEnv C ++ rtParams.zip vals).get x = none :=
  Knot.params_none C rtLocals rtParams vals (by decide) (by decide)

theorem shl3_ofNat (a : Nat) : BitVec.ofNat 64 a <<< (3 : Nat) = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod]; ring_nf

theorem cellA_shl3 (C : Ctx) (o a : Nat) :
    cellA C o + BitVec.ofNat 64 a <<< (3 : Nat) = cellA C (o + a) := by
  rw [shl3_ofNat]; simp only [cellA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; ring_nf

/-- `names.findIdx?` over the block's member names, as `nameIdxP` from `0`. -/
theorem findIdx_names (blk : List IConstantInfo) (k : Nat) (hk : k ≤ blk.length) (n : NIdx) :
    (match ((blk.take k).map (fun (c : IConstantInfo) => c.name)).findIdx? (· == n) with
      | some t => (pure t : AM Nat)
      | none => pure ((blk.take k).map (fun (c : IConstantInfo) => c.name)).length) = pure (nameIdxP blk k n k 0) := by
  rw [nameIdxP_eq blk k hk n k 0 (by omega) (by omega)]
  simp only [List.drop_zero, List.length_map, List.length_take, Nat.min_eq_left hk]
  cases (List.findIdx? (fun x => x == n) (List.map (fun (x : IConstantInfo) => x.name) (List.take k blk))) <;> simp [Option.elim]

/-- **`recTargetOf`**. -/
theorem rt_spec (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k mI : Nat) (ty : EIdx) (hk : k ≤ blk.length) (hlen : blk.length < 2 ^ 59)
    (hmI : mI < 2 ^ 64) (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hb : IndBlk C H ob blk) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rtParams.zip [cellA C ob, BitVec.ofNat 64 k, BitVec.ofNat 64 mI, Enc.idxW ty]))
      (rtBody C) s (recTargetOf ((blk.take k).map (fun (c : IConstantInfo) => c.name)) mI ty)
        (fun a w s' st => PostN (ctxH C H) a w s' st ∧ a ≤ k) := by
  refine specR_prologue (fun a w s' st L ⟨h1, h2⟩ => ⟨postN_locals _ a w s' st L h1, h2⟩) (rt_none _ _) ?_
  rw [recTargetOf]
  have hnl : ((blk.take k).map (fun (c : IConstantInfo) => c.name)).length = k := by simp; omega
  refine specR_callNIH (C := ctxH C H) rtR fStripPis [pFu, pH] [vv rtM, vv rtT] (stripBody C fStripPis 6)
    [BitVec.ofNat 64 mI, Enc.idxW ty] (by decide) rfl (by simp +decide [ctxLocals, rtLocals]) hcs
    ⟨by simp +decide [sev, Env.get, rtParams, ctxEnv], by simp +decide [sev, Env.get, rtParams, ctxEnv], trivial⟩
    (PostSP (ctxH C H)) (fun o w s' H' => (o = none → w = 0) ∧
      ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact stripPis_spec C hok hcs mI hmI H s ty _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
  have hpH : H <+: H1 := hp1
  have hb1 : IndBlk C H1 ob blk := indBlk_mono hb hpH
  let Γ0 : Env := ctxEnv (ctxH C H) ++ rtParams.zip [cellA C ob, BitVec.ofNat 64 k, BitVec.ofNat 64 mI, Enc.idxW ty]
  have gP : ∀ (Γ : Env), (∀ y, y ∈ rtParams → Γ.get y = Γ0.get y) → Γ.get rtP = some (cellA C ob) ∧
      Γ.get rtK = some (BitVec.ofNat 64 k) := fun Γ h => by
    rw [h rtP (by decide), h rtK (by decide)]; simp +decide [Γ0, Env.get, rtParams, ctxEnv]
  have retK : ∀ (Γ : Env) (H2 : List (BitVec 64)) (s2 : AState), H <+: H2 → Γ.get rtK = some (BitVec.ofNat 64 k) →
      SpecR (σ := σ) (Inv (ctxH C H2) s2 Γ [] (ctxLocals ++ rtLocals)) (.return (vv rtK)) s2 (pure k)
        (fun a w s' st => PostN (ctxH C H) a w s' st ∧ a ≤ k) :=
    fun Γ H2 s2 h2 hK => specR_returnI _ (BitVec.ofNat 64 k) (by simpa [sev] using hK)
      (fun t ht => ⟨⟨H2, h2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩, le_refl _⟩)
  rcases o with _ | ⟨tys, b⟩
  · have e0 := hn rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [hnl]
    exact retK _ H1 s1 hpH (by simp +decide [Env.get_cons, Env.get, rtParams, ctxEnv])
  · obtain ⟨ob', rfl, hblk⟩ := hsm tys b rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
    have hol := blkAt_lt hblk
    have hHN' : H1.length ≤ C.HN := hHN
    have hne : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    -- the block's length word, then the body behind the binder types
    have hl0 : (ctxH C H1).H[ob']? = some (BitVec.ofNat 64 (tys.length + 1)) := by
      show H1[ob']? = _; rw [hblk.1]; simp
    refine UD.specR_heapLoadI' (C := ctxH C H1) rtL (vv rtR) ob' _ hl0 (by simp +decide [ctxLocals, rtLocals])
      (by simp [sev, Env.get_cons]; rfl) ?_
    have hbw : (ctxH C H1).H[ob' + 1 + tys.length]? = some (Enc.idxW b) := by
      show H1[ob' + 1 + tys.length]? = _
      have := hblk.2 tys.length (by simp); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H1) rtB _ (ob' + 1 + tys.length) _ hbw (by simp +decide [ctxLocals, rtLocals])
      (by
        simp only [sev, sev_vv, Env.get_cons]; simp +decide
        show cellA C ob' + _ = cellA C _
        rw [cellA_shl3]; congr 1; omega) ?_
    dsimp only
    refine Knot.specR_tagIteV rtB b 6 (by decide) (by decide) (by simp [Env.get_cons]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [ite_eq_right (show ¬ (b.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      simp only [hnl]
      refine retK _ H1 s1 hpH ?_
      simp +decide [Env.get, rtParams, ctxEnv]
    rw [ite_eq_left (show (b.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by simp +decide [ctxLocals, rtLocals])
      (by simp +decide [Env.get_cons, Env.get, rtParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv rtB) (Enc.idxW b) (by simp +decide [ctxLocals, rtLocals]) (by simp +decide [sev, Env.get_cons]) ?_
    refine specR_viewXI ConRon.Arena.viewBind projBind b (fun vw hvw => viewBind_run b (Or.inr htg) s1 vw hvw)
      (by simp) (by simp +decide <;> rfl) (by simp +decide [Env.get_cons, Env.get, rtParams, ctxEnv] <;> rfl)
      (by simp +decide [ctxLocals, rtLocals]) (fun vw P htgv hsh => ?_)
    obtain ⟨dom, bd, hpb, hwv⟩ : ∃ dom bd, projBind vw = some (dom, bd) ∧ encEView vw = [Enc.idxW dom, Enc.idxW bd] := by
      have htT : b.tag.toNat = 6 := by rw [htg]; simp
      rw [htT] at htgv
      cases vw with
      | lam ty b => exact ⟨ty, b, rfl, rfl⟩
      | forallE ty b => exact ⟨ty, b, rfl, rfl⟩
      | _ => simp [ENodeView.tagN] at htgv <;> omega
    rw [hpb]; simp only
    refine specR_loadI' rtD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by simp +decide [ctxLocals, rtLocals])
      (by simp [sev, Env.get_cons]) (by simp) (by rw [hwv]; exact wordsAt_mem0 _ _ _ _) ?_
    refine specR_callNIM rtH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv rtD]
      getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom] (by decide) rfl (by simp +decide [ctxLocals, rtLocals]) hcg
      ⟨rfl, by simp [sev, Env.get_cons], trivial⟩
      (fun a w s' st => getAppFn coreWalkFuel dom s1 = .ok (a, s') ∧ Post (ctxH C H1) s1 a w s' st)
      (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
      (fun u hu _ hlk => specR_run (fun t ht => by
        subst ht
        exact getAppFn_spec (ctxH C H1) hcg coreWalkFuel dom s1 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
      (fun hh w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
    subst hw
    have hs' : s1 = s' := hs.symm
    subst hs'
    refine Knot.specR_tagIteV rtH hh 3 (by decide) (by decide) (by simp [Env.get_cons]) (fun htc => ?_) (fun htc => ?_)
    swap
    · rw [ite_eq_right (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htc)]
      simp only [hnl]
      refine retK _ H1 s1 hpH ?_
      simp +decide [Env.get, rtParams, ctxEnv]
    rw [ite_eq_left (show (hh.tag == ETag.const) = true by simp [htc, ETag.const])]
    refine specR_assignI lDh (vv rtH) (Enc.idxW hh) (by simp +decide [ctxLocals, rtLocals]) (by simp +decide [sev, Env.get_cons]) ?_
    refine ConPanqueque.T.Big.specR_viewP hh (by simp) (by simp +decide [Env.get_cons, Env.get, rtParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, rtParams, ctxEnv] <;> rfl) (by simp +decide [ctxLocals, rtLocals])
      (fun v P' hv htn _ => ?_)
    have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
    obtain ⟨cj, us, rfl⟩ := UD.tagN_const h3
    have hvc : s1.store.viewConst hh = some (cj, us) := ConPanqueque.T.WC.viewConst_of_view (by rw [htc]; rfl) hv
    refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
    dsimp only
    refine specR_loadI' rtN (vv lRp) P' (P' + BitVec.ofNat 64 0) (Enc.idxW cj) (by simp +decide [ctxLocals, rtLocals])
      (by simp [sev, Env.get_cons]) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P' (Enc.idxW cj) [Enc.idxW us] []) ?_
    refine specR_congr (m' := (pure (nameIdxP blk k cj k 0) : AM Nat) >>= fun r => pure r)
      (by rw [bind_pure]; exact congrFun (findIdx_names blk k hk cj) s1) ?_
    refine specR_callNIH (C := ctxH C H1) rtR fNameIdx niParams [vv rtP, .const 0, vv rtK, vv rtN] niBody
      [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 k, Enc.idxW cj] (by decide) rfl
      (by simp +decide [ctxLocals, rtLocals]) hcn
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rtParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, rtParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (fun a w s' st => (pure (nameIdxP blk k cj k 0) : AM Nat) s1 = .ok (a, s') ∧ PostN (ctxH C H1) a w s' st)
      (fun r w _ _ => w = BitVec.ofNat 64 r ∧ r ≤ k)
      (fun r w s' st ⟨hrun, H', hp', hw, hsr⟩ => by
        have hr : r = nameIdxP blk k cj k 0 := by
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun; exact hrun.1.symm
        exact ⟨H', hp', ⟨hw, hr ▸ nameIdxP_le _ _ _ _ _⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu niParams _ rfl hlk)
        (ni_spec C hcn blk ob k cj hk hlen k 0 H1 s1 (hp.trans hpH) hb1 (by omega) (by omega))))
      (fun r w s2 H2 hp2 ⟨hw, hrk⟩ => ?_)
    subst hw
    exact specR_returnI _ _ (by simp +decide [Env.get])
      (fun t' ht' => ⟨⟨H2, hpH.trans hp2, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩, hrk⟩)

end

end ConPanqueque.T.Ind
