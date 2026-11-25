import ConPanqueque.T.Ind.RecTarget
import ConRon.Arena.Inductives.Positivity

/-!
# The member a head names, and a constructor's member

`memberIdxAt? names lvls e`: a `const` head at the block's own universe arguments `lvls` (an interned list, so
handle equality) names the member it is among `names`; `none` otherwise.  `ctorMember?`: a constructor's
result head (`stripPis (nP + nF)`, `getAppFn`), read by `memberIdxAt?`.

Both return an index word: the member, or `k` (the member count) for `none`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI

/-- An optional member index as a word's number: the index, or `k` for none. -/
def optIdx (k : Nat) : Option Nat → Nat
  | some t => t
  | none => k

def miP := ofString "mi_p"
def miK := ofString "mi_k"
def miL := ofString "mi_l"
def miE := ofString "mi_e"
def miN := ofString "mi_n"
def miU := ofString "mi_u"
def miR := ofString "mi_r"
def fMemberIdx := ofString "memberIdxAt"

def miParams : List MlS := [miP, miK, miL, miE]
def miLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, miN, miU, miR]

def miBody : ProgHOL 64 := prologue miLocals
  (.ite (tagIsE miE 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv miE)) (.seq eViewP
    (.seq (.assign .local miN (.load .one (vv lRp)))
    (.seq (.assign .local miU (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv miU) (vv miL))
      (.seq (.call (some (some (.local, miR), none)) fNameIdx [vv miP, .const 0, vv miK, vv miN]) (.return (vv miR)))
      (.return (vv miK))))))))
    (.return (vv miK)))

section
variable {σ : Type}

theorem mi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ miLocals → (ctxEnv C ++ miParams.zip vals).get x = none :=
  Knot.params_none C miLocals miParams vals (by decide) (by decide)

/-- `names.findIdx?` as a member index: `nameIdxP` from `0`. -/
theorem findIdx_optIdx (blk : List IConstantInfo) (k : Nat) (hk : k ≤ blk.length) (n : NIdx) :
    optIdx k (((blk.take k).map (fun (c : IConstantInfo) => c.name)).findIdx? (· == n)) = nameIdxP blk k n k 0 := by
  rw [nameIdxP_eq blk k hk n k 0 (by omega) (by omega)]
  simp only [List.drop_zero]
  cases (List.findIdx? (fun x => x == n) (List.map (fun (x : IConstantInfo) => x.name) (List.take k blk))) <;>
    simp [Option.elim, optIdx]

theorem findIdx_lt (blk : List IConstantInfo) (k : Nat) (hk : k ≤ blk.length) (n : NIdx) (t : Nat)
    (h : ((blk.take k).map (fun (c : IConstantInfo) => c.name)).findIdx? (· == n) = some t) : t < k := by
  have := List.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨ht, -⟩ := this
  simp at ht; omega

/-- The post of the member-index functions: the word is `optIdx k`, and a member index is below `k`. -/
def PostMI (C : Ctx) (k : Nat) (a : Option Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  PostN C (optIdx k a) w s' st ∧ ∀ t, a = some t → t < k

/-- **`memberIdxAt?`**. -/
theorem mi_spec (C : Ctx)
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k : Nat) (lvls : LsIdx) (e : EIdx) (hk : k ≤ blk.length) (hlen : blk.length < 2 ^ 59)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hb : IndBlk C H ob blk) :
    SpecR (σ := σ) (Pre (ctxH C H) s (miParams.zip [cellA C ob, BitVec.ofNat 64 k, Enc.idxW lvls, Enc.idxW e])) miBody s
      (memberIdxAt? ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls e) (PostMI (ctxH C H) k) := by
  refine specR_prologue (fun a w s' st L ⟨h1, h2⟩ => ⟨postN_locals _ _ w s' st L h1, h2⟩) (mi_none _ _) ?_
  rw [memberIdxAt?]
  have retK : ∀ (Γ : Env) (M : Mem), Γ.get miK = some (BitVec.ofNat 64 k) →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ miLocals)) (.return (vv miK)) s (pure none) (PostMI (ctxH C H) k) :=
    fun Γ M hK => specR_returnI _ (BitVec.ofNat 64 k) (by simpa [sev] using hK)
      (fun t ht => ⟨⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩, fun _ e => by simp at e⟩)
  refine Knot.specR_tagIteV miE e 3 (by decide) (by decide) (by simp +decide [Env.get, miParams, ctxEnv])
    (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [ite_eq_right (show ¬ (e.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    refine retK _ _ ?_
    simp +decide [Env.get, miParams, ctxEnv]
  rw [ite_eq_left (show (e.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by simp +decide [ctxLocals, miLocals])
    (by simp +decide [Env.get, miParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv miE) (Enc.idxW e) (by simp +decide [ctxLocals, miLocals])
    (by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv]) ?_
  refine ConPanqueque.T.Big.specR_viewP e (by simp) (by simp +decide [Env.get_cons, Env.get, miParams, ctxEnv] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, miParams, ctxEnv] <;> rfl) (by simp +decide [ctxLocals, miLocals])
    (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨cj, us, rfl⟩ := UD.tagN_const h3
  have hvc : s.store.viewConst e = some (cj, us) := ConPanqueque.T.WC.viewConst_of_view (by rw [htc]; rfl) hv
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' miN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cj) (by simp +decide [ctxLocals, miLocals])
    (by simp [sev, Env.get_cons]) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW cj) [Enc.idxW us] []) ?_
  refine specR_loadI' miU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by simp +decide [ctxLocals, miLocals])
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW cj) (Enc.idxW us) [] []) ?_
  by_cases hu : us = lvls
  · subst hu
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ite_true]
    refine specR_congr (m' := (pure (nameIdxP blk k cj k 0) : AM Nat) >>= fun _ =>
        pure (((blk.take k).map (fun (c : IConstantInfo) => c.name)).findIdx? (· == cj))) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) miR fNameIdx niParams [vv miP, .const 0, vv miK, vv miN] niBody
      [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 k, Enc.idxW cj] (by decide) rfl
      (by simp +decide [ctxLocals, miLocals]) hcn
      ⟨by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (fun a w s' st => (pure (nameIdxP blk k cj k 0) : AM Nat) s = .ok (a, s') ∧ PostN (ctxH C H) a w s' st)
      (fun r w _ _ => w = BitVec.ofNat 64 r ∧ r = nameIdxP blk k cj k 0)
      (fun r w s' st ⟨hrun, H', hp', hw, hsr⟩ => by
        have hr : r = nameIdxP blk k cj k 0 := by
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun; exact hrun.1.symm
        exact ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu niParams _ rfl hlk)
        (ni_spec C hcn blk ob k cj hk hlen k 0 H s hp hb (by omega) (by omega))))
      (fun r w s1 H1 hp1 ⟨hw, hr⟩ => ?_)
    subst hw; subst hr
    exact specR_returnI _ (BitVec.ofNat 64 (nameIdxP blk k cj k 0)) (by simp +decide [Env.get])
      (fun t ht => ⟨⟨H1, hp1, by rw [findIdx_optIdx blk k hk cj], sr_of_eq ht.sr rfl rfl rfl rfl⟩,
        fun t' ht' => findIdx_lt blk k hk cj t' ht'⟩)
  · have hne : Enc.idxW us ≠ Enc.idxW lvls := fun h => hu (ConPanqueque.V.Enc.idxW_inj h)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, miParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
    have hb' : (us == lvls) = false := by simpa using hu
    simp only [hb', Bool.false_eq_true, ite_false]
    refine retK _ _ ?_
    simp +decide [Env.get_cons, Env.get, miParams, ctxEnv]

end

end ConPanqueque.T.Ind
