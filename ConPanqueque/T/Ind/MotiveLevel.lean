import ConPanqueque.T.Ind.PiTele
import ConPanqueque.T.Ind.ReadBlock
import ConPanqueque.T.Core.FormerSort
import ConPanqueque.T.Ex.Inst1

/-!
# `motiveLevel?`: the sort level of a recursor's motive

The motive application `body` has a prefix variable as its head (de Bruijn `k`, behind the `nIdx` indices and
the major); that binder's domain, read through `formerResSort`, ends in a sort.  `motiveLevel(p, L, n, b)`:
the prefix's `L` domains in cells from `p + 1`.  An index too big for a word halts (always allowed).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI ConPanqueque.T.WC

def mlP := ofString "ml_p"
def mlL := ofString "ml_l"
def mlN := ofString "ml_n"
def mlB := ofString "ml_b"
def mlH := ofString "ml_h"
def mlK := ofString "ml_k"
def mlI := ofString "ml_i"
def mlD := ofString "ml_d"
def mlR := ofString "ml_r"
def fMotiveLevel := ofString "motiveLevel"

def mlParams : List MlS := [mlP, mlL, mlN, mlB]
def mlLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, mlH, mlK, mlI, mlD, mlR]

def mlRest : ProgHOL 64 :=
  .ite (.shift .lsr (vv mlK) (.const 63)) hang
  (.ite (.cmp .lower (vv mlK) (.op .add [vv mlN, .const 1])) (.return (.const 0))
  (.ite (.cmp .lower (vv mlK) (.op .add [.op .add [vv mlN, .const 1], vv mlL]))
    (.seq (.assign .local mlI (.op .sub [.op .sub [vv mlL, .const 1], .op .sub [vv mlK, .op .add [vv mlN, .const 1]]]))
    (.seq (.assign .local mlD (.load .one (.op .add [vv mlP, .op .add [.panop .mul [vv mlI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, mlR), none)) fFs [vv mlD]) (.return (vv mlR)))))
    (.return (.const 0))))

def mlBody : ProgHOL 64 := prologue mlLocals
  (.seq (.call (some (some (.local, mlH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv mlB])
  (.ite (tagIsE mlH 0)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv mlH)) (.seq eViewP
      (.ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local mlK (.const 0)) mlRest)
        (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local mlK (.load .one (.op .add [vv lRp, .const 0])))
          mlRest) hang)))))
    (.return (.const 0))))

section
variable {σ : Type}

theorem ml_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mlLocals → (ctxEnv C ++ mlParams.zip vals).get x = none :=
  Knot.params_none C mlLocals mlParams vals (by decide) (by decide)

/-- The prefix's domains in cells from `op + 1`. -/
def EElems (H : List (BitVec 64)) (op : Nat) (xs : List EIdx) : Prop :=
  ∀ j (hj : j < xs.length), H[op + 1 + j]? = some (Enc.idxW xs[j])

/-- The motive's level once its de Bruijn index `k` (a word) is known. -/
theorem mlRest_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one))
    (hcf : C.code.lookup fFs = some ([(fsT, .one)], fsBody, .one))
    (pre : List EIdx) (op nIdx k : Nat) (hL : pre.length < 2 ^ 59) (hn : nIdx < 2 ^ 59) (hk : k < 2 ^ 64)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hpre : EElems H op pre) (s : AState) (Γ : Env) (M : Mem)
    (gP : Γ.get mlP = some (cellA C op)) (gL : Γ.get mlL = some (BitVec.ofNat 64 pre.length))
    (gN : Γ.get mlN = some (BitVec.ofNat 64 nIdx)) (gK : Γ.get mlK = some (BitVec.ofNat 64 k)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ mlLocals)) mlRest s
      (if nIdx + 1 ≤ k then
        if k < nIdx + 1 + pre.length then do
          let d ← exprGetD pre (pre.length - 1 - (k - (nIdx + 1)))
          formerResSort d
        else pure none
      else pure none) (PostOL (ctxH C H) s) := by
  unfold mlRest
  refine specR_ifI (.shift .lsr (vv mlK) (.const 63)) (BitVec.ofNat 64 k >>> (63 : BitVec 64).toNat)
    (by simp [sev, gK]) (fun _ => specR_hangI) (fun hw => ?_)
  have hk63 := (shr63_eq_zero k hk).mp hw
  have hN1 : sev Γ (.op .add [vv mlN, .const 1]) = some (BitVec.ofNat 64 (nIdx + 1)) := by
    simp [sev, gN]; exact word_add1_eq nIdx
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ (vv mlK) _ k (nIdx + 1) (by simp [sev, gK]) hN1 (by omega)
    (by omega)) (fun h => ?_) (fun h => ?_)
  · have c : k < nIdx + 1 := by by_cases c : k < nIdx + 1; exact c; simp [bw, c] at h
    rw [if_neg (by omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have c1 : ¬ k < nIdx + 1 := by intro c; simp [bw, c] at h
  rw [if_pos (by omega)]
  have hN2 : sev Γ (.op .add [.op .add [vv mlN, .const 1], vv mlL]) = some (BitVec.ofNat 64 (nIdx + 1 + pre.length)) := by
    simp only [sev] at hN1 ⊢; rw [hN1]; simp [gL]; exact ofNat_add_small _ _ (by omega)
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ (vv mlK) _ k (nIdx + 1 + pre.length) (by simp [sev, gK]) hN2
    (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
  · have c2 : k < nIdx + 1 + pre.length := by by_cases c : k < nIdx + 1 + pre.length; exact c; simp [bw, c] at h
    rw [if_pos c2]
    let idx := pre.length - 1 - (k - (nIdx + 1))
    have hix : idx < pre.length := by omega
    refine specR_assignI mlI _ (BitVec.ofNat 64 idx) (by simp +decide [ctxLocals, mlLocals])
      (by
        simp only [sev] at hN1 ⊢; rw [hN1]; simp [gL, gK]
        rw [ofNat_sub_small _ 1 (by omega) (by omega), ofNat_sub_small k (nIdx + 1) (by omega) (by omega),
          ofNat_sub_small _ _ (by omega) (by omega)]) ?_
    have hd : (ctxH C H).H[op + 1 + idx]? = some (Enc.idxW pre[idx]) := hpre idx hix
    refine UD.specR_heapLoadI' (C := ctxH C H) mlD _ (op + 1 + idx) _ hd (by simp +decide [ctxLocals, mlLocals])
      (by
        have g1 : (Env.get ((mlI, BitVec.ofNat 64 idx) :: Γ) mlP) = some (cellA C op) := by
          simp only [Env.get_cons, show mlP ≠ mlI by decide, ite_false]; exact gP
        simp only [sev, sev_vv, g1]; simp; exact cellA_mulIdx C op idx (by omega)) ?_
    have hget : exprGetD pre idx = pure pre[idx] := by simp [exprGetD, List.getElem?_eq_getElem hix]
    rw [hget, pure_bind]
    refine specR_congr (m' := formerResSort pre[idx] >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) mlR fFs [fsT] [vv mlD] fsBody [Enc.idxW pre[idx]] (by decide) rfl
      (by simp +decide [ctxLocals, mlLocals]) hcf ⟨by simp [sev, Env.get_cons], trivial⟩
      (PostOL (ctxH C H) s) (fun o w s' H' => s' = s ∧ w = optWG Enc.idxW o)
      (fun o w s' st ⟨hs, hw, H', hp', hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, hs ▸ hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [fsT] _ rfl hlk)
        (fs_spec (ctxH C H) hcp s pre[idx]))
      (fun o w s1 H1 hp1 ⟨hs1, hw⟩ => ?_)
    subst hs1; subst hw
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, rfl, H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have c2 : ¬ k < nIdx + 1 + pre.length := by intro c; simp [bw, c] at h
    rw [if_neg c2]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

/-- **`motiveLevel?`**. -/
theorem ml_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one))
    (hcf : C.code.lookup fFs = some ([(fsT, .one)], fsBody, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (pre : List EIdx) (op nIdx : Nat) (body : EIdx) (hL : pre.length < 2 ^ 59) (hn : nIdx < 2 ^ 59)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hpre : EElems H op pre) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (mlParams.zip [cellA C op, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 nIdx,
      Enc.idxW body])) mlBody s (motiveLevel? pre nIdx body) (PostOL (ctxH C H) s) := by
  refine specR_prologue (fun a w s' st L ⟨h1, h2, H', hp', h3⟩ => ⟨h1, h2, H', hp', sr_of_eq h3 rfl rfl rfl rfl⟩)
    (ml_none _ _) ?_
  unfold motiveLevel?
  refine specR_callNIM mlH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv mlB]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body] (by decide) rfl (by simp +decide [ctxLocals, mlLocals]) hcg
    ⟨rfl, by simp +decide [sev, Env.get, mlParams, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel body s = .ok (a, s') ∧ Post (ctxH C H) s a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H) hcg coreWalkFuel body s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  let Γ0 : Env := ctxEnv (ctxH C H) ++ mlParams.zip [cellA C op, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 nIdx,
    Enc.idxW body]
  have rest : ∀ (k : Nat) (Γ : Env), k < 2 ^ 64 → Γ.get mlP = some (cellA C op) →
      Γ.get mlL = some (BitVec.ofNat 64 pre.length) → Γ.get mlN = some (BitVec.ofNat 64 nIdx) →
      Γ.get mlK = some (BitVec.ofNat 64 k) → ∀ M,
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ mlLocals)) mlRest s
        (if nIdx + 1 ≤ k then
          if k < nIdx + 1 + pre.length then do
            let d ← exprGetD pre (pre.length - 1 - (k - (nIdx + 1)))
            let r ← piResult coreWalkFuel d
            if r.tag == ETag.sort then
              match ← viewSort r with
              | none => failDanglingE
              | some u => pure (some u)
            else pure none
          else pure none
        else pure none) (PostOL (ctxH C H) s) :=
    fun k Γ hk gP gL gN gK M => mlRest_spec C hok hcp hcf pre op nIdx k hL hn hk H hp hpre s Γ M gP gL gN gK
  refine Knot.specR_tagIteV mlH hd 0 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [ite_eq_left (show (hd.tag == ETag.bvar) = true by simp [htg, ETag.bvar])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv mlH) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    have h0 : hd.tag = 0 := htg
    refine specR_viewXI ConRon.Arena.viewBVar projBVar hd (fun vw hvw => viewBVar_run hd h0 s vw hvw)
      (by simp) (by simp +decide [Env.get_cons] <;> rfl) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl) (by decide)
      (fun vw P htg' hsh => ?_)
    have gs : ∀ y v, y ∈ mlParams → Γ0.get y = some v → ∀ (Γ : Env), (∀ z, z ∈ mlParams → Γ.get z = Γ0.get z) →
        Γ.get y = some v := fun y v hy h Γ hΓ => by rw [hΓ y hy]; exact h
    cases vw with
    | bvar i =>
      simp only [projBVar]
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, Enc.limbs,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI mlK (.const 0) 0 (by simp +decide [ctxLocals, mlLocals]) rfl ?_
        exact rest 0 _ (by decide) (by simp +decide [Env.get_cons, Env.get, mlParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, mlParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, mlParams, ctxEnv]) (by simp [Env.get_cons]) _
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' mlK _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by simp +decide [ctxLocals, mlLocals])
            (by simp +decide [sev, Env.get_cons]) rfl
            (by have := wordsAt_mem0 P (BitVec.ofNat 64 i) [] (M := []); simpa [encEView, Enc.encBVar, hl] using this) ?_
          exact rest i _ ib (by simp +decide [Env.get_cons, Env.get, mlParams, ctxEnv])
            (by simp +decide [Env.get_cons, Env.get, mlParams, ctxEnv])
            (by simp +decide [Env.get_cons, Env.get, mlParams, ctxEnv]) (by simp [Env.get_cons]) _
        · have hl := limbs_len_ge2 i (by omega)
          have hlt : (Enc.limbs i).length < 2 ^ 61 := hsh
          have hn0 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 0#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          have hn1 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 1#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hn0,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hn1,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)
    | _ => simp [ENodeView.tagN, h0] at htg'
  · rw [ite_eq_right (show ¬ (hd.tag == ETag.bvar) = true by simpa [ETag.bvar] using htg)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
