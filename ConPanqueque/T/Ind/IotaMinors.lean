import ConPanqueque.T.Ind.MotiveLevel

/-!
# A recursor's minor premises (`isMinorAt`, `minorsFrom`)

`isMinorAt(p, mot, q)`: the prefix binder `q`'s conclusion (behind its `∀`s, `piTele`) is headed by the motive
at prefix position `mot`.  `minorsFrom(p, L, mot, q)`: the positions from `q` on that are, as a block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI
open ConPanqueque.T.WC ConPanqueque.T.ExS ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA

def imP := ofString "im_p"
def imM := ofString "im_m"
def imQ := ofString "im_q"
def imD := ofString "im_d"
def imR := ofString "im_r"
def imN := ofString "im_n"
def imB := ofString "im_b"
def imH := ofString "im_h"
def imK := ofString "im_k"
def fIsMinor := ofString "isMinorAt"

def imParams : List MlS := [imP, imM, imQ]
def imLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, imD, imR, imN, imB, imH, imK]

def imRest : ProgHOL 64 :=
  .ite (.cmp .lower (vv imM) (vv imQ))
    (.return (.cmp .equal (vv imK) (.op .add [vv imN, .op .sub [.op .sub [vv imQ, .const 1], vv imM]])))
    (.return (.const 0))

def imBody : ProgHOL 64 := prologue imLocals
  (.seq (.assign .local imD (.load .one (.op .add [vv imP, .op .add [.panop .mul [vv imQ, .const 8], .const 8]])))
  (.seq (.call (some (some (.local, imR), none)) fPiTele [.const (BitVec.ofNat 64 coreWalkFuel), vv imD])
  (.seq (.assign .local imN (.load .one (vv imR)))
  (.seq (.assign .local imB (.load .one (.op .add [vv imR, .const 8])))
  (.seq (.call (some (some (.local, imH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv imB])
  (.ite (tagIsE imH 0)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv imH)) (.seq eViewP
      (.ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local imK (.const 0)) imRest)
        (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local imK (.load .one (.op .add [vv lRp, .const 0])))
          imRest) hang)))))
    (.return (.const 0))))))))

section
variable {σ : Type}

theorem im_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ imLocals → (ctxEnv C ++ imParams.zip vals).get x = none :=
  Knot.params_none C imLocals imParams vals (by decide) (by decide)

theorem imRest_spec (C : Ctx) (mot q n k : Nat) (hq : q < 2 ^ 59) (hm : mot < 2 ^ 59) (hn : n < 2 ^ 62)
    (hk : k < 2 ^ 64) (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (gM : Γ.get imM = some (BitVec.ofNat 64 mot)) (gQ : Γ.get imQ = some (BitVec.ofNat 64 q))
    (gN : Γ.get imN = some (BitVec.ofNat 64 n)) (gK : Γ.get imK = some (BitVec.ofNat 64 k)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) imRest s
      (if mot < q then pure (k == n + (q - 1 - mot)) else pure false) (PostB C) := by
  unfold imRest
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ (vv imM) (vv imQ) mot q (by simp [sev, gM]) (by simp [sev, gQ])
    (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
  · have c : mot < q := by by_cases c : mot < q; exact c; simp [bw, c] at h
    rw [if_pos c]
    have hs : sev Γ (.op .add [vv imN, .op .sub [.op .sub [vv imQ, .const 1], vv imM]]) =
        some (BitVec.ofNat 64 (n + (q - 1 - mot))) := by
      simp only [sev, sev_vv, gN, gQ, gM]; simp
      rw [ofNat_sub_small q 1 (by omega) (by omega), ofNat_sub_small (q - 1) mot (by omega) (by omega),
        ofNat_add_small n _ (by omega)]
    exact specR_returnI _ _ (ConPanqueque.T.WC.sev_eqNatB (by omega) (by omega) (by simp [sev, gK]) hs)
      (fun t ht => ⟨H, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have c : ¬ mot < q := by intro c; simp [bw, c] at h
    rw [if_neg c]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

/-- **`isMinorAt`**, at a position of the prefix. -/
theorem im_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fPiTele = some ([(pFu, .one), (pH, .one)], ptBody C fPiTele, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (pre : List EIdx) (op mot q : Nat) (hq : q < pre.length) (hL : pre.length < 2 ^ 59) (hm : mot < 2 ^ 59)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hpre : EElems H op pre) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (imParams.zip [cellA C op, BitVec.ofNat 64 mot, BitVec.ofNat 64 q])) imBody s
      (isMinorAt pre mot q) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (im_none _ _) ?_
  unfold isMinorAt
  have hget : exprGetD pre q = pure pre[q] := by simp [exprGetD, List.getElem?_eq_getElem hq]
  rw [hget, pure_bind]
  let Γ0 : Env := ctxEnv (ctxH C H) ++ imParams.zip [cellA C op, BitVec.ofNat 64 mot, BitVec.ofNat 64 q]
  have hd : (ctxH C H).H[op + 1 + q]? = some (Enc.idxW pre[q]) := hpre q hq
  refine UD.specR_heapLoadI' (C := ctxH C H) imD _ (op + 1 + q) _ hd (by simp +decide [ctxLocals, imLocals])
    (by simp +decide [sev, Env.get, imParams, ctxEnv]; exact cellA_mulIdx C op q (by omega)) ?_
  refine specR_callNIH (C := ctxH C H) imR fPiTele [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv imD]
    (ptBody C fPiTele) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW pre[q]] (by decide) rfl
    (by simp +decide [ctxLocals, imLocals]) hcp ⟨rfl, by simp [sev, Env.get_cons], trivial⟩
    (PostPT (ctxH C H) coreWalkFuel) (fun r w _ H' => r.1 < coreWalkFuel ∧
      ∃ ob, w = cellA C ob ∧ H'[ob]? = some (BitVec.ofNat 64 r.1) ∧ H'[ob + 1]? = some (Enc.idxW r.2))
    (fun r w s' st ⟨H', hp', hs, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact pt_spec C hok hcp coreWalkFuel (by decide) H s pre[q] _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun t wr s1 H1 hp1 ⟨htf, ob, hwr, hc0, hc1⟩ => ?_)
  subst hwr
  have hpH1 : H <+: H1 := hp1
  have hcw : coreWalkFuel < 2 ^ 62 := by decide
  refine UD.specR_heapLoadI' (C := ctxH C H1) imN (vv imR) ob _ hc0 (by simp +decide [ctxLocals, imLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) imB _ (ob + 1) _ hc1 (by simp +decide [ctxLocals, imLocals])
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ob) ?_
  refine specR_callNIM imH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv imB]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW t.2] (by decide) rfl (by simp +decide [ctxLocals, imLocals]) hcg
    ⟨rfl, by simp [sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel t.2 s1 = .ok (a, s') ∧ Post (ctxH C H1) s1 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun tt ht => by
      subst ht
      exact getAppFn_spec (ctxH C H1) hcg coreWalkFuel t.2 s1 CV.coreWalkFuel_lt tt ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s1 = s' := hs.symm
  subst hs'
  have hp1H : C.H <+: H1 := hp.trans hpH1
  have gs : ∀ (Γ : Env), (∀ z, z ∉ imLocals → Γ.get z = Γ0.get z) →
      Γ.get imM = some (BitVec.ofNat 64 mot) ∧ Γ.get imQ = some (BitVec.ofNat 64 q) := fun Γ hΓ => by
    rw [hΓ imM (by decide), hΓ imQ (by decide)]; simp +decide [Γ0, Env.get, imParams, ctxEnv]
  refine Knot.specR_tagIteV imH hd 0 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [ite_eq_left (show (hd.tag == ETag.bvar) = true by simp [htg, ETag.bvar])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv imH) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    have h0 : hd.tag = 0 := htg
    refine specR_viewXI ConRon.Arena.viewBVar projBVar hd (fun vw hvw => viewBVar_run hd h0 s1 vw hvw)
      (by simp) (by simp +decide [Env.get_cons] <;> rfl) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl)
      (by decide) (fun vw P htg' hsh => ?_)
    cases vw with
    | bvar i =>
      simp only [projBVar]
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, Enc.limbs,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI imK (.const 0) 0 (by simp +decide [ctxLocals, imLocals]) rfl ?_
        exact imRest_spec (ctxH C H) mot q t.1 0 (by omega) hm (by omega) (by decide) H1 hp1
          s1 _ _ _ (by simp +decide [Env.get_cons, Env.get, imParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, imParams, ctxEnv])
          (by simp +decide [Env.get_cons]) (by simp [Env.get_cons])
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' imK _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by simp +decide [ctxLocals, imLocals])
            (by simp +decide [sev, Env.get_cons]) rfl
            (by have := wordsAt_mem0 P (BitVec.ofNat 64 i) [] (M := []); simpa [encEView, Enc.encBVar, hl] using this) ?_
          exact imRest_spec (ctxH C H) mot q t.1 i (by omega) hm (by omega) ib H1 hp1
            s1 _ _ _ (by simp +decide [Env.get_cons, Env.get, imParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, imParams, ctxEnv])
            (by simp +decide [Env.get_cons]) (by simp [Env.get_cons])
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
    exact specR_returnI _ 0 rfl (fun tt ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def mnP := ofString "mn_p"
def mnL := ofString "mn_l"
def mnM := ofString "mn_m"
def mnQ := ofString "mn_q"
def mnB := ofString "mn_b"
def fMinorsFrom := ofString "minorsFrom"

def mnParams : List MlS := [mnP, mnL, mnM, mnQ]
def mnLocals : List MlS := gaaLocals ++ [mnB]

def mnBody (C : Ctx) : ProgHOL 64 := prologue mnLocals
  (.ite (.cmp .lower (vv mnQ) (vv mnL))
    (.seq (.call (some (some (.local, mnB), none)) fIsMinor [vv mnP, vv mnM, vv mnQ])
    (.seq (.call (some (some (.local, ExS.lY), none)) fMinorsFrom [vv mnP, vv mnL, vv mnM, .op .add [vv mnQ, .const 1]])
    (.ite (.cmp .notEqual (vv mnB) (.const 0))
      (.seq (.assign .local lA1 (vv mnQ)) (prependP C lA1))
      (.return (vv ExS.lY)))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem mn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mnLocals → (ctxEnv C ++ mnParams.zip vals).get x = none :=
  Knot.params_none C mnLocals mnParams vals (by decide) (by decide)

/-- A list of numbers as a block of a bigger heap. -/
def PostNL (C : Ctx) (xs : List Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ o, w = cellA C o ∧ BlkAt H' o (xs.map (BitVec.ofNat 64))

theorem postNL_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNL C a w s' st → PostNL C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

/-- **`minorsFrom`** from position `q`. -/
theorem mn_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMinorsFrom = some (mnParams.map (fun p => (p, ShapeHOL.one)), mnBody C, .one))
    (hci : C.code.lookup fIsMinor = some (imParams.map (fun p => (p, ShapeHOL.one)), imBody, .one))
    (hcp : C.code.lookup fPiTele = some ([(pFu, .one), (pH, .one)], ptBody C fPiTele, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (pre : List EIdx) (op mot : Nat) (hL : pre.length < 2 ^ 59) (hm : mot < 2 ^ 59) :
    ∀ f q (H : List (BitVec 64)) (s : AState), C.H <+: H → EElems H op pre → pre.length - q = f → q ≤ pre.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (mnParams.zip [cellA C op, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 mot,
        BitVec.ofNat 64 q])) (mnBody C) s (minorsFrom pre mot q) (PostNL (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro q H s hp hpre hf hq
    have hql : q = pre.length := by omega
    subst hql
    refine specR_prologue (postNL_locals _) (mn_none _ _) ?_
    rw [minorsFrom]
    have hlw := nd_lt_iff pre.length pre.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [ite_eq_right (by omega)]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by simp +decide [ctxLocals, mnLocals, gaaLocals, inst1Locals])
      (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    exact specR_returnI _ _ (by simp [sev] <;> rfl) (fun t ht => ⟨_, hp2.trans (img1_prefix _ _ _ hws),
      sr_of_eq ht.sr rfl rfl rfl rfl, H2.length, rfl, by simpa using img1_get H2 ws (0 : BitVec 64) hws,
      fun i hi => absurd hi (by simp)⟩)
  | succ f ih =>
    intro q H s hp hpre hf hq
    have hql : q < pre.length := by omega
    refine specR_prologue (postNL_locals _) (mn_none _ _) ?_
    rw [minorsFrom]
    have hlw := nd_lt_iff q pre.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hql])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [ite_eq_left hql]
    refine specR_callNIH (C := ctxH C H) mnB fIsMinor imParams [vv mnP, vv mnM, vv mnQ] imBody
      [cellA C op, BitVec.ofNat 64 mot, BitVec.ofNat 64 q] (by decide) rfl
      (by simp +decide [ctxLocals, mnLocals, gaaLocals, inst1Locals]) hci
      ⟨by simp +decide [sev, Env.get, mnParams, ctxEnv], by simp +decide [sev, Env.get, mnParams, ctxEnv],
        by simp +decide [sev, Env.get, mnParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu imParams _ rfl hlk)
        (im_spec C hok hcp hcg pre op mot q hql hL hm H hp hpre s))
      (fun b wb s1 H1 hp1 hwb => ?_)
    subst hwb
    have hpH1 : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fMinorsFrom mnParams [vv mnP, vv mnL, vv mnM, .op .add [vv mnQ, .const 1]]
      (mnBody C) [cellA C op, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 mot, BitVec.ofNat 64 (q + 1)] (by decide) rfl
      (by simp +decide [ctxLocals, mnLocals, gaaLocals, inst1Locals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mnParams, ctxEnv]; exact word_add1_eq q, trivial⟩
      (PostNL (ctxH C H1)) (fun xs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (xs.map (BitVec.ofNat 64)))
      (fun xs w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mnParams _ rfl hlk)
        (ih (q + 1) H1 s1 (hp.trans hpH1) (fun j hj => get_prefix (hpre j hj) hpH1) (by omega) (by omega)))
      (fun rest wr s2 H2 hp2 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    have hpH2 : H1 <+: H2 := hp2
    refine specR_ifI _ _ (sev_ne0 (b := b) (by simp +decide [sev, Env.get_cons])) (fun hb => ?_) (fun hb => ?_)
    · have hbt : b = true := by cases e : b; simp [e, boolW] at hb; rfl
      subst hbt
      simp only [ite_true]
      refine specR_assignI lA1 (vv mnQ) (BitVec.ofNat 64 q) (by simp +decide [ctxLocals, mnLocals, gaaLocals, inst1Locals])
        (by simp +decide [sev, Env.get_cons, Env.get, mnParams, ctxEnv]) ?_
      exact prepend_spec C hok lA1 (BitVec.ofNat 64 q) oy _ (by simp +decide [ctxLocals, mnLocals, gaaLocals, inst1Locals])
        (by simp +decide [Env.get_cons]) (by simp [Env.get_cons]) hblk (by decide)
        (by simp +decide [Env.get_cons, Env.get, mnParams, ctxEnv]) (by decide)
        (fun H' o t hpH hbk hsr => ⟨H', (hpH1.trans hpH2).trans hpH, hsr, o, rfl, by simpa using hbk⟩)
    · have hbf : b = false := by cases e : b; rfl; simp [e, boolW] at hb
      subst hbf
      simp only [Bool.false_eq_true, ite_false]
      exact specR_returnI _ _ (by simp [sev, Env.get_cons] <;> rfl) (fun t ht => ⟨H2, hpH1.trans hpH2,
        sr_of_eq ht.sr rfl rfl rfl rfl, oy, rfl, hblk⟩)

end

end ConPanqueque.T.Ind
