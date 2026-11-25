import ConPanqueque.T.Ind.IotaRec

/-!
# `iotaRecOf`: a recursor's `IotaRec`

The frame (`stripPis` the rule prefix, then the indices and the major, `motiveLevel?` of the body), the body's
head variable, then `iotaRecMajor`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI
open ConPanqueque.T.WC

/-- `stripPis k` strips exactly `k` binders. -/
theorem stripPis_length : ∀ (k : Nat) (h : EIdx) (s s' : AState) (tys : List EIdx) (b : EIdx),
    stripPis k h s = .ok (some (tys, b), s') → tys.length = k
  | 0, h, s, s', tys, b, hr => by
    simp only [stripPis, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hr
    obtain ⟨⟨rfl, -⟩, -⟩ := hr; rfl
  | k + 1, h, s, s', tys, b, hr => by
    rw [stripPis] at hr
    split at hr
    · obtain ⟨vb, s1, -, h1⟩ := bind_ok_inv' hr
      rcases vb with _ | ⟨ty, b'⟩
      · simp [failDanglingE, fail, throwThe, MonadExceptOf.throw, StateT.lift] at h1
      · obtain ⟨r, s2, h2, h3⟩ := bind_ok_inv' h1
        rcases r with _ | ⟨tys', b''⟩
        · simp [pure, StateT.pure, Except.pure] at h3
        · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h3
          obtain ⟨⟨rfl, -⟩, -⟩ := h3
          simp [stripPis_length k b' s1 s2 tys' b'' h2]
    · simp [pure, StateT.pure, Except.pure] at hr


def roT := ofString "ro_t"
def roM := ofString "ro_m"
def roR := ofString "ro_r"
def roN := ofString "ro_n"
def roA := ofString "ro_a"
def roL := ofString "ro_l"
def roS := ofString "ro_s"
def roB := ofString "ro_b"
def roC := ofString "ro_c"
def roE := ofString "ro_e"
def roU := ofString "ro_u"
def roH := ofString "ro_h"
def roK := ofString "ro_k"
def roX := ofString "ro_x"
def fIotaRecOf := ofString "iotaRecOf"

def roParams : List MlS := [roT, roM, roR]
def roLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, roN, roA, roL, roS, roB, roC, roE, roU, roH, roK, roX]

def roRest : ProgHOL 64 :=
  .ite (.shift .lsr (vv roK) (.const 63)) hang
    (.seq (.call (some (some (.local, roX), none)) fIotaRecMajor [vv roA, vv roR, vv roB, vv roN, vv roK])
      (.return (vv roX)))

def roBody : ProgHOL 64 := prologue roLocals
  (.seq (.call (some (some (.local, roN), none)) fTSub [vv roM, vv roR])
  (.seq (.call (some (some (.local, roA), none)) fStripPis [vv roR, vv roT])
  (.ite (.cmp .equal (vv roA) (.const 0)) (.return (.const 0))
  (.seq (.assign .local roL (.load .one (vv roA)))
  (.seq (.assign .local roS (.load .one (.op .add [vv roA, .shift .lsl (vv roL) (.const 3)])))
  (.seq (.call (some (some (.local, roB), none)) fStripPis [.op .add [vv roN, .const 1], vv roS])
  (.ite (.cmp .equal (vv roB) (.const 0)) (.return (.const 0))
  (.seq (.assign .local roC (.load .one (vv roB)))
  (.seq (.assign .local roE (.load .one (.op .add [vv roB, .shift .lsl (vv roC) (.const 3)])))
  (.seq (.call (some (some (.local, roU), none)) fMotiveLevel [vv roA, vv roR, vv roN, vv roE])
  (.ite (.cmp .equal (vv roU) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, roH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv roE])
  (.ite (tagIsE roH 0)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv roH)) (.seq eViewP
      (.ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local roK (.const 0)) roRest)
        (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local roK (.load .one (.op .add [vv lRp, .const 0])))
          roRest) hang)))))
    (.return (.const 0)))))))))))))))

section
variable {σ : Type}

theorem ro_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ roLocals → (ctxEnv C ++ roParams.zip vals).get x = none :=
  Knot.params_none C roLocals roParams vals (by decide) (by decide)

/-- The functions `iotaRecOf` calls, and theirs. -/
structure ROCodes (C : Ctx) extends IRCodes C : Prop where
  ro : C.code.lookup fIotaRecOf = some (roParams.map (fun p => (p, ShapeHOL.one)), roBody, .one)
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  ml : C.code.lookup fMotiveLevel = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  pir : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one)
  fs : C.code.lookup fFs = some ([(fsT, .one)], fsBody, .one)

theorem iotaRecOf_eq (cv : IConstantVal) (mI rP : Nat) : iotaRecOf cv mI rP = (do
    match ← stripPis rP cv.type with
    | none => pure none
    | some (pre, rest) =>
      match ← stripPis (mI - rP + 1) rest with
      | none => pure none
      | some (doms, body) =>
        match ← motiveLevel? pre (mI - rP) body with
        | none => pure none
        | some _ => do
          let hd ← getAppFn coreWalkFuel body
          if hd.tag == ETag.bvar then
            match ← viewBVar hd with
            | none => failDanglingE
            | some k => iotaRecMajor pre doms (mI - rP) rP k
          else pure none) := by
  unfold iotaRecOf iotaFrame
  simp only [bind_assoc]
  congr 1; funext o
  rcases o with _ | ⟨pre, rest⟩
  · simp
  · simp only [bind_assoc]
    congr 1; funext o2
    rcases o2 with _ | ⟨doms, body⟩
    · simp
    · simp only [bind_assoc]
      congr 1; funext o3
      rcases o3 with _ | u
      · simp
      · simp only [pure_bind]; rfl

end

section
variable {σ : Type}

/-- A `stripPis` call, its run kept: none is `0`, else the block. -/
theorem ro_strip (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (n : Nat) (hn : n < 2 ^ 64) (T : EIdx) (H : List (BitVec 64)) (s : AState)
    {β : Type} {Γ : Env} {D : List MlS} {M : Mem} {rest : ProgHOL 64} {k : Option (List EIdx × EIdx) → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (en eT : ExpHOL 64) (hx : x ∈ D)
    (hen : sev Γ en = some (BitVec.ofNat 64 n)) (heT : sev Γ eT = some (Enc.idxW T))
    (hk : ∀ o w s1 H1, H <+: H1 → stripPis n T s = .ok (o, s1) → (o = none → w = 0) →
      (∀ tys b, o = some (tys, b) → ∃ ob, w = cellA C ob ∧ BlkAt H1 ob (tys.map Enc.idxW ++ [Enc.idxW b])) →
      SpecR (Inv (ctxH C H1) s1 ((x, w) :: Γ) [] D) rest s1 (k o) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (.seq (.call (some (some (.local, x), none)) fStripPis [en, eT]) rest) s
      (stripPis n T >>= k) R :=
  specR_callNIH (C := ctxH C H) x fStripPis [pFu, pH] [en, eT] (stripBody C fStripPis 6) [BitVec.ofNat 64 n, Enc.idxW T]
    (by decide) rfl hx hcs ⟨hen, heT, trivial⟩
    (fun o w s' st => stripPis n T s = .ok (o, s') ∧ PostSP (ctxH C H) o w s' st)
    (fun o w s' H' => stripPis n T s = .ok (o, s') ∧ (o = none → w = 0) ∧
      ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨hr, H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨hr, h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw; exact stripPis_spec C hok hcs n hn H s T _ (pre_of_lookups hu [pFu, pH] _ rfl hlk)))
    (fun o w s1 H1 hp1 ⟨hr, h1, h2⟩ => hk o w s1 H1 hp1 hr h1 h2)

/-- The last word of a `stripPis` block. -/
theorem strip_last {H : List (BitVec 64)} {ob : Nat} {tys : List EIdx} {b : EIdx}
    (h : BlkAt H ob (tys.map Enc.idxW ++ [Enc.idxW b])) :
    H[ob]? = some (BitVec.ofNat 64 (tys.length + 1)) ∧ H[ob + 1 + tys.length]? = some (Enc.idxW b) ∧
    EElems H ob tys := by
  refine ⟨by rw [h.1]; simp, by have := h.2 tys.length (by simp); simpa using this, fun j hj => ?_⟩
  have := h.2 j (by simp; omega)
  rw [List.getElem_append_left (by simpa using hj)] at this; simpa using this

end

section
variable {σ : Type}

/-- **`iotaRecOf`**. -/
theorem ro_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : ROCodes C)
    (cv : IConstantVal) (mI rP : Nat) (hm : mI < 2 ^ 58) (hr : rP < 2 ^ 58) (H : List (BitVec 64)) (hp : C.H <+: H)
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (roParams.zip [Enc.idxW cv.type, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP])) roBody s
      (iotaRecOf cv mI rP) (PostIR (ctxH C H)) := by
  refine specR_prologue (postIR_locals _) (ro_none _ _) ?_
  rw [iotaRecOf_eq]
  let Γ0 : Env := ctxEnv (ctxH C H) ++ roParams.zip [Enc.idxW cv.type, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP]
  have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ roLocals → z ∉ roLocals →
      Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
    have hne : z ≠ x := fun e => hz (e ▸ hx)
    simp only [Env.get_cons, hne, ite_false]
  have pk : ∀ (Γ : Env), (∀ z, z ∉ roLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ roParams → ∀ v,
      Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
    have hyl : y ∉ roLocals := by
      simp only [roParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl <;> decide
    simp only [sev, sev_vv, hΓ y hyl, h]
  have vT : Γ0.get roT = some (Enc.idxW cv.type) := by simp +decide [Γ0, Env.get, roParams, ctxEnv]
  have vM : Γ0.get roM = some (BitVec.ofNat 64 mI) := by simp +decide [Γ0, Env.get, roParams, ctxEnv]
  have vR : Γ0.get roR = some (BitVec.ofNat 64 rP) := by simp +decide [Γ0, Env.get, roParams, ctxEnv]
  have retNone : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env), H <+: H1 →
      SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ roLocals)) (.return (.const 0)) s1 (pure none)
        (PostIR (ctxH C H)) := fun H1 s1 Γ hp1 =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun _ e => by simp at e⟩)
  -- nIdx
  let nIdx := mI - rP
  refine specR_pureBind nIdx ?_
  refine rb_tsub (D := ctxLocals ++ roLocals) C hc.ts mI rP (by omega) (by omega) H s roN (vv roM) (vv roR)
    (by simp +decide [ctxLocals, roLocals])
    (by have e : sev Γ0 (vv roM) = some (BitVec.ofNat 64 mI) := by simp only [sev, sev_vv, vM]
        exact e)
    (by have e : sev Γ0 (vv roR) = some (BitVec.ofNat 64 rP) := by simp only [sev, sev_vv, vR]
        exact e) (fun H1 hp1 => ?_)
  let Γ1 : Env := (roN, BitVec.ofNat 64 nIdx) :: Γ0
  have hΓ1 : ∀ z, z ∉ roLocals → Γ1.get z = Γ0.get z := fun z hz => cnl (by decide) hz
  -- the rule prefix
  refine ro_strip C hok hc.sp rP (by omega) cv.type H1 s roA (vv roR) (vv roT) (by simp +decide [ctxLocals, roLocals])
    (pk Γ1 hΓ1 roR (by decide) _ vR) (pk Γ1 hΓ1 roT (by decide) _ vT) (fun o wa s1 H2 hp2 hr1 hn1 hs1 => ?_)
  have hp12 : H1 <+: H2 := hp2
  rcases o with _ | ⟨pre, rst⟩
  · have e0 := hn1 rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact retNone H2 s1 _ (hp1.trans hp12)
  obtain ⟨oa, rfl, hba⟩ := hs1 pre rst rfl
  have hpl := stripPis_length _ _ _ _ _ _ hr1
  obtain ⟨ha0, haL, hpre⟩ := strip_last hba
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hba
  have hHN' : H2.length ≤ C.HN := hHN
  have hne : cellA C oa ≠ 0 := cellA_ne0 C hok oa (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H2) roL (vv roA) oa _ ha0 (by simp +decide [ctxLocals, roLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) roS _ (oa + 1 + pre.length) _ haL (by simp +decide [ctxLocals, roLocals])
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C oa + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  let Γ2 : Env := (roS, Enc.idxW rst) :: (roL, BitVec.ofNat 64 (pre.length + 1)) :: (roA, cellA C oa) :: Γ1
  have hΓ2 : ∀ z, z ∉ roLocals → Γ2.get z = Γ0.get z := fun z hz => by
    simp only [Γ2]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ1 z hz
  -- the indices and the major
  refine ro_strip C hok hc.sp (nIdx + 1) (by omega) rst H2 s1 roB _ (vv roS) (by simp +decide [ctxLocals, roLocals])
    (by simp only [sev, sev_vv, Γ2, Env.get_cons]; simp +decide; exact word_add1_eq nIdx)
    (by simp [Γ2, sev, Env.get_cons]) (fun o wb s2 H3 hp3 hr2 hn2 hs2 => ?_)
  have hp23 : H2 <+: H3 := hp3
  rcases o with _ | ⟨doms, body⟩
  · have e0 := hn2 rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact retNone H3 s2 _ ((hp1.trans hp12).trans hp23)
  obtain ⟨ob, rfl, hbb⟩ := hs2 doms body rfl
  have hdl := stripPis_length _ _ _ _ _ _ hr2
  obtain ⟨hb0, hbL, hdoms⟩ := strip_last hbb
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN3 => ?_)
  have hol3 := blkAt_lt hbb
  have hHN3' : H3.length ≤ C.HN := hHN3
  have hne3 : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne3)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H3) roC (vv roB) ob _ hb0 (by simp +decide [ctxLocals, roLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H3) roE _ (ob + 1 + doms.length) _ hbL (by simp +decide [ctxLocals, roLocals])
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C ob + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  let Γ3 : Env := (roE, Enc.idxW body) :: (roC, BitVec.ofNat 64 (doms.length + 1)) :: (roB, cellA C ob) :: Γ2
  have hΓ3 : ∀ z, z ∉ roLocals → Γ3.get z = Γ0.get z := fun z hz => by
    simp only [Γ3]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ2 z hz
  have hp03 : C.H <+: H3 := ((hp.trans hp1).trans hp12).trans hp23
  have hpre3 : EElems H3 oa pre := fun j hj => get_prefix (hpre j hj) hp23
  -- the motive's level
  refine specR_callNIH (C := ctxH C H3) roU fMotiveLevel mlParams [vv roA, vv roR, vv roN, vv roE] mlBody
    [cellA C oa, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 nIdx, Enc.idxW body] (by decide) rfl
    (by simp +decide [ctxLocals, roLocals]) hc.ml
    ⟨by simp +decide [Γ3, Γ2, sev, Env.get_cons], by rw [hpl]; exact pk Γ3 hΓ3 roR (by decide) _ vR,
      by simp +decide [Γ3, Γ2, Γ1, sev, Env.get_cons] <;> rfl, by simp [Γ3, sev, Env.get_cons], trivial⟩
    (PostOL (ctxH C H3) s2) (fun o w s' _ => s' = s2 ∧ w = optWG Enc.idxW o)
    (fun o w s' st ⟨hs, hw, H', hp', hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, hs ▸ hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
      (ml_spec C hok hc.pir hc.fs hc.ga pre oa nIdx body (by omega) (by omega) H3 hp03 hpre3 s2))
    (fun ou wu s3 H4 hp4 ⟨hs3, hwu⟩ => ?_)
  subst hs3; subst hwu
  have hp34 : H3 <+: H4 := hp4
  rw [show mI - rP = nIdx from rfl]
  rcases ou with _ | u
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact retNone H4 s3 _ (((hp1.trans hp12).trans hp23).trans hp34)
  have hne4 : optWG Enc.idxW (some u) ≠ 0 := by
    simp only [optWG]; intro e
    have h32 := idxW_lt32 u
    have := congrArg BitVec.toNat e; simp [BitVec.toNat_add] at this; omega
  refine specR_ifI _ 0 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne4)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [pure_bind]
  have hp04 : C.H <+: H4 := hp03.trans hp34
  let Γ4 : Env := (roU, optWG Enc.idxW (some u)) :: Γ3
  have hΓ4 : ∀ z, z ∉ roLocals → Γ4.get z = Γ0.get z := fun z hz => by
    simp only [Γ4]; rw [cnl (by decide) hz]; exact hΓ3 z hz
  -- the body's head
  refine specR_callNIM roH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv roE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body] (by decide) rfl (by simp +decide [ctxLocals, roLocals]) hc.ga
    ⟨rfl, by simp +decide [Γ4, Γ3, sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel body s3 = .ok (a, s') ∧ Post (ctxH C H4) s3 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u' hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H4) hc.ga coreWalkFuel body s3 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s3 = s' := hs.symm
  subst hs'
  have hpre4 : EElems H4 oa pre := fun j hj => get_prefix (hpre3 j hj) hp34
  have hdoms4 : EElems H4 ob doms := fun j hj => get_prefix (hdoms j hj) hp34
  have ha04 : H4[oa]? = some (BitVec.ofNat 64 (pre.length + 1)) := get_prefix ha0 (hp23.trans hp34)
  have rest : ∀ (k : Nat) (Γ : Env) (M : Mem), k < 2 ^ 64 → (∀ z, z ∉ roLocals → Γ.get z = Γ0.get z) →
      Γ.get roA = some (cellA C oa) → Γ.get roB = some (cellA C ob) → Γ.get roN = some (BitVec.ofNat 64 nIdx) →
      Γ.get roK = some (BitVec.ofNat 64 k) →
      SpecR (σ := σ) (Inv (ctxH C H4) s3 Γ M (ctxLocals ++ roLocals)) roRest s3 (iotaRecMajor pre doms nIdx rP k)
        (PostIR (ctxH C H)) := by
    intro k Γ M hk hΓ gA gB gN gK
    unfold roRest
    refine specR_ifI (.shift .lsr (vv roK) (.const 63)) (BitVec.ofNat 64 k >>> (63 : BitVec 64).toNat)
      (by simp [sev, gK]) (fun _ => specR_hangI) (fun hw => ?_)
    have hk63 := (shr63_eq_zero k hk).mp hw
    rw [← hpl]
    refine specR_congr (m' := iotaRecMajor pre doms nIdx pre.length k >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H4) roX fIotaRecMajor irmParams [vv roA, vv roR, vv roB, vv roN, vv roK]
      (irmBody C) [cellA C oa, BitVec.ofNat 64 pre.length, cellA C ob, BitVec.ofNat 64 nIdx, BitVec.ofNat 64 k]
      (by decide) rfl (by simp +decide [ctxLocals, roLocals]) hc.irm
      ⟨by simp [sev, gA], by rw [hpl]; exact pk Γ hΓ roR (by decide) _ vR, by simp [sev, gB], by simp [sev, gN],
        by simp [sev, gK], trivial⟩
      (PostIR (ctxH C H4)) (fun o w _ H' => (o = none → w = 0) ∧
        ∀ rr, o = some rr → ∃ ob', w = cellA C ob' ∧ IotaRecRep C H' ob' rr)
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu irmParams _ rfl hlk)
        (irm_spec ra C hok hc.toIRCodes pre doms oa ob nIdx k (by omega) (by omega) hk63 (by omega) H4 hp04 ha04 hpre4
          hdoms4 s3))
      (fun o wx s5 H5 hp5 ⟨h1, h2⟩ => ?_)
    exact specR_returnI _ wx (by simp [sev, Env.get_cons]) (fun t ht => ⟨H5,
      ((((hp1.trans hp12).trans hp23).trans hp34).trans hp5), sr_of_eq ht.sr rfl rfl rfl rfl, h1, h2⟩)
  refine Knot.specR_tagIteV roH hd 0 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [ite_eq_left (show (hd.tag == ETag.bvar) = true by simp [htg, ETag.bvar])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv roH) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    have h0 : hd.tag = 0 := htg
    refine specR_viewXI ConRon.Arena.viewBVar projBVar hd (fun vw hvw => viewBVar_run hd h0 s3 vw hvw)
      (by simp) (by simp +decide [Env.get_cons] <;> rfl) (by simp +decide [Env.get, Env.get_cons, ctxEnv] <;> rfl)
      (by decide) (fun vw P htg' hsh => ?_)
    have hΓ5 : ∀ (Γ : Env) (x : MlS) (v : BitVec 64), x ∈ roLocals → (∀ z, z ∉ roLocals → Γ.get z = Γ0.get z) →
        ∀ z, z ∉ roLocals → Env.get ((x, v) :: Γ) z = Γ0.get z := fun Γ x v hx hΓ z hz => by
      rw [cnl hx hz]; exact hΓ z hz
    cases vw with
    | bvar i =>
      simp only [projBVar]
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, Enc.limbs,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI roK (.const 0) 0 (by simp +decide [ctxLocals, roLocals]) rfl ?_
        refine rest 0 _ _ (by decide) ?_ ?_ ?_ ?_ ?_
        · intro z hz; repeat rw [cnl (by decide) hz]
          try exact hΓ4 z hz
        all_goals simp +decide [Γ4, Γ3, Γ2, Γ1, Env.get_cons]
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' roK _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by simp +decide [ctxLocals, roLocals])
            (by simp +decide [sev, Env.get_cons]) rfl
            (by have := wordsAt_mem0 P (BitVec.ofNat 64 i) [] (M := []); simpa [encEView, Enc.encBVar, hl] using this) ?_
          refine rest i _ _ ib ?_ ?_ ?_ ?_ ?_
          · intro z hz; repeat rw [cnl (by decide) hz]
            try exact hΓ4 z hz
          all_goals simp +decide [Γ4, Γ3, Γ2, Γ1, Env.get_cons]
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
    exact retNone H4 s3 _ (((hp1.trans hp12).trans hp23).trans hp34)

end

end ConPanqueque.T.Ind
