import ConPanqueque.T.Ind.IotaCtor
import ConPanqueque.T.Core.IotaFam

/-!
# A rule's parts past the parameters (`iotaPartsAtBody`)

The constructor's body at the rule's parameters, its `nfields` binders, and the indices behind the
parameters, with the shape guards. The answer is a six-word block: the four `PartsRep` words, then the
parameter domains `pd`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.Decl
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.ExSP
open ConPanqueque.T.ExIL (fInstLF ilParams fastBodyIL CodesIL fastIL_spec)

/-- A fresh block holding `cnt` of a block's elements from index `off` on. -/
def sliceCopyP (C : Ctx) (x src : MlS) (off : ExpHOL 64) (cnt : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lCn (vv cnt))
  (allocP C x (.shift .lsl (.op .add [vv lCn, .const 1]) (.const 3))
  (.seq (.store (vv x) (vv lCn))
  (.seq (.assign .local lSrc (.op .add [vv src, .shift .lsl (.op .add [off, .const 1]) (.const 3)]))
  (.seq (.assign .local lDst (.op .add [vv x, .const 8]))
  (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop rest))))))

section
variable {σ : Type}

theorem specR_sliceCopyI {α : Type} {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x src : MlS) (off : ExpHOL 64) (cnt : MlS) (oa a k : Nat) (xs : List (BitVec 64))
    (hD : x ∈ D ∧ lCn ∈ D ∧ lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hsrc : Γ.get src = some (cellA C oa))
    (hoff : ∀ v1 v2, sev ((x, v1) :: (lCn, v2) :: Γ) off = some (BitVec.ofNat 64 a)) (hak : a + k ≤ xs.length)
    (hcnt : Γ.get cnt = some (BitVec.ofNat 64 k)) (hb : BlkAt H oa xs) (hz : Γ.get lCz = none)
    (hne : x ≠ lCn ∧ x ≠ lSrc ∧ x ≠ lDst ∧ x ≠ lCi ∧ x ≠ lCz) (hsn : src ≠ lCn ∧ src ≠ x)
    (hcont : ∀ (H' : List (BitVec 64)) o, H <+: H' → H.length ≤ o → BlkAt H' o ((xs.drop a).take k) →
      SpecR (Inv (ctxH C H') s ((lCi, BitVec.ofNat 64 k) :: (lDst, cellA C (o + 1 + k)) ::
        (lSrc, cellA C (oa + 1 + a + k)) :: (x, cellA C o) :: (lCn, BitVec.ofNat 64 k) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (sliceCopyP C x src off cnt rest) s m R := by
  have hlen := blkAt_len hb
  refine specR_assignI lCn (vv cnt) (BitVec.ofNat 64 k) hD.2.1 (by simpa using hcnt) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) x _ (k + 1) (by omega) hD.1 (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get, hne.1.symm]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : H <+: H2 := hp2
  have hH12 := hp2'.length_le
  have hq0 : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) (vv lCn) H2.length hq0 (BitVec.ofNat 64 k)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, hne.1.symm]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 k))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 k) = B
  have hBlen : B.length = H2.length + (k + 1) := by rw [← hB]; simp [hws]
  refine specR_assignI lSrc _ (cellA C (oa + 1 + a)) hD.2.2.1
    (by
      simp +decide [sev, Env.get, hsn.1, hsn.2, hsrc]
      rw [hoff]; simp
      apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega) ?_
  refine specR_assignI lDst _ (cellA C (H2.length + 1)) hD.2.2.2.1
    (by simp +decide [sev, Env.get, hne.2.1]; exact cellA_add8 C _) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) hD.2.2.2.2.1 rfl ?_
  have hdl : ((xs.drop a).take k).length = k := by simp; omega
  have hsrcB : ∀ j (hj : j < ((xs.drop a).take k).length), B[oa + 1 + a + j]? = some ((xs.drop a).take k)[j] := by
    intro j hj
    rw [hdl] at hj
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega), List.getElem_take,
      List.getElem_drop]
    rw [show oa + 1 + a + j = oa + 1 + (a + j) by omega]
    exact (blkAt_mono hb hp2').2 (a + j) (by omega)
  refine specR_copyI (C := C) hok B ((xs.drop a).take k) (oa + 1 + a) (H2.length + 1)
    ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1, hD.2.2.2.2.2⟩ hsrcB (by rw [hdl]; omega) (by rw [hdl]; omega)
    (by rw [hdl]; omega) (by rw [hdl]; simp +decide [Env.get, hne.1.symm]) (by decide)
    (by simp +decide [Env.get, hne.2.2.2.2.symm]; exact hz) ?_
  rw [hdl]
  refine hcont _ H2.length ?_ hH12 ?_
  · refine hp2'.trans (prefix_of_get? (by rw [fillI_length, hBlen]; omega) (fun j hj => ?_))
    rw [fillI_get?, ite_eq_right (by omega), ← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  · have := WC.blk_of_fillI_hdr B ((xs.drop a).take k) H2.length
      (by rw [hdl, ← hB, List.getElem?_set_self (by simp; omega)]) (by rw [hdl, hBlen]; omega)
    rw [hdl] at this; exact this

end

section
variable {σ : Type}

def abN := ofString "ab_n"
def abMI := ofString "ab_mi"
def abRP := ofString "ab_rp"
def abNF := ofString "ab_nf"
def abLv := ofString "ab_lv"
def abPs := ofString "ab_ps"
def abPd := ofString "ab_pd"
def abCb := ofString "ab_cb"
def abPn := ofString "ab_pn"
def abB := ofString "ab_b"
def abS := ofString "ab_s"
def abSc := ofString "ab_sc"
def abC := ofString "ab_c"
def abA := ofString "ab_a"
def abAl := ofString "ab_al"
def abK := ofString "ab_k"
def abOf := ofString "ab_of"
def abI1 := ofString "ab_i1"
def abFd := ofString "ab_fd"
def abIx := ofString "ab_ix"
def abO := ofString "ab_o"
def fIotaPartsBody := ofString "iotaPartsAtBody"

def abParams : List MlS := [abN, abMI, abRP, abNF, abLv, abPs, abPd, abCb]
def abLocals : List MlS := [abPn, abB, abS, abSc, abC, abA, abAl, abK, abOf, abI1, abFd, abIx, abO,
  lCn, lSrc, lDst, lCi, lCz]

def abTail (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local abOf (.op .sub [vv abAl, vv abK]))
  (.seq (.assign .local abI1 (.op .sub [vv abSc, .const 1]))
  (sliceCopyP C abFd abS (.const 0) abI1
  (sliceCopyP C abIx abA (vv abOf) abK
  (alloc6 C abO (vv abFd) (vv abIx) (vv abLv) (vv abPs) (vv abPd) (.const 0) (.return (vv abO))))))

def abBody (C : Ctx) : ProgHOL 64 := prologue abLocals
  (.seq (.assign .local abPn (.load .one (vv abPs)))
  (.seq (.call (some (some (.local, abB), none)) ExIL.fInstLF
    [vv abPs, vv abPn, .const (BitVec.ofNat 64 coreWalkFuel), vv abCb, .const 0])
  (.seq (.call (some (some (.local, abS), none)) fStripPis [vv abNF, vv abB])
  (.ite (.cmp .equal (vv abS) (.const 0)) (.return (.const 0))
  (.seq (.assign .local abSc (.load .one (vv abS)))
  (.seq (.assign .local abC (.load .one (.op .add [vv abS, .shift .lsl (vv abSc) (.const 3)])))
  (.seq (.call (some (some (.local, abA), none)) fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv abC])
  (.seq (.assign .local abAl (.load .one (vv abA)))
  (.seq (.call (some (some (.local, abK), none)) fTSub [vv abAl, vv abN])
  (.ite (.cmp .equal (vv abPn) (vv abN))
    (.ite (.cmp .lower (vv abMI) (vv abRP)) (.return (.const 0))
      (.ite (.cmp .equal (vv abK) (.op .sub [vv abMI, vv abRP])) (abTail C) (.return (.const 0))))
    (.return (.const 0))))))))))))

/-- An optional parts-and-domains answer: `0` for none, else the four `PartsRep` words and the domains. -/
def PostAB (C : Ctx) (o : Option (IIotaParts × List EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ ip pd, o = some (ip, pd) → ∃ ob, w = cellA C ob ∧ PartsRep C H' ob ip ∧
      ∃ o4, H'[ob + 4]? = some (cellA C o4) ∧ BlkAt H' o4 (pd.map Enc.idxW)

theorem postAB_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostAB C a w s' st → PostAB C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem ab_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ abLocals → (ctxEnv C ++ abParams.zip vals).get x = none :=
  Knot.params_none C abLocals abParams vals (by decide) (by decide)

/-- The code `iotaPartsAtBody` runs. -/
structure ABCodes (C : Ctx) : Prop where
  ilf : C.code.lookup ExIL.fInstLF = some (ExIL.ilParams.map (fun p => (p, ShapeHOL.one)), ExIL.fastBodyIL C, .one)
  il : ExIL.CodesIL C
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  ts : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one)
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)

theorem codesIL_H {C : Ctx} (hc : CodesIL C) (H : List (BitVec 64)) : CodesIL (ctxH C H) :=
  ⟨hc.il, hc.bvb, ⟨hc.cb.bvr, hc.cb.memoGet, hc.cb.memoProbe, hc.cb.memoSet, hc.cb.memoIns⟩, hc.liftF,
    ⟨hc.cl.lift, hc.cl.memoGet, hc.cl.memoProbe, hc.cl.memoSet, hc.cl.memoIns, hc.cl.internApp, hc.cl.internLam,
      hc.cl.internForallE, hc.cl.internLet, hc.cl.internBVar, hc.cl.internProj⟩,
    hc.memoGet, hc.memoProbe, hc.memoSet, hc.memoIns, hc.internApp, hc.internLam, hc.internForallE, hc.internLet,
    hc.internBVar, hc.internProj⟩

theorem drop_slice {α β : Type} (f : α → β) (xs : List α) (c : Nat) :
    ((xs.map f).drop (xs.length - (xs.length - c))).take (xs.length - c) = (xs.drop c).map f := by
  rcases Nat.lt_or_ge xs.length c with h | h
  · rw [show xs.length - c = 0 by omega, List.take_zero, List.drop_of_length_le (by omega)]; rfl
  · rw [show xs.length - (xs.length - c) = c by omega, List.take_of_length_le (by simp), List.map_drop]

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; rw [h]

theorem ofNat_lt_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a < BitVec.ofNat 64 b ↔ a < b := by
  rw [BitVec.lt_def]; simp; omega

theorem sev_cmp2 (Γ : Env) (o : Flapjack.Cmp) (e1 e2 : ExpHOL 64) (a b : BitVec 64)
    (h1 : sev Γ e1 = some a) (h2 : sev Γ e2 = some b) :
    sev Γ (.cmp o e1 e2) = some (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL o a b then 1 else 0) := by
  simp [sev, h1, h2]

theorem sev_sub2 (Γ : Env) (e1 e2 : ExpHOL 64) (a b : BitVec 64)
    (h1 : sev Γ e1 = some a) (h2 : sev Γ e2 = some b) : sev Γ (.op .sub [e1, e2]) = some (a - b) := by
  simp [sev, h1, h2]

set_option maxHeartbeats 4000000 in
/-- **`iotaPartsAtBody`**. -/
theorem ab_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : ABCodes C)
    (cnP mI rP : Nat) (rl : IRecRule) (lvls : LsIdx) (params pd : List EIdx) (ctorBody : EIdx) (op opd : Nat)
    (hcn : cnP < 2 ^ 58) (hm : mI < 2 ^ 58) (hr : rP < 2 ^ 58) (hnf : rl.nfields < 2 ^ 58) (hpl : params.length < 2 ^ 59)
    (H : List (BitVec 64)) (hps : BlkAt H op (params.map Enc.idxW)) (hpd : BlkAt H opd (pd.map Enc.idxW))
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (abParams.zip [BitVec.ofNat 64 cnP, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP,
      BitVec.ofNat 64 rl.nfields, Enc.idxW lvls, cellA C op, cellA C opd, Enc.idxW ctorBody])) (abBody C) s
      (iotaPartsAtBody cnP mI rP rl lvls params pd ctorBody) (PostAB (ctxH C H)) := by
  refine specR_prologue (postAB_locals _) (ab_none _ _) ?_
  unfold iotaPartsAtBody
  let Γ0 : Env := ctxEnv (ctxH C H) ++ abParams.zip [BitVec.ofNat 64 cnP, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP,
      BitVec.ofNat 64 rl.nfields, Enc.idxW lvls, cellA C op, cellA C opd, Enc.idxW ctorBody]
  have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ abLocals → z ∉ abLocals →
      Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
    have hne : z ≠ x := fun e => hz (e ▸ hx)
    simp only [Env.get_cons, hne, ite_false]
  have pk : ∀ (Γ : Env), (∀ z, z ∉ abLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ abParams → ∀ v,
      Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
    have hyl : y ∉ abLocals := by
      simp only [abParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp only [sev, sev_vv, hΓ y hyl, h]
  have vN : Γ0.get abN = some (BitVec.ofNat 64 cnP) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vMI : Γ0.get abMI = some (BitVec.ofNat 64 mI) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vRP : Γ0.get abRP = some (BitVec.ofNat 64 rP) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vNF : Γ0.get abNF = some (BitVec.ofNat 64 rl.nfields) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vLv : Γ0.get abLv = some (Enc.idxW lvls) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vPs : Γ0.get abPs = some (cellA C op) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vPd : Γ0.get abPd = some (cellA C opd) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vCb : Γ0.get abCb = some (Enc.idxW ctorBody) := by simp +decide [Γ0, Env.get, abParams, ctxEnv]
  have vZ : Γ0.get lCz = none := ab_none (ctxH C H) _ lCz (by decide)
  have retNone : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env), H <+: H1 →
      SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ abLocals)) (.return (.const 0)) s1 (pure none)
        (PostAB (ctxH C H)) := fun H1 s1 Γ hp1 =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun _ _ e => by simp at e⟩)
  have hpsl := blkAt_len hps
  simp only [List.length_map] at hpsl
  have hc0 : (ctxH C H).H[op]? = some (BitVec.ofNat 64 params.length) := by show H[op]? = _; rw [hps.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) abPn (vv abPs) op _ hc0 (by simp +decide [ctxLocals, abLocals])
    (pk Γ0 (fun _ _ => rfl) abPs (by decide) _ vPs) ?_
  let Γ1 : Env := (abPn, BitVec.ofNat 64 params.length) :: Γ0
  have hΓ1 : ∀ z, z ∉ abLocals → Γ1.get z = Γ0.get z := fun z hz => cnl (by decide) hz
  -- the body at the parameters
  refine ILP.callE_spec (C := ctxH C H) abB ExIL.fInstLF ExIL.ilParams
    [vv abPs, vv abPn, .const (BitVec.ofNat 64 coreWalkFuel), vv abCb, .const 0] (ExIL.fastBodyIL C)
    [cellA C op, BitVec.ofNat 64 params.toArray.size, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ctorBody,
      BitVec.ofNat 64 0] (by decide) rfl (by simp +decide [ctxLocals, abLocals]) hc.ilf
    ⟨pk Γ1 hΓ1 abPs (by decide) _ vPs, by simp [Γ1, sev, Env.get_cons], rfl, pk Γ1 hΓ1 abCb (by decide) _ vCb, rfl,
      trivial⟩
    (ExIL.fastIL_spec ra (ctxH C H) (ctxOK_H hok H) (codesIL_H hc.il H) op params.toArray
      ⟨by simp; omega, fun j hj => by
        have := hps.2 j (by simp at hj ⊢; omega)
        show H[op + 1 + j]? = _
        simpa using this⟩ s coreWalkFuel ctorBody 0 (by unfold coreWalkFuel; decide) (by decide))
    (fun body s1 => ?_)
  let Γ2 : Env := (abB, Enc.idxW body) :: Γ1
  have hΓ2 : ∀ z, z ∉ abLocals → Γ2.get z = Γ0.get z := fun z hz => by
    simp only [Γ2]; rw [cnl (by decide) hz]; exact hΓ1 z hz
  -- the fields
  refine ro_strip C hok hc.sp rl.nfields (by omega) body H s1 abS (vv abNF) (vv abB)
    (by simp +decide [ctxLocals, abLocals]) (pk Γ2 hΓ2 abNF (by decide) _ vNF) (by simp [Γ2, sev, Env.get_cons])
    (fun o wa s2 H2 hp2 hr1 hn1 hs1 => ?_)
  have hp12 : H <+: H2 := hp2
  rcases o with _ | ⟨tys, concl⟩
  · have e0 := hn1 rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact retNone H2 s2 _ hp12
  obtain ⟨oa, rfl, hba⟩ := hs1 tys concl rfl
  have hfl := stripPis_length _ _ _ _ _ _ hr1
  obtain ⟨ha0, haL, -⟩ := strip_last hba
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hba
  have hHN' : H2.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hne : cellA C oa ≠ 0 := cellA_ne0 C hok oa (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H2) abSc (vv abS) oa _ ha0 (by simp +decide [ctxLocals, abLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) abC _ (oa + 1 + tys.length) _ haL (by simp +decide [ctxLocals, abLocals])
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C oa + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  let Γ3 : Env := (abC, Enc.idxW concl) :: (abSc, BitVec.ofNat 64 (tys.length + 1)) :: (abS, cellA C oa) :: Γ2
  have hΓ3 : ∀ z, z ∉ abLocals → Γ3.get z = Γ0.get z := fun z hz => by
    simp only [Γ3]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ2 z hz
  -- the conclusion's arguments
  refine specR_callNIH (C := ctxH C H2) abA fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv abC] (gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW concl] (by decide) rfl (by simp +decide [ctxLocals, abLocals]) hc.gaa
    ⟨rfl, by simp [Γ3, sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H2)) (fun args w _ H' => ∃ oA, w = cellA C oA ∧ BlkAt H' oA (args.map Enc.idxW))
    (fun args w s' st ⟨H', oA, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨oA, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ConPanqueque.T.ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H2 concl s2))
    (fun args wA s3 H3 hp3 ⟨oA, hwA, hab⟩ => ?_)
  subst hwA
  have hp23 : H2 <+: H3 := hp3
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN3 => ?_)
  have hHN3' : H3.length ≤ C.HN := hHN3
  have hal := blkAt_len hab
  simp only [List.length_map] at hal
  have hA0 : (ctxH C H3).H[oA]? = some (BitVec.ofNat 64 args.length) := by show H3[oA]? = _; rw [hab.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H3) abAl (vv abA) oA _ hA0 (by simp +decide [ctxLocals, abLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  let Γ4 : Env := (abAl, BitVec.ofNat 64 args.length) :: (abA, cellA C oA) :: Γ3
  have hΓ4 : ∀ z, z ∉ abLocals → Γ4.get z = Γ0.get z := fun z hz => by
    simp only [Γ4]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ3 z hz
  refine specR_pureBind (args.length - cnP) ?_
  refine rb_tsub (D := ctxLocals ++ abLocals) C hc.ts args.length cnP (by omega) (by omega) H3 s3 abK (vv abAl) (vv abN)
    (by simp +decide [ctxLocals, abLocals]) (by simp [Γ4, sev, Env.get_cons])
    (pk Γ4 hΓ4 abN (by decide) _ vN) (fun H4 hp4 => ?_)
  have hp34 : H3 <+: H4 := hp4
  have hpA : H <+: H4 := (hp12.trans hp23).trans hp34
  let Γ5 : Env := (abK, BitVec.ofNat 64 (args.length - cnP)) :: Γ4
  have hΓ5 : ∀ z, z ∉ abLocals → Γ5.get z = Γ0.get z := fun z hz => by
    simp only [Γ5]; rw [cnl (by decide) hz]; exact hΓ4 z hz
  have gPn : sev Γ5 (vv abPn) = some (BitVec.ofNat 64 params.length) := by
    simp +decide [Γ5, Γ4, Γ3, Γ2, Γ1, sev, Env.get_cons]
  have gN := pk Γ5 hΓ5 abN (by decide) _ vN
  have gMI := pk Γ5 hΓ5 abMI (by decide) _ vMI
  have gRP := pk Γ5 hΓ5 abRP (by decide) _ vRP
  have gK : sev Γ5 (vv abK) = some (BitVec.ofNat 64 (args.length - cnP)) := by simp [Γ5, sev, Env.get_cons]
  have wcE : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal
      (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a = b) := fun a b ha hb => by
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h : a = b
    · subst h; simp
    · simp [h, (ofNat_eq_iff ha hb).not.mpr h]
  have wcL : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower
      (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := fun a b ha hb => by
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h : a < b
    · simp [h, (ofNat_lt_iff ha hb).mpr h]
    · simp [h, (ofNat_lt_iff ha hb).not.mpr h]
  by_cases hpc : params.length = cnP
  · refine specR_ifI _ 1 (by rw [sev_cmp2 _ _ _ _ _ _ gPn gN, wcE _ _ (by omega) (by omega)]; simp [hpc])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_pos hpc]
    by_cases hrm : rP ≤ mI
    · refine specR_ifI _ 0 (by rw [sev_cmp2 _ _ _ _ _ _ gMI gRP, wcL _ _ (by omega) (by omega)]; simp; omega)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_pos hrm]
      have gS : sev Γ5 (.op .sub [vv abMI, vv abRP]) = some (BitVec.ofNat 64 (mI - rP)) := by
        rw [sev_sub2 _ _ _ _ _ gMI gRP]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
      by_cases hix : (args.drop cnP).length = mI - rP
      · have hix' : args.length - cnP = mI - rP := by simpa using hix
        refine specR_ifI _ 1 (by rw [sev_cmp2 _ _ _ _ _ _ gK gS, wcE _ _ (by omega) (by omega)]; simp [hix'])
          (fun _ => ?_) (fun h => absurd h (by decide))
        rw [if_pos hix]
        -- the answer
        have gAl : sev Γ5 (vv abAl) = some (BitVec.ofNat 64 args.length) := by simp +decide [Γ5, Γ4, sev, Env.get_cons]
        have gSc : sev Γ5 (vv abSc) = some (BitVec.ofNat 64 (tys.length + 1)) := by
          simp +decide [Γ5, Γ4, Γ3, sev, Env.get_cons]
        refine specR_assignI abOf _ (BitVec.ofNat 64 (args.length - (args.length - cnP)))
          (by simp +decide [ctxLocals, abLocals])
          (by rw [sev_sub2 _ _ _ _ _ gAl gK]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) ?_
        refine specR_assignI abI1 _ (BitVec.ofNat 64 tys.length) (by simp +decide [ctxLocals, abLocals])
          (by
            have e : sev ((abOf, BitVec.ofNat 64 (args.length - (args.length - cnP))) :: Γ5) (vv abSc) =
                some (BitVec.ofNat 64 (tys.length + 1)) := by
              simp only [sev, sev_vv, Env.get_cons, show abSc ≠ abOf by decide, ite_false] at gSc ⊢; exact gSc
            rw [sev_sub2 _ _ _ _ _ e rfl]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega) ?_
        let Γ6 : Env := (abI1, BitVec.ofNat 64 tys.length) ::
          (abOf, BitVec.ofNat 64 (args.length - (args.length - cnP))) :: Γ5
        have hΓ6 : ∀ z, z ∉ abLocals → Γ6.get z = Γ0.get z := fun z hz => by
          simp only [Γ6]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ5 z hz
        have hz6 : Γ6.get lCz = none := by
          simp +decide only [Γ6, Γ5, Γ4, Γ3, Γ2, Γ1, Env.get_cons, ite_false]; exact vZ
        have hbaH4 := blkAt_mono hba (hp23.trans hp34)
        refine specR_sliceCopyI hok abFd abS (.const 0) abI1 oa 0 tys.length (tys.map Enc.idxW ++ [Enc.idxW concl])
          (by simp +decide [ctxLocals, abLocals])
          (by simp +decide [Γ6, Γ5, Γ4, Γ3, Env.get_cons]) (fun _ _ => rfl) (by simp)
          (by simp [Γ6, Env.get_cons]) hbaH4 hz6 (by decide) (by decide) (fun H5 o5 hp5 hl5 hb5 => ?_)
        have hfd : ((tys.map Enc.idxW ++ [Enc.idxW concl]).drop 0).take tys.length = tys.map Enc.idxW := by simp
        rw [hfd] at hb5
        let Γ7 : Env := (lCi, BitVec.ofNat 64 tys.length) :: (lDst, cellA C (o5 + 1 + tys.length)) ::
          (lSrc, cellA C (oa + 1 + 0 + tys.length)) :: (abFd, cellA C o5) :: (lCn, BitVec.ofNat 64 tys.length) :: Γ6
        have hz7 : Γ7.get lCz = none := by simp +decide only [Γ7, Env.get_cons, ite_false]; exact hz6
        have habH5 := blkAt_mono hab (hp34.trans hp5)
        refine specR_sliceCopyI hok abIx abA (vv abOf) abK oA (args.length - (args.length - cnP)) (args.length - cnP)
          (args.map Enc.idxW) (by simp +decide [ctxLocals, abLocals])
          (by simp +decide [Γ7, Γ6, Γ5, Γ4, Env.get_cons]) (fun _ _ => by simp +decide [Γ7, Γ6, sev, Env.get_cons])
          (by simp) (by simp +decide [Γ7, Γ6, Γ5, Env.get_cons]) habH5 hz7 (by decide) (by decide)
          (fun H6 o6 hp6 hl6 hb6 => ?_)
        rw [drop_slice] at hb6
        have hp56 : H5 <+: H6 := hp6
        have hb5' := blkAt_mono hb5 hp56
        refine specR_alloc6I (ctxOK_H hok H6) abO (vv abFd) (vv abIx) (vv abLv) (vv abPs) (vv abPd) (.const 0)
          (cellA C o5) (cellA C o6) (Enc.idxW lvls) (cellA C op) (cellA C opd) 0 (by simp +decide [ctxLocals, abLocals])
          (fun _ => by simp +decide [sev, Env.get_cons])
          (fun _ => by simp +decide [sev, Env.get_cons])
          (fun _ => by
            simp +decide only [sev, sev_vv, Env.get_cons, ite_false]
            exact (pk Γ6 hΓ6 abLv (by decide) _ vLv))
          (fun _ => by
            simp +decide only [sev, sev_vv, Env.get_cons, ite_false]
            exact (pk Γ6 hΓ6 abPs (by decide) _ vPs))
          (fun _ => by
            simp +decide only [sev, sev_vv, Env.get_cons, ite_false]
            exact (pk Γ6 hΓ6 abPd (by decide) _ vPd))
          (fun _ => rfl) (fun H7 ws hp7 hws hroom => ?_)
        have hp67 : H6 <+: H7 := hp7
        refine specR_returnI (vv abO) (cellA C H7.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ?_)
        have hpi := img6_prefix H7 ws (cellA C o5) (cellA C o6) (Enc.idxW lvls) (cellA C op) (cellA C opd) 0 hws
        obtain ⟨g0, g1, g2, g3, g4, -⟩ :=
          img6_get H7 ws (cellA C o5) (cellA C o6) (Enc.idxW lvls) (cellA C op) (cellA C opd) 0 hws
        have hpall : H <+: img6 H7 ws (cellA C o5) (cellA C o6) (Enc.idxW lvls) (cellA C op) (cellA C opd) 0 :=
          (((hpA.trans hp5).trans hp56).trans hp67).trans hpi
        refine ⟨_, hpall, sr_of_eq ht.sr rfl rfl rfl rfl, fun e => by simp at e, fun ip pd' e => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        have h67 := hp67.trans hpi
        refine ⟨H7.length, rfl, ⟨⟨o5, g0, blkAt_mono hb5' h67⟩, ⟨o6, g1, blkAt_mono hb6 h67⟩, g2,
          ⟨op, g3, blkAt_mono hps hpall⟩⟩, opd, g4, blkAt_mono hpd hpall⟩
      · have hix' : args.length - cnP ≠ mI - rP := by simpa using hix
        refine specR_ifI _ 0 (by rw [sev_cmp2 _ _ _ _ _ _ gK gS, wcE _ _ (by omega) (by omega)]; simp [hix'])
          (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg hix]
        exact retNone H4 s3 _ hpA
    · refine specR_ifI _ 1 (by rw [sev_cmp2 _ _ _ _ _ _ gMI gRP, wcL _ _ (by omega) (by omega)]; simp; omega)
        (fun _ => ?_) (fun h => absurd h (by decide))
      rw [if_neg hrm]
      exact retNone H4 s3 _ hpA
  · refine specR_ifI _ 0 (by rw [sev_cmp2 _ _ _ _ _ _ gPn gN, wcE _ _ (by omega) (by omega)]; simp [hpc])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_neg hpc]
    exact retNone H4 s3 _ hpA

end

end ConPanqueque.T.Ind
