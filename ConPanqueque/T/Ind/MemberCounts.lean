import ConPanqueque.T.Ind.FindRec
import ConPanqueque.T.Ind.BlockCounts
import ConPanqueque.T.Ind.CallG

/-!
# `blockMemberCounts`: every member's index count

For member `m` from `0` to `k - 1`: the first recursor whose major names it (`findRec`), then `blockCounts`;
the counts land in an output array of `k` cells the caller allocated.  Errors halt (`unwrapE`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP

/-- The recursor counts `blockCounts` reads off a found recursor tuple. -/
def recCounts (q : Option (IConstantVal × Nat × Nat × Bool × List IRecRule)) : Option (Nat × Nat) :=
  match q with
  | some q => some (q.2.1, q.2.2.1)
  | none => none

theorem unwrap_bmc_cons (nPd k nC : Nat) (names : List NIdx)
    (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)) (m : Nat) (cvT : IConstantVal)
    (ts : List IConstantVal) :
    unwrapE (blockMemberCounts nPd k nC names rs m (cvT :: ts)) = (do
      let q ← rs.findM? fun q => do pure ((← recTargetOf names q.2.1 q.1.type) == m)
      let c ← unwrapE (blockCounts nPd k nC rs.length cvT (recCounts q))
      let ns ← unwrapE (blockMemberCounts nPd k nC names rs (m + 1) ts)
      pure (c.2 :: ns)) := by
  simp only [unwrapE, blockMemberCounts, bind_assoc]
  congr 1; funext q
  simp only [recCounts]
  congr 1; funext e
  cases e with
  | error er => simp [fail_bind']
  | ok c =>
    simp only [pure_bind, bind_assoc]
    congr 1; funext e2
    cases e2 with
    | error er => simp only [fail_bind']; exact funext fun _ => rfl
    | ok ns => simp

theorem unwrap_bmc_nil (nPd k nC : Nat) (names : List NIdx)
    (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)) (m : Nat) :
    unwrapE (blockMemberCounts nPd k nC names rs m []) = pure [] := by
  simp [unwrapE, blockMemberCounts]

def bmP := ofString "bm_p"
def bmM := ofString "bm_m"
def bmK := ofString "bm_k"
def bmNC := ofString "bm_nc"
def bmNR := ofString "bm_nr"
def bmNP := ofString "bm_np"
def bmO := ofString "bm_o"
def bmJ := ofString "bm_j"
def bmQ := ofString "bm_q"
def bmI := ofString "bm_i"
def bmR := ofString "bm_r"
def bmH := ofString "bm_h"
def bmT := ofString "bm_t"
def bmC := ofString "bm_c"
def fBMC := ofString "blockMemberCounts"

def bmParams : List MlS := [bmP, bmM, bmK, bmNC, bmNR, bmNP, bmO]
def bmLocals : List MlS := [bmJ, bmQ, bmI, bmR, bmH, bmT, bmC]

def bmN : ExpHOL 64 := .op .add [vv bmK, .op .add [vv bmNC, vv bmNR]]

/-- `has, mI, rP` of the found recursor (or none). -/
def bmRecP (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower (vv bmJ) bmN)
    (.seq (.assign .local bmQ (.load .one (.op .add [vv bmP, .op .add [.panop .mul [vv bmJ, .const 8], .const 8]])))
      (.seq (.assign .local bmI (.load .one (.op .add [vv bmQ, .const (BitVec.ofNat 64 (8 * 4))])))
        (.seq (.assign .local bmR (.load .one (.op .add [vv bmQ, .const (BitVec.ofNat 64 (8 * 5))])))
          (.seq (.assign .local bmH (.const 1)) rest))))
    (.seq (.assign .local bmI (.const 0)) (.seq (.assign .local bmR (.const 0)) (.seq (.assign .local bmH (.const 0)) rest)))

/-- After the recursor: the member's type, its count, the store, the rest. -/
def bmTail : ProgHOL 64 :=
  .seq (.assign .local bmQ (.load .one (.op .add [vv bmP, .op .add [.panop .mul [vv bmM, .const 8], .const 8]])))
  (.seq (.assign .local bmT (.load .one (.op .add [vv bmQ, .const (BitVec.ofNat 64 (8 * 3))])))
  (.seq (.call (some (some (.local, bmC), none)) fBlockCounts
      [vv bmNP, vv bmK, vv bmNC, vv bmNR, vv bmT, vv bmH, vv bmI, vv bmR])
  (.seq (.store (.op .add [vv bmO, .panop .mul [vv bmM, .const 8]]) (vv bmC))
  (.seq (.call (some (some (.local, bmC), none)) fBMC
      [vv bmP, .op .add [vv bmM, .const 1], vv bmK, vv bmNC, vv bmNR, vv bmNP, vv bmO])
    (.return (.const 0))))))

def bmBody : ProgHOL 64 := prologue bmLocals
  (.ite (.cmp .lower (vv bmM) (vv bmK))
    (.seq (.call (some (some (.local, bmJ), none)) fFindRec [vv bmP, .op .add [vv bmK, vv bmNC], bmN, vv bmK, vv bmM])
      (bmRecP bmTail))
    (.return (.const 0)))

section
variable {σ : Type}

theorem bm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bmLocals → (ctxEnv C ++ bmParams.zip vals).get x = none :=
  Knot.params_none C bmLocals bmParams vals (by decide) (by decide)

/-- The post: the counts of members `m …` sit in the output array from cell `oa + m`; the base heap `H0` (the
block's) stays a prefix. -/
def PostBM (C : Ctx) (H0 : List (BitVec 64)) (oa m : Nat) (ns : List Nat) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', H0 <+: H' ∧ SR (ctxH C H') s' st ∧ (∀ i (hi : i < ns.length), H'[oa + m + i]? = some (BitVec.ofNat 64 ns[i])) ∧
    ∀ i (hi : i < ns.length), ns[i] < 2 ^ 63

theorem postBM_locals (C : Ctx) (H0 : List (BitVec 64)) (oa m : Nat) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostBM C H0 oa m a w s' st → PostBM C H0 oa m a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h, hb⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h, hb⟩

theorem prefix_set {H0 H : List (BitVec 64)} (hp : H0 <+: H) {j : Nat} (hj : H0.length ≤ j) (v : BitVec 64) :
    H0 <+: H.set j v := by
  obtain ⟨r, rfl⟩ := hp
  refine ⟨r.set (j - H0.length) v, ?_⟩
  rw [List.set_append_right _ _ hj]

end

section
variable {σ : Type}

theorem cellA_mulOff (C : Ctx) (o j : Nat) (hj : j < 2 ^ 59) :
    cellA C o + BitVec.ofNat 64 j * 8#64 = cellA C (o + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem prefix_take_of {H0 L : List (BitVec 64)} (h : H0 <+: L) {j : Nat} (hj : H0.length ≤ j) :
    H0 <+: L.take j := by
  obtain ⟨r, rfl⟩ := h
  rw [List.take_append, List.take_of_length_le hj]
  exact List.prefix_append _ _

theorem take_drop_cons {α : Type} (l : List α) (k m : Nat) (hm : m < k) (hk : k ≤ l.length) :
    (l.take k).drop m = l[m]'(by omega) :: (l.take k).drop (m + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]; simp

/-- **`blockMemberCounts`** from member `m`, errors halting. -/
theorem bm_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fBMC = some (bmParams.map (fun p => (p, ShapeHOL.one)), bmBody, .one))
    (hcf : C.code.lookup fFindRec = some (frParams.map (fun p => (p, ShapeHOL.one)), frBody, .one))
    (hcb : C.code.lookup fBlockCounts = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody, .one))
    (hcp : C.code.lookup fPbc = some ([(pFu, .one), (pH, .one)], pbcBody fPbc, .one))
    (hcr : C.code.lookup fRecTarget = some (rtParams.map (fun p => (p, ShapeHOL.one)), rtBody C, .one))
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k nC nR nPd oa : Nat) (Hb : List (BitVec 64))
    (hlen : blk.length = k + nC + nR) (hb59 : blk.length < 2 ^ 59) (hnPd : nPd < 2 ^ 59)
    (hrk : ∀ i, k + nC ≤ i → i < blk.length → kindAt blk i = some 5)
    (hCb : C.H <+: Hb) (hblk : IndBlk C Hb ob blk) :
    ∀ f m (H0 H : List (BitVec 64)) (s : AState), Hb <+: H0 → H0 <+: H → H0.length ≤ oa + m → oa + k ≤ H.length →
      k - m = f → m ≤ k →
      SpecR (σ := σ) (Pre (ctxH C H) s (bmParams.zip [cellA C ob, BitVec.ofNat 64 m, BitVec.ofNat 64 k,
        BitVec.ofNat 64 nC, BitVec.ofNat 64 nR, BitVec.ofNat 64 nPd, cellA C oa])) bmBody s
        (unwrapE (blockMemberCounts nPd k nC (recNames blk k) ((blk.drop (k + nC)).map recT) m
          (((blk.take k).drop m).map (·.toConstantVal)))) (PostBM C H0 oa m) := by
  intro f
  induction f with
  | zero =>
    intro m H0 H s hb0 h0 hl0 hoa hf hm
    have hmk : m = k := by omega
    subst hmk
    refine specR_prologue (postBM_locals _ _ _ _) (bm_none _ _) ?_
    have hlw := nd_lt_iff m m (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, bmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_eq_nil_of_le (by simp : (blk.take m).length ≤ m), List.map_nil, unwrap_bmc_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, h0, sr_of_eq ht.sr rfl rfl rfl rfl, fun i hi => absurd hi (by simp),
      fun i hi => absurd hi (by simp)⟩)
  | succ f ih =>
    intro m H0 H s hb0 h0 hl0 hoa hf hm
    have hmk : m < k := by omega
    refine specR_prologue (postBM_locals _ _ _ _) (bm_none _ _) ?_
    have hlw := nd_lt_iff m k (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, bmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hmk])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [take_drop_cons blk k m hmk (by omega), List.map_cons, unwrap_bmc_cons]
    have hrsl : ((blk.drop (k + nC)).map recT).length = nR := by simp; omega
    rw [hrsl]
    have hbH : Hb <+: H := hb0.trans h0
    have hbI : IndBlk C H ob blk := indBlk_mono hblk hbH
    -- the rest after the recursor's counts, from any bigger heap
    have tail : ∀ (H1 : List (BitVec 64)) (s1 : AState) (rc : Option (Nat × Nat))
        (Γ : Env), H <+: H1 →
        (∀ y, y ∈ bmParams → Γ.get y = (ctxEnv (ctxH C H) ++ bmParams.zip [cellA C ob, BitVec.ofNat 64 m,
          BitVec.ofNat 64 k, BitVec.ofNat 64 nC, BitVec.ofNat 64 nR, BitVec.ofNat 64 nPd, cellA C oa]).get y) →
        (∀ mI rP, rc = some (mI, rP) → mI < 2 ^ 63 ∧ rP < 2 ^ 63) →
        Γ.get bmH = some ((rWords rc)[0]!) → Γ.get bmI = some ((rWords rc)[1]!) →
        Γ.get bmR = some ((rWords rc)[2]!) →
        SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ bmLocals)) bmTail s1
          (do
            let c ← unwrapE (blockCounts nPd k nC nR blk[m].toConstantVal rc)
            let ns ← unwrapE (blockMemberCounts nPd k nC (recNames blk k) ((blk.drop (k + nC)).map recT) (m + 1)
              (((blk.take k).drop (m + 1)).map (·.toConstantVal)))
            pure (c.2 :: ns)) (PostBM C H0 oa m) := by
      intro H1 s1 rc Γ hpH1 hpar hrc gH gI gR
      have hbI1 : IndBlk C H1 ob blk := indBlk_mono hbI hpH1
      obtain ⟨os, hosl, hblkp, hcie⟩ := id hbI1
      have hom : m < os.length := by omega
      have hpa : ∀ y, y ∈ bmParams → ∀ v, (ctxEnv (ctxH C H) ++ bmParams.zip [cellA C ob, BitVec.ofNat 64 m,
          BitVec.ofNat 64 k, BitVec.ofNat 64 nC, BitVec.ofNat 64 nR, BitVec.ofNat 64 nPd, cellA C oa]).get y = some v →
          sev Γ (vv y) = some v := fun y hy v h => by simp only [sev, sev_vv, hpar y hy, h]
      have gP := hpa bmP (by decide) (cellA C ob) (by simp +decide [Env.get, bmParams, ctxEnv])
      have gM := hpa bmM (by decide) (BitVec.ofNat 64 m) (by simp +decide [Env.get, bmParams, ctxEnv])
      have hw : (ctxH C H1).H[ob + 1 + m]? = some (cellA C os[m]) := by
        show H1[ob + 1 + m]? = _
        have := hblkp.2 m (by simp; omega); simpa using this
      refine UD.specR_heapLoadI' (C := ctxH C H1) bmQ _ (ob + 1 + m) _ hw (by simp +decide [ctxLocals, bmLocals])
        (by simp only [sev] at gP gM ⊢; rw [gP, gM]; simp; exact cellA_mulIdx C ob m (by omega)) ?_
      have hcv := (hcie m (by omega) hom).1
      have hty : (ctxH C H1).H[os[m] + 3]? = some (Enc.idxW blk[m].toConstantVal.type) := by
        have := hcv.2.2; rw [show os[m] + 1 + 2 = os[m] + 3 by omega] at this; exact this
      refine UD.specR_heapLoadI' (C := ctxH C H1) bmT _ (os[m] + 3) _ hty (by simp +decide [ctxLocals, bmLocals])
        (by simp only [sev, sev_vv, Env.get_cons]; simp; exact cellA_plus C _ 3) ?_
      let Γt : Env := (bmT, Enc.idxW blk[m].toConstantVal.type) :: (bmQ, cellA C os[m]) :: Γ
      have up : ∀ y v, y ≠ bmT → y ≠ bmQ → sev Γ (vv y) = some v → sev Γt (vv y) = some v := fun y v h1 h2 h => by
        simp only [sev, sev_vv, Γt, Env.get_cons, ite_eq_right h1, ite_eq_right h2] at h ⊢; exact h
      have gget : ∀ y v, y ≠ bmT → y ≠ bmQ → Γ.get y = some v → sev Γt (vv y) = some v := fun y v h1 h2 h =>
        up y v h1 h2 (by simp only [sev, sev_vv, h])
      have gNP := up bmNP _ (by decide) (by decide) (hpa bmNP (by decide) (BitVec.ofNat 64 nPd) (by simp +decide [Env.get, bmParams, ctxEnv]))
      have gK' := up bmK _ (by decide) (by decide) (hpa bmK (by decide) (BitVec.ofNat 64 k) (by simp +decide [Env.get, bmParams, ctxEnv]))
      have gNC' := up bmNC _ (by decide) (by decide) (hpa bmNC (by decide) (BitVec.ofNat 64 nC) (by simp +decide [Env.get, bmParams, ctxEnv]))
      have gNR' := up bmNR _ (by decide) (by decide) (hpa bmNR (by decide) (BitVec.ofNat 64 nR) (by simp +decide [Env.get, bmParams, ctxEnv]))
      have gT : sev Γt (vv bmT) = some (Enc.idxW blk[m].toConstantVal.type) := by simp [Γt, sev, Env.get_cons]
      have gH' := gget bmH _ (by decide) (by decide) gH
      have gI' := gget bmI _ (by decide) (by decide) gI
      have gR' := gget bmR _ (by decide) (by decide) gR
      refine specR_callNIH (C := ctxH C H1) bmC fBlockCounts bcParams
        [vv bmNP, vv bmK, vv bmNC, vv bmNR, vv bmT, vv bmH, vv bmI, vv bmR] bcBody
        ([BitVec.ofNat 64 nPd, BitVec.ofNat 64 k, BitVec.ofNat 64 nC, BitVec.ofNat 64 nR, Enc.idxW blk[m].toConstantVal.type]
          ++ rWords rc) (by decide) (by cases rc <;> rfl) (by simp +decide [ctxLocals, bmLocals]) hcb
        (by cases rc <;> exact ⟨gNP, gK', gNC', gNR', gT, gH', gI', gR', trivial⟩)
        (PostBC (ctxH C H1)) (fun c w _ _ => w = BitVec.ofNat 64 c.2 ∧ c.2 < 2 ^ 63)
        (fun c w s' st ⟨H', hp', hw', hsr, hb'⟩ => ⟨H', hp', ⟨hw', hb'⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bcParams _ (by cases rc <;> rfl) hlk)
          (bc_spec C hcp nPd k nC nR blk[m].toConstantVal rc ⟨by omega, by omega, by omega, by omega⟩ hrc H1 s1))
        (fun c wc s2 H2 hp2 ⟨hwc, hcb⟩ => ?_)
      subst hwc
      have hpH2 : H <+: H2 := hpH1.trans hp2
      have hl2 : oa + m < H2.length := by have := hpH2.length_le; omega
      have gO := up bmO _ (by decide) (by decide) (hpa bmO (by decide) (cellA C oa) (by simp +decide [Env.get, bmParams, ctxEnv]))
      have gM' := up bmM _ (by decide) (by decide) gM
      refine specR_heapStoreI (ctxOK_H hok H2) (.op .add [vv bmO, .panop .mul [vv bmM, .const 8]]) (vv bmC) (oa + m)
        hl2 (BitVec.ofNat 64 c.2)
        (by
          have e1 : sev ((bmC, BitVec.ofNat 64 c.2) :: Γt) (vv bmO) = some (cellA C oa) := by
            simp only [sev, sev_vv, Env.get_cons, ite_eq_right (show bmO ≠ bmC by decide)] at gO ⊢; exact gO
          have e2 : sev ((bmC, BitVec.ofNat 64 c.2) :: Γt) (vv bmM) = some (BitVec.ofNat 64 m) := by
            simp only [sev, sev_vv, Env.get_cons, ite_eq_right (show bmM ≠ bmC by decide)] at gM' ⊢; exact gM'
          simp only [sev] at e1 e2 ⊢; rw [e1, e2]; simp; exact cellA_mulOff C oa m (by omega))
        (by simp [sev, Env.get_cons]) ?_
      have hl3 : (H2.set (oa + m) (BitVec.ofNat 64 c.2)).length = H2.length := by simp
      let H3 := H2.set (oa + m) (BitVec.ofNat 64 c.2)
      have h0H2 : H0 <+: H2 := h0.trans hpH2
      have h0H3 : H0 <+: H3 := prefix_set h0H2 (by omega) _
      let H0' := H3.take (oa + m + 1)
      have h00' : H0 <+: H0' := prefix_take_of h0H3 (by omega)
      have h0'3 : H0' <+: H3 := List.take_prefix _ _
      have hH0'l : H0'.length = oa + m + 1 := by simp only [H0', H3, List.length_take, List.length_set]; omega
      have hcell : H0'[oa + m]? = some (BitVec.ofNat 64 c.2) := by
        simp only [H0', H3, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by omega)
      let Γs : Env := (bmC, BitVec.ofNat 64 c.2) :: Γt
      have us : ∀ y v, y ≠ bmC → sev Γt (vv y) = some v → sev Γs (vv y) = some v := fun y v h1 h => by
        simp only [sev, sev_vv, Γs, Env.get_cons, ite_eq_right h1] at h ⊢; exact h
      have gPs := us bmP _ (by decide) (up bmP _ (by decide) (by decide) gP)
      have gMs := us bmM _ (by decide) gM'
      have gKs := us bmK _ (by decide) gK'
      have gNCs := us bmNC _ (by decide) gNC'
      have gNRs := us bmNR _ (by decide) gNR'
      have gNPs := us bmNP _ (by decide) gNP
      have gOs := us bmO _ (by decide) gO
      refine specR_callNIG (C := ctxH (ctxH C H2) H3) bmC fBMC bmParams
        [vv bmP, .op .add [vv bmM, .const 1], vv bmK, vv bmNC, vv bmNR, vv bmNP, vv bmO] bmBody
        [cellA C ob, BitVec.ofNat 64 (m + 1), BitVec.ofNat 64 k, BitVec.ofNat 64 nC, BitVec.ofNat 64 nR,
          BitVec.ofNat 64 nPd, cellA C oa] (by decide) rfl (by simp +decide [ctxLocals, bmLocals]) hc
        ⟨gPs, by simp only [sev] at gMs ⊢; rw [gMs]; simp; exact word_add1_eq m, gKs, gNCs, gNRs, gNPs, gOs, trivial⟩
        (PostBM C H0' oa (m + 1)) (fun ns w _ H' => H0' <+: H' ∧
          (∀ i (hi : i < ns.length), H'[oa + (m + 1) + i]? = some (BitVec.ofNat 64 ns[i])) ∧
          ∀ i (hi : i < ns.length), ns[i] < 2 ^ 63)
        (fun ns w s' st ⟨H', hp', hs', hc', hb'⟩ => ⟨H', ⟨hp', hc', hb'⟩, hs'⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bmParams _ rfl hlk)
          (ih (m + 1) H0' H3 s2 (hb0.trans h00') h0'3 (by rw [hH0'l]; omega) (by rw [hl3]; have := hpH2.length_le; omega)
            (by omega) (by omega)))
        (fun ns w s3 H4 ⟨h0'4, hcells, hbs⟩ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, h00'.trans h0'4, sr_of_eq ht.sr rfl rfl rfl rfl, fun i hi => by
        cases i with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          obtain ⟨r, hr⟩ := h0'4; rw [← hr, List.getElem?_append_left (by rw [hH0'l]; omega)]; exact hcell
        | succ i =>
          simp only [List.getElem_cons_succ]
          rw [show oa + m + (i + 1) = oa + (m + 1) + i by omega]
          exact hcells i (by simpa using hi), fun i hi => by
      cases i with
      | zero => simpa using hcb
      | succ i => simpa using hbs i (by simpa using hi)⟩)
    let Γ0 : Env := ctxEnv (ctxH C H) ++ bmParams.zip [cellA C ob, BitVec.ofNat 64 m,
      BitVec.ofNat 64 k, BitVec.ofNat 64 nC, BitVec.ofNat 64 nR, BitVec.ofNat 64 nPd, cellA C oa]
    have gK : Γ0.get bmK = some (BitVec.ofNat 64 k) := by simp +decide [Γ0, Env.get, bmParams, ctxEnv]
    have gNC : Γ0.get bmNC = some (BitVec.ofNat 64 nC) := by simp +decide [Γ0, Env.get, bmParams, ctxEnv]
    have gNR : Γ0.get bmNR = some (BitVec.ofNat 64 nR) := by simp +decide [Γ0, Env.get, bmParams, ctxEnv]
    have hNe : sev Γ0 bmN = some (BitVec.ofNat 64 blk.length) := by
      simp only [bmN, sev, sev_vv, gK, gNC, gNR, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        ofNat_add_small nC nR (by omega), ofNat_add_small k (nC + nR) (by omega)]
      congr 2; omega
    refine specR_callNIH (C := ctxH C H) bmJ fFindRec frParams [vv bmP, .op .add [vv bmK, vv bmNC], bmN, vv bmK, vv bmM]
      frBody [cellA C ob, BitVec.ofNat 64 (k + nC), BitVec.ofNat 64 blk.length, BitVec.ofNat 64 k, BitVec.ofNat 64 m]
      (by decide) rfl (by simp +decide [ctxLocals, bmLocals]) hcf
      ⟨by simp +decide [sev, Env.get, bmParams, ctxEnv],
        by simp +decide [sev, Env.get, bmParams, ctxEnv]; exact ofNat_add_small k nC (by omega), hNe,
        by simp +decide [sev, Env.get, bmParams, ctxEnv], by simp +decide [sev, Env.get, bmParams, ctxEnv], trivial⟩
      (PostFR (ctxH C H) blk (k + nC) blk.length)
      (fun a w _ _ => (a = none ∧ w = BitVec.ofNat 64 blk.length) ∨
        ∃ r, ∃ hr : r < blk.length, k + nC ≤ r ∧ r < blk.length ∧ a = some (recT blk[r]) ∧ w = BitVec.ofNat 64 r)
      (fun a w s' st ⟨H', hp', hs', h'⟩ => ⟨H', hp', h', hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu frParams _ rfl hlk)
        (fr_spec C hok hcf hcr hcs hcg hcn blk ob k m (by omega) hb59 (by omega) (blk.length - (k + nC)) (k + nC) H s
          (hCb.trans hbH) hbI rfl (by omega) hrk))
      (fun a wj s1 H1 hp1 hq => ?_)
    have hpH : H <+: H1 := hp1
    have hbI1 : IndBlk C H1 ob blk := indBlk_mono hbI hpH
    let Γ1 : Env := (bmJ, wj) :: Γ0
    have L1 : ∀ y, y ≠ bmJ → Env.get Γ1 y = Env.get Γ0 y := fun y h => by simp only [Γ1, Env.get_cons, ite_eq_right h]
    have hNe1 : sev Γ1 bmN = some (BitVec.ofNat 64 blk.length) := by
      simp only [bmN, sev, sev_vv, L1 bmK (by decide), L1 bmNC (by decide), L1 bmNR (by decide)] at hNe ⊢; exact hNe
    have pk : ∀ y, y ∈ bmParams → ∀ (Γ : Env), (∀ z, z ≠ bmJ → z ≠ bmQ → z ≠ bmI → z ≠ bmR → z ≠ bmH →
        Env.get Γ z = Env.get Γ1 z) → Env.get Γ y = Env.get Γ0 y := by
      intro y hy Γ hΓ
      simp only [bmParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [hΓ y (by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) (by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
        (by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) (by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
        (by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide),
        L1 y (by rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    rcases hq with ⟨rfl, rfl⟩ | ⟨r, hr, hr1, hr2, rfl, rfl⟩
    · -- no recursor names the member
      refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ1 (vv bmJ) bmN blk.length blk.length (by simp [Γ1, sev, Env.get_cons])
        hNe1 (by omega) (by omega)) (fun h => by simp [bw] at h) (fun _ => ?_)
      refine specR_assignI bmI (.const 0) 0 (by simp +decide [ctxLocals, bmLocals]) rfl ?_
      refine specR_assignI bmR (.const 0) 0 (by simp +decide [ctxLocals, bmLocals]) rfl ?_
      refine specR_assignI bmH (.const 0) 0 (by simp +decide [ctxLocals, bmLocals]) rfl ?_
      refine tail H1 s1 none _ hpH (fun y hy => pk y hy _ ?_) (fun _ _ h => by simp at h) ?_ ?_ ?_
      · intro z h1 h2 h3 h4 h5
        rw [Env.get_cons, ite_eq_right h5, Env.get_cons, ite_eq_right h4, Env.get_cons, ite_eq_right h3]
      · simp [Env.get_cons, rWords]
      · simp +decide [Env.get_cons, rWords]
      · simp +decide [Env.get_cons, rWords]
    · -- recursor `r`
      have hk5 := hrk r hr1 hr
      obtain ⟨os, hosl, hblkp, hcie⟩ := id hbI1
      have hor : r < os.length := by omega
      have hci := hcie r hr hor
      refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ1 (vv bmJ) bmN r blk.length (by simp [Γ1, sev, Env.get_cons])
        hNe1 (by omega) (by omega)) (fun _ => ?_) (fun h => by simp [bw, hr] at h)
      have hw : (ctxH C H1).H[ob + 1 + r]? = some (cellA C os[r]) := by
        show H1[ob + 1 + r]? = _
        have := hblkp.2 r (by simp; omega); simpa using this
      refine UD.specR_heapLoadI' (C := ctxH C H1) bmQ _ (ob + 1 + r) _ hw (by simp +decide [ctxLocals, bmLocals])
        (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Γ1, Γ0, Env.get, bmParams, ctxEnv]
            exact cellA_mulIdx C ob r (by omega)) ?_
      generalize hcr : blk[r] = ci at hci hk5
      cases ci with
      | recInfo cvR mI rP isK rules =>
        obtain ⟨-, -, ⟨hmi, hmi63⟩, ⟨hrp, hrp63⟩, -, -⟩ := hci
        have hsQ : ∀ (Γ : Env), Γ.get bmQ = some (cellA C os[r]) → ∀ q, sev Γ (.op .add [vv bmQ, .const (BitVec.ofNat 64 (8 * q))]) =
            some (cellA C (os[r] + q)) := by
          intro Γ hq q; simp only [sev, sev_vv, hq]; simp; exact cellA_plus C _ q
        refine UD.specR_heapLoadI' (C := ctxH C H1) bmI _ (os[r] + 4) _ hmi (by simp +decide [ctxLocals, bmLocals])
          (hsQ _ (by simp [Env.get_cons]) 4) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H1) bmR _ (os[r] + 5) _ hrp (by simp +decide [ctxLocals, bmLocals])
          (hsQ _ (by simp +decide [Env.get_cons]) 5) ?_
        refine specR_assignI bmH (.const 1) 1 (by simp +decide [ctxLocals, bmLocals]) rfl ?_
        simp only [recCounts, recT_rec]
        refine tail H1 s1 (some (mI, rP)) _ hpH (fun y hy => pk y hy _ ?_) ?_ ?_ ?_ ?_
        · intro z h1 h2 h3 h4 h5
          rw [Env.get_cons, ite_eq_right h5, Env.get_cons, ite_eq_right h4, Env.get_cons, ite_eq_right h3,
            Env.get_cons, ite_eq_right h2]
        · intro a b h; cases h; constructor <;> omega
        · simp [Env.get_cons, rWords]
        · simp +decide [Env.get_cons, rWords]
        · simp +decide [Env.get_cons, rWords]
      | _ => simp [kindAt, List.getElem?_eq_getElem hr, hcr, kindOf] at hk5

end

end ConPanqueque.T.Ind
