import ConPanqueque.T.Ind.ReplaceFVars
import ConRon.Arena.Inductives.GenRec

/-!
# The classes made checkable (`classKeyOf`) and the generated-recursor class pass

`tcmBody`: `(ds.drop i).mapM (targetCanonParams pfvs)` as a fresh block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def tcmA := ofString "tcm_a"
def tcmI := ofString "tcm_i"
def tcmN := ofString "tcm_n"
def tcmP := ofString "tcm_p"
def tcmX := ofString "tcm_x"
def tcmY := ofString "tcm_y"
def fTcpMap := ofString "tcpMap"

def tcmParams : List MlS := [tcmA, tcmI, tcmN, tcmP]
def tcmLocals : List MlS := gaaLocals ++ [tcmX, tcmY]

def tcmBody (C : Ctx) : ProgHOL 64 := prologue tcmLocals
  (.ite (.cmp .lower (vv tcmI) (vv tcmN))
    (.seq (.assign .local tcmX (.load .one (.op .add [vv tcmA, .op .add [.panop .mul [vv tcmI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, tcmY), none)) fTcp [vv tcmX, vv tcmP])
    (.seq (.call (some (some (.local, ExS.lY), none)) fTcpMap [vv tcmA, .op .add [vv tcmI, .const 1], vv tcmN, vv tcmP])
      (prependP C tcmY))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem tcm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tcmLocals → (ctxEnv C ++ tcmParams.zip vals).get x = none :=
  Knot.params_none C tcmLocals tcmParams vals (by decide) (by decide)

/-- **`tcpMap`** from position `i`. -/
theorem tcm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RFWCodes C)
    (hct : C.code.lookup fTcp = some (tcpParams.map (fun p => (p, ShapeHOL.one)), tcpBody, .one))
    (hcl : C.code.lookup fTcpMap = some (tcmParams.map (fun p => (p, ShapeHOL.one)), tcmBody C, .one))
    (pfvs ds : List EIdx) (pp pa : Nat) (H0 : List (BitVec 64)) (hpf : BlkAt H0 pp (pfvs.map Enc.idxW))
    (hA : BlkAt H0 pa (ds.map Enc.idxW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState), ds.length - i = f → i ≤ ds.length → C.H <+: H → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (tcmParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 ds.length,
        cellA C pp])) (tcmBody C) s ((ds.drop i).mapM (targetCanonParams pfvs)) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp h0
    have hin : i = ds.length := by omega
    subst hin
    refine specR_prologue (postA_locals _) (tcm_none _ _) ?_
    have hal := blkAt_len_le (blkAt_mono hA h0)
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff ds.length ds.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, tcmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.mapM_nil]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      hp2.trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp h0
    have hin : i < ds.length := by omega
    refine specR_prologue (postA_locals _) (tcm_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le (blkAt_mono hA h0)
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i ds.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tcmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, List.mapM_cons]
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) tcmX _ (pa + 1 + i) _ (get_prefix hx h0) (by decide)
      (by simp +decide [sev, Env.get, tcmParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine specR_callNIH (C := ctxH C H) tcmY fTcp tcpParams [vv tcmX, vv tcmP] tcpBody [Enc.idxW ds[i], cellA C pp]
      (by decide) rfl (by decide) hct
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tcmParams, ctxEnv], trivial⟩
      (PostK (ctxH C H)) (fun y w _ _ => w = Enc.idxW y) (fun y w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcpParams _ rfl hlk)
        (tcp_spec ra C hok hc hct pfvs pp H hp (blkAt_mono hpf h0) s ds[i]))
      (fun y w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fTcpMap tcmParams [vv tcmA, .op .add [vv tcmI, .const 1], vv tcmN, vv tcmP]
      (tcmBody C) [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ds.length, cellA C pp] (by decide) rfl (by decide) hcl
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tcmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tcmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, tcmParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tcmParams, ctxEnv],
        trivial⟩
      (PostA (ctxH C H1)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcmParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1') (h0.trans hp1')))
      (fun ys w s2 H2 hp2 ⟨o2, hw, hb2⟩ => ?_)
    subst hw
    refine ExPre.prepend_spec C hok (H := H2) tcmY (Enc.idxW y) o2 (ys.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hb2 (by decide)
      (by simp +decide [Env.get_cons, Env.get, tcmParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, (hp1'.trans (hp2 : H1 <+: H2)).trans hp', rfl, by simpa using hb, hsr⟩

end

/-! ## The parameters closed over the recursor's (`allM`, an open one halts) -/

/-- The twin's closedness test, named. -/
def closedAt (nP : Nat) (x : EIdx) : AM Bool := do
  if (← bvarB coreWalkFuel x) != 0 then pure false
  else pure ((← fvarB coreWalkFuel x) ≤ nP)

def cklA := ofString "ckl_a"
def cklI := ofString "ckl_i"
def cklN := ofString "ckl_n"
def cklP := ofString "ckl_p"
def cklX := ofString "ckl_x"
def cklB := ofString "ckl_b"
def cklR := ofString "ckl_r"
def fClosedAll := ofString "closedAll"

def cklParams : List MlS := [cklA, cklI, cklN, cklP]
def cklLocals : List MlS := [cklX, cklB, cklR]

def cklBody : ProgHOL 64 := prologue cklLocals
  (.ite (.cmp .lower (vv cklI) (vv cklN))
    (.seq (.assign .local cklX (.load .one (.op .add [vv cklA, .op .add [.panop .mul [vv cklI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, cklB), none)) ExB.fBvarB [.const (BitVec.ofNat 64 coreWalkFuel), vv cklX])
    (.ite (.cmp .equal (vv cklB) (.const 0))
      (.seq (.call (some (some (.local, cklB), none)) ExF.fFvarB [.const (BitVec.ofNat 64 coreWalkFuel), vv cklX])
      (.ite (.cmp .lower (vv cklP) (vv cklB)) hang
        (.seq (.call (some (some (.local, cklR), none)) fClosedAll [vv cklA, .op .add [vv cklI, .const 1], vv cklN, vv cklP])
          (.return (vv cklR)))))
      hang)))
    (.return (.const 1)))

section
variable {σ : Type}

theorem ckl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cklLocals → (ctxEnv C ++ cklParams.zip vals).get x = none :=
  Knot.params_none C cklLocals cklParams vals (by decide) (by decide)

/-- **`closedAll`** from position `i` (a `false` halts). -/
theorem ckl_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fClosedAll = some (cklParams.map (fun p => (p, ShapeHOL.one)), cklBody, .one))
    (hcB : ExB.CodesB C (ExB.bodyB C))
    (hbvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one))
    (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (ds : List EIdx) (pa nP : Nat) (hnP : nP < 2 ^ 63) (H : List (BitVec 64)) (hA : BlkAt H pa (ds.map Enc.idxW)) :
    ∀ f i (s : AState), ds.length - i = f → i ≤ ds.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cklParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 ds.length,
        BitVec.ofNat 64 nP])) cklBody s ((ds.drop i).allM (closedAt nP)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = ds.length := by omega
    subst hin
    refine specR_prologue (postB_locals _) (ckl_none _ _) ?_
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff ds.length ds.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cklParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.allM_nil]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < ds.length := by omega
    refine specR_prologue (postB_locals _) (ckl_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i ds.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cklParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, List.allM_cons]
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) cklX _ (pa + 1 + i) _ hx (by decide)
      (by simp +decide [sev, Env.get, cklParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    unfold closedAt
    simp only [bind_assoc]
    refine specR_callNIM cklB ExB.fBvarB [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cklX] (ExB.bvbBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW ds[i]] (by decide) rfl (by decide) hbvb
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩ (ExF.PostN (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExB.bvarB_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hcB) s coreWalkFuel ds[i] CV.coreWalkFuel_lt))
      (fun b w s1 st ⟨hw, hb, _⟩ => ?_)
    subst hw
    by_cases hb0 : b = 0
    swap
    · have hw0 : natW b ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp [natW] at this; omega
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw0)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    subst hb0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, bind_assoc]
    refine specR_callNIM cklB ExF.fFvarB [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cklX] (ExF.fvbBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW ds[i]] (by decide) rfl (by decide) hfvb
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩ (ExF.PostN (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExF.fvarB_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hcF) s1 coreWalkFuel ds[i] CV.coreWalkFuel_lt))
      (fun fb w s2 st ⟨hw, hfb, _⟩ => ?_)
    subst hw
    have hlw2 := ConPanqueque.T.Decl.nd_lt_iff nP fb (by omega) (by omega)
    by_cases hle : fb ≤ nP
    swap
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cklParams, ctxEnv, natW,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cklParams, ctxEnv, natW,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [pure_bind, decide_eq_true_eq, hle, if_true]
    refine specR_congr (m' := (ds.drop (i + 1)).allM (closedAt nP) >>= fun r => pure r) (by rw [bind_pure]; rfl) ?_
    refine specR_callNIH (C := ctxH C H) cklR fClosedAll cklParams [vv cklA, .op .add [vv cklI, .const 1], vv cklN, vv cklP]
      cklBody [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ds.length, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cklParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cklParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cklParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cklParams, ctxEnv],
        trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cklParams _ rfl hlk) (ih (i + 1) s2 (by omega) (by omega)))
      (fun b w s3 H3 hp3 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classKeyOf` -/

/-- A class key at `o`: `[ind, lvls, ds block]`. -/
def KeyRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (k : ClassKey) : Prop :=
  H[o]? = some (Enc.idxW k.ind) ∧ H[o + 1]? = some (Enc.idxW k.lvls) ∧
    ∃ od, H[o + 2]? = some (cellA C od) ∧ BlkAt H od (k.ds.map Enc.idxW)

theorem keyRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {k : ClassKey}
    (h : KeyRep C H o k) : KeyRep C H' o k :=
  let ⟨a, b, od, c, d⟩ := h; ⟨get_prefix a hp, get_prefix b hp, od, get_prefix c hp, blkAt_mono d hp⟩

/-- A key as a fresh record. -/
def PostKey (C : Ctx) (k : ClassKey) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ KeyRep C H' o k ∧ SR (ctxH C H') s' st

theorem postKey_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostKey (σ := σ) C a w s' st → PostKey C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, hk, hs⟩ => ⟨H', o, hp, hw, hk, sr_of_eq hs rfl rfl rfl rfl⟩

def ckoK := ofString "cko_k"
def ckoP := ofString "cko_p"
def ckoN := ofString "cko_n"
def ckoDs := ofString "cko_ds"
def ckoDn := ofString "cko_dn"
def ckoD2 := ofString "cko_d2"
def ckoD2n := ofString "cko_d2n"
def ckoR := ofString "cko_r"
def ckoI := ofString "cko_i"
def ckoL := ofString "cko_l"
def ckoW := ofString "cko_w"
def fClassKeyOf := ofString "classKeyOf"

def ckoParams : List MlS := [ckoK, ckoP, ckoN]
def ckoLocals : List MlS := [ckoDs, ckoDn, ckoD2, ckoD2n, ckoR, ckoI, ckoL, ckoW]

def ckoBody (C : Ctx) : ProgHOL 64 := prologue ckoLocals
  (.seq (.assign .local ckoDs (.load .one (.op .add [vv ckoK, .const 16])))
  (.seq (.assign .local ckoDn (.load .one (vv ckoDs)))
  (.seq (.call (some (some (.local, ckoD2), none)) fTcpMap [vv ckoDs, .const 0, vv ckoDn, vv ckoP])
  (.seq (.assign .local ckoD2n (.load .one (vv ckoD2)))
  (.seq (.call (some (some (.local, ckoR), none)) fClosedAll [vv ckoD2, .const 0, vv ckoD2n, vv ckoN])
  (.ite (.cmp .equal (vv ckoR) (.const 0)) Decl.rejectP
  (.seq (.assign .local ckoI (.load .one (vv ckoK)))
  (.seq (.assign .local ckoL (.load .one (.op .add [vv ckoK, .const 8])))
  (alloc3 C ckoW (vv ckoI) (vv ckoL) (vv ckoD2) (.return (vv ckoW)))))))))))

/-- The code `classKeyOf` runs. -/
structure CKOCodes (C : Ctx) : Prop where
  self : C.code.lookup fClassKeyOf = some (ckoParams.map (fun p => (p, ShapeHOL.one)), ckoBody C, .one)
  rfw : RFWCodes C
  tcp : C.code.lookup fTcp = some (tcpParams.map (fun p => (p, ShapeHOL.one)), tcpBody, .one)
  tcm : C.code.lookup fTcpMap = some (tcmParams.map (fun p => (p, ShapeHOL.one)), tcmBody C, .one)
  ckl : C.code.lookup fClosedAll = some (cklParams.map (fun p => (p, ShapeHOL.one)), cklBody, .one)
  cB : ExB.CodesB C (ExB.bodyB C)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  cF : ExF.CodesF C (ExF.bodyF C)
  fvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)

section
variable {σ : Type}

theorem cko_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ckoLocals → (ctxEnv C ++ ckoParams.zip vals).get x = none :=
  Knot.params_none C ckoLocals ckoParams vals (by decide) (by decide)

set_option maxHeartbeats 4000000 in
/-- **`classKeyOf`** (an open parameter halts). -/
theorem cko_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CKOCodes C)
    (nP : Nat) (hnP : nP < 2 ^ 63) (pfvs : List EIdx) (pp ok : Nat) (k : ClassKey) (H : List (BitVec 64))
    (hp : C.H <+: H) (hpf : BlkAt H pp (pfvs.map Enc.idxW)) (hk : KeyRep C H ok k) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ckoParams.zip [cellA C ok, cellA C pp, BitVec.ofNat 64 nP])) (ckoBody C) s
      (classKeyOf nP pfvs k) (PostKey (ctxH C H)) := by
  refine specR_prologue (postKey_locals _) (cko_none _ _) ?_
  obtain ⟨hki, hkl, od, hkd, hds⟩ := hk
  refine UD.specR_heapLoadI' (C := ctxH C H) ckoDs _ (ok + 2) _ hkd (by decide)
    (by simp +decide [sev, Env.get, ckoParams, ctxEnv]; exact cellA_add_ofNat C ok 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) ckoDn (vv ckoDs) od _ hds.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  unfold classKeyOf classKeyCanon
  simp only [bind_assoc, pure_bind]
  refine specR_congr (m' := ((k.ds.drop 0).mapM (targetCanonParams pfvs)) >>= fun ds => _) (by rw [List.drop_zero]) ?_
  refine specR_callNIH (C := ctxH C H) ckoD2 fTcpMap tcmParams [vv ckoDs, .const 0, vv ckoDn, vv ckoP] (tcmBody C)
    [cellA C od, BitVec.ofNat 64 0, BitVec.ofNat 64 k.ds.length, cellA C pp] (by decide) rfl (by decide) hc.tcm
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, List.length_map],
      by simp +decide [sev, Env.get_cons, Env.get, ckoParams, ctxEnv], trivial⟩
    (PostA (ctxH C H)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
    (fun ys w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcmParams _ rfl hlk)
      (tcm_spec ra C hok hc.rfw hc.tcp hc.tcm pfvs k.ds pp od H hpf hds _ 0 H s rfl (by omega) hp (List.prefix_refl _)))
    (fun ds2 w s1 H1 hp1 ⟨o2, hw, hb2⟩ => ?_)
  subst hw
  have hp1' : H <+: H1 := hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) ckoD2n (vv ckoD2) o2 _ hb2.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_congr (m' := (ds2.drop 0).allM (closedAt nP) >>= fun closed =>
      if closed = true then pure { k with ds := ds2 }
      else (do fail (CheckError.invalid "target rec: the major's parameters mention more than the recursor's parameters")
               pure { k with ds := ds2 })) (by rw [List.drop_zero]; rfl) ?_
  refine specR_callNIH (C := ctxH C H1) ckoR fClosedAll cklParams [vv ckoD2, .const 0, vv ckoD2n, vv ckoN] cklBody
    [cellA C o2, BitVec.ofNat 64 0, BitVec.ofNat 64 ds2.length, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc.ckl
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, List.length_map],
      by simp +decide [sev, Env.get_cons, Env.get, ckoParams, ctxEnv], trivial⟩
    (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cklParams _ rfl hlk)
      (ckl_spec C hok hc.ckl hc.cB hc.bvb hc.cF hc.fvb ds2 o2 nP hnP H1 hb2 _ 0 s1 rfl (by omega)))
    (fun b w s2 H2 hp2 hw => ?_)
  subst hw
  have hp2' : H1 <+: H2 := hp2
  refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get_cons]; exact eqz_b b)
    (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H2) ckoI (vv ckoK) ok _ (get_prefix hki (hp1'.trans hp2')) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, ckoParams, ctxEnv]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) ckoL _ (ok + 1) _ (get_prefix hkl (hp1'.trans hp2')) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, ckoParams, ctxEnv]; exact cellA_add8 C ok) ?_
  refine specR_alloc3I (ctxOK_H hok H2) ckoW (vv ckoI) (vv ckoL) (vv ckoD2) (Enc.idxW k.ind) (Enc.idxW k.lvls)
    (cellA C o2) (by decide) (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun H3 ws hp3 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H3 ws (Enc.idxW k.ind) (Enc.idxW k.lvls) (cellA C o2) hws
  have h3 := img3_prefix H3 ws (Enc.idxW k.ind) (Enc.idxW k.lvls) (cellA C o2) hws
  have hp23 : H2 <+: _ := (hp3 : H2 <+: H3).trans h3
  exact specR_returnI (vv ckoW) (cellA C H3.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, H3.length, (hp1'.trans hp2').trans hp23, rfl, ⟨g0, g1, o2, g2, blkAt_mono hb2 (hp2'.trans hp23)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
