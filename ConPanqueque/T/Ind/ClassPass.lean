import ConPanqueque.T.Ind.TargetMajor

/-!
# The generated recursor's class pass (`checkBlockClasses`)

`clsBody`: the motive slots' keys (`ClassRead.classes`), as a block of pointers to key records (a motive slot at
`os` holds its key at `os + 1`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- The keys of the motive slots. -/
def slotKeys : List ClassSlot → List ClassKey
  | [] => []
  | .motive k :: r => k :: slotKeys r
  | .minor _ _ _ :: r => slotKeys r

theorem classes_eq (slots : List ClassSlot) : ClassRead.classes slots = slotKeys slots := by
  induction slots with
  | nil => rfl
  | cons sl r ih => cases sl <;> simp [ClassRead.classes, slotKeys, List.filterMap_cons] at ih ⊢ <;> exact ih

def clsS := ofString "cls_s"
def clsI := ofString "cls_i"
def clsN := ofString "cls_n"
def clsP := ofString "cls_p"
def clsT := ofString "cls_t"
def clsK := ofString "cls_k"
def fSlotKeys := ofString "slotKeys"

def clsParams : List MlS := [clsS, clsI, clsN]
def clsLocals : List MlS := gaaLocals ++ [clsP, clsT, clsK]

def clsBody (C : Ctx) : ProgHOL 64 := prologue clsLocals
  (.ite (.cmp .lower (vv clsI) (vv clsN))
    (.seq (.assign .local clsP (.load .one (.op .add [vv clsS, .op .add [.panop .mul [vv clsI, .const 8], .const 8]])))
    (.seq (.assign .local clsT (.load .one (vv clsP)))
    (.seq (.call (some (some (.local, ExS.lY), none)) fSlotKeys [vv clsS, .op .add [vv clsI, .const 1], vv clsN])
    (.ite (.cmp .equal (vv clsT) (.const 0))
      (.seq (.assign .local clsK (.op .add [vv clsP, .const 8])) (prependP C clsK))
      (.return (vv ExS.lY))))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem cls_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ clsLocals → (ctxEnv C ++ clsParams.zip vals).get x = none :=
  Knot.params_none C clsLocals clsParams vals (by decide) (by decide)

/-- The keys as a fresh block. -/
def PostKeys (C : Ctx) (ks : List ClassKey) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ KeyBlk C H' o ks ∧ SR (ctxH C H') s' st

theorem postKeys_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostKeys (σ := σ) C a w s' st → PostKeys C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, h1, hs⟩ => ⟨H', o, hp, hw, h1, sr_of_eq hs rfl rfl rfl rfl⟩

theorem slotKeys_drop (sls : List ClassSlot) (i : Nat) (hi : i < sls.length) :
    slotKeys (sls.drop i) = (match sls[i] with
      | .motive k => [k]
      | .minor _ _ _ => []) ++ slotKeys (sls.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]; cases sls[i] <;> rfl

/-- **`slotKeys`** over a slot block from position `i`. -/
theorem cls_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fSlotKeys = some (clsParams.map (fun p => (p, ShapeHOL.one)), clsBody C, .one))
    (sls : List ClassSlot) (ob : Nat) (H0 : List (BitVec 64)) (hS : SlotBlk C H0 ob sls) (hsl : sls.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), sls.length - i = f → i ≤ sls.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (clsParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length]))
        (clsBody C) s (pure (slotKeys (sls.drop i))) (PostKeys (ctxH C H)) := by
  obtain ⟨ps, hpl, hpb, hpr⟩ := hS
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (postKeys_locals _) (cls_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, clsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      hp2.trans hpr', rfl, ⟨[], rfl, ⟨by simpa [slotKeys] using hg, fun i hi => absurd hi (by simp [slotKeys])⟩,
        fun k hk => absurd hk (by simp [slotKeys])⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < sls.length := by omega
    refine specR_prologue (postKeys_locals _) (cls_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, clsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [slotKeys_drop sls i hin]
    obtain ⟨op, hop, hrep⟩ := hpr i hin
    have hpi : (ps.map (cellA C))[i]'(by simp; omega) = cellA C op := by
      simp only [List.getElem_map]; rw [List.getElem?_eq_some_iff] at hop; obtain ⟨_, h⟩ := hop; rw [h]
    have hcell := hpb.2 i (by simp; omega)
    rw [hpi] at hcell
    refine UD.specR_heapLoadI' (C := ctxH C H) clsP _ (ob + 1 + i) _ (get_prefix hcell hp) (by decide)
      (by simp +decide [sev, Env.get, clsParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    have htag : H0[op]? = some (match sls[i] with | .motive _ => 0 | .minor _ _ _ => 1) := by
      cases h : sls[i] with
      | motive k => rw [h] at hrep; exact hrep.1
      | minor c cn ihs => rw [h] at hrep; exact hrep.1
    refine UD.specR_heapLoadI' (C := ctxH C H) clsT (vv clsP) op _ (get_prefix htag hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine specR_congr (m' := (pure (slotKeys (sls.drop (i + 1))) : AM (List ClassKey)) >>= fun r =>
      pure ((match sls[i] with | .motive k => [k] | .minor _ _ _ => []) ++ r)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fSlotKeys clsParams [vv clsS, .op .add [vv clsI, .const 1], vv clsN]
      (clsBody C) [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, clsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, clsParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, clsParams, ctxEnv], trivial⟩
      (PostKeys (ctxH C H)) (fun r w _ H' => ∃ o, w = cellA C o ∧ KeyBlk C H' o r)
      (fun r w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu clsParams _ rfl hlk) (ih (i + 1) H s (by omega) (by omega) hp))
      (fun r w s1 H1 hp1 ⟨o1, hw, hb1⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases hsi : sls[i] with
    | motive k =>
      rw [hsi] at hrep
      simp only
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI clsK _ (cellA C (op + 1)) (by decide) (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
      obtain ⟨qs, hql, hqb, hqr⟩ := hb1
      refine ExPre.prepend_spec C hok (H := H1) clsK (cellA C (op + 1)) o1 (qs.map (cellA C)) (by decide)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hqb (by decide)
        (by simp +decide [Env.get_cons, Env.get, clsParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
      obtain ⟨_, k1, k2, od, k3, k4⟩ := hrep
      have hk : KeyRep C H' (op + 1) k :=
        ⟨get_prefix k1 ((hp.trans hp1').trans hp'), get_prefix k2 ((hp.trans hp1').trans hp'), od,
          get_prefix k3 ((hp.trans hp1').trans hp'), blkAt_mono k4 ((hp.trans hp1').trans hp')⟩
      exact ⟨H', o, hp1'.trans hp', rfl, ⟨(op + 1) :: qs, by simp [hql], by simp only [List.map_cons]; exact hb,
        fun k' hk' => by
          cases k' with
          | zero => exact ⟨op + 1, rfl, hk⟩
          | succ k' =>
            obtain ⟨op', h1, h2⟩ := hqr k' (by simpa using hk')
            exact ⟨op', by simpa using h1, keyRep_mono hp' h2⟩⟩, hsr⟩
    | minor c cn ihs =>
      simp only [List.nil_append]
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ (cellA C o1) (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H1, o1, hp1', rfl, hb1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `ks.mapM (classKeyOf nP pfvs)` -/

def ckmK := ofString "ckm_k"
def ckmI := ofString "ckm_i"
def ckmN := ofString "ckm_n"
def ckmP := ofString "ckm_p"
def ckmNp := ofString "ckm_np"
def ckmX := ofString "ckm_x"
def ckmY := ofString "ckm_y"
def fKeysOf := ofString "classKeysOf"

def ckmParams : List MlS := [ckmK, ckmI, ckmN, ckmP, ckmNp]
def ckmLocals : List MlS := gaaLocals ++ [ckmX, ckmY]

def ckmBody (C : Ctx) : ProgHOL 64 := prologue ckmLocals
  (.ite (.cmp .lower (vv ckmI) (vv ckmN))
    (.seq (.assign .local ckmX (.load .one (.op .add [vv ckmK, .op .add [.panop .mul [vv ckmI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, ckmY), none)) fClassKeyOf [vv ckmX, vv ckmP, vv ckmNp])
    (.seq (.call (some (some (.local, ExS.lY), none)) fKeysOf
        [vv ckmK, .op .add [vv ckmI, .const 1], vv ckmN, vv ckmP, vv ckmNp])
      (prependP C ckmY))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem ckm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ckmLocals → (ctxEnv C ++ ckmParams.zip vals).get x = none :=
  Knot.params_none C ckmLocals ckmParams vals (by decide) (by decide)

/-- **`classKeysOf`** from key `i`. -/
theorem ckm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CKOCodes C)
    (hcl : C.code.lookup fKeysOf = some (ckmParams.map (fun p => (p, ShapeHOL.one)), ckmBody C, .one))
    (nP : Nat) (hnP : nP < 2 ^ 63) (pfvs : List EIdx) (ks : List ClassKey) (ok pp : Nat) (H0 : List (BitVec 64))
    (hK : KeyBlk C H0 ok ks) (hpf : BlkAt H0 pp (pfvs.map Enc.idxW)) (hkl : ks.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), ks.length - i = f → i ≤ ks.length → C.H <+: H → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (ckmParams.zip [cellA C ok, BitVec.ofNat 64 i, BitVec.ofNat 64 ks.length,
        cellA C pp, BitVec.ofNat 64 nP])) (ckmBody C) s ((ks.drop i).mapM (classKeyOf nP pfvs)) (PostKeys (ctxH C H)) := by
  obtain ⟨ps, hpl, hpb, hpr⟩ := hK
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp h0
    have hin : i = ks.length := by omega
    subst hin
    refine specR_prologue (postKeys_locals _) (ckm_none _ _) ?_
    have hlw := nd_lt_iff ks.length ks.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ckmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.mapM_nil]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      hp2.trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, fun k hk => absurd hk (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp h0
    have hin : i < ks.length := by omega
    refine specR_prologue (postKeys_locals _) (ckm_none _ _) ?_
    have hlw := nd_lt_iff i ks.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ckmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, List.mapM_cons]
    obtain ⟨okp, hokp, hkr⟩ := hpr i hin
    have hpi : (ps.map (cellA C))[i]'(by simp; omega) = cellA C okp := by
      simp only [List.getElem_map]; rw [List.getElem?_eq_some_iff] at hokp; obtain ⟨_, h⟩ := hokp; rw [h]
    have hcell := hpb.2 i (by simp; omega)
    rw [hpi] at hcell
    refine UD.specR_heapLoadI' (C := ctxH C H) ckmX _ (ok + 1 + i) _ (get_prefix hcell h0) (by decide)
      (by simp +decide [sev, Env.get, ckmParams, ctxEnv]; exact cellA_mulIdx C ok i (by omega)) ?_
    refine specR_callNIH (C := ctxH C H) ckmY fClassKeyOf ckoParams [vv ckmX, vv ckmP, vv ckmNp] (ckoBody C)
      [cellA C okp, cellA C pp, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ckmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ckmParams, ctxEnv], trivial⟩
      (PostKey (ctxH C H)) (fun k w _ H' => ∃ o, w = cellA C o ∧ KeyRep C H' o k)
      (fun k w s' st ⟨H', o, hp', hw, hk, hsr⟩ => ⟨H', hp', ⟨o, hw, hk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ckoParams _ rfl hlk)
        (cko_spec ra C hok hc nP hnP pfvs pp okp ks[i] H hp (blkAt_mono hpf h0) (keyRep_mono h0 hkr) s))
      (fun k w s1 H1 hp1 ⟨ok1, hw, hk1⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fKeysOf ckmParams
      [vv ckmK, .op .add [vv ckmI, .const 1], vv ckmN, vv ckmP, vv ckmNp] (ckmBody C)
      [cellA C ok, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ks.length, cellA C pp, BitVec.ofNat 64 nP]
      (by decide) rfl (by decide) hcl
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ckmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ckmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, ckmParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ckmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ckmParams, ctxEnv], trivial⟩
      (PostKeys (ctxH C H1)) (fun r w _ H' => ∃ o, w = cellA C o ∧ KeyBlk C H' o r)
      (fun r w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ckmParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1') (h0.trans hp1')))
      (fun r w s2 H2 hp2 ⟨o2, hw, hb2⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    obtain ⟨qs, hql, hqb, hqr⟩ := hb2
    refine ExPre.prepend_spec C hok (H := H2) ckmY (cellA C ok1) o2 (qs.map (cellA C)) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hqb (by decide)
      (by simp +decide [Env.get_cons, Env.get, ckmParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, (hp1'.trans hp2').trans hp', rfl, ⟨ok1 :: qs, by simp [hql], by simp only [List.map_cons]; exact hb,
      fun k' hk' => by
        cases k' with
        | zero => exact ⟨ok1, rfl, keyRep_mono (hp2'.trans hp') hk1⟩
        | succ k' =>
          obtain ⟨op', h1, h2⟩ := hqr k' (by simpa using hk')
          exact ⟨op', by simpa using h1, keyRep_mono hp' h2⟩⟩, hsr⟩

end

/-! ## Exactly one class per member -/

def cntT := ofString "cnt_t"
def cntI := ofString "cnt_i"
def cntN := ofString "cnt_n"
def cntW := ofString "cnt_w"
def cntP := ofString "cnt_p"
def cntM := ofString "cnt_m"
def cntR := ofString "cnt_r"
def fCountMember := ofString "countMember"

def cntParams : List MlS := [cntT, cntI, cntN, cntW]
def cntLocals : List MlS := [cntP, cntM, cntR]

/-- The majors from `i` whose member word is `w` (`= t + 1`), counted. -/
def cntBody : ProgHOL 64 := prologue cntLocals
  (.ite (.cmp .lower (vv cntI) (vv cntN))
    (.seq (.assign .local cntP (.load .one (.op .add [vv cntT, .op .add [.panop .mul [vv cntI, .const 8], .const 8]])))
    (.seq (.assign .local cntM (.load .one (.op .add [vv cntP, .const 16])))
    (.seq (.call (some (some (.local, cntR), none)) fCountMember [vv cntT, .op .add [vv cntI, .const 1], vv cntN, vv cntW])
    (.ite (.cmp .equal (vv cntM) (vv cntW)) (.return (.op .add [vv cntR, .const 1])) (.return (vv cntR))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem cnt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cntLocals → (ctxEnv C ++ cntParams.zip vals).get x = none :=
  Knot.params_none C cntLocals cntParams vals (by decide) (by decide)

theorem filter_len_le {α : Type} (l : List α) (f : α → Bool) : (l.filter f).length ≤ l.length := List.length_filter_le f l

/-- **`countMember`** from position `i`. -/
theorem cntm_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fCountMember = some (cntParams.map (fun p => (p, ShapeHOL.one)), cntBody, .one))
    (pfvs : List EIdx) (ms : List TargetMajor) (ot t : Nat) (ht : t < 2 ^ 62) (H : List (BitVec 64))
    (hT : TMBlk C H ot pfvs ms) (hml : ms.length < 2 ^ 59) :
    ∀ f i (s : AState), ms.length - i = f → i ≤ ms.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cntParams.zip [cellA C ot, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length,
        BitVec.ofNat 64 (t + 1)])) cntBody s (pure (((ms.drop i).filter (·.member == some t)).length))
        (PostN (ctxH C H)) := by
  obtain ⟨ps, hpl, hpb, hpr⟩ := hT
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = ms.length := by omega
    subst hin
    refine specR_prologue (postN_locals _) (cnt_none _ _) ?_
    have hlw := nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cntParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < ms.length := by omega
    refine specR_prologue (postN_locals _) (cnt_none _ _) ?_
    have hlw := nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cntParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hrep, -, -⟩ := hpr i hin
    have hpi : (ps.map (cellA C))[i]'(by simp; omega) = cellA C op := by
      simp only [List.getElem_map]; rw [List.getElem?_eq_some_iff] at hop; obtain ⟨_, h⟩ := hop; rw [h]
    have hcell := hpb.2 i (by simp; omega)
    rw [hpi] at hcell
    refine UD.specR_heapLoadI' (C := ctxH C H) cntP _ (ot + 1 + i) _ hcell (by decide)
      (by simp +decide [sev, Env.get, cntParams, ctxEnv]; exact cellA_mulIdx C ot i (by omega)) ?_
    obtain ⟨-, -, -, -, -, -, -, -, hmb, hmbd⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxH C H) cntM _ (op + 2) _ hmb (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 2) ?_
    rw [List.drop_eq_getElem_cons hin, List.filter_cons]
    have hlen := filter_len_le (ms.drop (i + 1)) (·.member == some t)
    simp only [List.length_drop] at hlen
    refine specR_congr (m' := (pure (((ms.drop (i + 1)).filter (·.member == some t)).length) : AM Nat) >>= fun r =>
      pure (if (ms[i].member == some t) = true then r + 1 else r)) (by split <;> simp_all) ?_
    refine specR_callNIH (C := ctxH C H) cntR fCountMember cntParams [vv cntT, .op .add [vv cntI, .const 1], vv cntN, vv cntW]
      cntBody [cellA C ot, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length, BitVec.ofNat 64 (t + 1)] (by decide) rfl
      (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cntParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cntParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cntParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cntParams, ctxEnv],
        trivial⟩
      (PostN (ctxH C H)) (fun r w _ _ => w = BitVec.ofNat 64 r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cntParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun r w s1 H1 hp1 hw => ?_)
    subst hw
    by_cases he : ms[i].member = some t
    · rw [he] at hmb
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cntParams, ctxEnv, optNatW, he,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [he, beq_self_eq_true, if_true]
      exact specR_returnI _ (BitVec.ofNat 64 (r + 1)) (by simp [sev, Env.get_cons]; exact word_add1_eq r)
        (fun t' ht' => ⟨H1, hp1, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
    have hw : optNatW ms[i].member ≠ BitVec.ofNat 64 (t + 1) := by
      rcases hm : ms[i].member with _ | u
      · intro e; have := congrArg BitVec.toNat e; simp [optNatW] at this; omega
      · have hu := hmbd u hm
        intro e; have := congrArg BitVec.toNat e; simp [optNatW] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exact he (by rw [hm]; congr 1; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cntParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    have hb : (ms[i].member == some t) = false := by simpa using he
    simp only [hb, Bool.false_eq_true, if_false]
    exact specR_returnI _ (BitVec.ofNat 64 r) (by simp [sev, Env.get_cons])
      (fun t' ht' => ⟨H1, hp1, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)

end

def unqT := ofString "unq_t"
def unqN := ofString "unq_n"
def unqI := ofString "unq_i"
def unqK := ofString "unq_k"
def unqC := ofString "unq_c"
def unqR := ofString "unq_r"
def fOnePerMember := ofString "onePerMember"

def unqParams : List MlS := [unqT, unqN, unqI, unqK]
def unqLocals : List MlS := [unqC, unqR]

def unqBody : ProgHOL 64 := prologue unqLocals
  (.ite (.cmp .lower (vv unqI) (vv unqK))
    (.seq (.call (some (some (.local, unqC), none)) fCountMember [vv unqT, .const 0, vv unqN, .op .add [vv unqI, .const 1]])
    (.ite (.cmp .equal (vv unqC) (.const 1))
      (.seq (.call (some (some (.local, unqR), none)) fOnePerMember [vv unqT, vv unqN, .op .add [vv unqI, .const 1], vv unqK])
        (.return (vv unqR)))
      (.return (.const 0))))
    (.return (.const 1)))

section
variable {σ : Type}

theorem unq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ unqLocals → (ctxEnv C ++ unqParams.zip vals).get x = none :=
  Knot.params_none C unqLocals unqParams vals (by decide) (by decide)

theorem range_drop_cons (K t : Nat) (ht : t < K) : (List.range K).drop t = t :: (List.range K).drop (t + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using ht)]; simp

/-- **`onePerMember`** from member `t`. -/
theorem unq_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fOnePerMember = some (unqParams.map (fun p => (p, ShapeHOL.one)), unqBody, .one))
    (hcc : C.code.lookup fCountMember = some (cntParams.map (fun p => (p, ShapeHOL.one)), cntBody, .one))
    (pfvs : List EIdx) (ms : List TargetMajor) (ot K : Nat) (hK : K < 2 ^ 61) (hml : ms.length < 2 ^ 59) :
    ∀ f t (H : List (BitVec 64)) (s : AState), K - t = f → t ≤ K → TMBlk C H ot pfvs ms →
      SpecR (σ := σ) (Pre (ctxH C H) s (unqParams.zip [cellA C ot, BitVec.ofNat 64 ms.length, BitVec.ofNat 64 t,
        BitVec.ofNat 64 K])) unqBody s
        (pure (((List.range K).drop t).all (fun t => (ms.filter (·.member == some t)).length == 1)))
        (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro t H s hf ht hT
    have htK : t = K := by omega
    subst htK
    refine specR_prologue (postB_locals _) (unq_none _ _) ?_
    have hlw := nd_lt_iff t t (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, unqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [show (List.range t).drop t = [] by simp]
    exact specR_returnI _ 1 rfl (fun t' ht' => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro t H s hf ht hT
    have htK : t < K := by omega
    refine specR_prologue (postB_locals _) (unq_none _ _) ?_
    have hlw := nd_lt_iff t K (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, unqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr htK])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [range_drop_cons K t htK, List.all_cons]
    have hcnt := filter_len_le ms (·.member == some t)
    refine specR_pureBind ((ms.drop 0).filter (·.member == some t)).length ?_
    refine specR_callNIH (C := ctxH C H) unqC fCountMember cntParams [vv unqT, .const 0, vv unqN, .op .add [vv unqI, .const 1]]
      cntBody [cellA C ot, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.length, BitVec.ofNat 64 (t + 1)] (by decide) rfl
      (by decide) hcc
      ⟨by simp +decide [sev, Env.get, unqParams, ctxEnv], rfl, by simp +decide [sev, Env.get, unqParams, ctxEnv],
        by simp +decide [sev, Env.get, unqParams, ctxEnv]; exact word_add1_eq t, trivial⟩
      (fun a w s' st => (pure ((ms.drop 0).filter (·.member == some t)).length : AM Nat) s = .ok (a, s') ∧
        PostN (ctxH C H) a w s' st)
      (fun a w s' _ => (pure ((ms.drop 0).filter (·.member == some t)).length : AM Nat) s = .ok (a, s') ∧
        w = BitVec.ofNat 64 a)
      (fun a w s' st ⟨hrun, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hrun, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cntParams _ rfl hlk)
        (cntm_spec C hok hcc pfvs ms ot t (by omega) H hT hml _ 0 s rfl (by omega))))
      (fun a w s1 H1 hp1 ⟨hrun, hw⟩ => ?_)
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨hra, hs1⟩ := hrun
    subst hw; subst hs1; subst hra
    simp only [List.drop_zero]
    by_cases h1 : (ms.filter (·.member == some t)).length = 1
    · rw [h1]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, Bool.true_and]
      refine specR_congr (m' := (pure (((List.range K).drop (t + 1)).all (fun t => (ms.filter (·.member == some t)).length == 1)) :
        AM Bool) >>= fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) unqR fOnePerMember unqParams [vv unqT, vv unqN, .op .add [vv unqI, .const 1], vv unqK]
        unqBody [cellA C ot, BitVec.ofNat 64 ms.length, BitVec.ofNat 64 (t + 1), BitVec.ofNat 64 K] (by decide) rfl
        (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, unqParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, unqParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, unqParams, ctxEnv]; exact word_add1_eq t,
          by simp +decide [sev, Env.get_cons, Env.get, unqParams, ctxEnv], trivial⟩
        (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu unqParams _ rfl hlk)
          (ih (t + 1) H1 s (by omega) (by omega) (tmBlk_mono hp1 hT)))
        (fun b w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [Env.get]) (fun t' ht' => ⟨H2, (hp1 : H <+: H1).trans hp2, rfl,
        sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
    · have hne : BitVec.ofNat 64 (ms.filter (·.member == some t)).length ≠ 1#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      have hb : ((ms.filter (·.member == some t)).length == 1) = false := by simpa using h1
      simp only [hb, Bool.false_and]
      exact specR_returnI _ 0 rfl (fun t' ht' => ⟨H1, hp1, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)

end

/-! ## `checkBlockClasses` -/

def cbcM := ofString "cbc_m"
def cbcNp := ofString "cbc_np"
def cbcRs := ofString "cbc_rs"
def cbcL := ofString "cbc_l"
def cbcPp := ofString "cbc_pp"
def cbcRd := ofString "cbc_rd"
def cbcSs := ofString "cbc_ss"
def cbcSn := ofString "cbc_sn"
def cbcKs := ofString "cbc_ks"
def cbcKn := ofString "cbc_kn"
def cbcKs2 := ofString "cbc_ks2"
def cbcKn2 := ofString "cbc_kn2"
def cbcMs := ofString "cbc_ms"
def cbcMn := ofString "cbc_mn"
def cbcK := ofString "cbc_k"
def cbcU := ofString "cbc_u"
def cbcW := ofString "cbc_w"
def fCheckBlockClasses := ofString "checkBlockClasses"

def cbcParams : List MlS := [cbcM, cbcNp, cbcRs, cbcL, cbcPp]
def cbcLocals : List MlS := [cbcRd, cbcSs, cbcSn, cbcKs, cbcKn, cbcKs2, cbcKn2, cbcMs, cbcMn, cbcK, cbcU, cbcW]

def cbcBody (C : Ctx) : ProgHOL 64 := prologue cbcLocals
  (.seq (.call (some (some (.local, cbcRd), none)) fClassRead [vv cbcM, vv cbcNp, vv cbcNp, vv cbcRs])
  (.seq (.assign .local cbcSs (.load .one (vv cbcRd)))
  (.seq (.assign .local cbcSn (.load .one (vv cbcSs)))
  (.seq (.call (some (some (.local, cbcKs), none)) fSlotKeys [vv cbcSs, .const 0, vv cbcSn])
  (.seq (.assign .local cbcKn (.load .one (vv cbcKs)))
  (.seq (.call (some (some (.local, cbcKs2), none)) fKeysOf [vv cbcKs, .const 0, vv cbcKn, vv cbcPp, vv cbcNp])
  (.seq (.assign .local cbcKn2 (.load .one (vv cbcKs2)))
  (.seq (.call (some (some (.local, cbcMs), none)) fClassMajors [vv cbcKs2, .const 0, vv cbcKn2, vv cbcM, vv cbcNp, vv cbcL, vv cbcPp])
  (.seq (.assign .local cbcMn (.load .one (vv cbcMs)))
  (.seq (.assign .local cbcK (.load .one (vv cbcM)))
  (.seq (.call (some (some (.local, cbcU), none)) fOnePerMember [vv cbcMs, vv cbcMn, .const 0, vv cbcK])
  (.ite (.cmp .equal (vv cbcU) (.const 0)) Decl.rejectP
  (alloc2 C cbcW (vv cbcRd) (vv cbcMs) (.return (vv cbcW)))))))))))))))

/-- The code `checkBlockClasses` runs. -/
structure CBCCodes (C : Ctx) : Prop where
  self : C.code.lookup fCheckBlockClasses = some (cbcParams.map (fun p => (p, ShapeHOL.one)), cbcBody C, .one)
  crd : CRDCodes C
  crdc : C.code.lookup fClassRead = some (crdParams.map (fun p => (p, ShapeHOL.one)), crdBody C, .one)
  cls : C.code.lookup fSlotKeys = some (clsParams.map (fun p => (p, ShapeHOL.one)), clsBody C, .one)
  cko : CKOCodes C
  ckm : C.code.lookup fKeysOf = some (ckmParams.map (fun p => (p, ShapeHOL.one)), ckmBody C, .one)
  cmj : CMJCodes C
  cnt : C.code.lookup fCountMember = some (cntParams.map (fun p => (p, ShapeHOL.one)), cntBody, .one)
  unq : C.code.lookup fOnePerMember = some (unqParams.map (fun p => (p, ShapeHOL.one)), unqBody, .one)

section
variable {σ : Type}

theorem cbc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cbcLocals → (ctxEnv C ++ cbcParams.zip vals).get x = none :=
  Knot.params_none C cbcLocals cbcParams vals (by decide) (by decide)

/-- The class pass's answer: `[classRead record, majors block]`. -/
def PostCBC (C : Ctx) (pfvs : List EIdx) (r : ClassRead × List TargetMajor) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H' o ord oms, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (cellA C ord) ∧ ClassReadRep C H' ord r.1 ∧
    H'[o + 1]? = some (cellA C oms) ∧ TMBlk C H' oms pfvs r.2 ∧ SR (ctxH C H') s' st

theorem postCBC_locals (C : Ctx) (pfvs : List EIdx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCBC (σ := σ) C pfvs a w s' st → PostCBC C pfvs a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, ord, oms, hp, hw, h1, h2, h3, h4, hs⟩ =>
    ⟨H', o, ord, oms, hp, hw, h1, h2, h3, h4, sr_of_eq hs rfl rfl rfl rfl⟩

end

section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`checkBlockClasses`** (an off-shape family, an outside class, or a member not of exactly one class halts). -/
theorem cbc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CBCCodes C)
    (mode : ConLeche.CheckMode) (p : BlockShape) (pfvs : List EIdx) (om orr ol pp : Nat) (H : List (BitVec 64))
    (hp : C.H <+: H) (hM : PtrsRep C H om (MemberRep C H) p.members) (hR : PtrsRep C H orr (RecRep C H) p.recs)
    (hml : p.members.length < 2 ^ 59) (hpnP : p.nP < 2 ^ 56) (hrl : p.recs.length < 2 ^ 59)
    (hmI : ∀ i (hi : i < p.recs.length), p.recs[i].mI < 2 ^ 56) (hrP : ∀ i (hi : i < p.recs.length), p.recs[i].rP < 2 ^ 61)
    (hnI : ∀ i (hi : i < p.members.length), p.members[i].nIdx < 2 ^ 63)
    (hlps : EBlk H ol (p.lps.map Enc.idxW)) (hlpl : p.lps.length < 2 ^ 59) (hpf : BlkAt H pp (pfvs.map Enc.idxW))
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (cbcParams.zip [cellA C om, BitVec.ofNat 64 p.nP, cellA C orr, cellA C ol, cellA C pp]))
      (cbcBody C) s (checkBlockClasses mode C.fe p pfvs) (PostCBC (ctxH C H) pfvs) := by
  refine specR_prologue (postCBC_locals _ _) (cbc_none _ _) ?_
  unfold checkBlockClasses
  refine specR_callNIH (C := ctxH C H) cbcRd fClassRead crdParams [vv cbcM, vv cbcNp, vv cbcNp, vv cbcRs] (crdBody C)
    [cellA C om, BitVec.ofNat 64 p.nP, BitVec.ofNat 64 p.nP, cellA C orr] (by decide) rfl (by decide) hc.crdc
    ⟨by simp +decide [sev, Env.get, cbcParams, ctxEnv], by simp +decide [sev, Env.get, cbcParams, ctxEnv],
      by simp +decide [sev, Env.get, cbcParams, ctxEnv], by simp +decide [sev, Env.get, cbcParams, ctxEnv], trivial⟩
    (PostCR (ctxH C H)) (fun o w _ H' => ∃ rd ob, o = some rd ∧ w = cellA C ob ∧ ClassReadRep C H' ob rd)
    (fun o w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crdParams _ rfl hlk)
      (crd_spec ra C hok hc.crd p p.nP p.recs om orr H hp hM hR hml (by omega) hpnP hrl hmI hrP s))
    (fun o w s1 H1 hp1 ⟨rd, ord, ho, hw, hrd⟩ => ?_)
  subst ho; subst hw
  simp only
  have hp1' : H <+: H1 := hp1
  obtain ⟨os, orc, hos, hS, horc, hrc⟩ := id hrd
  refine UD.specR_heapLoadI' (C := ctxH C H1) cbcSs (vv cbcRd) ord _ hos (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  obtain ⟨ps, hpl, hpb, hpr⟩ := id hS
  refine UD.specR_heapLoadI' (C := ctxH C H1) cbcSn (vv cbcSs) os _ hpb.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t1 ht1 => ?_
  have hsl := Big.blk_small0 (ctxOK_H hok H1) ht1.sr hpb
  simp only [List.length_map] at hsl
  rw [classes_eq]
  refine specR_pureBind (slotKeys (rd.slots.drop 0)) ?_
  refine specR_callNIH (C := ctxH C H1) cbcKs fSlotKeys clsParams [vv cbcSs, .const 0, vv cbcSn] (clsBody C)
    [cellA C os, BitVec.ofNat 64 0, BitVec.ofNat 64 rd.slots.length] (by decide) rfl (by decide) hc.cls
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, List.length_map, hpl], trivial⟩
    (fun a w s' st => (pure (slotKeys (rd.slots.drop 0)) : AM (List ClassKey)) s1 = .ok (a, s') ∧
      PostKeys (ctxH C H1) a w s' st)
    (fun a w s' H' => (pure (slotKeys (rd.slots.drop 0)) : AM (List ClassKey)) s1 = .ok (a, s') ∧
      ∃ o, w = cellA C o ∧ KeyBlk C H' o a)
    (fun a w s' st ⟨hrun, H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu clsParams _ rfl hlk)
      (cls_spec C hok hc.cls rd.slots os H1 hS (by omega) _ 0 H1 s1 rfl (by omega) (List.prefix_refl _))))
    (fun ks w s2 H2 hp2 ⟨hrun, oks, hw, hks⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs2⟩ := hrun
  subst hw; subst hs2; subst hra
  simp only [List.drop_zero] at hks ⊢
  have hp2' : H1 <+: H2 := hp2
  obtain ⟨qs, hql, hqb, hqr⟩ := id hks
  refine UD.specR_heapLoadI' (C := ctxH C H2) cbcKn (vv cbcKs) oks _ hqb.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t2 ht2 => ?_
  have hkl := Big.blk_small0 (ctxOK_H hok H2) ht2.sr hqb
  simp only [List.length_map] at hkl
  refine specR_congr (m' := ((slotKeys rd.slots).drop 0).mapM (classKeyOf p.nP pfvs) >>= fun keys => _)
    (by rw [List.drop_zero]) ?_
  have hpH2 : H <+: H2 := hp1'.trans hp2'
  refine specR_callNIH (C := ctxH C H2) cbcKs2 fKeysOf ckmParams [vv cbcKs, .const 0, vv cbcKn, vv cbcPp, vv cbcNp]
    (ckmBody C) [cellA C oks, BitVec.ofNat 64 0, BitVec.ofNat 64 (slotKeys rd.slots).length, cellA C pp,
      BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hc.ckm
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, List.length_map, hql],
      by simp +decide [sev, Env.get_cons, Env.get, cbcParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cbcParams, ctxEnv],
      trivial⟩
    (PostKeys (ctxH C H2)) (fun r w _ H' => ∃ o, w = cellA C o ∧ KeyBlk C H' o r)
    (fun r w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ckmParams _ rfl hlk)
      (ckm_spec ra C hok hc.cko hc.ckm p.nP (by omega) pfvs (slotKeys rd.slots) oks pp H2 hks (blkAt_mono hpf hpH2)
        (by omega) _ 0 H2 s1 rfl (by omega) (hp.trans hpH2) (List.prefix_refl _)))
    (fun keys w s3 H3 hp3 ⟨oky, hw, hky⟩ => ?_)
  subst hw
  have hp3' : H2 <+: H3 := hp3
  obtain ⟨qs2, hql2, hqb2, -⟩ := id hky
  refine UD.specR_heapLoadI' (C := ctxH C H3) cbcKn2 (vv cbcKs2) oky _ hqb2.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t3 ht3 => ?_
  have hkl2 := Big.blk_small0 (ctxOK_H hok H3) ht3.sr hqb2
  simp only [List.length_map] at hkl2
  have hpH3 : H <+: H3 := hpH2.trans hp3'
  refine specR_congr (m' := classMajors mode C.fe p pfvs (keys.drop 0) >>= fun ms => _) (by rw [List.drop_zero]) ?_
  refine specR_callNIH (C := ctxH C H3) cbcMs fClassMajors cmjParams
    [vv cbcKs2, .const 0, vv cbcKn2, vv cbcM, vv cbcNp, vv cbcL, vv cbcPp] (cmjBody C)
    [cellA C oky, BitVec.ofNat 64 0, BitVec.ofNat 64 keys.length, cellA C om, BitVec.ofNat 64 p.nP, cellA C ol, cellA C pp]
    (by decide) rfl (by decide) hc.cmj.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, List.length_map, hql2],
      by simp +decide [sev, Env.get_cons, Env.get, cbcParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cbcParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cbcParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cbcParams, ctxEnv],
      trivial⟩
    (PostTMs (ctxH C H3) pfvs) (fun ms w _ H' => ∃ o, w = cellA C o ∧ TMBlk C H' o pfvs ms)
    (fun ms w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmjParams _ rfl hlk)
      (cmj_spec ra C hok hc.cmj mode C.fe p pfvs keys oky om ol pp H3 hky (ptrsRep_mono hpH3 (fun _ _ h => memberRep_mono hpH3 h) hM)
        hml (by omega) hnI (eblk_mono hlps hpH3) hlpl (blkAt_mono hpf hpH3) (by omega) _ 0 H3 s3 rfl (by omega)
        (hp.trans hpH3) (List.prefix_refl _)))
    (fun ms w s4 H4 hp4 ⟨oms, hw, hms⟩ => ?_)
  subst hw
  have hp4' : H3 <+: H4 := hp4
  obtain ⟨qs3, hql3, hqb3, -⟩ := id hms
  refine UD.specR_heapLoadI' (C := ctxH C H4) cbcMn (vv cbcMs) oms _ hqb3.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hM4 := ptrsRep_mono (hpH3.trans hp4') (fun _ _ h => memberRep_mono (hpH3.trans hp4') h) hM
  refine UD.specR_heapLoadI' (C := ctxH C H4) cbcK (vv cbcM) om _ hM4.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cbcParams, ctxEnv]; rfl) ?_
  refine specR_atEntry fun t4 ht4 => ?_
  have hml4 := Big.blk_small0 (ctxOK_H hok H4) ht4.sr hqb3
  simp only [List.length_map] at hml4
  refine specR_pureBind (((List.range p.k).drop 0).all (fun t => (ms.filter (·.member == some t)).length == 1)) ?_
  refine specR_callNIH (C := ctxH C H4) cbcU fOnePerMember unqParams [vv cbcMs, vv cbcMn, .const 0, vv cbcK] unqBody
    [cellA C oms, BitVec.ofNat 64 ms.length, BitVec.ofNat 64 0, BitVec.ofNat 64 p.k] (by decide) rfl (by decide) hc.unq
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, List.length_map, hql3], rfl,
      by simp +decide [sev, Env.get_cons, BlockShape.k], trivial⟩
    (fun a w s' st => (pure (((List.range p.k).drop 0).all (fun t => (ms.filter (·.member == some t)).length == 1)) :
      AM Bool) s4 = .ok (a, s') ∧ PostB (ctxH C H4) a w s' st)
    (fun a w s' _ => (pure (((List.range p.k).drop 0).all (fun t => (ms.filter (·.member == some t)).length == 1)) :
      AM Bool) s4 = .ok (a, s') ∧ w = boolW a)
    (fun a w s' st ⟨hrun, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hrun, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu unqParams _ rfl hlk)
      (unq_spec C hok hc.unq hc.cnt pfvs ms oms p.k (by simp [BlockShape.k]; omega) (by omega) _ 0 H4 s4 rfl (by omega) hms)))
    (fun b w s5 H5 hp5 ⟨hrun, hw⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hrb, hs5⟩ := hrun
  subst hw; subst hs5; subst hrb
  try simp only [List.drop_zero]
  have hp5' : H4 <+: H5 := hp5
  refine specR_failIteF (c := (List.range p.k).all (fun t => (ms.filter (·.member == some t)).length == 1)) _ _
    (by simp +decide [sev, Env.get_cons]; exact eqz_b _) (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
  refine specR_alloc2I (ctxOK_H hok H5) cbcW (vv cbcRd) (vv cbcMs) (cellA C ord) (cellA C oms) (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun H6 ws hp6 hws => ?_)
  obtain ⟨g0, g1⟩ := img2_get H6 ws (cellA C ord) (cellA C oms) hws
  have h6 := img2_prefix H6 ws (cellA C ord) (cellA C oms) hws
  have hp56 : H5 <+: _ := (hp6 : H5 <+: H6).trans h6
  refine specR_returnI (vv cbcW) (cellA C H6.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ?_)
  have hp16 : H1 <+: _ := ((hp2'.trans hp3').trans hp4').trans (hp5'.trans hp56)
  exact ⟨_, H6.length, ord, oms, (hp1'.trans hp16), rfl, g0,
    ⟨os, orc, get_prefix hos hp16, slotBlk_mono hp16 hS, get_prefix horc hp16, blkAt_mono hrc hp16⟩, g1,
    tmBlk_mono (hp5'.trans hp56) hms, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.Ind
