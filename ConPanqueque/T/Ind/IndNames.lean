import ConPanqueque.T.Ind.KindsFlat
import ConPanqueque.T.Ind.IndParams
import ConPanqueque.T.Decl.StepDefn

/-!
# The block's names: none a pinned `And` name, none reserved (else hang)

`ibnBody`: for each constant of an `IndBlk` block, its name is in neither pinned `And` range (`fPim` at
`[11,12)` and `[48,50)`) nor the pin table's reserved list (`fRsm`); a hit hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def ibvB := ofString "ibv_b"
def ibvI := ofString "ibv_i"
def ibvN := ofString "ibv_n"
def ibvR := ofString "ibv_r"
def ibvRl := ofString "ibv_rl"
def ibvP := ofString "ibv_p"
def ibvNm := ofString "ibv_nm"
def ibvA := ofString "ibv_a"
def ibvC := ofString "ibv_c"
def ibvD := ofString "ibv_d"
def ibvX := ofString "ibv_x"
def fIbn := ofString "blockNamesFree"

def ibnParams : List MlS := [ibvB, ibvI, ibvN, ibvR, ibvRl]
def ibnLocals : List MlS := [ibvP, ibvNm, ibvA, ibvC, ibvD, ibvX]

def ibnBody : ProgHOL 64 := prologue ibnLocals
  (.ite (.cmp .lower (vv ibvI) (vv ibvN))
    (.seq (.assign .local ibvP (.load .one (.op .add [vv ibvB, .op .add [.panop .mul [vv ibvI, .const 8], .const 8]])))
    (.seq (.assign .local ibvNm (.load .one (.op .add [vv ibvP, .const 8])))
    (.seq (.call (some (some (.local, ibvA), none)) fPim [vv ibvNm, .const 11, .const 12])
    (.seq (.call (some (some (.local, ibvC), none)) fPim [vv ibvNm, .const 48, .const 50])
    (.seq (.call (some (some (.local, ibvD), none)) fRsm [vv ibvNm, vv ibvR, .const 0, vv ibvRl])
    (.ite (.op .or [vv ibvA, .op .or [vv ibvC, vv ibvD]]) hang
    (.seq (.call (some (some (.local, ibvX), none)) fIbn [vv ibvB, .op .add [vv ibvI, .const 1], vv ibvN, vv ibvR, vv ibvRl])
      (.return (.const 0)))))))))
    (.return (.const 0)))

structure IBNCodes (C : Ctx) : Prop where
  pim : C.code.lookup fPim = some (Decl.pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one)
  rsm : C.code.lookup fRsm = some (Decl.rmParams.map (fun p => (p, ShapeHOL.one)), rsmBody, .one)
  self : C.code.lookup fIbn = some (ibnParams.map (fun p => (p, ShapeHOL.one)), ibnBody, .one)

/-- A block name that is free: in neither `And` range, not reserved. -/
def NameFree (C : Ctx) (n : NIdx) : Prop :=
  pinIn C 11 12 n = false ∧ pinIn C 48 50 n = false ∧ C.pins.reserved.contains n = false

def bsqB := ofString "bsq_b"
def bsqJ := ofString "bsq_j"
def bsqN := ofString "bsq_n"
def bsqR := ofString "bsq_r"
def bsqA := ofString "bsq_a"
def bsqP := ofString "bsq_p"
def bsqX := ofString "bsq_x"
def bsqY := ofString "bsq_y"
def bsqZ := ofString "bsq_z"
def fBsq := ofString "blockSliceEq"

def bsqParams : List MlS := [bsqB, bsqJ, bsqN, bsqR, bsqA]
def bsqLocals : List MlS := [bsqP, bsqX, bsqY, bsqZ]

/-- Do the block's names from `J` on match the reserved list from `A + J` on. -/
def bsqBody : ProgHOL 64 := prologue bsqLocals
  (.ite (.cmp .lower (vv bsqJ) (vv bsqN))
    (.seq (.assign .local bsqP (.load .one (.op .add [vv bsqB, .op .add [.panop .mul [vv bsqJ, .const 8], .const 8]])))
    (.seq (.assign .local bsqX (.load .one (.op .add [vv bsqP, .const 8])))
    (.seq (.assign .local bsqY (.load .one (.op .add [vv bsqR,
        .op .add [.panop .mul [.op .add [vv bsqA, vv bsqJ], .const 8], .const 8]])))
    (.ite (.cmp .equal (vv bsqX) (vv bsqY))
      (.seq (.call (some (some (.local, bsqZ), none)) fBsq [vv bsqB, .op .add [vv bsqJ, .const 1], vv bsqN, vv bsqR, vv bsqA])
        (.return (vv bsqZ)))
      (.return (.const 0))))))
    (.return (.const 1)))

structure BSQCodes (C : Ctx) : Prop where
  self : C.code.lookup fBsq = some (bsqParams.map (fun p => (p, ShapeHOL.one)), bsqBody, .one)

/-- The match from `J` on. -/
def bsqVal (blk : List IConstantInfo) (rs : List NIdx) (A J : Nat) : Bool :=
  ((blk.drop J).zip ((rs.drop (A + J)))).all (fun p => p.1.name == p.2) && decide (blk.length - J ≤ rs.length - (A + J))

section
variable {σ : Type}

/-- The state unchanged, a fact learned, the heap only grown. -/
def PostKFH (C : Ctx) (s : AState) (P : Prop) (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ P ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postKFH_locals (C : Ctx) (s : AState) (P : Prop) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostKFH C s P a w s' st → PostKFH C s P a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, h1, H', h2, h3⟩ => ⟨h0, h1, H', h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem ibn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ibnLocals → (ctxEnv C ++ ibnParams.zip vals).get x = none :=
  Knot.params_none C ibnLocals ibnParams vals (by decide) (by decide)

theorem ci_name_eq (c : IConstantInfo) : c.name = c.toConstantVal.name := by cases c <;> rfl

theorem or3_bw (a b c : Bool) : (boolW a ||| (boolW b ||| boolW c)) = boolW (a || b || c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- **The block's names from position `i` on are free** (else hang). -/
theorem ibn_spec (C : Ctx) (hok : CtxOK C) (hc : IBNCodes C)
    (blk : List IConstantInfo) (ob : Nat) (hblk : IndBlk C C.H ob blk) (oR : Nat)
    (hR : EBlk C.EH oR (C.pins.reserved.map Enc.idxW)) (hRl : C.pins.reserved.length < 2 ^ 62) :
    ∀ f i (H : List (BitVec 64)) (s : AState), blk.length - i = f → i ≤ blk.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (ibnParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 blk.length,
          ecell C oR, BitVec.ofNat 64 C.pins.reserved.length])) ibnBody s
        (pure ()) (PostKFH (ctxH C H) s (∀ c ∈ blk.drop i, NameFree C c.name)) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := hblk
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hpH
    have hil : i = blk.length := by omega
    subst hil
    refine specR_prologue (postKFH_locals _ _ _) (ibn_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len (ctxOK_H hok H) hHN (blkAt_mono hosb hpH)
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, ibnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hpH
    have hil : i < blk.length := by omega
    refine specR_prologue (postKFH_locals _ _ _) (ibn_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hosbH := blkAt_mono hosb hpH
    have hbl := blkAt_len (ctxOK_H hok H) hHN hosbH
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, ibnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : i < os.length := by omega
    have h1 := hosbH.2 i (by simpa using hio)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) ibvP _ (ob + 1 + i) _ h1 (by decide)
      (by simp +decide [sev, Env.get, ibnParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    have hcie := cie_mono hpH (hosr i hil hio)
    have hnm : H[os[i] + 1]? = some (Enc.idxW blk[i].name) := by rw [ci_name_eq]; exact hcie.1.1
    refine UD.specR_heapLoadI' (C := ctxH C H) ibvNm _ (os[i] + 1) _ hnm (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C os[i]) ?_
    set n := blk[i].name with hn
    refine specR_callPure (C := ctxH C H) ibvA fPim Decl.pmParams [vv ibvNm, .const 11, .const 12] (pimBody C)
      [Enc.idxW n, BitVec.ofNat 64 11, BitVec.ofNat 64 12] (pinIn C 11 12 n) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Decl.pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s n 12 (by decide) _ 11 H hpH rfl (by omega)))
      (fun w1 H1 hp1 hw1 => ?_)
    subst hw1
    have hp1' : C.H <+: H1 := hpH.trans hp1
    refine specR_callPure (C := ctxH C H1) ibvC fPim Decl.pmParams [vv ibvNm, .const 48, .const 50] (pimBody C)
      [Enc.idxW n, BitVec.ofNat 64 48, BitVec.ofNat 64 50] (pinIn C 48 50 n) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩
      (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Decl.pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s n 50 (by decide) _ 48 H1 hp1' rfl (by omega)))
      (fun w2 H2 hp2 hw2 => ?_)
    subst hw2
    have hp2' : C.H <+: H2 := hp1'.trans hp2
    refine specR_callPure (C := ctxH C H2) ibvD fRsm Decl.rmParams [vv ibvNm, vv ibvR, .const 0, vv ibvRl] rsmBody
      [Enc.idxW n, ecell C oR, BitVec.ofNat 64 0, BitVec.ofNat 64 C.pins.reserved.length]
      (C.pins.reserved.contains n) (by decide) rfl (by decide) hc.rsm
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ibnParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, ibnParams, ctxEnv], trivial⟩
      (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Decl.rmParams _ rfl hlk)
        (Decl.rsm_spec C hc.rsm C.pins.reserved oR hR hRl n s _ 0 H2 hp2' rfl (Nat.zero_le _)))
      (fun w3 H3 hp3 hw3 => ?_)
    subst hw3
    have hp3' : C.H <+: H3 := hp2'.trans hp3
    by_cases hfree : NameFree C n
    swap
    · refine specR_ifI _ (boolW (pinIn C 11 12 n || pinIn C 48 50 n || C.pins.reserved.contains n)) (by
        simp only [sev, sev_vv, Env.get_cons]; simp +decide [or3_bw])
        (fun _ => specR_hangI) (fun h => ?_)
      exfalso; apply hfree
      have : (pinIn C 11 12 n || pinIn C 48 50 n || C.pins.reserved.contains n) = false := by
        cases e : (pinIn C 11 12 n || pinIn C 48 50 n || C.pins.reserved.contains n) <;> simp_all [boolW]
      simp only [Bool.or_eq_false_iff] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    obtain ⟨f1, f2, f3⟩ := hfree
    have f3' : n ∉ C.pins.reserved := by simpa using f3
    refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [or3_bw, f1, f2, f3, f3'])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) ibvX fIbn ibnParams
      [vv ibvB, .op .add [vv ibvI, .const 1], vv ibvN, vv ibvR, vv ibvRl] ibnBody
      [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 blk.length, ecell C oR,
        BitVec.ofNat 64 C.pins.reserved.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ibnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ibnParams, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, ibnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ibnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ibnParams, ctxEnv], trivial⟩
      (PostKFH (ctxH C H3) s (∀ c ∈ blk.drop (i + 1), NameFree C c.name))
      (fun _ _ s' _ => s' = s ∧ ∀ c ∈ blk.drop (i + 1), NameFree C c.name)
      (fun a w s' st ⟨hs', hP, H', hp', hsr⟩ => ⟨H', hp', ⟨hs', hP⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibnParams _ rfl hlk)
        (ih (i + 1) H3 s (by omega) (by omega) hp3'))
      (fun _ w s1 H4 hp4 ⟨hs1, hall⟩ => ?_)
    subst s1
    have hp4' : H <+: H4 := hp1.trans (hp2.trans (hp3.trans hp4))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by
      rw [List.drop_eq_getElem_cons hil]
      intro c hc'
      rcases List.mem_cons.mp hc' with e | e
      · subst e; exact ⟨f1, f2, f3⟩
      · exact hall c e, H4, hp4', sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem bsqVal_stop (blk : List IConstantInfo) (rs : List NIdx) (A : Nat) (h : A + blk.length ≤ rs.length) :
    bsqVal blk rs A blk.length = true := by
  simp [bsqVal]

theorem bsqVal_step (blk : List IConstantInfo) (rs : List NIdx) (A J : Nat) (hJ : J < blk.length)
    (h : A + blk.length ≤ rs.length) :
    bsqVal blk rs A J = ((blk[J].name == rs[A + J]'(by omega)) && bsqVal blk rs A (J + 1)) := by
  unfold bsqVal
  rw [List.drop_eq_getElem_cons hJ, List.drop_eq_getElem_cons (show A + J < rs.length by omega)]
  simp only [List.zip_cons_cons, List.all_cons, show A + (J + 1) = A + J + 1 by omega]
  have h1 : decide (blk.length - J ≤ rs.length - (A + J)) = true := by simp; omega
  have h2 : decide (blk.length - (J + 1) ≤ rs.length - (A + J + 1)) = true := by simp; omega
  rw [h1, h2]; simp [Bool.and_assoc]

theorem bsq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bsqLocals → (ctxEnv C ++ bsqParams.zip vals).get x = none :=
  Knot.params_none C bsqLocals bsqParams vals (by decide) (by decide)

/-- **The block's names against a reserved slice**, from position `J`. -/
theorem bsq_spec (C : Ctx) (hok : CtxOK C) (hc : BSQCodes C)
    (blk : List IConstantInfo) (ob : Nat) (hblk : IndBlk C C.H ob blk) (rs : List NIdx) (oR : Nat)
    (hR : EBlk C.EH oR (rs.map Enc.idxW)) (A : Nat) (hA : A + blk.length ≤ rs.length) (hRl : rs.length < 2 ^ 59) :
    ∀ f J (H : List (BitVec 64)) (s : AState), blk.length - J = f → J ≤ blk.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (bsqParams.zip [cellA C ob, BitVec.ofNat 64 J, BitVec.ofNat 64 blk.length,
          ecell C oR, BitVec.ofNat 64 A])) bsqBody s (pure (bsqVal blk rs A J)) (PostB (ctxH C H)) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := hblk
  intro f
  induction f with
  | zero =>
    intro J H s hf hJ hpH
    have hil : J = blk.length := by omega
    subst hil
    refine specR_prologue (postB_locals _) (bsq_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len (ctxOK_H hok H) hHN (blkAt_mono hosb hpH)
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, bsqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [bsqVal_stop blk rs A hA]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro J H s hf hJ hpH
    have hil : J < blk.length := by omega
    refine specR_prologue (postB_locals _) (bsq_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hosbH := blkAt_mono hosb hpH
    have hbl := blkAt_len (ctxOK_H hok H) hHN hosbH
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff J blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, bsqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : J < os.length := by omega
    have h1 := hosbH.2 J (by simpa using hio)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) bsqP _ (ob + 1 + J) _ h1 (by decide)
      (by simp +decide [sev, Env.get, bsqParams, ctxEnv]; exact cellA_mulIdx C ob J (by omega)) ?_
    have hcie := cie_mono hpH (hosr J hil hio)
    have hnm : H[os[J] + 1]? = some (Enc.idxW blk[J].name) := by rw [ci_name_eq]; exact hcie.1.1
    refine UD.specR_heapLoadI' (C := ctxH C H) bsqX _ (os[J] + 1) _ hnm (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C os[J]) ?_
    have hr := hR.2 (A + J) (by simp; omega)
    rw [List.getElem_map] at hr
    refine specR_envLoadI bsqY _ (oR + 1 + (A + J)) _ (by decide) (by
        simp +decide [sev, Env.get_cons, Env.get, bsqParams, ctxEnv]
        rw [← BitVec.ofNat_add]; exact WC.ecell_idx C oR (A + J)) hr ?_
    rw [bsqVal_step blk rs A J hil hA]
    by_cases heq : blk[J].name = rs[A + J]'(by omega)
    swap
    · refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact fun h => heq (Enc.idxW_inj h)) (fun h => absurd rfl h) (fun _ => ?_)
      have : (blk[J].name == rs[A + J]'(by omega)) = false := by simpa using heq
      rw [this, Bool.false_and]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, heq])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have : (blk[J].name == rs[A + J]'(by omega)) = true := by simpa using heq
    rw [this, Bool.true_and]
    refine specR_congr (m' := (pure (bsqVal blk rs A (J + 1)) : AM Bool) >>= fun b => pure b) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) bsqZ fBsq bsqParams
      [vv bsqB, .op .add [vv bsqJ, .const 1], vv bsqN, vv bsqR, vv bsqA] bsqBody
      [cellA C ob, BitVec.ofNat 64 (J + 1), BitVec.ofNat 64 blk.length, ecell C oR, BitVec.ofNat 64 A]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, bsqParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bsqParams, ctxEnv]; exact e_succ J,
        by simp +decide [sev, Env.get_cons, Env.get, bsqParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bsqParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bsqParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bsqParams _ rfl hlk)
        (ih (J + 1) H s (by omega) (by omega) hpH))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
