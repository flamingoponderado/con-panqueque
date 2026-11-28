import ConPanqueque.Front.Dispatch
import ConPanqueque.T.Big.NatBin

/-! # Large `natVal` literals: the arithmetic

A literal at or above `natCap` of at most 36 digits is `hi · 10^18 + lo`, both parts read by
`readNatSat` (each below the cap); the product and the sum go through the verified bignum
procedures, and `litBlk` interns the result.  Here: the digit-split lemma on con-leche's reader, and
an inline one-word block. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend
open ConLeche.Frontend (IdTable)

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

/-- The accumulator comes out times a power of ten. -/
theorem readL_acc (bs : List UInt8) (e : Nat) (he : e ≤ bs.length) :
    ∀ n i acc, e - i = n → readL bs i e acc = acc * 10 ^ (e - i) + readL bs i e 0 := by
  intro n
  induction n with
  | zero =>
    intro i acc hn
    rw [readL_end bs i e acc (by omega), readL_end bs i e 0 (by omega), show e - i = 0 by omega]; simp
  | succ n ih =>
    intro i acc hn
    rw [readL_step bs i e acc (by omega) (by omega), readL_step bs i e 0 (by omega) (by omega),
      ih (i + 1) _ (by omega), ih (i + 1) (0 * 10 + _) (by omega), show e - i = e - (i + 1) + 1 by omega,
      Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    rw [Nat.mul_comm 10]

/-- Reading `[i, e)` is reading `[i, m)`, then `[m, e)` from that accumulator. -/
theorem readL_mid (bs : List UInt8) (e m : Nat) (hme : m ≤ e) (he : e ≤ bs.length) :
    ∀ n i acc, m - i = n → i ≤ m → readL bs i e acc = readL bs m e (readL bs i m acc) := by
  intro n
  induction n with
  | zero =>
    intro i acc hn him
    obtain rfl : i = m := by omega
    rw [readL_end bs i i acc (by omega)]
  | succ n ih =>
    intro i acc hn him
    rw [readL_step bs i e acc (by omega) (by omega), readL_step bs i m acc (by omega) (by omega)]
    exact ih (i + 1) _ (by omega) (by omega)

/-- **The digit split**: `[i, e)` reads as `[i, m)` shifted by `e - m` digits plus `[m, e)`. -/
theorem readL_split (bs : List UInt8) (i m e : Nat) (him : i ≤ m) (hme : m ≤ e) (he : e ≤ bs.length) :
    readL bs i e 0 = readL bs i m 0 * 10 ^ (e - m) + readL bs m e 0 := by
  rw [readL_mid bs e m hme he _ i 0 rfl him, readL_acc bs e he _ m _ rfl]

section
variable {σ : Type}

/-- An inline one-word block `[w ≠ 0, w]` (the limbs of `w`) at a fresh `x`. -/
def wblkP (C : Ctx) (x : MlS) (v : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 16) (.seq (.store (vv x) (.cmp .notEqual v (.const 0)))
    (.seq (.store (.op .add [vv x, .const 8]) v) rest))

theorem specR_wblkI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (v : ExpHOL 64) (w : Nat)
    (hw : w < ConPanqueque.T.Big.B) (hv : ∀ a, sev ((x, a) :: Γ) v = some (BitVec.ofNat 64 w)) (hx : x ∈ D)
    (hk : ∀ H' o, C.H <+: H' → BlkAt H' o (Enc.limbs w) →
      SpecR (Inv (ctxH C H') s ((x, cellA C o) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (wblkP C x v rest) s m R := by
  unfold wblkP
  refine specR_allocI x (.const 16) 2 (by decide) hx (fun v => by simp [sev]) (fun H' ws hpre hwl hcap => ?_)
  have hj : H'.length < (ctxH C (H' ++ ws)).H.length := by show _ < (H' ++ ws).length; simp; omega
  have hB : ConPanqueque.T.Big.B = 2 ^ 64 := rfl
  let hdr : BitVec 64 := BitVec.ofNat 64 (Enc.limbs w).length
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) _ _ hj hdr (by simp [sev]; rfl) ?_ ?_
  · simp only [sev, hv, hdr, ConPanqueque.T.Big.limbs_word w hw]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h0 : w = 0
    · simp [h0]
    · have : BitVec.ofNat 64 w ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp [h0]; exact this
  have hj2 : H'.length + 1 < (ctxH C ((H' ++ ws).set H'.length hdr)).H.length := by
    show _ < ((H' ++ ws).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ v _ hj2 (BitVec.ofNat 64 w)
    (by simp [sev]; exact cellA_add8 C _) (hv _) ?_
  have hp1 := prefix_set_ge (hpre.trans (List.prefix_append _ ws)) _ hpre.length_le hdr
  have hp2 := prefix_set_ge hp1 (H'.length + 1) (by have := hpre.length_le; omega) (BitVec.ofNat 64 w)
  refine hk _ H'.length hp2 ?_
  have e1 : (((H' ++ ws).set H'.length hdr).set (H'.length + 1) (BitVec.ofNat 64 w))[H'.length]? = some hdr := by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have e2 : (((H' ++ ws).set H'.length hdr).set (H'.length + 1) (BitVec.ofNat 64 w))[H'.length + 1]? =
      some (BitVec.ofNat 64 w) := by
    rw [List.getElem?_set_self (by simp; omega)]
  refine ⟨e1, fun i hi => ?_⟩
  have hl : (Enc.limbs w).length = if w = 0 then 0 else 1 := by
    rw [ConPanqueque.T.Big.limbs_word w hw]; split <;> rfl
  by_cases h0 : w = 0
  · rw [hl, ite_eq_left h0] at hi; omega
  have hi0 : i = 0 := by rw [hl, ite_eq_right h0] at hi; omega
  subst hi0
  rw [ConPanqueque.T.Big.limbs_getElem w 0 hi]
  show (((H' ++ ws).set H'.length hdr).set (H'.length + 1) (BitVec.ofNat 64 w))[H'.length + 1 + 0]? = _
  rw [Nat.add_zero, e2, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hw]

end

def kH2 := ofString "kh2"
def kL2 := ofString "kl2"
def kM2 := ofString "km2"
def kD2 := ofString "kd2"
def kX2 := ofString "kx2"
def kT2 := ofString "kt2"
def kY2 := ofString "ky2"
def kP2 := ofString "kp2"
def kS2 := ofString "ks2"

/-- `10 ^ 18`. -/
def tenE : Nat := 1000000000000000000

theorem tenE_eq : tenE = 10 ^ 18 := by decide

theorem len_le1 {w : Nat} (h : w < ConPanqueque.T.Big.B) : (Enc.limbs w).length ≤ 1 :=
  (ConPanqueque.T.Big.limbs_length_lt_iff w 1).mpr (by simpa using h)

theorem len_ge1 {w : Nat} (h : w ≠ 0) : 1 ≤ (Enc.limbs w).length := by
  rw [ConPanqueque.T.Big.limbs_pos h]; simp

section
variable {σ : Type}

/-- `natVal (hi · 10^18 + lo)` at index `i`, `hi` in `kH2` and `lo` in `kL2`. -/
def exBigP (C : Ctx) : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
   (wblkP C kX2 (vv kH2) (wblkP C kT2 (.const (BitVec.ofNat 64 tenE)) (wblkP C kY2 (vv kL2)
    (.seq (.call (some (some (.local, kP2), none)) ConPanqueque.T.Big.fMul [vv kX2, vv kT2])
    (.seq (.call (some (some (.local, kS2), none)) ConPanqueque.T.Big.fAdd [vv kP2, vv kY2])
    (.seq (.call (some (some (.local, fh), none)) ConPanqueque.T.Big.fLitB [vv kS2])
      (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0)))))))))

theorem exBig_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcM : C.code.lookup ConPanqueque.T.Big.fMul = some (ConPanqueque.T.Big.mulParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.mulBody C, .one))
    (hcA : C.code.lookup ConPanqueque.T.Big.fAdd = some (ConPanqueque.T.Big.addParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.addBody C, .one))
    (hcB : C.code.lookup ConPanqueque.T.Big.fLitB =
      some ([(ConPanqueque.T.Big.iLx, .one)], ConPanqueque.T.Big.litBlkBody C, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fh, kX2, kT2, kY2, kP2, kS2], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i hi lo : Nat) (hi64 : i < 2 ^ 64) (hhi : hi < natCap) (hlo : lo < natCap) (hbig : natCap ≤ hi * tenE + lo)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hH : Γ.get kH2 = some (BitVec.ofNat 64 hi))
    (hL : Γ.get kL2 = some (BitVec.ofNat 64 lo)) :
    SpecR (Inv (σ := σ) C s Γ M D) (exBigP C) s (parseExprEntryD st i (.natVal (hi * tenE + lo)))
      (ExPost C jE cap st i) := by
  have hNB : natCap < ConPanqueque.T.Big.B := by unfold natCap; decide
  unfold exBigP
  refine specR_exFresh (hD fx (by simp)) st jE cap hrel hcap i hi64 hTE hC hI (fun hic hg => ?_)
  have hm : parseExprEntryD st i (.natVal (hi * tenE + lo)) =
      (internE (.lit (.natVal (hi * tenE + lo))) >>= fun e =>
        (pure { st with exprs := st.exprs.insert i e } : AM StateD)) := by
    simp [parseExprEntryD, StateD.freshExpr, IdTable.bound_eq, hg]
  rw [hm]
  refine specR_dropMem ?_
  refine specR_wblkI hok kX2 (vv kH2) hi (by omega)
    (fun a => by simp (config := {decide := true}) [sev, vv, Env.get_cons, hH]) (hD _ (by simp))
    (fun H1 o1 hp1 hb1 => ?_)
  refine specR_wblkI (C := ctxH C H1) (ctxOK_H hok _) kT2 (.const (BitVec.ofNat 64 tenE)) tenE (by decide)
    (fun a => rfl) (hD _ (by simp)) (fun H2 o2 hp2 hb2 => ?_)
  refine specR_wblkI (C := ctxH (ctxH C H1) H2) (ctxOK_H hok _) kY2 (vv kL2) lo (by omega)
    (fun a => by simp (config := {decide := true}) [sev, vv, Env.get_cons, hL]) (hD _ (by simp))
    (fun H3 o3 hp3 hb3 => ?_)
  have hp2' : H1 <+: H2 := hp2
  have hp3' : H2 <+: H3 := hp3
  have hpos : hi * tenE ≠ 0 := by intro h0; rw [h0] at hbig; omega
  refine ConPanqueque.T.Big.specR_callPH (C := ctxH C H3) (k := fun _ =>
      internE (.lit (.natVal (hi * tenE + lo))) >>= fun e => (pure { st with exprs := st.exprs.insert i e } : AM StateD))
    kP2 ConPanqueque.T.Big.fMul ConPanqueque.T.Big.mulParams [vv kX2, vv kT2] (ConPanqueque.T.Big.mulBody C)
    [cellA C o1, cellA C o2] (hi * tenE) (by decide) rfl (hD _ (by simp)) hcM
    ⟨by simp (config := {decide := true}) [sev, vv, Env.get_cons],
     by simp (config := {decide := true}) [sev, vv, Env.get_cons]; rfl, trivial⟩
    (ConPanqueque.T.Big.mul_spec (ctxH C H3) (ctxOK_H hok _) s hi tenE o1 o2
      (blkAt_mono hb1 (hp2'.trans hp3')) (blkAt_mono hb2 hp3')
      (by have := len_le1 (w := hi) (by omega); have := len_le1 (w := tenE) (by decide); omega))
    (fun H4 o4 hp4 hb4 => ?_)
  have hp4' : H3 <+: H4 := hp4
  have hl4 : (Enc.limbs (hi * tenE)).length < 2 ^ 60 := by
    have : (Enc.limbs (hi * tenE)).length ≤ 2 := (ConPanqueque.T.Big.limbs_length_lt_iff _ 2).mpr (by
      have : hi * tenE < natCap * tenE := Nat.mul_lt_mul_of_pos_right hhi (by decide)
      have : natCap * tenE < ConPanqueque.T.Big.B ^ 2 := by unfold natCap tenE; decide
      omega)
    omega
  refine ConPanqueque.T.Big.specR_callPH (C := ctxH C H4) (k := fun _ =>
      internE (.lit (.natVal (hi * tenE + lo))) >>= fun e => (pure { st with exprs := st.exprs.insert i e } : AM StateD))
    kS2 ConPanqueque.T.Big.fAdd ConPanqueque.T.Big.addParams [vv kP2, vv kY2] (ConPanqueque.T.Big.addBody C)
    [cellA C o4, cellA C o3] (hi * tenE + lo) (by decide) rfl (hD _ (by simp)) hcA
    ⟨by simp (config := {decide := true}) [sev, vv, Env.get_cons]; rfl,
     by simp (config := {decide := true}) [sev, vv, Env.get_cons]; rfl, trivial⟩
    (ConPanqueque.T.Big.add_spec (ctxH C H4) (ctxOK_H hok _) s (hi * tenE) lo o4 o3 hb4 (blkAt_mono hb3 hp4')
      (by have := len_le1 (w := lo) (by omega); have := len_ge1 hpos; omega) hl4)
    (fun H5 o5 hp5 hb5 => ?_)
  have hp5' : H4 <+: H5 := hp5
  refine ConPanqueque.T.Big.specR_callKH (C := ctxH C H5) fh ConPanqueque.T.Big.fLitB [ConPanqueque.T.Big.iLx]
    [vv kS2] (ConPanqueque.T.Big.litBlkBody C) [cellA C o5] (by decide) rfl (hD fh (by simp)) hcB
    ⟨by simp (config := {decide := true}) [sev, vv, Env.get_cons]; rfl, trivial⟩
    (ConPanqueque.T.Big.litBlk_spec ra (ctxH C H5) (ctxOK_H hok _) s _ o5 hb5) (fun a s' H6 hp6 => ?_)
  have hp6' : H5 <+: H6 := hp6
  have hpall : C.H <+: H6 := hp1.trans (hp2'.trans (hp3'.trans (hp4'.trans (hp5'.trans hp6'))))
  refine specR_weakenH (C := C) (H := H6) hpall ?_
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp (config := {decide := true}) [sev, vv, Env.get_cons, hTE]) i hic a
    (by simp (config := {decide := true}) [sev, vv, Env.get_cons, hI])
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)



/-- A `natVal` at or above the cap, of 19 to 36 digits in `[kQ, kN)`: split at 18 digits from the end. -/
def bigNatP (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local kD2 (.op .sub [vv kN, vv kQ]))
  (.ite (.cmp .lower (vv kD2) (.const 37))
   (.ite (.cmp .lower (.const 18) (vv kD2))
    (.seq (.assign .local kM2 (.op .sub [vv kN, .const 18]))
    (.seq (callTo kH2 fReadNat [vv kBA, vv kQ, vv kM2])
    (.seq (callTo kL2 fReadNat [vv kBA, vv kM2, vv kN])
    (.ite (.cmp .lower (vv kH2) (.const (BitVec.ofNat 64 natCap)))
     (.ite (.cmp .lower (vv kL2) (.const (BitVec.ofNat 64 natCap))) (capG fI (exBigP C)) hang) hang))))
    hang) hang)

theorem bw_lt {a b : Nat} (h : bw (a < b) ≠ 0) : a < b := by
  by_cases e : a < b
  · exact e
  · simp [bw, e] at h

theorem bigNat_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcR : C.code.lookup fReadNat = some ([(sB, .one), (sI, .one), (sE, .one)], rnFun, .one))
    (hcM : C.code.lookup ConPanqueque.T.Big.fMul = some (ConPanqueque.T.Big.mulParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.mulBody C, .one))
    (hcA : C.code.lookup ConPanqueque.T.Big.fAdd = some (ConPanqueque.T.Big.addParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.addBody C, .one))
    (hcB : C.code.lookup ConPanqueque.T.Big.fLitB =
      some ([(ConPanqueque.T.Big.iLx, .one)], ConPanqueque.T.Big.litBlkBody C, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [kD2, kM2, kH2, kL2, fx, fh, kX2, kT2, kY2, kP2, kS2], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (q c : Nat) (hqc : q ≤ c) (hcb : c ≤ b.size)
    (hd : DigitsIn b.data.toList q c) (n : Nat) (hn : n = readL b.data.toList q c 0) (hbig : natCap ≤ n) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hQ : Γ.get kQ = some (BitVec.ofNat 64 q)) (hN : Γ.get kN = some (BitVec.ofNat 64 c))
    (hBA : Γ.get kBA = some (cellA C bufJ)) :
    SpecR (Inv (σ := σ) C s Γ M D) (bigNatP C) s (parseExprEntryD st i (.natVal n)) (ExPost C jE cap st i) := by
  have hsmall := hbuf.small
  have hplat := hbuf.plat
  have hNB : natCap < 2 ^ 64 := by unfold natCap; decide
  unfold bigNatP
  refine specR_assignI kD2 _ (BitVec.ofNat 64 (c - q)) (hD _ (by simp))
    (by simp only [sev, vv, hN, hQ, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]) ?_
  let Γ1 : Env := (kD2, BitVec.ofNat 64 (c - q)) :: Γ
  refine specR_ifI _ _ (sev_lower Γ1 (vv kD2) (.const 37) (c - q) 37 (by simp [Γ1, sev, vv, Env.get_cons]) rfl
    (by omega) (by decide)) (fun h37 => ?_) (fun _ => specR_hangI)
  refine specR_ifI _ _ (sev_lower Γ1 (.const 18) (vv kD2) 18 (c - q) rfl (by simp [Γ1, sev, vv, Env.get_cons])
    (by decide) (by omega)) (fun h18 => ?_) (fun _ => specR_hangI)
  have hd37 := bw_lt h37
  have hd18 := bw_lt h18
  refine specR_assignI kM2 _ (BitVec.ofNat 64 (c - 18)) (hD _ (by simp))
    (by simp (config := {decide := true}) only [Γ1, sev, vv, Env.get_cons, hN, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, ite_false]
        rw [show (18 : BitVec 64) = BitVec.ofNat 64 18 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]) ?_
  let Γ2 : Env := (kM2, BitVec.ofNat 64 (c - 18)) :: Γ1
  have hrn : ∀ (q' c' : Nat), q' ≤ c' → c' ≤ c → q ≤ q' → ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)),
      ∀ (Δ : Env) (M' : Mem), Inv C s Δ M' D t → callee.lookup sB = some (.val (.word (cellA C bufJ))) →
      callee.lookup sI = some (.val (.word (BitVec.ofNat 64 q'))) →
      callee.lookup sE = some (.val (.word (BitVec.ofNat 64 c'))) →
      RetP (callEntryStateHOLFinite t callee) rnFun
        (fun w => w = BitVec.ofNat 64 (min (readL b.data.toList q' c' 0) natCap)) := by
    intro q' c' h1 h2 h3 t callee Δ M' ht c1 c2 c3
    have hb := bytesAt_congr (t := t)
      (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _))
      (u := callEntryStateHOLFinite t callee) rfl rfl rfl
    exact retP_of_retSpec (rnFun_spec _ (cellA C bufJ) b.data.toList q' c' hb h1 (by simp; omega)
      (fun k hk a1 a2 => hd k hk (by omega) (by omega)) c1 c3 c2) rfl
  refine specR_retP3 kH2 fReadNat sB sI sE rnFun (vv kBA) (vv kQ) (vv kM2) (cellA C bufJ)
    (BitVec.ofNat 64 q) (BitVec.ofNat 64 (c - 18)) _ (by decide) (by decide) (by decide) (hD _ (by simp)) hcR
    (by simp (config := {decide := true}) [Γ2, Γ1, sev, vv, Env.get_cons, hBA])
    (by simp (config := {decide := true}) [Γ2, Γ1, sev, vv, Env.get_cons, hQ])
    (by simp (config := {decide := true}) [Γ2, sev, vv, Env.get_cons])
    (fun t callee ht c1 c2 c3 => hrn q (c - 18) (by omega) (by omega) (Nat.le_refl _) t callee _ _ ht c1 c2 c3)
    (fun w1 hw1 => ?_)
  subst hw1
  let Γ3 : Env := (kH2, BitVec.ofNat 64 (min (readL b.data.toList q (c - 18) 0) natCap)) :: Γ2
  refine specR_retP3 kL2 fReadNat sB sI sE rnFun (vv kBA) (vv kM2) (vv kN) (cellA C bufJ)
    (BitVec.ofNat 64 (c - 18)) (BitVec.ofNat 64 c) _ (by decide) (by decide) (by decide) (hD _ (by simp)) hcR
    (by simp (config := {decide := true}) [Γ3, Γ2, Γ1, sev, vv, Env.get_cons, hBA])
    (by simp (config := {decide := true}) [Γ3, Γ2, sev, vv, Env.get_cons])
    (by simp (config := {decide := true}) [Γ3, Γ2, Γ1, sev, vv, Env.get_cons, hN])
    (fun t callee ht c1 c2 c3 => hrn (c - 18) c (by omega) (Nat.le_refl _) (by omega) t callee _ _ ht c1 c2 c3)
    (fun w2 hw2 => ?_)
  subst hw2
  let hi := readL b.data.toList q (c - 18) 0
  let lo := readL b.data.toList (c - 18) c 0
  let Γ4 : Env := (kL2, BitVec.ofNat 64 (min lo natCap)) :: Γ3
  refine specR_ifI _ _ (sev_lower Γ4 (vv kH2) (.const (BitVec.ofNat 64 natCap)) (min hi natCap) natCap
    (by simp (config := {decide := true}) [Γ4, Γ3, sev, vv, Env.get_cons]; rfl) rfl (by omega) hNB)
    (fun hH => ?_) (fun _ => specR_hangI)
  refine specR_ifI _ _ (sev_lower Γ4 (vv kL2) (.const (BitVec.ofNat 64 natCap)) (min lo natCap) natCap
    (by simp (config := {decide := true}) [Γ4, sev, vv, Env.get_cons]) rfl (by omega) hNB)
    (fun hL => ?_) (fun _ => specR_hangI)
  have hH' := bw_lt hH
  have hL' := bw_lt hL
  have ehi : min hi natCap = hi := by omega
  have elo : min lo natCap = lo := by omega
  have hsplit : n = hi * tenE + lo := by
    rw [hn, readL_split b.data.toList q (c - 18) c (by omega) (by omega) (by simp; omega),
      show c - (c - 18) = 18 by omega, tenE_eq]
  have g4 : ∀ y, y ∉ [kL2, kH2, kM2, kD2] → Γ4.get y = Γ.get y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Γ4, Γ3, Γ2, Γ1, Env.get_cons, ite_eq_right hy.1, ite_eq_right hy.2.1, ite_eq_right hy.2.2.1,
      ite_eq_right hy.2.2.2]
  refine specR_capG fI i (by rw [g4 _ (by decide)]; exact hI) (fun hiN hI' => ?_)
  have := natCap_lt
  rw [hsplit]
  exact exBig_spec ra C hok hcM hcA hcB s Γ4 M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)) st jE cap hrel hcap i hi lo
    (by omega) (by omega) (by omega) (by rw [← hsplit]; exact hbig)
    (by rw [g4 _ (by decide)]; exact hTE) (by rw [g4 _ (by decide)]; exact hC) hI'
    (by simp (config := {decide := true}) [Γ4, Γ3, Env.get_cons]; rw [ehi])
    (by simp (config := {decide := true}) [Γ4, Env.get_cons, elo])

end

end ConPanqueque.Front
