import ConPanqueque.Front.ExprLine
import ConPanqueque.Front.Name

/-! # Name lines: fields read again from the record

`num`: the prefix (guarded below the cap) and the capped number.  `str`: the prefix, and the
string's position; the string scanner is run again there and returns its closing quote, and only a
plain string (no escapes) gets through, whose bytes are the name's component. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ScanRes NameRec scanString)

variable {σ : Type}

/-- `ssFun_sound` with the body's start before its end. -/
theorem ssFun_sound2 (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi0 : i.toNat ≤ b.size) (hc : SkipPlainCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t ssFun (fun w => ∃ e : USize, w = BitVec.ofNat 64 e.toNat ∧ e.toNat < b.size ∧ i.toNat + 1 ≤ e.toNat ∧ ∃ s,
      ConLeche.Frontend.scanString b i = .ok s (e + 1) ∧ s.toUTF8 = b.extract (i + 1).toNat e.toNat) := by
  rcases ssFun_spec t A b.data.toList i.toNat hb (by simpa using hi0) hc lb (by simpa using ln) li with
    hs | ⟨w, r1, ⟨e, rfl, hi', he, hie, hq0, hqe, hpl⟩, r2⟩
  · exact Or.inl hs
  · have heU : (USize.ofNat e).toNat = e := by
      rw [USize.toNat_ofNat']
      simp only [USize.size_eq_two_pow, hp.bits]; apply Nat.mod_eq_of_lt; have := hp.size; simp at he; omega
    refine Or.inr ⟨_, r1, ⟨USize.ofNat e, by rw [heU], by rw [heU]; simpa using he, by rw [heU]; exact hie, ?_⟩, r2⟩
    have he' : (USize.ofNat e).toNat < b.size := by rw [heU]; simpa using he
    have hi : i.toNat < b.size := by simpa using hi'
    obtain ⟨s, h1, h2⟩ := scanString_plain hp i (USize.ofNat e) hi he' (by rw [heU]; omega)
      (by rw [List.getElem?_eq_getElem (by simpa using hi)] at hq0; exact Option.some.inj hq0)
      (by rw [List.getElem?_eq_getElem he] at hqe
          simp only [heU]; exact Option.some.inj hqe)
      (fun k hk h1 h2 => hpl k hk h1 (by rw [heU] at h2; exact h2))
    exact ⟨s, h1, h2⟩

def numInits : List (BitVec 64) := [0, 0]
def fNumF (k : Nat) : MlS := ofString ("numf" ++ toString k)

/-- A `num` name line: prefix (slot 1) to `fU`, number (slot 0) to `fV2`. -/
def numLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fU (fNumF 1) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fV2 (fNumF 0) [vv kBA, vv kBN, vv kPos])
      (capG fI (capG fU (nmNumP C))))

theorem numLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup fInternNNum = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lNw, .one)], nameNumBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fNumF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanNumNameSpec numInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fU, fV2, fx, fy, fh, kKA0, kL1], x ∈ D)
    (st : StateD) (jN cap : Nat) (hrel : TblRel C.H jN cap st.names) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : NameRec) (hr : ConLeche.Frontend.scanNumName b pos = .ok r e) (i : Nat)
    (hTN : Γ.get fTN = some (cellA C jN)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (numLineP C) s (parseNameEntryD st i r) (NmPost C jN cap st i) := by
  have hS := fun k hk => slotCall (s := s) (D := D) hok hbuf hsc pos _ _ (fun u hb hc l1 l2 l3 =>
    numNameSlot_sound u (cellA C bufJ) b hbuf.plat hb hc pos hpos l1 l2 l3 k hk r e hr)
  unfold numLineP
  refine specR_fieldI fU (fNumF 1) _ bufJ b pos _ (hD _ (by simp)) (hcT 1 (by decide)) hBA hBN hP (hS 1 (by decide))
    (fun w1 ⟨s1, hK1, hr1, hs1⟩ => ?_)
  have hn1 := slotN hK1 rfl hs1
  have g1 : ∀ y, y ≠ fU → Env.get ((fU, w1) :: Γ) y = Γ.get y := fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_fieldI fV2 (fNumF 0) _ bufJ b pos _ (hD _ (by simp)) (hcT 0 (by decide))
    (by rw [g1 _ (by decide)]; exact hBA) (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP)
    (hS 0 (by decide)) (fun w2 ⟨s2, hK2, hr2, hs2⟩ => ?_)
  have hn2 := slotN hK2 rfl hs2
  have q1 := hr1.symm.trans hr2
  simp only [NameRec.num.injEq] at q1
  rw [q1.1] at hn1
  rw [hr2]
  let Γ2 : Env := (fV2, w2) :: (fU, w1) :: Γ
  have g2 : ∀ y, y ≠ fV2 → y ≠ fU → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h, if_neg h']
  refine specR_capG fI i (by rw [g2 _ (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  refine specR_capG fU _ (by simp only [Γ2, Env.get_cons, if_neg (show fU ≠ fV2 by decide), if_pos]; rw [hn1])
    (fun haN hU' => ?_)
  have := natCap_lt
  exact nmNum_spec ra C hok hf hcN s Γ2 M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp))
    st jN cap hrel hcap i _ _ (by omega) (by omega)
    (by rw [g2 _ (by decide) (by decide)]; exact hTN) (by rw [g2 _ (by decide) (by decide)]; exact hC) hI' hU'
    (by simp only [Γ2, Env.get_cons, if_pos]; rw [hn2])

def strInits : List (BitVec 64) := [0, BitVec.ofNat 64 listSentinel]
def fStrF (k : Nat) : MlS := ofString ("strf" ++ toString k)
/-- The string's closing quote. -/
def kSE := ofString "kse"

/-- A `str` name line: prefix (slot 0) to `fU`, the string's position (slot 1) to `kQ`; the string
scanner gives its closing quote, then `kQ`/`kN` are its body's start and length. -/
def strLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fU (fStrF 0) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo kQ (fStrF 1) [vv kBA, vv kBN, vv kPos])
      (.ite (.cmp .equal (vv kQ) (.const (BitVec.ofNat 64 listSentinel))) hang
        (.seq (callTo kSE fStr [vv kBA, vv kBN, vv kQ])
          (.seq (.assign .local kQ (.op .add [vv kQ, .const 1]))
            (.seq (.assign .local kN (.op .sub [vv kSE, vv kQ]))
              (capG fI (capG fU (nmStrP C))))))))

theorem extract_toList (b : ByteArray) (a e : Nat) :
    (b.extract a e).data.toList = (b.data.toList.drop a).take (e - a) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

theorem strLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcS : C.code.lookup fStr = some ([(sB, .one), (sN, .one), (sI, .one)], ssFun, .one))
    (hcT : ∀ k, k < 2 → C.code.lookup (fStrF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanStrNameSpec strInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fU, kQ, kSE, kN, fx, fy, fh, kKA0, kKA, kK, kC, kS, kW, kJ, kL1], x ∈ D)
    (st : StateD) (jN cap : Nat) (hrel : TblRel C.H jN cap st.names) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : NameRec) (hr : ConLeche.Frontend.scanStrName b pos = .ok r e) (i : Nat)
    (hTN : Γ.get fTN = some (cellA C jN)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (strLineP C) s (parseNameEntryD st i r) (NmPost C jN cap st i) := by
  have hplat := hbuf.plat
  have hsmall := hbuf.small
  have hS := fun k hk => slotCall (s := s) (D := D) hok hbuf hsc pos _ _ (fun u hb hc l1 l2 l3 =>
    strNameSlot_sound u (cellA C bufJ) b hbuf.plat hb hc pos hpos l1 l2 l3 k hk r e hr)
  unfold strLineP
  refine specR_fieldI fU (fStrF 0) _ bufJ b pos _ (hD _ (by simp)) (hcT 0 (by decide)) hBA hBN hP (hS 0 (by decide))
    (fun w1 ⟨s1, hK1, hr1, hs1⟩ => ?_)
  have hn1 := slotN hK1 rfl hs1
  have g1 : ∀ y, y ≠ fU → Env.get ((fU, w1) :: Γ) y = Γ.get y := fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_fieldI kQ (fStrF 1) _ bufJ b pos _ (hD _ (by simp)) (hcT 1 (by decide))
    (by rw [g1 _ (by decide)]; exact hBA) (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP)
    (hS 1 (by decide)) (fun w2 ⟨s2, hK2, hr2, hs2⟩ => ?_)
  have hst := slotS hK2 rfl hs2
  have q1 := hr1.symm.trans hr2
  simp only [NameRec.str.injEq] at q1
  rw [q1.1] at hn1
  rw [hr2]
  let Γ2 : Env := (kQ, w2) :: (fU, w1) :: Γ
  have g2 : ∀ y, y ≠ kQ → y ≠ fU → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h, if_neg h']
  refine specR_ifI _ _ (sev_eq_c' Γ2 kQ w2 (BitVec.ofNat 64 listSentinel) (by simp only [Γ2, Env.get_cons, if_pos]))
    (fun _ => specR_hangI) (fun hw => ?_)
  have hw' : w2 ≠ BitVec.ofNat 64 listSentinel := by intro h; simp [bw, h] at hw
  obtain ⟨p, e0, hwp, hsc0⟩ := hst.resolve_right (fun ⟨_, h⟩ => hw' h)
  have hpb : p.toNat < b.size := scanString_lt hplat hsc0
  refine specR_retP3 kSE fStr sB sN sI ssFun (vv kBA) (vv kBN) (vv kQ) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 p.toNat) _ (by decide) (by decide) (by decide) (hD _ (by simp)) hcS
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hBA)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hBN)
    (by simp only [sev, vv, Γ2, Env.get_cons, if_pos]; rw [hwp])
    (fun t callee ht c1 c2 c3 => slotCall (s := s) (D := D) hok hbuf hsc p ssFun _ (fun u hb hc l1 l2 l3 =>
      ssFun_sound2 u (cellA C bufJ) b hplat hb p (Nat.le_of_lt hpb) hc.2.2.2.1 l1 l2 l3) t callee _ _ ht c1 c2 c3)
    (fun w3 ⟨ee, hw3, hee, hpe, s', hs', hutf⟩ => ?_)
  have hstr : (s2.getD 1 default).str = s' := scanString_det hsc0 hs'
  let Γ3 : Env := (kSE, w3) :: Γ2
  have g3 : ∀ y, y ≠ kSE → y ≠ kQ → y ≠ fU → Γ3.get y = Γ.get y := fun y h0 h h' => by
    simp only [Γ3, Env.get_cons, if_neg h0]; exact g2 y h h'
  refine specR_assignI kQ _ (BitVec.ofNat 64 (p.toNat + 1)) (hD _ (by simp))
    (by simp only [sev, vv, Γ3, Γ2, Env.get_cons, if_neg (show kQ ≠ kSE by decide), if_pos, hwp]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add64]) ?_
  let Γ4 : Env := (kQ, BitVec.ofNat 64 (p.toNat + 1)) :: Γ3
  refine specR_assignI kN _ (BitVec.ofNat 64 (ee.toNat - (p.toNat + 1))) (hD _ (by simp))
    (by simp only [sev, vv, Γ4, Γ3, Env.get_cons, if_neg (show kSE ≠ kQ by decide), if_pos, hw3]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]) ?_
  let Γ5 : Env := (kN, BitVec.ofNat 64 (ee.toNat - (p.toNat + 1))) :: Γ4
  have g5 : ∀ y, y ≠ kN → y ≠ kQ → y ≠ kSE → y ≠ fU → Γ5.get y = Γ.get y := fun y hn hq hs hu => by
    simp only [Γ5, Γ4, Env.get_cons, if_neg hn, if_neg hq]; exact g3 y hs hq hu
  refine specR_capG fI i (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  refine specR_capG fU _ (by simp only [Γ5, Γ4, Γ3, Γ2, Env.get_cons, if_neg (show fU ≠ kN by decide),
    if_neg (show fU ≠ kQ by decide), if_neg (show fU ≠ kSE by decide), if_pos]; rw [hn1]) (fun haN hU' => ?_)
  have := natCap_lt
  have hp1 : (p + 1).toNat = p.toNat + 1 := ConLeche.Frontend.usizeStep b p ((hplat.lt_iff p).mpr hpb)
  refine nmStr_spec ra C hok hf hcN s _ M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    st jN cap hrel hcap bufJ (p.toNat + 1) (ee.toNat - (p.toNat + 1)) b.data.toList hbuf.pk
    (by simp; omega) (by simpa using hsmall) (by simpa using hbuf.len) i _ (s2.getD 1 default).str
    (by omega) (by omega) ?_
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hC) hI' hU'
    (by simp only [Γ5, Γ4, Env.get_cons, if_neg (show kQ ≠ kN by decide), if_pos])
    (by simp only [Γ5, Env.get_cons, if_pos])
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
  rw [hstr]
  show s'.toUTF8.data.toList = _
  rw [hutf, extract_toList, hp1]

end ConPanqueque.Front
