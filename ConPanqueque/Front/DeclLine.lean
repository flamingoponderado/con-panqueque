import ConPanqueque.Front.Decl
import ConPanqueque.Scan.DeclFields

/-! # Declaration lines: fields read again from the record, then the record procedure

A declaration line's payload slot holds the record's position.  Each field is one call of the
record function returning that slot (`Scan/DeclFields.lean`); the slot kinds turn the returned word
into the field the declaration's builder reads. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ScanRes scanNatList scanString scanHints HintsRec DeclRec CVRec)

variable {σ : Type}

theorem slot_get {ks : List Nat} {s : List SVal} {k kd : Nat} (hK : KindsOK ks s) (hk : ks[k]? = some kd) :
    ∃ hl : k < s.length, s[k].kind = kd := by
  have hl : k < s.length := by
    rw [hK.1]
    by_cases h : k < ks.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hk; cases hk
  refine ⟨hl, ?_⟩
  have := hK.2 k hl
  rw [hk] at this
  exact (Option.some.inj this).symm

theorem getD_slot {s : List SVal} {k : Nat} (hl : k < s.length) : s.getD k default = s[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl

theorem slotN {b : ByteArray} {w : BitVec 64} {ks : List Nat} {s : List SVal} {k : Nat} (hK : KindsOK ks s)
    (hk : ks[k]? = some 0) (h : ∀ hk' : k < s.length, SlotOK b w s[k]) :
    w = BitVec.ofNat 64 (min (s.getD k default).nat natCap) := by
  obtain ⟨hl, hkd⟩ := slot_get hK hk
  have h' := h hl
  rw [getD_slot hl]
  cases hs : s[k] <;> rw [hs] at hkd h' <;> simp [SVal.kind] at hkd
  exact h'

theorem slotL {b : ByteArray} {w : BitVec 64} {ks : List Nat} {s : List SVal} {k : Nat} (hK : KindsOK ks s)
    (hk : ks[k]? = some 1) (h : ∀ hk' : k < s.length, SlotOK b w s[k]) :
    (∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanNatList b p = .ok (s.getD k default).list e) ∨
      ((s.getD k default).list = [] ∧ w = BitVec.ofNat 64 listSentinel) := by
  obtain ⟨hl, hkd⟩ := slot_get hK hk
  have h' := h hl
  rw [getD_slot hl]
  cases hs : s[k] <;> rw [hs] at hkd h' <;> simp [SVal.kind] at hkd
  exact h'

theorem slotS {b : ByteArray} {w : BitVec 64} {ks : List Nat} {s : List SVal} {k : Nat} (hK : KindsOK ks s)
    (hk : ks[k]? = some 2) (h : ∀ hk' : k < s.length, SlotOK b w s[k]) :
    (∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanString b p = .ok (s.getD k default).str e) ∨
      ((s.getD k default).str = "" ∧ w = BitVec.ofNat 64 listSentinel) := by
  obtain ⟨hl, hkd⟩ := slot_get hK hk
  have h' := h hl
  rw [getD_slot hl]
  cases hs : s[k] <;> rw [hs] at hkd h' <;> simp [SVal.kind] at hkd
  exact h'

theorem slotB {b : ByteArray} {w : BitVec 64} {ks : List Nat} {s : List SVal} {k : Nat} (hK : KindsOK ks s)
    (hk : ks[k]? = some 3) (h : ∀ hk' : k < s.length, SlotOK b w s[k]) :
    w = bw ((s.getD k default).bool = true) := by
  obtain ⟨hl, hkd⟩ := slot_get hK hk
  have h' := h hl
  rw [getD_slot hl]
  cases hs : s[k] <;> rw [hs] at hkd h' <;> simp [SVal.kind] at hkd
  exact h'

theorem slotH {b : ByteArray} {w : BitVec 64} {ks : List Nat} {s : List SVal} {k : Nat} (hK : KindsOK ks s)
    (hk : ks[k]? = some 4) (h : ∀ hk' : k < s.length, SlotOK b w s[k]) :
    (∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanHints b p = .ok (s.getD k default).hint e) ∨
      ((s.getD k default).hint = .regular 0 ∧ w = BitVec.ofNat 64 listSentinel) := by
  obtain ⟨hl, hkd⟩ := slot_get hK hk
  have h' := h hl
  rw [getD_slot hl]
  cases hs : s[k] <;> rw [hs] at hkd h' <;> simp [SVal.kind] at hkd
  exact h'

/-- The record's position in the buffer. -/
def kPos := ofString "kpos"

def thmInits : List (BitVec 64) := [BitVec.ofNat 64 listSentinel, 0, 0, 0]
def fThmF (k : Nat) : MlS := ofString ("thmf" ++ toString k)

/-- A theorem line: its four fields, then the record. -/
def thLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fV2 (fThmF 0) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fU (fThmF 1) [vv kBA, vv kBN, vv kPos])
      (.seq (callTo fW3 (fThmF 2) [vv kBA, vv kBN, vv kPos])
        (.seq (callTo kVl (fThmF 3) [vv kBA, vv kBN, vv kPos]) (vdP C 2))))

theorem thLine_spec (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcT : ∀ k, k < 4 → C.code.lookup (fThmF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanThmDeclSpec thmInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fV2, fU, fW3, kVl, fy, fz, kVh, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (pos e : USize) (hpos : pos.toNat ≤ b.size) (d : DeclRec) (hd : ConLeche.Frontend.scanThmDecl b pos = .ok d e)
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (thLineP C) s (processLineCoreD st d)
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hplat := hbuf.plat
  have hbt : ∀ (t : PState σ) (Δ : Env) (M' : Mem), Inv C s Δ M' D t → BytesAt t (cellA C bufJ) b.data.toList :=
    fun t Δ M' ht => bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)
  have call : ∀ (Δ : Env) (x : MlS) (k : Nat) (hk : k < 4) (rest : ProgHOL 64)
      {R : StateD ⊕ RecordVerdict → BitVec 64 → AState → PState σ → Prop}, x ∈ D →
      Δ.get kBA = some (cellA C bufJ) → Δ.get kBN = some (BitVec.ofNat 64 b.size) →
      Δ.get kPos = some (BitVec.ofNat 64 pos.toNat) →
      (∀ w (sl : List SVal), KindsOK [1, 0, 0, 0] sl → d = DeclRec.thm ⟨(sl.getD 1 default).nat,
          (sl.getD 0 default).list, (sl.getD 2 default).nat⟩ (sl.getD 3 default).nat →
        (∀ hk' : k < sl.length, SlotOK b w sl[k]) →
        SpecR (Inv C s ((x, w) :: Δ) M D) rest s (processLineCoreD st d) R) →
      SpecR (Inv C s Δ M D) (.seq (callTo x (fThmF k) [vv kBA, vv kBN, vv kPos]) rest) s (processLineCoreD st d) R :=
    fun Δ x k hk rest R hx h1 h2 h3 hk2 =>
      specR_retP3 x (fThmF k) sB sN sI _ (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
        (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) hx (hcT k hk)
        (by simpa [sev, vv] using h1) (by simpa [sev, vv] using h2) (by simpa [sev, vv] using h3)
        (fun t callee ht c1 c2 c3 => thmSlot_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hplat
          (bytesAt_congr (t := t) (hbt t _ _ ht) rfl rfl rfl) (hsc _ (by show t.code = C.code; exact ht.sr.code))
          pos hpos c1 c2 c3 k hk d e hd)
        (fun w ⟨sl, hK, hdl, hsl⟩ => hk2 w sl hK hdl hsl)
  unfold thLineP
  refine call Γ fV2 0 (by decide) _ (hD _ (by simp)) hBA hBN hP (fun w0 s0 hK0 hd0 hs0 => ?_)
  subst hd0
  have hl0 := slotL hK0 rfl hs0
  let Γ1 : Env := (fV2, w0) :: Γ
  have g1 : ∀ y, y ≠ fV2 → Γ1.get y = Γ.get y := fun y h => by simp only [Γ1, Env.get_cons, if_neg h]
  refine call Γ1 fU 1 (by decide) _ (hD _ (by simp)) (by rw [g1 _ (by decide)]; exact hBA)
    (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP) (fun w1 s1 hK1 hd1 hs1 => ?_)
  have hn1 := slotN hK1 rfl hs1
  let Γ2 : Env := (fU, w1) :: Γ1
  have g2 : ∀ y, y ≠ fU → y ≠ fV2 → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h]; exact g1 y h'
  refine call Γ2 fW3 2 (by decide) _ (hD _ (by simp)) (by rw [g2 _ (by decide) (by decide)]; exact hBA)
    (by rw [g2 _ (by decide) (by decide)]; exact hBN) (by rw [g2 _ (by decide) (by decide)]; exact hP)
    (fun w2 s2 hK2 hd2 hs2 => ?_)
  have hn2 := slotN hK2 rfl hs2
  let Γ3 : Env := (fW3, w2) :: Γ2
  have g3 : ∀ y, y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ3.get y = Γ.get y := fun y h h1 h2 => by
    simp only [Γ3, Env.get_cons, if_neg h]; exact g2 y h1 h2
  refine call Γ3 kVl 3 (by decide) _ (hD _ (by simp)) (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hP) (fun w3 s3 hK3 hd3 hs3 => ?_)
  have hn3 := slotN hK3 rfl hs3
  simp only [DeclRec.thm.injEq, CVRec.mk.injEq] at hd1 hd2 hd3
  rw [← hd1.1.1] at hn1
  rw [← hd2.1.2.2] at hn2
  rw [← hd3.2] at hn3
  let Γ4 : Env := (kVl, w3) :: Γ3
  have g4 : ∀ y, y ≠ kVl → y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ4.get y = Γ.get y := fun y h h1 h2 h3 => by
    simp only [Γ4, Env.get_cons, if_neg h]; exact g3 y h1 h2 h3
  have hus : (s0.getD 0 default).list.length < 2 ^ 59 := by
    have := hbuf.small
    rcases hl0 with ⟨p, e', -, hsc'⟩ | ⟨h0, -⟩
    · have := scanNatList_len hsc'; omega
    · rw [h0]; simp
  refine vdP_spec C hok hnc hcN s Γ4 M D (fun x hx => hD x (by
      rcases List.mem_append.mp hx with h | h
      · refine List.mem_append_left _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp
      · exact List.mem_append_right _ h))
    st F rb capD jN jL jE cap bufJ b hlay hreln hrele hcap hcapN hbuf hdr hcapD
    ⟨(s0.getD 1 default).nat, (s0.getD 0 default).list, (s0.getD 2 default).nat⟩ (s0.getD 3 default).nat hus w0 hl0
    2 (fun cvh vlh => .thmDecl cvh vlh) (fun cvh vlh H r hr h0 h1 h4 => thmEnc C F cvh vlh H r hr h0 h1 h4)
    (fun nmh tyh vlh h1 h2 h3 hall => processThm_ok st _ _ nmh tyh vlh h1 h2 h3 hall)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hTE)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hC)
    (by simp only [Γ4, Γ3, Γ2, Env.get_cons, if_neg (show fU ≠ kVl by decide), if_neg (show fU ≠ fW3 by decide), if_pos]
        rw [hn1])
    (by simp only [Γ4, Γ3, Env.get_cons, if_neg (show fW3 ≠ kVl by decide), if_pos]; rw [hn2])
    (by simp only [Γ4, Env.get_cons, if_pos]; rw [hn3])
    (by simp only [Γ4, Γ3, Γ2, Γ1, Env.get_cons, if_neg (show fV2 ≠ kVl by decide), if_neg (show fV2 ≠ fW3 by decide),
          if_neg (show fV2 ≠ fU by decide), if_pos])
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hCD)

def opqInits : List (BitVec 64) := [0, BitVec.ofNat 64 listSentinel, 0, 0, 0]
def fOpqF (k : Nat) : MlS := ofString ("opqf" ++ toString k)

/-- An opaque line: its five fields, then the record (an unsafe one hangs). -/
def opLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fV2 (fOpqF 1) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fU (fOpqF 2) [vv kBA, vv kBN, vv kPos])
      (.seq (callTo fW3 (fOpqF 3) [vv kBA, vv kBN, vv kPos])
        (.seq (callTo kVl (fOpqF 4) [vv kBA, vv kBN, vv kPos])
          (.seq (callTo kUs (fOpqF 0) [vv kBA, vv kBN, vv kPos]) (opP C)))))

theorem opLine_spec (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcT : ∀ k, k < 5 → C.code.lookup (fOpqF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanOpaqueDeclSpec opqInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [kUs, fV2, fU, fW3, kVl, fy, fz, kVh, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (pos e : USize) (hpos : pos.toNat ≤ b.size) (d : DeclRec) (hd : ConLeche.Frontend.scanOpaqueDecl b pos = .ok d e)
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (opLineP C) s (processLineCoreD st d)
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hplat := hbuf.plat
  have hbt : ∀ (t : PState σ) (Δ : Env) (M' : Mem), Inv C s Δ M' D t → BytesAt t (cellA C bufJ) b.data.toList :=
    fun t Δ M' ht => bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)
  have call : ∀ (Δ : Env) (x : MlS) (k : Nat) (hk : k < 5) (rest : ProgHOL 64)
      {R : StateD ⊕ RecordVerdict → BitVec 64 → AState → PState σ → Prop}, x ∈ D →
      Δ.get kBA = some (cellA C bufJ) → Δ.get kBN = some (BitVec.ofNat 64 b.size) →
      Δ.get kPos = some (BitVec.ofNat 64 pos.toNat) →
      (∀ w (sl : List SVal), KindsOK [3, 1, 0, 0, 0] sl → d = DeclRec.opaq ⟨(sl.getD 2 default).nat,
          (sl.getD 1 default).list, (sl.getD 3 default).nat⟩ (sl.getD 4 default).nat (sl.getD 0 default).bool →
        (∀ hk' : k < sl.length, SlotOK b w sl[k]) →
        SpecR (Inv C s ((x, w) :: Δ) M D) rest s (processLineCoreD st d) R) →
      SpecR (Inv C s Δ M D) (.seq (callTo x (fOpqF k) [vv kBA, vv kBN, vv kPos]) rest) s (processLineCoreD st d) R :=
    fun Δ x k hk rest R hx h1 h2 h3 hk2 =>
      specR_retP3 x (fOpqF k) sB sN sI _ (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
        (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) hx (hcT k hk)
        (by simpa [sev, vv] using h1) (by simpa [sev, vv] using h2) (by simpa [sev, vv] using h3)
        (fun t callee ht c1 c2 c3 => opaqueSlot_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hplat
          (bytesAt_congr (t := t) (hbt t _ _ ht) rfl rfl rfl) (hsc _ (by show t.code = C.code; exact ht.sr.code))
          pos hpos c1 c2 c3 k hk d e hd)
        (fun w ⟨sl, hK, hdl, hsl⟩ => hk2 w sl hK hdl hsl)
  unfold opLineP
  refine call Γ fV2 1 (by decide) _ (hD _ (by simp)) hBA hBN hP (fun w0 s0 hK0 hd0 hs0 => ?_)
  subst hd0
  have hl0 := slotL hK0 rfl hs0
  let Γ1 : Env := (fV2, w0) :: Γ
  have g1 : ∀ y, y ≠ fV2 → Γ1.get y = Γ.get y := fun y h => by simp only [Γ1, Env.get_cons, if_neg h]
  refine call Γ1 fU 2 (by decide) _ (hD _ (by simp)) (by rw [g1 _ (by decide)]; exact hBA)
    (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP) (fun w1 s1 hK1 hd1 hs1 => ?_)
  have hn1 := slotN hK1 rfl hs1
  let Γ2 : Env := (fU, w1) :: Γ1
  have g2 : ∀ y, y ≠ fU → y ≠ fV2 → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h]; exact g1 y h'
  refine call Γ2 fW3 3 (by decide) _ (hD _ (by simp)) (by rw [g2 _ (by decide) (by decide)]; exact hBA)
    (by rw [g2 _ (by decide) (by decide)]; exact hBN) (by rw [g2 _ (by decide) (by decide)]; exact hP)
    (fun w2 s2 hK2 hd2 hs2 => ?_)
  have hn2 := slotN hK2 rfl hs2
  let Γ3 : Env := (fW3, w2) :: Γ2
  have g3 : ∀ y, y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ3.get y = Γ.get y := fun y h h1 h2 => by
    simp only [Γ3, Env.get_cons, if_neg h]; exact g2 y h1 h2
  refine call Γ3 kVl 4 (by decide) _ (hD _ (by simp)) (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hP) (fun w3 s3 hK3 hd3 hs3 => ?_)
  have hn3 := slotN hK3 rfl hs3
  let Γ4 : Env := (kVl, w3) :: Γ3
  have g4 : ∀ y, y ≠ kVl → y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ4.get y = Γ.get y := fun y h h1 h2 h3 => by
    simp only [Γ4, Env.get_cons, if_neg h]; exact g3 y h1 h2 h3
  refine call Γ4 kUs 0 (by decide) _ (hD _ (by simp))
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hP) (fun w4 s4 hK4 hd4 hs4 => ?_)
  have hb4 := slotB hK4 rfl hs4
  simp only [DeclRec.opaq.injEq, CVRec.mk.injEq] at hd1 hd2 hd3 hd4
  rw [← hd1.1.1] at hn1
  rw [← hd2.1.2.2] at hn2
  rw [← hd3.2.1] at hn3
  rw [← hd4.2.2] at hb4
  let Γ5 : Env := (kUs, w4) :: Γ4
  have g5 : ∀ y, y ≠ kUs → y ≠ kVl → y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ5.get y = Γ.get y := fun y h0 h h1 h2 h3 => by
    simp only [Γ5, Env.get_cons, if_neg h0]; exact g4 y h h1 h2 h3
  refine opP_ifun C s Γ5 M D w4 (by simp only [Γ5, Env.get_cons, if_pos]) (fun hz => ?_)
  have hsafe : (s0.getD 0 default).bool = false := by
    cases hbv : (s0.getD 0 default).bool
    · rfl
    · rw [hbv] at hb4; simp [bw] at hb4; rw [hb4] at hz; cases hz
  rw [hsafe]
  have hus : (s0.getD 1 default).list.length < 2 ^ 59 := by
    have := hbuf.small
    rcases hl0 with ⟨p, e', -, hsc'⟩ | ⟨h0, -⟩
    · have := scanNatList_len hsc'; omega
    · rw [h0]; simp
  refine vdP_spec C hok hnc hcN s Γ5 M D (fun x hx => hD x (by
      rcases List.mem_append.mp hx with h | h
      · refine List.mem_append_left _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp
      · exact List.mem_append_right _ h))
    st F rb capD jN jL jE cap bufJ b hlay hreln hrele hcap hcapN hbuf hdr hcapD
    ⟨(s0.getD 2 default).nat, (s0.getD 1 default).list, (s0.getD 3 default).nat⟩ (s0.getD 4 default).nat hus w0 hl0
    3 (fun cvh vlh => .opaqueDecl cvh vlh) (fun cvh vlh H r hr h0 h1 h4 => opaqEnc C F cvh vlh H r hr h0 h1 h4)
    (fun nmh tyh vlh h1 h2 h3 hall => processOpaque_ok st _ _ nmh tyh vlh h1 h2 h3 hall)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTE)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC)
    (by simp only [Γ5, Γ4, Γ3, Γ2, Env.get_cons, if_neg (show fU ≠ kUs by decide), if_neg (show fU ≠ kVl by decide),
          if_neg (show fU ≠ fW3 by decide), if_pos]
        rw [hn1])
    (by simp only [Γ5, Γ4, Γ3, Env.get_cons, if_neg (show fW3 ≠ kUs by decide), if_neg (show fW3 ≠ kVl by decide),
          if_pos]; rw [hn2])
    (by simp only [Γ5, Γ4, Env.get_cons, if_neg (show kVl ≠ kUs by decide), if_pos]; rw [hn3])
    (by simp only [Γ5, Γ4, Γ3, Γ2, Γ1, Env.get_cons, if_neg (show fV2 ≠ kUs by decide),
          if_neg (show fV2 ≠ kVl by decide), if_neg (show fV2 ≠ fW3 by decide), if_neg (show fV2 ≠ fU by decide), if_pos])
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hCD)

def defInits : List (BitVec 64) :=
  [BitVec.ofNat 64 listSentinel, BitVec.ofNat 64 listSentinel, 0, BitVec.ofNat 64 listSentinel, 0, 0]
def fDefF (k : Nat) : MlS := ofString ("deff" ++ toString k)

/-- A definition line: its six fields, then the record. -/
def dfLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fV2 (fDefF 1) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fU (fDefF 2) [vv kBA, vv kBN, vv kPos])
      (.seq (callTo fW3 (fDefF 4) [vv kBA, vv kBN, vv kPos])
        (.seq (callTo kVl (fDefF 5) [vv kBA, vv kBN, vv kPos])
          (.seq (callTo kHn (fDefF 0) [vv kBA, vv kBN, vv kPos])
            (.seq (callTo kSf (fDefF 3) [vv kBA, vv kBN, vv kPos]) (dfP C))))))

theorem dfLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcS : C.code.lookup fSafe = some ([(sB, .one), (sN, .one), (sI, .one)], sfFun, .one))
    (hcH : C.code.lookup fHintV = some ([(sB, .one), (sN, .one), (sI, .one)], hvFun, .one))
    (hhc : ∀ t : PState σ, t.code = C.code → HvCodes t)
    (hcT : ∀ k, k < 6 → C.code.lookup (fDefF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanDefDeclSpec defInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [kHn, kSf, fV2, fU, fW3, kVl, fy, fz, kVh, kT, kHv, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (pos e : USize) (hpos : pos.toNat ≤ b.size) (d : DeclRec) (hd : ConLeche.Frontend.scanDefDecl b pos = .ok d e)
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (dfLineP C) s (processLineCoreD st d)
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hplat := hbuf.plat
  have hbt : ∀ (t : PState σ) (Δ : Env) (M' : Mem), Inv C s Δ M' D t → BytesAt t (cellA C bufJ) b.data.toList :=
    fun t Δ M' ht => bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)
  have call : ∀ (Δ : Env) (x : MlS) (k : Nat) (hk : k < 6) (rest : ProgHOL 64)
      {R : StateD ⊕ RecordVerdict → BitVec 64 → AState → PState σ → Prop}, x ∈ D →
      Δ.get kBA = some (cellA C bufJ) → Δ.get kBN = some (BitVec.ofNat 64 b.size) →
      Δ.get kPos = some (BitVec.ofNat 64 pos.toNat) →
      (∀ w (sl : List SVal), KindsOK [4, 1, 0, 2, 0, 0] sl → d = DeclRec.defn ⟨(sl.getD 2 default).nat,
          (sl.getD 1 default).list, (sl.getD 4 default).nat⟩ (sl.getD 5 default).nat (sl.getD 0 default).hint
          (sl.getD 3 default).str →
        (∀ hk' : k < sl.length, SlotOK b w sl[k]) →
        SpecR (Inv C s ((x, w) :: Δ) M D) rest s (processLineCoreD st d) R) →
      SpecR (Inv C s Δ M D) (.seq (callTo x (fDefF k) [vv kBA, vv kBN, vv kPos]) rest) s (processLineCoreD st d) R :=
    fun Δ x k hk rest R hx h1 h2 h3 hk2 =>
      specR_retP3 x (fDefF k) sB sN sI _ (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
        (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) hx (hcT k hk)
        (by simpa [sev, vv] using h1) (by simpa [sev, vv] using h2) (by simpa [sev, vv] using h3)
        (fun t callee ht c1 c2 c3 => defSlot_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hplat
          (bytesAt_congr (t := t) (hbt t _ _ ht) rfl rfl rfl) (hsc _ (by show t.code = C.code; exact ht.sr.code))
          pos hpos c1 c2 c3 k hk d e hd)
        (fun w ⟨sl, hK, hdl, hsl⟩ => hk2 w sl hK hdl hsl)
  unfold dfLineP
  refine call Γ fV2 1 (by decide) _ (hD _ (by simp)) hBA hBN hP (fun w0 s0 hK0 hd0 hs0 => ?_)
  subst hd0
  have hl0 := slotL hK0 rfl hs0
  let Γ1 : Env := (fV2, w0) :: Γ
  have g1 : ∀ y, y ≠ fV2 → Γ1.get y = Γ.get y := fun y h => by simp only [Γ1, Env.get_cons, if_neg h]
  refine call Γ1 fU 2 (by decide) _ (hD _ (by simp)) (by rw [g1 _ (by decide)]; exact hBA)
    (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP) (fun w1 s1 hK1 hd1 hs1 => ?_)
  have hn1 := slotN hK1 rfl hs1
  let Γ2 : Env := (fU, w1) :: Γ1
  have g2 : ∀ y, y ≠ fU → y ≠ fV2 → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h]; exact g1 y h'
  refine call Γ2 fW3 4 (by decide) _ (hD _ (by simp)) (by rw [g2 _ (by decide) (by decide)]; exact hBA)
    (by rw [g2 _ (by decide) (by decide)]; exact hBN) (by rw [g2 _ (by decide) (by decide)]; exact hP)
    (fun w2 s2 hK2 hd2 hs2 => ?_)
  have hn2 := slotN hK2 rfl hs2
  let Γ3 : Env := (fW3, w2) :: Γ2
  have g3 : ∀ y, y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ3.get y = Γ.get y := fun y h h1 h2 => by
    simp only [Γ3, Env.get_cons, if_neg h]; exact g2 y h1 h2
  refine call Γ3 kVl 5 (by decide) _ (hD _ (by simp)) (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hP) (fun w3 s3 hK3 hd3 hs3 => ?_)
  have hn3 := slotN hK3 rfl hs3
  let Γ4 : Env := (kVl, w3) :: Γ3
  have g4 : ∀ y, y ≠ kVl → y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ4.get y = Γ.get y := fun y h h1 h2 h3 => by
    simp only [Γ4, Env.get_cons, if_neg h]; exact g3 y h1 h2 h3
  refine call Γ4 kHn 0 (by decide) _ (hD _ (by simp))
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hP) (fun w4 s4 hK4 hd4 hs4 => ?_)
  have hh4 := slotH hK4 rfl hs4
  let Γ5 : Env := (kHn, w4) :: Γ4
  have g5 : ∀ y, y ≠ kHn → y ≠ kVl → y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ5.get y = Γ.get y := fun y h0 h h1 h2 h3 => by
    simp only [Γ5, Env.get_cons, if_neg h0]; exact g4 y h h1 h2 h3
  refine call Γ5 kSf 3 (by decide) _ (hD _ (by simp))
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hP) (fun w5 s5 hK5 hd5 hs5 => ?_)
  have hs5' := slotS hK5 rfl hs5
  simp only [DeclRec.defn.injEq, CVRec.mk.injEq] at hd1 hd2 hd3 hd4 hd5
  rw [← hd1.1.1] at hn1
  rw [← hd2.1.2.2] at hn2
  rw [← hd3.2.1] at hn3
  rw [← hd4.2.2.1] at hh4
  rw [← hd5.2.2.2] at hs5'
  let Γ6 : Env := (kSf, w5) :: Γ5
  have g6 : ∀ y, y ≠ kSf → y ≠ kHn → y ≠ kVl → y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ6.get y = Γ.get y :=
    fun y h00 h0 h h1 h2 h3 => by simp only [Γ6, Env.get_cons, if_neg h00]; exact g5 y h0 h h1 h2 h3
  have hus : (s0.getD 1 default).list.length < 2 ^ 59 := by
    have := hbuf.small
    rcases hl0 with ⟨p, e', -, hsc'⟩ | ⟨h0, -⟩
    · have := scanNatList_len hsc'; omega
    · rw [h0]; simp
  refine dfP_spec ra C hok hnc hcN hcS hcH hhc s Γ6 M D (fun x hx => hD x (by
      rcases List.mem_append.mp hx with h | h
      · refine List.mem_append_left _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      · exact List.mem_append_right _ h))
    st F rb capD jN jL jE cap bufJ b hlay hreln hrele hcap hcapN hbuf hdr hcapD
    ⟨(s0.getD 2 default).nat, (s0.getD 1 default).list, (s0.getD 4 default).nat⟩ (s0.getD 5 default).nat
    (s0.getD 0 default).hint (s0.getD 3 default).str hus w0 w4 w5 hl0 hh4 hs5'
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTE)
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC)
    (by simp only [Γ6, Γ5, Γ4, Γ3, Γ2, Env.get_cons, if_neg (show fU ≠ kSf by decide), if_neg (show fU ≠ kHn by decide),
          if_neg (show fU ≠ kVl by decide), if_neg (show fU ≠ fW3 by decide), if_pos]
        rw [hn1])
    (by simp only [Γ6, Γ5, Γ4, Γ3, Env.get_cons, if_neg (show fW3 ≠ kSf by decide), if_neg (show fW3 ≠ kHn by decide),
          if_neg (show fW3 ≠ kVl by decide), if_pos]; rw [hn2])
    (by simp only [Γ6, Γ5, Γ4, Env.get_cons, if_neg (show kVl ≠ kSf by decide), if_neg (show kVl ≠ kHn by decide),
          if_pos]; rw [hn3])
    (by simp only [Γ6, Γ5, Γ4, Γ3, Γ2, Γ1, Env.get_cons, if_neg (show fV2 ≠ kSf by decide),
          if_neg (show fV2 ≠ kHn by decide), if_neg (show fV2 ≠ kVl by decide), if_neg (show fV2 ≠ fW3 by decide),
          if_neg (show fV2 ≠ fU by decide), if_pos])
    (by simp only [Γ6, Γ5, Env.get_cons, if_neg (show kHn ≠ kSf by decide), if_pos])
    (by simp only [Γ6, Env.get_cons, if_pos])
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hCD)

end ConPanqueque.Front
