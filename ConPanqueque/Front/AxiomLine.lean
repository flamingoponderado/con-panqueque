import ConPanqueque.Front.DeclLine
import ConPanqueque.Front.AxiomRec
import ConPanqueque.Scan.DeclFields2


/-! # An axiom line: four fields, then the `sorryAx` record -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front
open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ScanRes scanNatList scanString scanHints HintsRec DeclRec CVRec)
variable {σ : Type}

def axInits : List (BitVec 64) := [0, BitVec.ofNat 64 listSentinel, 0, 0]
def fAxF (k : Nat) : MlS := ofString ("axf" ++ toString k)

/-- An axiom line: its four fields, then the record (an unsafe one, or one not named `sorryAx`, hangs). -/
def axLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fV2 (fAxF 1) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fU (fAxF 2) [vv kBA, vv kBN, vv kPos])
      (.seq (callTo fW3 (fAxF 3) [vv kBA, vv kBN, vv kPos])
        (.seq (callTo kUs (fAxF 0) [vv kBA, vv kBN, vv kPos]) (axP C))))

theorem axLine_spec (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcT : ∀ k, k < 4 → C.code.lookup (fAxF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanAxiomDeclSpec axInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [kUs, fV2, fU, fW3, kVl, fy, fz, kVh, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (pos e : USize) (hpos : pos.toNat ≤ b.size) (d : DeclRec) (hd : ConLeche.Frontend.scanAxiomDecl b pos = .ok d e)
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (axLineP C) s (processLineCoreD st d)
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hplat := hbuf.plat
  have hbt : ∀ (t : PState σ) (Δ : Env) (M' : Mem), Inv C s Δ M' D t → BytesAt t (cellA C bufJ) b.data.toList :=
    fun t Δ M' ht => bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)
  have call : ∀ (Δ : Env) (x : MlS) (k : Nat) (hk : k < 4) (rest : ProgHOL 64)
      {R : StateD ⊕ RecordVerdict → BitVec 64 → AState → PState σ → Prop}, x ∈ D →
      Δ.get kBA = some (cellA C bufJ) → Δ.get kBN = some (BitVec.ofNat 64 b.size) →
      Δ.get kPos = some (BitVec.ofNat 64 pos.toNat) →
      (∀ w (sl : List SVal), KindsOK [3, 1, 0, 0] sl → d = DeclRec.ax ⟨(sl.getD 2 default).nat,
          (sl.getD 1 default).list, (sl.getD 3 default).nat⟩ (sl.getD 0 default).bool →
        (∀ hk' : k < sl.length, SlotOK b w sl[k]) →
        SpecR (Inv C s ((x, w) :: Δ) M D) rest s (processLineCoreD st d) R) →
      SpecR (Inv C s Δ M D) (.seq (callTo x (fAxF k) [vv kBA, vv kBN, vv kPos]) rest) s (processLineCoreD st d) R :=
    fun Δ x k hk rest R hx h1 h2 h3 hk2 =>
      specR_retP3 x (fAxF k) sB sN sI _ (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
        (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) hx (hcT k hk)
        (by simpa [sev, vv] using h1) (by simpa [sev, vv] using h2) (by simpa [sev, vv] using h3)
        (fun t callee ht c1 c2 c3 => axiomSlot_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hplat
          (bytesAt_congr (t := t) (hbt t _ _ ht) rfl rfl rfl) (hsc _ (by show t.code = C.code; exact ht.sr.code))
          pos hpos c1 c2 c3 k hk d e hd)
        (fun w ⟨sl, hK, hdl, hsl⟩ => hk2 w sl hK hdl hsl)
  unfold axLineP
  refine call Γ fV2 1 (by decide) _ (hD _ (by simp)) hBA hBN hP (fun w0 s0 hK0 hd0 hs0 => ?_)
  subst hd0
  have hl0 := slotL hK0 rfl hs0
  let Γ1 : Env := (fV2, w0) :: Γ
  have g1 : ∀ y, y ≠ fV2 → Γ1.get y = Γ.get y := fun y h => by simp only [Γ1, Env.get_cons, ite_eq_right h]
  refine call Γ1 fU 2 (by decide) _ (hD _ (by simp)) (by rw [g1 _ (by decide)]; exact hBA)
    (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP) (fun w1 s1 hK1 hd1 hs1 => ?_)
  have hn1 := slotN hK1 rfl hs1
  let Γ2 : Env := (fU, w1) :: Γ1
  have g2 : ∀ y, y ≠ fU → y ≠ fV2 → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, ite_eq_right h]; exact g1 y h'
  refine call Γ2 fW3 3 (by decide) _ (hD _ (by simp)) (by rw [g2 _ (by decide) (by decide)]; exact hBA)
    (by rw [g2 _ (by decide) (by decide)]; exact hBN) (by rw [g2 _ (by decide) (by decide)]; exact hP)
    (fun w2 s2 hK2 hd2 hs2 => ?_)
  have hn2 := slotN hK2 rfl hs2
  let Γ3 : Env := (fW3, w2) :: Γ2
  have g3 : ∀ y, y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ3.get y = Γ.get y := fun y h h1 h2 => by
    simp only [Γ3, Env.get_cons, ite_eq_right h]; exact g2 y h1 h2
  refine call Γ3 kUs 0 (by decide) _ (hD _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hP) (fun w4 s4 hK4 hd4 hs4 => ?_)
  have hb4 := slotB hK4 rfl hs4
  simp only [DeclRec.ax.injEq, CVRec.mk.injEq] at hd1 hd2 hd4
  rw [← hd1.1.1] at hn1
  rw [← hd2.1.2.2] at hn2
  rw [← hd4.2] at hb4
  let Γ5 : Env := (kUs, w4) :: Γ3
  have g5 : ∀ y, y ≠ kUs → y ≠ fW3 → y ≠ fU → y ≠ fV2 → Γ5.get y = Γ.get y := fun y h0 h1 h2 h3 => by
    simp only [Γ5, Env.get_cons, ite_eq_right h0]; exact g3 y h1 h2 h3
  refine axP_ifun C s Γ5 M D w4 (by simp only [Γ5, Env.get_cons, ite_eq_left]) (fun hz => ?_)
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
  refine axVd_spec C hok hnc hcN s Γ5 M D (fun x hx => hD x (by
      rcases List.mem_append.mp hx with h | h
      · refine List.mem_append_left _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp
      · exact List.mem_append_right _ h))
    st F rb capD jN jL jE cap bufJ b hlay hreln hrele hcap hcapN hbuf hdr hcapD
    ⟨(s0.getD 2 default).nat, (s0.getD 1 default).list, (s0.getD 3 default).nat⟩ hus w0 hl0
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hTE)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hC)
    (by simp only [Γ5, Γ3, Γ2, Env.get_cons, ite_eq_right (show fU ≠ kUs by decide),
          ite_eq_right (show fU ≠ fW3 by decide), ite_eq_left]
        rw [hn1])
    (by simp only [Γ5, Γ3, Env.get_cons, ite_eq_right (show fW3 ≠ kUs by decide), ite_eq_left]; rw [hn2])
    (by simp only [Γ5, Γ3, Γ2, Γ1, Env.get_cons, ite_eq_right (show fV2 ≠ kUs by decide),
          ite_eq_right (show fV2 ≠ fW3 by decide), ite_eq_right (show fV2 ≠ fU by decide), ite_eq_left])
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide)]; exact hCD)

end ConPanqueque.Front
