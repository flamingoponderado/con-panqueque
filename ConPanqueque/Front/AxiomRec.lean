import ConPanqueque.Front.Decl

/-! # An axiom record in the value heap

The twin pushes every safe axiom record. The port takes those named by an accepted axiom's pin
(`axPinSlots`: `sorryAx`, `Quot.sound`, `propext`, `Classical.choice`, `Lean.trustCompiler`,
`Lean.ofReduceNat`, `Lean.ofReduceBool`): the record's name and type through the tables, the name tested
against those pins in turn (any other hangs), then the five-cell record of kind `5` whose value cell holds
the name. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec DeclRec HintsRec scanNatList scanString scanHints)

variable {σ : Type}

theorem processAx_ok (st : StateD) (cv : CVRec) (nmh : NIdx) (tyh : EIdx)
    (hnm : st.names.get? cv.name = some nmh) (hty : st.exprs.get? cv.type = some tyh)
    (hlps : ∀ j (hj : j < cv.levelParams.length), (st.names.get? cv.levelParams[j]).isSome) :
    processLineCoreD st (.ax cv false) =
      pure (.inl { st with decls := st.decls.push (.axiomDecl
        ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩) }) := by
  have hm := mapM_name_ok st cv.levelParams hlps
  simp [processLineCoreD, parseCVD, StateD.name, getDeclD, StateD.expr, hnm, hty, hm, pushDecl]

/-- The name (`fy`) against the pins at slots `is` in turn: equal to one, the record; to none, a hang. -/
def axChain (C : Ctx) : List Nat → ProgHOL 64
  | [] => hang
  | i :: is => .seq (.assign .local kVh (.load .one (.const (ecell C (C.PO + i)))))
      (.ite (.cmp .notEqual (vv fy) (vv kVh)) (axChain C is) (vdTail C 5))

/-- A safe axiom: name and type through the tables, the name an accepted axiom's pin (else hang), the
record. -/
def axVd (C : Ctx) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblGetP fz (vv fTE) (vv fCap) (vv fW3) (axChain C ConPanqueque.Bridge.axPinSlots))

theorem axVd_spec (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fy, fz, kVh, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (cv : CVRec) (hus : cv.levelParams.length < 2 ^ 59) (wpos : BitVec 64)
    (hslot : (∃ (pos e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ scanNatList b pos = .ok cv.levelParams e0) ∨
      (cv.levelParams = [] ∧ wpos = BitVec.ofNat 64 listSentinel))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hU : Γ.get fU = some (BitVec.ofNat 64 (min cv.name natCap)))
    (hW : Γ.get fW3 = some (BitVec.ofNat 64 (min cv.type natCap)))
    (hV : Γ.get fV2 = some wpos)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (axVd C) s (processLineCoreD st (.ax cv false))
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hNC : min cv.name natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hTC : min cv.type natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  unfold axVd
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv fU)
    (by simpa [sev, vv] using hTN) (by simpa [sev, vv] using hC) _ hNC (by simpa [sev, vv] using hU)
    (fun nmh hnm => ?_)
  have hnm' := get_capped hreln hcapN _ nmh hnm
  have g1 : ∀ y, y ≠ fy → Env.get ((fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ) y = Env.get Γ y :=
    fun y h => by simp only [Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fz (hD fz (by simp)) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv fW3)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTE) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC)
    _ hTC (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hW) (fun tyh hty => ?_)
  have hty' := get_capped hrele hcapN _ tyh hty
  let Γ2 : Env := (fz, Enc.idxW tyh) :: (fz, Enc.idxW tyh + 1) :: (fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ
  have g2 : ∀ y, y ≠ fz → y ≠ fy → Env.get Γ2 y = Env.get Γ y := fun y h1 h2 => by
    simp only [Γ2, Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  -- the record, once the name is pin `i`'s
  have fin : ∀ (i : Nat) (hi : i < C.pins.names.size), nmh = C.pins.names[i] →
      ConPanqueque.Bridge.AxPinName C.pins nmh → ∀ (Γ3 : Env),
      Γ3.get kVh = some (Enc.idxW C.pins.names[i]) → (∀ y, y ≠ kVh → y ≠ fz → y ≠ fy → Env.get Γ3 y = Env.get Γ y) →
      Env.get Γ3 fy = some (Enc.idxW nmh) → Env.get Γ3 fz = some (Enc.idxW tyh) →
      SpecR (Inv (σ := σ) C s Γ3 M D) (vdTail C 5) s (processLineCoreD st (.ax cv false))
        (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
    intro i hi hs hpin Γ3 hv3 g3 hy3 hz3
    exact vdTail_spec C hok hnc hcN s Γ3 M D (fun x hx => hD x (by simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))
      st F rb capD jN jL jE cap bufJ b hlay hreln hcap hcapN hbuf hdr hcapD cv.levelParams hus wpos hslot 5
      (Enc.idxW nmh) (Enc.idxW tyh) (Enc.idxW C.pins.names[i])
      (fun lpsH => .axiomDecl ⟨nmh, lpsH, tyh⟩)
      (fun H r o hr ho h0 h1 h2 h3 h4 hb =>
        ⟨hr, h0, ⟨o, ho, by simpa using h1, by simpa using h2, by simpa using h3, hb, by simpa using hus⟩, ⟨_, h4⟩, hpin⟩)
      (fun hall => processAx_ok st cv nmh tyh hnm' hty' hall)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hTN)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hC)
      hy3 hz3 hv3
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hV)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hRB)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hCD)
  have chain : ∀ (is : List Nat), (∀ i ∈ is, i ∈ ConPanqueque.Bridge.axPinSlots) → ∀ (Γ3 : Env),
      (∀ y, y ≠ kVh → y ≠ fz → y ≠ fy → Env.get Γ3 y = Env.get Γ y) →
      Env.get Γ3 fy = some (Enc.idxW nmh) → Env.get Γ3 fz = some (Enc.idxW tyh) →
      SpecR (Inv (σ := σ) C s Γ3 M D) (axChain C is) s (processLineCoreD st (.ax cv false))
        (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
    intro is
    induction is with
    | nil => exact fun _ _ _ _ _ => specR_hangI
    | cons i is ih =>
      intro hmem Γ3 g3 hy3 hz3
      have hiS : i ∈ ConPanqueque.Bridge.axPinSlots := hmem i (by simp)
      have hsz : i < C.pins.names.size := by
        rw [hok.pinsRel.1]
        simp only [ConPanqueque.Bridge.axPinSlots, List.mem_cons, List.not_mem_nil, or_false] at hiS
        rcases hiS with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      refine specR_envLoadI (C := C) kVh _ (C.PO + i) _ (hD kVh (by simp)) rfl (hok.pinsRel.2.1 _ hsz) ?_
      let Γ4 : Env := (kVh, Enc.idxW C.pins.names[i]) :: Γ3
      have g4 : ∀ y, y ≠ kVh → y ≠ fz → y ≠ fy → Env.get Γ4 y = Env.get Γ y := fun y h0 h1 h2 => by
        simp only [Γ4, Env.get_cons, ite_eq_right h0]; exact g3 y h0 h1 h2
      have hy4 : Env.get Γ4 fy = some (Enc.idxW nmh) := by
        simp only [Γ4, Env.get_cons, ite_eq_right (show fy ≠ kVh by decide)]; exact hy3
      have hz4 : Env.get Γ4 fz = some (Enc.idxW tyh) := by
        simp only [Γ4, Env.get_cons, ite_eq_right (show fz ≠ kVh by decide)]; exact hz3
      by_cases hs : nmh = C.pins.names[i]
      · refine specR_ifI _ 0 (by simp +decide [sev, vv, Env.get_cons, hy3, T.Decl.cmpNe_idxW_f hs])
          (fun h => absurd rfl h) (fun _ => ?_)
        exact fin _ hsz hs ⟨i, hiS, by rw [Array.getElem?_eq_getElem hsz, hs]⟩ Γ4 (by simp [Γ4]) g4 hy4 hz4
      refine specR_ifI _ 1 (by simp +decide [sev, vv, Env.get_cons, hy3, T.Decl.cmpNe_idxW_t hs]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact ih (fun j hj => hmem j (by simp [hj])) Γ4 g4 hy4 hz4
  exact chain _ (fun i hi => hi) Γ2 (fun y _ h1 h2 => g2 y h1 h2)
    (by simp only [Γ2, Env.get_cons, ite_eq_right (show fy ≠ fz by decide), ite_eq_left])
    (by simp only [Γ2, Env.get_cons, ite_eq_left])

/-- An axiom record: unsafe ones hang. -/
def axP (C : Ctx) : ProgHOL 64 := .ite (vv kUs) hang (axVd C)

theorem axP_ifun (C : Ctx) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) {m : AM (StateD ⊕ RecordVerdict)}
    {R : StateD ⊕ RecordVerdict → BitVec 64 → AState → PState σ → Prop} (wu : BitVec 64)
    (hu : Γ.get kUs = some wu) (h : wu = 0 → SpecR (Inv (σ := σ) C s Γ M D) (axVd C) s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (axP C) s m R := by
  unfold axP
  refine specR_ifI _ wu (by simpa [sev, vv] using hu) (fun _ => specR_hangI) h

end ConPanqueque.Front
