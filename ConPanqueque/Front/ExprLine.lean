import ConPanqueque.Front.DeclLine
import ConPanqueque.Front.Expr

/-! # Expression lines: fields read again from the record, guarded below the cap

A slot or the line's index holds a capped number (`min n natCap`).  `capG x` hangs unless the word
is below `natCap`, after which it is the number itself, so the interning procedures run at exact
indices.  (No table reaches `natCap`, so nothing a guard rejects could have been bound.) -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ScanRes ExprRec NameRec)

variable {σ : Type}

/-- Hang unless `x` is below the cap. -/
def capG (x : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower (vv x) (.const (BitVec.ofNat 64 natCap))) rest hang

theorem natCap_lt : natCap < 2 ^ 64 := by unfold natCap; decide

theorem specR_capG {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (a : Nat)
    (hx : Γ.get x = some (BitVec.ofNat 64 (min a natCap)))
    (hk : a < natCap → Γ.get x = some (BitVec.ofNat 64 a) → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (capG x rest) s m R := by
  unfold capG
  refine specR_ifI _ _ (sev_lower Γ (vv x) _ (min a natCap) natCap (by simpa [sev, vv] using hx) rfl
    (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) natCap_lt) natCap_lt) (fun hw => ?_) (fun _ => specR_hangI)
  have hl : min a natCap < natCap := by
    by_cases h : min a natCap < natCap
    · exact h
    · simp [bw, h] at hw
  have ha : a < natCap := by omega
  exact hk ha (by rw [hx, show min a natCap = a by omega])

/-- A binary expression line (`app`, `lam`, `forallE`): slot 1 to `fU`, slot 0 to `fV2`. -/
def binLineP (f : MlS) (fF : Nat → MlS) : ProgHOL 64 :=
  .seq (callTo fU (fF 1) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fV2 (fF 0) [vv kBA, vv kBN, vv kPos])
      (capG fI (capG fU (capG fV2 (exBinP f)))))

theorem binLine_spec (C : Ctx) (hok : CtxOK C) (f : MlS) (fF : Nat → MlS) (body : Nat → ProgHOL 64)
    (rmk : Nat → Nat → ExprRec) (hinj : ∀ a c a' c', rmk a c = rmk a' c' → a = a' ∧ c = c') (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fU, fV2], x ∈ D) (st : StateD) (jE cap : Nat)
    (b : ByteArray) (bufJ : Nat) (r : ExprRec) (pos : USize) (i : Nat)
    (hcT : ∀ k, k < 2 → C.code.lookup (fF k) = some ([(sB, .one), (sN, .one), (sI, .one)], body k, .one))
    (hsl : ∀ k, k < 2 → ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (Δ : Env) (M' : Mem),
      Inv C s Δ M' D t → callee.lookup sB = some (.val (.word (cellA C bufJ))) →
      callee.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      callee.lookup sI = some (.val (.word (BitVec.ofNat 64 pos.toNat))) →
      RetP (callEntryStateHOLFinite t callee) (body k) (fun w => ∃ sl : List SVal, KindsOK [0, 0] sl ∧
        r = rmk (sl.getD 1 default).nat (sl.getD 0 default).nat ∧ ∀ hk' : k < sl.length, SlotOK b w sl[k]))
    (hspec : ∀ (Γ' : Env) (a c : Nat), a < 2 ^ 64 → c < 2 ^ 64 → i < 2 ^ 64 →
      Γ'.get fTE = some (cellA C jE) → Γ'.get fCap = some (BitVec.ofNat 64 cap) →
      Γ'.get fI = some (BitVec.ofNat 64 i) → Γ'.get fU = some (BitVec.ofNat 64 a) →
      Γ'.get fV2 = some (BitVec.ofNat 64 c) →
      SpecR (Inv (σ := σ) C s Γ' M D) (exBinP f) s (parseExprEntryD st i (rmk a c)) (ExPost C jE cap st i))
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (binLineP f fF) s (parseExprEntryD st i r) (ExPost C jE cap st i) := by
  unfold binLineP
  refine specR_retP3 fU (fF 1) sB sN sI _ (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) (hD _ (by simp)) (hcT 1 (by decide))
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hP)
    (fun t callee ht c1 c2 c3 => hsl 1 (by decide) t callee _ _ ht c1 c2 c3) (fun w1 ⟨s1, hK1, hr1, hs1⟩ => ?_)
  have hn1 := slotN hK1 rfl hs1
  have g1 : ∀ y, y ≠ fU → Env.get ((fU, w1) :: Γ) y = Γ.get y := fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_retP3 fV2 (fF 0) sB sN sI _ (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) (hD _ (by simp)) (hcT 0 (by decide))
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hBA) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hBN)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hP)
    (fun t callee ht c1 c2 c3 => hsl 0 (by decide) t callee _ _ ht c1 c2 c3) (fun w0 ⟨s0, hK0, hr0, hs0⟩ => ?_)
  have hn0 := slotN hK0 rfl hs0
  obtain ⟨e1, -⟩ := hinj _ _ _ _ (hr1.symm.trans hr0)
  rw [e1] at hn1
  rw [hr0]
  let Γ2 : Env := (fV2, w0) :: (fU, w1) :: Γ
  have g2 : ∀ y, y ≠ fV2 → y ≠ fU → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h, if_neg h']
  refine specR_capG fI i (by rw [g2 _ (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  refine specR_capG fU _ (by simp only [Γ2, Env.get_cons, if_neg (show fU ≠ fV2 by decide), if_pos]; rw [hn1])
    (fun haN hU' => ?_)
  refine specR_capG fV2 _ (by simp only [Γ2, Env.get_cons, if_pos]; rw [hn0]) (fun hcN hV' => ?_)
  exact hspec Γ2 _ _ (by have := natCap_lt; omega) (by have := natCap_lt; omega) (by have := natCap_lt; omega)
    (by rw [g2 _ (by decide) (by decide)]; exact hTE) (by rw [g2 _ (by decide) (by decide)]; exact hC) hI' hU' hV'

def appInits : List (BitVec 64) := [0, 0]
def fAppF (k : Nat) : MlS := ofString ("appf" ++ toString k)

theorem appLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fAppF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun appSpec appInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fU, fV2, fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : ExprRec) (hr : ConLeche.Frontend.scanAppExpr b pos = .ok r e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (binLineP fInternApp fAppF) s (parseExprEntryD st i r) (ExPost C jE cap st i) :=
  binLine_spec C hok fInternApp fAppF (fun k => recFun appSpec appInits (vv (slotName k))) ExprRec.app
    (fun a c a' c' h => by injection h with h1 h2; exact ⟨h1, h2⟩) s Γ M D
    (fun x hx => hD x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl <;> simp))
    st jE cap b bufJ r pos i hcT
    (fun k hk t callee Δ M' ht c1 c2 c3 => appSlot_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hbuf.plat
      (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _))
        rfl rfl rfl) (hsc _ (by show t.code = C.code; exact ht.sr.code)) pos hpos c1 c2 c3 k hk r e hr)
    (fun Γ' a c ha hc hi h1 h2 h3 h4 h5 =>
      exApp_spec ra C hok hcA s Γ' M D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl <;> simp)) st jE cap hrel hcap i a c hi ha hc h1 h2 h3 h4 h5)
    hTE hC hI hP hBA hBN

def lamInits : List (BitVec 64) := [0, 0]
def fLamF (k : Nat) : MlS := ofString ("lamf" ++ toString k)

theorem lamLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fLamF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLamExprSpec lamInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fU, fV2, fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : ExprRec) (hr : ConLeche.Frontend.scanLamExpr b pos = .ok r e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (binLineP fInternLam fLamF) s (parseExprEntryD st i r) (ExPost C jE cap st i) :=
  binLine_spec C hok fInternLam fLamF (fun k => recFun scanLamExprSpec lamInits (vv (slotName k))) ExprRec.lam
    (fun a c a' c' h => by injection h with h1 h2; exact ⟨h1, h2⟩) s Γ M D
    (fun x hx => hD x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl <;> simp))
    st jE cap b bufJ r pos i hcT
    (fun k hk t callee Δ M' ht c1 c2 c3 => lamSlot_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hbuf.plat
      (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _))
        rfl rfl rfl) (hsc _ (by show t.code = C.code; exact ht.sr.code)) pos hpos c1 c2 c3 k hk r e hr)
    (fun Γ' a c ha hc hi h1 h2 h3 h4 h5 =>
      exLam_spec ra C hok hcA s Γ' M D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl <;> simp)) st jE cap hrel hcap i a c hi ha hc h1 h2 h3 h4 h5)
    hTE hC hI hP hBA hBN

def allInits : List (BitVec 64) := [0, 0]
def fAllF (k : Nat) : MlS := ofString ("allf" ++ toString k)

theorem allLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fAllF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanForallExprSpec allInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fU, fV2, fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : ExprRec) (hr : ConLeche.Frontend.scanForallExpr b pos = .ok r e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (binLineP fInternForallE fAllF) s (parseExprEntryD st i r) (ExPost C jE cap st i) :=
  binLine_spec C hok fInternForallE fAllF (fun k => recFun scanForallExprSpec allInits (vv (slotName k))) ExprRec.forallE
    (fun a c a' c' h => by injection h with h1 h2; exact ⟨h1, h2⟩) s Γ M D
    (fun x hx => hD x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl <;> simp))
    st jE cap b bufJ r pos i hcT
    (fun k hk t callee Δ M' ht c1 c2 c3 => forallSlot_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hbuf.plat
      (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _))
        rfl rfl rfl) (hsc _ (by show t.code = C.code; exact ht.sr.code)) pos hpos c1 c2 c3 k hk r e hr)
    (fun Γ' a c ha hc hi h1 h2 h3 h4 h5 =>
      exForall_spec ra C hok hcA s Γ' M D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl <;> simp)) st jE cap hrel hcap i a c hi ha hc h1 h2 h3 h4 h5)
    hTE hC hI hP hBA hBN

/-- A field call: `x := fn(buf, len, pos)`. -/
theorem specR_fieldI {α : Type} {C : Ctx} {s : AState} {Δ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x fn : MlS) (body : ProgHOL 64)
    (bufJ : Nat) (b : ByteArray) (pos : USize) (P : BitVec 64 → Prop) (hx : x ∈ D)
    (hcode : C.code.lookup fn = some ([(sB, .one), (sN, .one), (sI, .one)], body, .one))
    (hBA : Δ.get kBA = some (cellA C bufJ)) (hBN : Δ.get kBN = some (BitVec.ofNat 64 b.size))
    (hP : Δ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hb : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (Δ' : Env) (M' : Mem),
      Inv C s Δ' M' D t → callee.lookup sB = some (.val (.word (cellA C bufJ))) →
      callee.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      callee.lookup sI = some (.val (.word (BitVec.ofNat 64 pos.toNat))) →
      RetP (callEntryStateHOLFinite t callee) body P)
    (hk : ∀ w, P w → SpecR (Inv C s ((x, w) :: Δ) M D) rest s m R) :
    SpecR (Inv C s Δ M D) (.seq (callTo x fn [vv kBA, vv kBN, vv kPos]) rest) s m R :=
  specR_retP3 x fn sB sN sI body (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 pos.toNat) P (by decide) (by decide) (by decide) hx hcode
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hP)
    (fun t callee ht c1 c2 c3 => hb t callee _ _ ht c1 c2 c3) hk

/-- A scanner's RetP spec, at the callee state of a call made in the `Inv` world. -/
theorem slotCall {C : Ctx} (hok : CtxOK C) {bufJ : Nat} {b : ByteArray} (hbuf : BufOK C bufJ b) {s : AState}
    {D : List MlS} (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t) (pos : USize) (body : ProgHOL 64)
    (P : BitVec 64 → Prop)
    (hS : ∀ u : PanSemStateFiniteExact 64 σ, BytesAt u (cellA C bufJ) b.data.toList → ScanCodes u →
      u.locals.lookup sB = some (.val (.word (cellA C bufJ))) →
      u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 pos.toNat))) → RetP u body P) :
    ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (Δ' : Env) (M' : Mem),
      Inv C s Δ' M' D t → callee.lookup sB = some (.val (.word (cellA C bufJ))) →
      callee.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      callee.lookup sI = some (.val (.word (BitVec.ofNat 64 pos.toNat))) →
      RetP (callEntryStateHOLFinite t callee) body P :=
  fun t callee _ _ ht c1 c2 c3 => hS _ (bytesAt_congr (t := t)
    (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)) rfl rfl rfl)
    (hsc _ (by show t.code = C.code; exact ht.sr.code)) c1 c2 c3

def letInits : List (BitVec 64) := [0, 0, 0]
def fLetF (k : Nat) : MlS := ofString ("letf" ++ toString k)

/-- A `letE` line: type (slot 1) to `fU`, value (slot 2) to `fV2`, body (slot 0) to `fTN`. -/
def letLineP : ProgHOL 64 :=
  .seq (callTo fU (fLetF 1) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fV2 (fLetF 2) [vv kBA, vv kBN, vv kPos])
      (.seq (callTo fTN (fLetF 0) [vv kBA, vv kBN, vv kPos])
        (capG fI (capG fU (capG fV2 (capG fTN exLetP))))))

theorem letLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcL : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 3 → C.code.lookup (fLetF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLetExprSpec letInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fU, fV2, fTN, fx, fy, fz, fW3, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : ExprRec) (hr : ConLeche.Frontend.scanLetExpr b pos = .ok r e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) letLineP s (parseExprEntryD st i r) (ExPost C jE cap st i) := by
  have hS := fun k hk => slotCall (s := s) (D := D) hok hbuf hsc pos _ _ (fun u hb hc l1 l2 l3 =>
    letSlot_sound u (cellA C bufJ) b hbuf.plat hb hc pos hpos l1 l2 l3 k hk r e hr)
  unfold letLineP
  refine specR_fieldI fU (fLetF 1) _ bufJ b pos _ (hD _ (by simp)) (hcT 1 (by decide)) hBA hBN hP (hS 1 (by decide))
    (fun w1 ⟨s1, hK1, hr1, hs1⟩ => ?_)
  have hn1 := slotN hK1 rfl hs1
  have g1 : ∀ y, y ≠ fU → Env.get ((fU, w1) :: Γ) y = Γ.get y := fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_fieldI fV2 (fLetF 2) _ bufJ b pos _ (hD _ (by simp)) (hcT 2 (by decide))
    (by rw [g1 _ (by decide)]; exact hBA) (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP)
    (hS 2 (by decide)) (fun w2 ⟨s2, hK2, hr2, hs2⟩ => ?_)
  have hn2 := slotN hK2 rfl hs2
  let Γ2 : Env := (fV2, w2) :: (fU, w1) :: Γ
  have g2 : ∀ y, y ≠ fV2 → y ≠ fU → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h, if_neg h']
  refine specR_fieldI fTN (fLetF 0) _ bufJ b pos _ (hD _ (by simp)) (hcT 0 (by decide))
    (by rw [g2 _ (by decide) (by decide)]; exact hBA) (by rw [g2 _ (by decide) (by decide)]; exact hBN)
    (by rw [g2 _ (by decide) (by decide)]; exact hP) (hS 0 (by decide)) (fun w0 ⟨s0, hK0, hr0, hs0⟩ => ?_)
  have hn0 := slotN hK0 rfl hs0
  have q1 := hr1.symm.trans hr0
  have q2 := hr2.symm.trans hr0
  simp only [ExprRec.letE.injEq] at q1 q2
  rw [q1.1] at hn1
  rw [q2.2.1] at hn2
  rw [hr0]
  let Γ3 : Env := (fTN, w0) :: Γ2
  have g3 : ∀ y, y ≠ fTN → y ≠ fV2 → y ≠ fU → Γ3.get y = Γ.get y := fun y h0 h h' => by
    simp only [Γ3, Env.get_cons, if_neg h0]; exact g2 y h h'
  refine specR_capG fI i (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  refine specR_capG fU _ (by simp only [Γ3, Γ2, Env.get_cons, if_neg (show fU ≠ fTN by decide),
    if_neg (show fU ≠ fV2 by decide), if_pos]; rw [hn1]) (fun haN hU' => ?_)
  refine specR_capG fV2 _ (by simp only [Γ3, Γ2, Env.get_cons, if_neg (show fV2 ≠ fTN by decide), if_pos]; rw [hn2])
    (fun hbN hV' => ?_)
  refine specR_capG fTN _ (by simp only [Γ3, Env.get_cons, if_pos]; rw [hn0]) (fun hcN hW' => ?_)
  have := natCap_lt
  exact exLet_spec ra C hok hcL s Γ3 M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp))
    st jE cap hrel hcap i _ _ _ (by omega) (by omega) (by omega) (by omega)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hTE) (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hC)
    hI' hU' hV' hW'

def projInits : List (BitVec 64) := [0, 0, 0]
def fProjF (k : Nat) : MlS := ofString ("projf" ++ toString k)

/-- A `proj` line: type name (slot 2) to `fU`, field index (slot 0) to `fV2`, struct (slot 1) to `fW3`. -/
def projLineP : ProgHOL 64 :=
  .seq (callTo fU (fProjF 2) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fV2 (fProjF 0) [vv kBA, vv kBN, vv kPos])
      (.seq (callTo fW3 (fProjF 1) [vv kBA, vv kBN, vv kPos])
        (capG fI (capG fU (capG fV2 (capG fW3 exProjP))))))

theorem projLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcP : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 3 → C.code.lookup (fProjF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanProjExprSpec projInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fU, fV2, fW3, fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE jN cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hreln : TblRel C.H jN cap st.names)
    (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : ExprRec) (hr : ConLeche.Frontend.scanProjExpr b pos = .ok r e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hTN : Γ.get fTN = some (cellA C jN))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) projLineP s (parseExprEntryD st i r) (ExPost C jE cap st i) := by
  have hS := fun k hk => slotCall (s := s) (D := D) hok hbuf hsc pos _ _ (fun u hb hc l1 l2 l3 =>
    projSlot_sound u (cellA C bufJ) b hbuf.plat hb hc pos hpos l1 l2 l3 k hk r e hr)
  unfold projLineP
  refine specR_fieldI fU (fProjF 2) _ bufJ b pos _ (hD _ (by simp)) (hcT 2 (by decide)) hBA hBN hP (hS 2 (by decide))
    (fun w1 ⟨s1, hK1, hr1, hs1⟩ => ?_)
  have hn1 := slotN hK1 rfl hs1
  have g1 : ∀ y, y ≠ fU → Env.get ((fU, w1) :: Γ) y = Γ.get y := fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_fieldI fV2 (fProjF 0) _ bufJ b pos _ (hD _ (by simp)) (hcT 0 (by decide))
    (by rw [g1 _ (by decide)]; exact hBA) (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP)
    (hS 0 (by decide)) (fun w2 ⟨s2, hK2, hr2, hs2⟩ => ?_)
  have hn2 := slotN hK2 rfl hs2
  let Γ2 : Env := (fV2, w2) :: (fU, w1) :: Γ
  have g2 : ∀ y, y ≠ fV2 → y ≠ fU → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h, if_neg h']
  refine specR_fieldI fW3 (fProjF 1) _ bufJ b pos _ (hD _ (by simp)) (hcT 1 (by decide))
    (by rw [g2 _ (by decide) (by decide)]; exact hBA) (by rw [g2 _ (by decide) (by decide)]; exact hBN)
    (by rw [g2 _ (by decide) (by decide)]; exact hP) (hS 1 (by decide)) (fun w0 ⟨s0, hK0, hr0, hs0⟩ => ?_)
  have hn0 := slotN hK0 rfl hs0
  have q1 := hr1.symm.trans hr0
  have q2 := hr2.symm.trans hr0
  simp only [ExprRec.proj.injEq] at q1 q2
  rw [q1.1] at hn1
  rw [q2.2.1] at hn2
  rw [hr0]
  let Γ3 : Env := (fW3, w0) :: Γ2
  have g3 : ∀ y, y ≠ fW3 → y ≠ fV2 → y ≠ fU → Γ3.get y = Γ.get y := fun y h0 h h' => by
    simp only [Γ3, Env.get_cons, if_neg h0]; exact g2 y h h'
  refine specR_capG fI i (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  refine specR_capG fU _ (by simp only [Γ3, Γ2, Env.get_cons, if_neg (show fU ≠ fW3 by decide),
    if_neg (show fU ≠ fV2 by decide), if_pos]; rw [hn1]) (fun haN hU' => ?_)
  refine specR_capG fV2 _ (by simp only [Γ3, Γ2, Env.get_cons, if_neg (show fV2 ≠ fW3 by decide), if_pos]; rw [hn2])
    (fun hbN hV' => ?_)
  refine specR_capG fW3 _ (by simp only [Γ3, Env.get_cons, if_pos]; rw [hn0]) (fun hcN hW' => ?_)
  have := natCap_lt
  have h62 : natCap < 2 ^ 63 := by unfold natCap; decide
  exact exProj_spec ra C hok hcP s Γ3 M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl <;> simp))
    st jE jN cap hrel hreln hcap i _ _ _ (by omega) (by omega) (by omega) (by omega) 0
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hTE) (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hC) hI' hU' hV' hW'

def constInits : List (BitVec 64) := [0, BitVec.ofNat 64 listSentinel]
def fConstF (k : Nat) : MlS := ofString ("constf" ++ toString k)

/-- A `const` line: name (slot 0) to `fU`, level list slot (slot 1) to `fV2`. -/
def constLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fU (fConstF 0) [vv kBA, vv kBN, vv kPos])
    (.seq (callTo fV2 (fConstF 1) [vv kBA, vv kBN, vv kPos])
      (capG fI (capG fU (exConstP C))))

theorem constLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcLs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (hcC : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (hcT : ∀ k, k < 2 → C.code.lookup (fConstF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanConstExprSpec constInits (vv (slotName k)), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fU, fV2, fx, fy, kG2, kKA0, kN, kK, kX, kY, kLs, fh], x ∈ D)
    (st : StateD) (jE jL jN cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hrell : TblRel C.H jL cap st.levels)
    (hreln : TblRel C.H jN cap st.names) (hcap : 8 * cap < 2 ^ 64) (hcapN : cap ≤ natCap)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (hpos : pos.toNat ≤ b.size)
    (r : ExprRec) (hr : ConLeche.Frontend.scanConstExpr b pos = .ok r e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hTL : Γ.get fTL = some (cellA C jL))
    (hTN : Γ.get fTN = some (cellA C jN)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (constLineP C) s (parseExprEntryD st i r) (ExPost C jE cap st i) := by
  have hS := fun k hk => slotCall (s := s) (D := D) hok hbuf hsc pos _ _ (fun u hb hc l1 l2 l3 =>
    constSlot_sound u (cellA C bufJ) b hbuf.plat hb hc pos hpos l1 l2 l3 k hk r e hr)
  unfold constLineP
  refine specR_fieldI fU (fConstF 0) _ bufJ b pos _ (hD _ (by simp)) (hcT 0 (by decide)) hBA hBN hP (hS 0 (by decide))
    (fun w1 ⟨s1, hK1, hr1, hs1⟩ => ?_)
  have hn1 := slotN hK1 rfl hs1
  have g1 : ∀ y, y ≠ fU → Env.get ((fU, w1) :: Γ) y = Γ.get y := fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_fieldI fV2 (fConstF 1) _ bufJ b pos _ (hD _ (by simp)) (hcT 1 (by decide))
    (by rw [g1 _ (by decide)]; exact hBA) (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP)
    (hS 1 (by decide)) (fun w2 ⟨s2, hK2, hr2, hs2⟩ => ?_)
  have hl2 := slotL hK2 rfl hs2
  have q1 := hr1.symm.trans hr2
  simp only [ExprRec.const.injEq] at q1
  rw [q1.1] at hn1
  rw [hr2]
  let Γ2 : Env := (fV2, w2) :: (fU, w1) :: Γ
  have g2 : ∀ y, y ≠ fV2 → y ≠ fU → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h, if_neg h']
  refine specR_capG fI i (by rw [g2 _ (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  refine specR_capG fU _ (by simp only [Γ2, Env.get_cons, if_neg (show fU ≠ fV2 by decide), if_pos]; rw [hn1])
    (fun haN hU' => ?_)
  have := natCap_lt
  have hus : (s2.getD 1 default).list.length < 2 ^ 60 := by
    have := hbuf.small
    rcases hl2 with ⟨p, e', -, hsc'⟩ | ⟨h0, -⟩
    · have := scanNatList_len hsc'; omega
    · rw [h0]; simp
  exact exConst_spec ra C hok hnc hcN hcLs hcC s Γ2 M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    st jE jL jN cap hrel hrell hreln hcap hcapN bufJ b hbuf _ hus w2 hl2 i _ (by omega) (by omega)
    (by rw [g2 _ (by decide) (by decide)]; exact hTE) (by rw [g2 _ (by decide) (by decide)]; exact hTL)
    (by rw [g2 _ (by decide) (by decide)]; exact hTN) (by rw [g2 _ (by decide) (by decide)]; exact hC) hI' hU'
    (by rw [g2 _ (by decide) (by decide)]; exact hBA) (by rw [g2 _ (by decide) (by decide)]; exact hBN)
    (by simp only [Γ2, Env.get_cons, if_pos])

end ConPanqueque.Front
