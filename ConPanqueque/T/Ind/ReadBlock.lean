import ConPanqueque.T.Ind.ReadBlockTwin
import ConPanqueque.T.Ind.IndParams
import ConPanqueque.T.Ind.AllLps

/-!
# `readBlock`

The block's shape, as a heap record (`ShapeRep`): the split (three `tagRun`s; the records must be the types,
then the constructors, then at least one recursor), the member counts into an array, the level-parameter
checks (`allLps`), then `rbTail`'s pieces, each its own function, and the seven-word shape block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI

theorem bind_ok_inv' {α β : Type} {m : AM α} {k : α → AM β} {s : AState} {a : β} {s' : AState}
    (h : (m >>= k) s = .ok (a, s')) : ∃ b s1, m s = .ok (b, s1) ∧ k b s1 = .ok (a, s') := by
  simp only [bind, StateT.bind] at h
  cases hm : m s with
  | error e => rw [hm] at h; cases h
  | ok p => obtain ⟨b, s1⟩ := p; rw [hm] at h; exact ⟨b, s1, rfl, h⟩

/-- The member counts are one per member. -/
theorem bmc_length (nPd k nC : Nat) (names : List NIdx) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)) :
    ∀ (ts : List IConstantVal) (m : Nat) (s s' : AState) (ns : List Nat),
      unwrapE (blockMemberCounts nPd k nC names rs m ts) s = .ok (ns, s') → ns.length = ts.length
  | [], m, s, s', ns, h => by
    rw [unwrap_bmc_nil] at h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | t :: ts, m, s, s', ns, h => by
    rw [unwrap_bmc_cons] at h
    obtain ⟨q, s1, -, h1⟩ := bind_ok_inv' h
    obtain ⟨c, s2, -, h2⟩ := bind_ok_inv' h1
    obtain ⟨ns', s3, h3, h4⟩ := bind_ok_inv' h2
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h4
    obtain ⟨rfl, -⟩ := h4
    simp [bmc_length nPd k nC names rs ts (m + 1) s2 s3 ns' h3]

def alloc7 (C : Ctx) (x : MlS) (e0 e1 e2 e3 e4 e5 e6 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 56) (.seq (.store (vv x) e0)
    (.seq (.store (.op .add [vv x, .const 8]) e1) (.seq (.store (.op .add [vv x, .const 16]) e2)
    (.seq (.store (.op .add [vv x, .const 24]) e3) (.seq (.store (.op .add [vv x, .const 32]) e4)
    (.seq (.store (.op .add [vv x, .const 40]) e5) (.seq (.store (.op .add [vv x, .const 48]) e6) rest)))))))

/-- The image after writing seven words at `H2.length …`. -/
def img7 (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) : List (BitVec 64) :=
  (((((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2).set (H2.length + 3) w3).set
    (H2.length + 4) w4).set (H2.length + 5) w5).set (H2.length + 6) w6

section
variable {σ : Type}

theorem specR_alloc7I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (e0 e1 e2 e3 e4 e5 e6 : ExpHOL 64) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (hx : x ∈ D)
    (h0 : ∀ v, sev ((x, v) :: Γ) e0 = some w0) (h1 : ∀ v, sev ((x, v) :: Γ) e1 = some w1)
    (h2 : ∀ v, sev ((x, v) :: Γ) e2 = some w2) (h3 : ∀ v, sev ((x, v) :: Γ) e3 = some w3)
    (h4 : ∀ v, sev ((x, v) :: Γ) e4 = some w4) (h5 : ∀ v, sev ((x, v) :: Γ) e5 = some w5)
    (h6 : ∀ v, sev ((x, v) :: Γ) e6 = some w6)
    (hk : ∀ (H2 ws : List (BitVec 64)), C.H <+: H2 → ws.length = 7 →
      SpecR (Inv (ctxH C (img7 H2 ws w0 w1 w2 w3 w4 w5 w6)) s ((x, cellA C H2.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (alloc7 C x e0 e1 e2 e3 e4 e5 e6 rest) s m R := by
  unfold alloc7
  refine specR_allocI x _ 7 (by decide) hx (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) e0 H2.length (by simp [ctxH, hws]) w0 (by simp [cellA, ctxH])
    (h0 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e1 (H2.length + 1) (by simp [ctxH, hws]) w1
    (by simp [sev]; exact cellA_add_ofNat C H2.length 1) (h1 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e2 (H2.length + 2) (by simp [ctxH, hws]) w2
    (by simp [sev]; exact cellA_add_ofNat C H2.length 2) (h2 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e3 (H2.length + 3) (by simp [ctxH, hws]) w3
    (by simp [sev]; exact cellA_add_ofNat C H2.length 3) (h3 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e4 (H2.length + 4) (by simp [ctxH, hws]) w4
    (by simp [sev]; exact cellA_add_ofNat C H2.length 4) (h4 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e5 (H2.length + 5) (by simp [ctxH, hws]) w5
    (by simp [sev]; exact cellA_add_ofNat C H2.length 5) (h5 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e6 (H2.length + 6) (by simp [ctxH, hws]) w6
    (by simp [sev]; exact cellA_add_ofNat C H2.length 6) (h6 _) ?_
  exact hk H2 ws hp hws

theorem img7_prefix (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (h : ws.length = 7) :
    H2 <+: img7 H2 ws w0 w1 w2 w3 w4 w5 w6 :=
  prefix_of_get? (by simp [img7, h]) (fun k hk => by
    simp only [img7]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_append_left hk])

theorem img7_get (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (h : ws.length = 7) :
    ∀ i (hi : i < 7), (img7 H2 ws w0 w1 w2 w3 w4 w5 w6)[H2.length + i]? = some ([w0, w1, w2, w3, w4, w5, w6][i]'(by simp; omega)) := by
  have hl : (H2 ++ ws).length = H2.length + 7 := by simp [h]
  intro i hi
  simp only [img7]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · repeat rw [List.getElem?_set_ne (by omega)]
    rw [Nat.add_zero, List.getElem?_set_self (by omega)]; rfl
  all_goals
    repeat (first | (rw [List.getElem?_set_self (by simp [hl]; omega)]) | (rw [List.getElem?_set_ne (by omega)]))
    rfl

end

def rbP := ofString "rb_p"
def rbNP := ofString "rb_np"
def rbN := ofString "rb_n"
def rbK := ofString "rb_k"
def rbE := ofString "rb_e"
def rbF := ofString "rb_f"
def rbC := ofString "rb_c"
def rbR := ofString "rb_r"
def rbA := ofString "rb_a"
def rbX := ofString "rb_x"
def rbQ := ofString "rb_q"
def rbL := ofString "rb_l"
def rbT := ofString "rb_t"
def rbI := ofString "rb_i"
def rbS := ofString "rb_s"
def rbIP := ofString "rb_ip"
def rbLV := ofString "rb_lv"
def rbG := ofString "rb_g"
def rbMS := ofString "rb_ms"
def rbRC := ofString "rb_rc"
def rbLR := ofString "rb_lr"
def rbLG := ofString "rb_lg"
def rbEL := ofString "rb_el"
def rbO := ofString "rb_o"
def fReadBlock := ofString "readBlock"

def rbParams : List MlS := [rbP, rbNP]
def rbLocals : List MlS := [rbN, rbK, rbE, rbF, rbC, rbR, rbA, rbX, rbQ, rbL, rbT, rbI, rbS, rbIP, rbLV, rbG, rbMS,
  rbRC, rbLR, rbLG, rbEL, rbO]

def rbCall (x f : MlS) (es : List (ExpHOL 64)) : ProgHOL 64 → ProgHOL 64 :=
  .seq (.call (some (some (.local, x), none)) f es)

def rbLoad (x : MlS) (e : ExpHOL 64) : ProgHOL 64 → ProgHOL 64 := .seq (.assign .local x (.load .one e))

def rbAssign (x : MlS) (e : ExpHOL 64) : ProgHOL 64 → ProgHOL 64 := .seq (.assign .local x e)

/-- Hang unless `e`. -/
def rbGuard (e : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 := .ite e rest hang

def rbShape (C : Ctx) (lg : ExpHOL 64) : ProgHOL 64 :=
  alloc7 C rbO (vv rbMS) (vv rbRC) (vv rbNP) (vv rbEL) (vv rbS) lg (vv rbIP) (.return (vv rbO))

def rbBody (C : Ctx) : ProgHOL 64 := prologue rbLocals
  (rbLoad rbN (vv rbP)
  (rbCall rbK fTagRun [vv rbP, .const 0, vv rbN, .const 3]
  (rbCall rbE fTagRun [vv rbP, vv rbK, vv rbN, .const 4]
  (rbCall rbF fTagRun [vv rbP, vv rbE, vv rbN, .const 5]
  (rbGuard (.cmp .equal (vv rbF) (vv rbN))
  (.ite (.cmp .equal (vv rbK) (.const 0)) hang
  (.ite (.cmp .equal (vv rbE) (vv rbN)) hang
  (rbAssign rbC (.op .sub [vv rbE, vv rbK])
  (rbAssign rbR (.op .sub [vv rbN, vv rbE])
  (allocP C rbA (.op .add [.panop .mul [vv rbK, .const 8], .const 8])
  (rbCall rbX fBMC [vv rbP, .const 0, vv rbK, vv rbC, vv rbR, vv rbNP, vv rbA]
  (rbLoad rbQ (.op .add [vv rbP, .const 8])
  (rbLoad rbL (.op .add [vv rbQ, .const 16])
  (rbCall rbX fAllLps [vv rbP, .const 0, vv rbK, vv rbL, .const 0, vv rbNP]
  (rbGuard (.cmp .notEqual (vv rbX) (.const 0))
  (rbCall rbX fAllLps [vv rbP, vv rbK, vv rbE, vv rbL, .const 1, vv rbNP]
  (rbGuard (.cmp .notEqual (vv rbX) (.const 0))
  (rbLoad rbT (.op .add [vv rbQ, .const 24])
  (rbLoad rbI (vv rbA)
  (rbCall rbS fResSort [.op .add [vv rbNP, vv rbI], vv rbT]
  (rbCall rbIP fIsPropL [vv rbS]
  (rbCall rbLV fParamLevels [vv rbL]
  (rbCall rbG fBlockGroups [vv rbP, vv rbK, vv rbC, vv rbLV, vv rbNP]
  (rbCall rbMS fMembersOf [vv rbP, vv rbK, vv rbA, vv rbG]
  (rbCall rbRC fRecShapes [vv rbP, vv rbE, vv rbN, vv rbK]
  (rbLoad rbQ (.op .add [vv rbP, .op .add [.panop .mul [vv rbE, .const 8], .const 8]])
  (rbLoad rbLR (.op .add [vv rbQ, .const 16])
  (rbCall rbLG fLargeChk [vv rbLR, vv rbL]
  (.ite (.cmp .notEqual (vv rbLG) (.const 0))
    (rbLoad rbEL (.op .add [vv rbLR, .const 8]) (rbShape C (.const 1)))
    (rbAssign rbEL (.const (Enc.idxW anonH)) (rbShape C (.const 0))))))))))))))))))))))))))))))))

/-- The functions `readBlock` calls, and theirs. -/
structure RBCodes (C : Ctx) : Prop where
  rb : C.code.lookup fReadBlock = some (rbParams.map (fun p => (p, ShapeHOL.one)), rbBody C, .one)
  tr : C.code.lookup fTagRun = some (trParams.map (fun p => (p, ShapeHOL.one)), trBody, .one)
  bm : C.code.lookup fBMC = some (bmParams.map (fun p => (p, ShapeHOL.one)), bmBody, .one)
  fr : C.code.lookup fFindRec = some (frParams.map (fun p => (p, ShapeHOL.one)), frBody, .one)
  bc : C.code.lookup fBlockCounts = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody, .one)
  pbc : C.code.lookup fPbc = some ([(pFu, .one), (pH, .one)], pbcBody fPbc, .one)
  rt : C.code.lookup fRecTarget = some (rtParams.map (fun p => (p, ShapeHOL.one)), rtBody C, .one)
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  ga : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  ni : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one)
  al : C.code.lookup fAllLps = some (alParams.map (fun p => (p, ShapeHOL.one)), ConPanqueque.T.Ind.alBody, .one)
  le : C.code.lookup fLpsEq = some (leParams.map (fun p => (p, ShapeHOL.one)), leBody, .one)
  leg : C.code.lookup fLpsEqGo = some (legParams.map (fun p => (p, ShapeHOL.one)), legBody, .one)
  rs : C.code.lookup fResSort = some (rsParams.map (fun p => (p, ShapeHOL.one)), rsBody C, .one)
  ip : C.code.lookup fIsPropL = some (ipParams.map (fun p => (p, ShapeHOL.one)), ipBody C, .one)
  eqv : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one)
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  ilp : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ils : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  bg : C.code.lookup fBlockGroups = some (bgParams.map (fun p => (p, ShapeHOL.one)), bgBody C, .one)
  bo : C.code.lookup fBgOuter = some (boParams.map (fun p => (p, ShapeHOL.one)), boBody C, .one)
  gf : C.code.lookup fGrpFill = some (gfParams.map (fun p => (p, ShapeHOL.one)), gfBody C, .one)
  cm : C.code.lookup fCtorMember = some (cmParams.map (fun p => (p, ShapeHOL.one)), cmBody C, .one)
  mi : C.code.lookup fMemberIdx = some (miParams.map (fun p => (p, ShapeHOL.one)), miBody, .one)
  mo : C.code.lookup fMembersOf = some (moParams.map (fun p => (p, ShapeHOL.one)), moBody C, .one)
  mf : C.code.lookup fMembersFill = some (mfParams.map (fun p => (p, ShapeHOL.one)), mfBody C, .one)
  rh : C.code.lookup fRecShapes = some (rhParams.map (fun p => (p, ShapeHOL.one)), rhBody C, .one)
  rc : C.code.lookup fRecsFill = some (rcParams.map (fun p => (p, ShapeHOL.one)), rcBody C, .one)
  lg : C.code.lookup fLargeChk = some (lgParams.map (fun p => (p, ShapeHOL.one)), lgBody, .one)
  lh : C.code.lookup fLpsHas = some (lhParams.map (fun p => (p, ShapeHOL.one)), lhBody, .one)

section
variable {σ : Type}

theorem rb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rbLocals → (ctxEnv C ++ rbParams.zip vals).get x = none :=
  Knot.params_none C rbLocals rbParams vals (by decide) (by decide)

/-- The block's shape, a record in a bigger heap. -/
def PostRB (C : Ctx) (p : BlockShape) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ o, w = cellA C o ∧ ShapeRep C H' o p

theorem postRB_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRB C a w s' st → PostRB C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

/-- A `tagRun` call: the run's end, the state kept. -/
theorem rb_tagRun (C : Ctx) (hc : RBCodes C) (blk : List IConstantInfo) (ob t j : Nat) (ht : t < 6)
    (hlen : blk.length < 2 ^ 59) (hj : j ≤ blk.length) (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H)
    (hb : IndBlk C H ob blk) {β : Type} {Γ : Env} {D : List MlS} {M : Mem} {rest : ProgHOL 64} {k : Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (es : List (ExpHOL 64)) (hx : x ∈ D)
    (hes : EvAll (fun e v => sev Γ e = some v) es [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 blk.length,
      BitVec.ofNat 64 t])
    (hk : ∀ H1, H <+: H1 → SpecR (Inv (ctxH C H1) s ((x, BitVec.ofNat 64 (runEnd blk t (blk.length - j) j)) :: Γ) [] D)
      rest s (k (runEnd blk t (blk.length - j) j)) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (.seq (.call (some (some (.local, x), none)) fTagRun es) rest) s
      (pure (runEnd blk t (blk.length - j) j) >>= k) R :=
  specR_callNIH (C := ctxH C H) x fTagRun trParams es trBody _ (by decide) rfl hx hc.tr hes
    (fun a w s' st => (pure (runEnd blk t (blk.length - j) j) : AM Nat) s = .ok (a, s') ∧ PostN (ctxH C H) a w s' st)
    (fun a w s' H' => w = BitVec.ofNat 64 a ∧ a = runEnd blk t (blk.length - j) j ∧ s' = s)
    (fun a w s' st ⟨hr, H', hp', hw, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact ⟨H', hp', ⟨hw, hr.1.symm, hr.2.symm⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu trParams _ rfl hlk)
      (tr_spec C hc.tr blk ob t ht hlen (blk.length - j) j H s hp hb rfl hj)))
    (fun a w s' H' hp' ⟨hw, ha, hs'⟩ => by subst hw; subst ha; subst hs'; exact hk H' hp')

end

section
variable {σ : Type}

theorem sev_ne0 {Γ : Env} {x : MlS} {b : Bool} (h : sev Γ (vv x) = some (boolW b)) :
    sev Γ (.cmp .notEqual (vv x) (.const 0)) = some (boolW b) := by
  simp only [sev] at h ⊢; rw [h]; cases b <;> simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem specR_pureBind {α β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (a : α)
    (h : SpecR P c s ((pure a : AM α) >>= fun _ => m) R) : SpecR P c s m R :=
  specR_congr (m' := (pure a : AM α) >>= fun _ => m) (by simp) h

theorem kinds_mem {blk : List IConstantInfo} {K n t : Nat} (h : ∀ i, K ≤ i → i < n → kindAt blk i = some t)
    (hn : n ≤ blk.length) : ∀ x ∈ (blk.drop K).take (n - K), kindOf x = t := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take, List.length_drop] at hi
  have := h (K + i) (by omega) (by omega)
  simp only [kindAt, List.getElem?_eq_getElem (show K + i < blk.length by omega)] at this
  simpa using this

theorem mapM_len {α β : Type} (f : α → AM β) : ∀ (l : List α) (s s' : AState) (r : List β),
    l.mapM f s = .ok (r, s') → r.length = l.length
  | [], s, s', r, h => by
    simp only [List.mapM_nil, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | a :: l, s, s', r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, s1, -, h1⟩ := bind_ok_inv' h
    obtain ⟨bs, s2, h2, h3⟩ := bind_ok_inv' h1
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, -⟩ := h3
    simp [mapM_len f l s1 s2 bs h2]

theorem bg_len (names : List NIdx) (lvls : LsIdx) (nP k : Nat) (ctors : List (IConstantVal × Nat)) (s s' : AState)
    (gs : List (List (IConstantVal × Nat))) (h : blockGroups names lvls nP k ctors s = .ok (gs, s')) : gs.length = k := by
  rw [blockGroups_eq] at h
  have := mapM_len _ _ _ _ _ h
  simpa using this

theorem largeT_some {lps rl : List NIdx} {e : NIdx} (h : largeT lps rl = some e) : ∃ r, rl = e :: r := by
  cases rl with
  | nil => simp [largeT] at h
  | cons e' r =>
    simp only [largeT] at h
    split at h
    · cases h; exact ⟨r, rfl⟩
    · cases h

theorem ctorT_fst {c : IConstantInfo} (h : kindOf c = 4) : (ctorT c).1 = c.toConstantVal := by
  cases c <;> simp [kindOf] at h; rfl

theorem recT_fst {c : IConstantInfo} (h : kindOf c = 5) : (recT c).1 = c.toConstantVal := by
  cases c <;> simp [kindOf] at h; rfl

set_option maxHeartbeats 8000000 in
/-- **`readBlock`**. -/
theorem rb_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RBCodes C)
    (blk : List IConstantInfo) (ob nPd : Nat) (hlen : blk.length < 2 ^ 59) (hnP : nPd < 2 ^ 59)
    (hlp : ∀ i (hi : i < blk.length), blk[i].toConstantVal.levelParams.length < 2 ^ 59)
    (hA : denoteN C.St.ns anonH = some .anonymous)
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H)))
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hblk : IndBlk C H ob blk) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rbParams.zip [cellA C ob, BitVec.ofNat 64 nPd])) (rbBody C) s
      (unwrapE (readBlock nPd blk)) (PostRB (ctxH C H)) := by
  refine specR_prologue (postRB_locals _) (rb_none _ _) ?_
  obtain ⟨os, hosl, hblkp, hcie⟩ := id hblk
  let Γ0 : Env := ctxEnv (ctxH C H) ++ rbParams.zip [cellA C ob, BitVec.ofNat 64 nPd]
  have vP : Γ0.get rbP = some (cellA C ob) := by simp +decide [Γ0, Env.get, rbParams, ctxEnv]
  have vNP : Γ0.get rbNP = some (BitVec.ofNat 64 nPd) := by simp +decide [Γ0, Env.get, rbParams, ctxEnv]
  have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ rbLocals → z ∉ rbLocals →
      Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
    have hne : z ≠ x := fun e => hz (e ▸ hx)
    simp only [Env.get_cons, hne, ite_false]
  have pk : ∀ (Γ : Env), (∀ z, z ∉ rbLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ rbParams → ∀ v,
      Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
    have hyl : y ∉ rbLocals := by
      simp only [rbParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl <;> decide
    simp only [sev, sev_vv, hΓ y hyl, h]
  have hn0 : (ctxH C H).H[ob]? = some (BitVec.ofNat 64 blk.length) := by
    show H[ob]? = _; rw [hblkp.1]; simp [hosl]
  refine UD.specR_heapLoadI' (C := ctxH C H) rbN (vv rbP) ob _ hn0 (by simp +decide [ctxLocals, rbLocals])
    (by simp only [sev, sev_vv, vP]; rfl) ?_
  let Γ1 : Env := (rbN, BitVec.ofNat 64 blk.length) :: Γ0
  have hΓ1 : ∀ z, z ∉ rbLocals → Γ1.get z = Γ0.get z := fun z hz => cnl (by decide) hz
  have gP1 := pk Γ1 hΓ1 rbP (by decide) _ vP
  have gN1 : sev Γ1 (vv rbN) = some (BitVec.ofNat 64 blk.length) := by simp [Γ1, sev, Env.get_cons]
  -- the types' run
  let K := runEnd blk 3 (blk.length - 0) 0
  obtain ⟨-, hK, h3, h3n⟩ := runEnd_spec blk 3 (blk.length - 0) 0 (by omega) (by omega)
  refine specR_congr (m' := (pure K : AM Nat) >>= fun _ => unwrapE (readBlock nPd blk)) (by simp) ?_
  refine rb_tagRun C hc blk ob 3 0 (by decide) hlen (by omega) H s hp hblk rbK _ (by simp +decide [ctxLocals, rbLocals])
    ⟨gP1, rfl, gN1, rfl, trivial⟩ (fun H1 hp1 => ?_)
  let Γ2 : Env := (rbK, BitVec.ofNat 64 K) :: Γ1
  have hΓ2 : ∀ z, z ∉ rbLocals → Γ2.get z = Γ0.get z := fun z hz => by
    simp only [Γ2]; rw [cnl (by decide) hz]; exact hΓ1 z hz
  have gK2 : sev Γ2 (vv rbK) = some (BitVec.ofNat 64 K) := by simp [Γ2, sev, Env.get_cons]
  have gN2 : sev Γ2 (vv rbN) = some (BitVec.ofNat 64 blk.length) := by simp +decide [Γ2, Γ1, sev, Env.get_cons]
  have hb1 : IndBlk C H1 ob blk := indBlk_mono hblk hp1
  -- the constructors' run
  let E := runEnd blk 4 (blk.length - K) K
  obtain ⟨hKE, hE, h4, h4n⟩ := runEnd_spec blk 4 (blk.length - K) K (by omega) hK
  refine specR_congr (m' := (pure E : AM Nat) >>= fun _ => unwrapE (readBlock nPd blk)) (by simp) ?_
  refine rb_tagRun C hc blk ob 4 K (by decide) hlen hK H1 s (hp.trans hp1) hb1 rbE _ (by simp +decide [ctxLocals, rbLocals])
    ⟨pk Γ2 hΓ2 rbP (by decide) _ vP, gK2, gN2, rfl, trivial⟩ (fun H2 hp2 => ?_)
  let Γ3 : Env := (rbE, BitVec.ofNat 64 E) :: Γ2
  have hΓ3 : ∀ z, z ∉ rbLocals → Γ3.get z = Γ0.get z := fun z hz => by
    simp only [Γ3]; rw [cnl (by decide) hz]; exact hΓ2 z hz
  have gE3 : sev Γ3 (vv rbE) = some (BitVec.ofNat 64 E) := by simp [Γ3, sev, Env.get_cons]
  have gN3 : sev Γ3 (vv rbN) = some (BitVec.ofNat 64 blk.length) := by simp +decide [Γ3, Γ2, Γ1, sev, Env.get_cons]
  have gK3 : sev Γ3 (vv rbK) = some (BitVec.ofNat 64 K) := by simp +decide [Γ3, Γ2, sev, Env.get_cons]
  have hb2 : IndBlk C H2 ob blk := indBlk_mono hb1 hp2
  -- the recursors' run
  let F := runEnd blk 5 (blk.length - E) E
  obtain ⟨hEF, hF, h5, -⟩ := runEnd_spec blk 5 (blk.length - E) E (by omega) hE
  refine specR_congr (m' := (pure F : AM Nat) >>= fun _ => unwrapE (readBlock nPd blk)) (by simp) ?_
  refine rb_tagRun C hc blk ob 5 E (by decide) hlen hE H2 s ((hp.trans hp1).trans hp2) hb2 rbF _
    (by simp +decide [ctxLocals, rbLocals]) ⟨pk Γ3 hΓ3 rbP (by decide) _ vP, gE3, gN3, rfl, trivial⟩ (fun H3 hp3 => ?_)
  let Γ4 : Env := (rbF, BitVec.ofNat 64 F) :: Γ3
  have hΓ4 : ∀ z, z ∉ rbLocals → Γ4.get z = Γ0.get z := fun z hz => by
    simp only [Γ4]; rw [cnl (by decide) hz]; exact hΓ3 z hz
  have hb3 : IndBlk C H3 ob blk := indBlk_mono hb2 hp3
  have hp03 : C.H <+: H3 := ((hp.trans hp1).trans hp2).trans hp3
  -- the guards
  refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (Γ := Γ4) (x := F) (y := blk.length) (by omega) (by omega)
    (by simp [Γ4, sev, Env.get_cons]) (by simp +decide [Γ4, Γ3, Γ2, Γ1, sev, Env.get_cons])) (fun hFn => ?_)
    (fun _ => specR_hangI)
  have hFl : F = blk.length := by by_cases c : F = blk.length; exact c; simp [boolW, c] at hFn
  refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (Γ := Γ4) (x := K) (y := 0) (by omega) (by omega)
    (by simp +decide [Γ4, Γ3, Γ2, sev, Env.get_cons]) rfl) (fun _ => specR_hangI) (fun hK0 => ?_)
  have hKp : 0 < K := by by_cases c : K = 0; simp [boolW, c] at hK0; omega
  refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (Γ := Γ4) (x := E) (y := blk.length) (by omega) (by omega)
    (by simp +decide [Γ4, Γ3, sev, Env.get_cons]) (by simp +decide [Γ4, Γ3, Γ2, Γ1, sev, Env.get_cons]))
    (fun _ => specR_hangI) (fun hEn => ?_)
  have hEl : E < blk.length := by by_cases c : E = blk.length; simp [boolW, c] at hEn; omega
  -- the split, and `readBlock` flattened
  let nC := E - K
  have hKnC : K + nC = E := by omega
  obtain ⟨b0, bs, hbl⟩ : ∃ b0 bs, blk = b0 :: bs := by
    cases e : blk with
    | nil => simp [e] at hEl
    | cons b0 bs => exact ⟨b0, bs, rfl⟩
  have hc0 : (blk.take K).map (·.toConstantVal) = blk[0].toConstantVal :: ((blk.take K).drop 1).map (·.toConstantVal) := by
    subst hbl; obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [hK']; simp
  have hr0 : ((blk.drop K).drop nC).map recT = recT blk[E] :: (blk.drop (E + 1)).map recT := by
    rw [List.drop_drop, show K + nC = E by omega, List.drop_eq_getElem_cons hEl, List.map_cons]
  have htw := rb_twin nPd blk K nC (by omega) (fun i hi => by simpa using h3 i (by omega) hi) h3n
    (fun i hi => h4 (K + i) (by omega) (by omega)) (by rw [hKnC]; exact h4n)
    (fun i hi hil => h5 i (by omega) (by omega)) _ _ hc0 _ _ hr0
  rw [htw]
  have hname : ∀ (c : IConstantInfo), c.toConstantVal.name = c.name := fun c => by cases c <;> rfl
  have hbm : unwrapE (blockMemberCounts nPd (blk[0].toConstantVal :: ((blk.take K).drop 1).map (·.toConstantVal)).length
      (((blk.drop K).take nC).map ctorT).length
      ((blk[0].toConstantVal :: ((blk.take K).drop 1).map (·.toConstantVal)).map (·.name))
      (recT blk[E] :: (blk.drop (E + 1)).map recT) 0 (blk[0].toConstantVal :: ((blk.take K).drop 1).map (·.toConstantVal))) =
      unwrapE (blockMemberCounts nPd K nC (recNames blk K) ((blk.drop (K + nC)).map recT) 0
        (((blk.take K).drop 0).map (·.toConstantVal))) := by
    rw [← hc0, ← hr0, List.drop_drop]
    simp only [List.length_map, List.length_take, List.length_drop, List.map_map, List.drop_zero, recNames]
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    congr 2
    congr 1; funext c; exact hname c
  rw [hbm]
  -- nC, nR
  have gE4 : sev Γ4 (vv rbE) = some (BitVec.ofNat 64 E) := by simp +decide [Γ4, Γ3, sev, Env.get_cons]
  have gK4 : sev Γ4 (vv rbK) = some (BitVec.ofNat 64 K) := by simp +decide [Γ4, Γ3, Γ2, sev, Env.get_cons]
  have gN4 : sev Γ4 (vv rbN) = some (BitVec.ofNat 64 blk.length) := by simp +decide [Γ4, Γ3, Γ2, Γ1, sev, Env.get_cons]
  refine specR_assignI rbC _ (BitVec.ofNat 64 nC) (by simp +decide [ctxLocals, rbLocals])
    (by simp only [sev] at gE4 gK4 ⊢; rw [gE4, gK4]; simp; exact ofNat_sub_small E K hKE (by omega)) ?_
  let nR := blk.length - E
  let Γ5 : Env := (rbC, BitVec.ofNat 64 nC) :: Γ4
  have gE5 : sev Γ5 (vv rbE) = some (BitVec.ofNat 64 E) := by simp +decide [Γ5, sev, Env.get_cons] at gE4 ⊢; exact gE4
  have gN5 : sev Γ5 (vv rbN) = some (BitVec.ofNat 64 blk.length) := by
    simp +decide [Γ5, sev, Env.get_cons] at gN4 ⊢; exact gN4
  refine specR_assignI rbR _ (BitVec.ofNat 64 nR) (by simp +decide [ctxLocals, rbLocals])
    (by simp only [sev] at gE5 gN5 ⊢; rw [gE5, gN5]; simp; exact ofNat_sub_small blk.length E (by omega) (by omega)) ?_
  let Γ6 : Env := (rbR, BitVec.ofNat 64 nR) :: Γ5
  have hΓ6 : ∀ z, z ∉ rbLocals → Γ6.get z = Γ0.get z := fun z hz => by
    simp only [Γ6, Γ5]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ4 z hz
  have gK6 : sev Γ6 (vv rbK) = some (BitVec.ofNat 64 K) := by simp +decide [Γ6, Γ5, sev, Env.get_cons] at gK4 ⊢; exact gK4
  -- the counts' array
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H3.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H3) rbA _ (K + 1) (by omega) (by simp +decide [ctxLocals, rbLocals])
    (fun v => by
      have h1 : sev ((rbA, v) :: Γ6) (vv rbK) = some (BitVec.ofNat 64 K) := by
        simp only [sev, sev_vv, Env.get_cons, show rbK ≠ rbA by decide, ite_false] at gK6 ⊢; exact gK6
      simp only [sev] at h1 ⊢; rw [h1]; simp; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H4 ws hp4 hws hroom4 => ?_)
  have hp4' : H3 <+: H4 := hp4
  have hl4 := hp4'.length_le
  have hroom4' : H4.length + (K + 1) ≤ C.HN := hroom4
  let oa := H4.length
  let Γ7 : Env := (rbA, cellA (ctxH C H3) oa) :: Γ6
  have hΓ7 : ∀ z, z ∉ rbLocals → Γ7.get z = Γ0.get z := fun z hz => by
    simp only [Γ7]; rw [cnl (by decide) hz]; exact hΓ6 z hz
  have hb4 : IndBlk C H4 ob blk := indBlk_mono hb3 hp4'
  have hp04 : C.H <+: H4 := hp03.trans hp4'
  refine specR_callNIG (C := ctxH C (H4 ++ ws)) rbX fBMC bmParams
    [vv rbP, .const 0, vv rbK, vv rbC, vv rbR, vv rbNP, vv rbA] bmBody
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 K, BitVec.ofNat 64 nC, BitVec.ofNat 64 nR, BitVec.ofNat 64 nPd,
      cellA C oa] (by decide) rfl (by simp +decide [ctxLocals, rbLocals]) hc.bm
    ⟨pk Γ7 hΓ7 rbP (by decide) _ vP, rfl, by simp +decide [Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons] <;> rfl,
      by simp +decide [Γ7, Γ6, Γ5, sev, Env.get_cons], by simp +decide [Γ7, Γ6, sev, Env.get_cons],
      pk Γ7 hΓ7 rbNP (by decide) _ vNP, by simp [Γ7, sev, Env.get_cons]; rfl, trivial⟩
    (fun ns w s' st => unwrapE (blockMemberCounts nPd K nC (recNames blk K) ((blk.drop (K + nC)).map recT) 0
        (((blk.take K).drop 0).map (·.toConstantVal))) s = .ok (ns, s') ∧ PostBM C H4 oa 0 ns w s' st)
    (fun ns w s' H' => H4 <+: H' ∧ (∀ i (hi : i < ns.length), H'[oa + 0 + i]? = some (BitVec.ofNat 64 ns[i])) ∧
      (∀ i (hi : i < ns.length), ns[i] < 2 ^ 63) ∧ ns.length = K)
    (fun ns w s' st ⟨hr, H', hp', hs', hcells, hbd⟩ => ⟨H', ⟨hp', hcells, hbd, by
      have := bmc_length _ _ _ _ _ _ _ _ _ _ hr; simp at this; omega⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu bmParams _ rfl hlk)
      (bm_spec C hok hc.bm hc.fr hc.bc hc.pbc hc.rt hc.sp hc.ga hc.ni blk ob K nC nR nPd oa H4 (by omega) hlen
        (by omega) (fun i hi hil => h5 i (by omega) (by omega)) hp04 hb4 K 0 H4 (H4 ++ ws) s (List.prefix_refl _)
        (List.prefix_append _ _) (by omega) (by simp [hws]; omega) (by omega) (by omega))))
    (fun nIdxs w s5 H5 ⟨hp5, hcells, hnb, hnl⟩ => ?_)
  have hp45 : H4 <+: H5 := hp5
  have hHH5 : H <+: H5 := ((((hp1.trans hp2).trans hp3).trans hp4').trans hp45)
  have hp05 : C.H <+: H5 := hp.trans hHH5
  have hb5 : IndBlk C H5 ob blk := indBlk_mono hblk hHH5
  let Γ8 : Env := (rbX, w) :: Γ7
  have hΓ8 : ∀ z, z ∉ rbLocals → Γ8.get z = Γ0.get z := fun z hz => by
    simp only [Γ8]; rw [cnl (by decide) hz]; exact hΓ7 z hz
  -- record 0 and its universe parameters
  have hos0 : 0 < os.length := by omega
  have hci0 := hcie 0 (by omega) hos0
  obtain ⟨-, ⟨wl, hwl, hel⟩, hty0⟩ := hci0.1
  obtain ⟨ol, rfl, hblkl⟩ := enlist_cell (C := C) hel
  have hq0 : (ctxH C H5).H[ob + 1]? = some (cellA C os[0]) := by
    show H5[ob + 1]? = _
    have := hblkp.2 0 (by simp; omega); simp at this; exact get_prefix this hHH5
  refine UD.specR_heapLoadI' (C := ctxH C H5) rbQ _ (ob + 1) _ hq0 (by simp +decide [ctxLocals, rbLocals])
    (by
      have gP := pk Γ8 hΓ8 rbP (by decide) _ vP
      have e : sev Γ8 (.op .add [vv rbP, .const 8]) = some (cellA C (ob + 1)) := by
        simp only [sev] at gP ⊢; rw [gP]; simp; exact cellA_add8 C ob
      exact e) ?_
  let Γ9 : Env := (rbQ, cellA C os[0]) :: Γ8
  have hΓ9 : ∀ z, z ∉ rbLocals → Γ9.get z = Γ0.get z := fun z hz => by
    simp only [Γ9]; rw [cnl (by decide) hz]; exact hΓ8 z hz
  have hsQ : ∀ (Γ : Env), Γ.get rbQ = some (cellA C os[0]) → ∀ q, sev Γ (.op .add [vv rbQ,
      .const (BitVec.ofNat 64 (8 * q))]) = some (cellA C (os[0] + q)) := by
    intro Γ hq q; simp only [sev, sev_vv, hq]; simp; exact cellA_plus C _ q
  have hl0 : (ctxH C H5).H[os[0] + 2]? = some (cellA C ol) := by
    show H5[os[0] + 2]? = _
    rw [show os[0] + 2 = os[0] + 1 + 1 by omega]; exact get_prefix hwl hHH5
  refine UD.specR_heapLoadI' (C := ctxH C H5) rbL _ (os[0] + 2) _ hl0 (by simp +decide [ctxLocals, rbLocals])
    (hsQ Γ9 (by simp [Γ9, Env.get_cons]) 2) ?_
  let lps0 := blk[0].toConstantVal.levelParams
  have hbl5 : EBlk H5 ol (lps0.map Enc.idxW) := eblk_mono hblkl hHH5
  have hl0len : lps0.length < 2 ^ 59 := hlp 0 (by omega)
  let Γ10 : Env := (rbL, cellA C ol) :: Γ9
  have hΓ10 : ∀ z, z ∉ rbLocals → Γ10.get z = Γ0.get z := fun z hz => by
    simp only [Γ10]; rw [cnl (by decide) hz]; exact hΓ9 z hz
  have gK10 : sev Γ10 (vv rbK) = some (BitVec.ofNat 64 K) := by
    simp +decide [Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons] <;> rfl
  have gE10 : sev Γ10 (vv rbE) = some (BitVec.ofNat 64 E) := by
    simp +decide [Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, sev, Env.get_cons] <;> rfl
  -- the types' universe parameters
  let b1 := ((blk.drop 0).take (K - 0)).all (lpsOk lps0 false nPd)
  refine specR_pureBind b1 ?_
  refine specR_callNIH (C := ctxH C H5) rbX fAllLps alParams [vv rbP, .const 0, vv rbK, vv rbL, .const 0, vv rbNP]
    alBody [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 K, cellA C ol, 0, BitVec.ofNat 64 nPd] (by decide) rfl
    (by simp +decide [ctxLocals, rbLocals]) hc.al
    ⟨pk Γ10 hΓ10 rbP (by decide) _ vP, rfl, gK10, by simp [Γ10, sev, Env.get_cons], rfl,
      pk Γ10 hΓ10 rbNP (by decide) _ vNP, trivial⟩
    (fun b w s' st => (pure b1 : AM Bool) s5 = .ok (b, s') ∧ PostB (ctxH C H5) b w s' st)
    (fun b w s' H' => w = boolW b ∧ b = b1 ∧ s' = s5)
    (fun b w s' st ⟨hr, H', hp', hw, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact ⟨H', hp', ⟨hw, hr.1.symm, hr.2.symm⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu alParams _ rfl hlk)
      (al_spec C hc.al hc.le hc.leg blk ob ol K nPd lps0 false (by omega) hlen hl0len (by omega) hlp (K - 0) 0 H5 s5
        hp05 hb5 hbl5 rfl (by omega) (fun h => absurd h (by decide)))))
    (fun b w s6 H6 hp6 ⟨hw, hb, hs6⟩ => ?_)
  subst hw; subst hb; subst hs6
  have hp56 : H5 <+: H6 := hp6
  let Γ11 : Env := (rbX, boolW b1) :: Γ10
  have hΓ11 : ∀ z, z ∉ rbLocals → Γ11.get z = Γ0.get z := fun z hz => by
    simp only [Γ11]; rw [cnl (by decide) hz]; exact hΓ10 z hz
  refine specR_ifI _ _ (sev_ne0 (Γ := Γ11) (x := rbX) (b := b1) (by simp [Γ11, sev, Env.get_cons]))
    (fun hb1 => ?_) (fun _ => specR_hangI)
  have hb1t : b1 = true := by cases e : b1; simp [e, boolW] at hb1; rfl
  have hA1 : ((blk[0].toConstantVal :: ((blk.take K).drop 1).map (·.toConstantVal)).all
      fun c => c.levelParams == blk[0].toConstantVal.levelParams) = true := by
    rw [← hc0, List.all_map]
    have : b1 = (blk.take K).all (lpsOk lps0 false nPd) := by simp [b1]
    rw [this] at hb1t
    simpa [lpsOk, Function.comp_def] using hb1t
  simp only [hA1, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the constructors' universe parameters and parameter count
  have hb6 : IndBlk C H6 ob blk := indBlk_mono hb5 hp56
  have hp06 : C.H <+: H6 := hp05.trans hp56
  let b2 := ((blk.drop K).take (E - K)).all (lpsOk lps0 true nPd)
  refine specR_pureBind b2 ?_
  refine specR_callNIH (C := ctxH C H6) rbX fAllLps alParams [vv rbP, vv rbK, vv rbE, vv rbL, .const 1, vv rbNP]
    alBody [cellA C ob, BitVec.ofNat 64 K, BitVec.ofNat 64 E, cellA C ol, 1, BitVec.ofNat 64 nPd] (by decide) rfl
    (by simp +decide [ctxLocals, rbLocals]) hc.al
    ⟨pk Γ11 hΓ11 rbP (by decide) _ vP, by simp +decide [Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons] <;> rfl,
      by simp +decide [Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, sev, Env.get_cons] <;> rfl, by simp +decide [Γ11, Γ10, sev, Env.get_cons], rfl,
      pk Γ11 hΓ11 rbNP (by decide) _ vNP, trivial⟩
    (fun b w s' st => (pure b2 : AM Bool) s6 = .ok (b, s') ∧ PostB (ctxH C H6) b w s' st)
    (fun b w s' H' => w = boolW b ∧ b = b2 ∧ s' = s6)
    (fun b w s' st ⟨hr, H', hp', hw, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact ⟨H', hp', ⟨hw, hr.1.symm, hr.2.symm⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu alParams _ rfl hlk)
      (al_spec C hc.al hc.le hc.leg blk ob ol E nPd lps0 true (by omega) hlen hl0len (by omega) hlp (E - K) K H6 s6
        hp06 hb6 (eblk_mono hbl5 hp56) rfl hKE (fun _ i h1 h2 => h4 i h1 h2))))
    (fun b w s7 H7 hp7 ⟨hw, hb, hs7⟩ => ?_)
  subst hw; subst hb; subst hs7
  have hp67 : H6 <+: H7 := hp7
  let Γ12 : Env := (rbX, boolW b2) :: Γ11
  have hΓ12 : ∀ z, z ∉ rbLocals → Γ12.get z = Γ0.get z := fun z hz => by
    simp only [Γ12]; rw [cnl (by decide) hz]; exact hΓ11 z hz
  refine specR_ifI _ _ (sev_ne0 (Γ := Γ12) (x := rbX) (b := b2) (by simp [Γ12, sev, Env.get_cons]))
    (fun hb2 => ?_) (fun _ => specR_hangI)
  have hb2t : b2 = true := by cases e : b2; simp [e, boolW] at hb2; rfl
  have hk4 := kinds_mem (blk := blk) (K := K) (n := E) (t := 4) h4 hE
  have hall := List.all_eq_true.mp hb2t
  have hB : ((((blk.drop K).take nC).map ctorT).all fun c => c.2.1 == nPd) = true := by
    rw [List.all_map]; apply List.all_eq_true.mpr; intro x hx
    have := hall x hx; simp [lpsOk] at this; simp [this.2]
  have hCc : ((((blk.drop K).take nC).map ctorT).all fun c => c.1.levelParams == blk[0].toConstantVal.levelParams) = true := by
    rw [List.all_map]; apply List.all_eq_true.mpr; intro x hx
    have := hall x hx; simp [lpsOk] at this
    simp [ctorT_fst (hk4 x hx), this.1, lps0]
  simp only [hB, hCc, Bool.not_true, Bool.false_eq_true, ite_false]
  -- `rbTail`, at the block's indices
  rw [← hc0, ← hr0]
  have e1 : ((blk.take K).map (·.toConstantVal)).map (·.name) = (blk.take K).map (fun (c : IConstantInfo) => c.name) := by
    rw [List.map_map]; congr 1; funext c; exact hname c
  have e2 : ((blk.take K).map (·.toConstantVal)).length = K := by simp; omega
  have e3 : (((blk.drop K).take nC).map ctorT).map (fun c => (c.1, c.2.2)) = ((blk.drop K).take nC).map ctorPair := by
    rw [List.map_map]; rfl
  have e4 : ((blk.drop K).drop nC).map recT = (blk.drop E).map recT := by rw [List.drop_drop, hKnC]
  obtain ⟨n0, ns', hns⟩ : ∃ n0 ns', nIdxs = n0 :: ns' := by
    cases e : nIdxs with
    | nil => rw [e] at hnl; simp at hnl; omega
    | cons n0 ns' => exact ⟨n0, ns', rfl⟩
  have hhd : nIdxs.headD 0 = n0 := by rw [hns]; rfl
  have hn0b : n0 < 2 ^ 63 := by have := hnb 0 (by omega); simpa [hns] using this
  simp only [rbTail, e1, e2, e3, e4, hhd]
  have hp57 : H5 <+: H7 := hp56.trans hp67
  have hHH7 : H <+: H7 := hHH5.trans hp57
  have hp07 : C.H <+: H7 := hp.trans hHH7
  have hb7 : IndBlk C H7 ob blk := indBlk_mono hblk hHH7
  -- the type, the first index count, the result sort
  have hty7 : (ctxH C H7).H[os[0] + 3]? = some (Enc.idxW blk[0].toConstantVal.type) := by
    show H7[os[0] + 3]? = _; rw [show os[0] + 3 = os[0] + 1 + 2 by omega]; exact get_prefix hty0 hHH7
  refine UD.specR_heapLoadI' (C := ctxH C H7) rbT _ (os[0] + 3) _ hty7 (by simp +decide [ctxLocals, rbLocals])
    (hsQ _ (by simp +decide [Γ12, Γ11, Γ10, Γ9, Env.get_cons]) 3) ?_
  have hi7 : (ctxH C H7).H[oa]? = some (BitVec.ofNat 64 n0) := by
    show H7[oa]? = _
    have := hcells 0 (by omega); simp only [Nat.add_zero, hns, List.getElem_cons_zero] at this
    exact get_prefix this hp57
  refine UD.specR_heapLoadI' (C := ctxH C H7) rbI (vv rbA) oa _ hi7 (by simp +decide [ctxLocals, rbLocals])
    (by simp +decide [Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, sev, Env.get_cons]; rfl) ?_
  let Γ13 : Env := (rbI, BitVec.ofNat 64 n0) :: (rbT, Enc.idxW blk[0].toConstantVal.type) :: Γ12
  have hΓ13 : ∀ z, z ∉ rbLocals → Γ13.get z = Γ0.get z := fun z hz => by
    simp only [Γ13]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ12 z hz
  have gNP13 := pk Γ13 hΓ13 rbNP (by decide) _ vNP
  refine specR_callNIH (C := ctxH C H7) rbS fResSort rsParams [.op .add [vv rbNP, vv rbI], vv rbT] (rsBody C)
    [BitVec.ofNat 64 (nPd + n0), Enc.idxW blk[0].toConstantVal.type] (by decide) rfl
    (by simp +decide [ctxLocals, rbLocals]) hc.rs
    ⟨by
      have e : sev Γ13 (.op .add [vv rbNP, vv rbI]) = some (BitVec.ofNat 64 (nPd + n0)) := by
        simp only [sev] at gNP13 ⊢; rw [gNP13]; simp [Γ13, Env.get_cons]; exact ofNat_add_small nPd n0 (by omega)
      exact e, by simp +decide [Γ13, sev, Env.get_cons], trivial⟩
    (PostRS (ctxH C H7)) (fun u w s' _ => w = Enc.idxW u ∧ (denoteL s'.store.ls u).isSome = true)
    (fun u w s' st ⟨H', hp', hw, hsr, hd⟩ => ⟨H', hp', ⟨hw, hd⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rsParams _ rfl hlk)
      (rs_spec C hok hc.sp (nPd + n0) (by omega) blk[0].toConstantVal.type H7 s7))
    (fun us ws8 s8 H8 hp8 ⟨hws8, hden⟩ => ?_)
  subst hws8
  have hp78 : H7 <+: H8 := hp8
  have hp08 : C.H <+: H8 := hp07.trans hp78
  let Γ14 : Env := (rbS, Enc.idxW us) :: Γ13
  have hΓ14 : ∀ z, z ∉ rbLocals → Γ14.get z = Γ0.get z := fun z hz => by
    simp only [Γ14]; rw [cnl (by decide) hz]; exact hΓ13 z hz
  -- the flag
  refine specR_callNIH (C := ctxH C H8) rbIP fIsPropL ipParams [vv rbS] (ipBody C) [Enc.idxW us] (by decide) rfl
    (by simp +decide [ctxLocals, rbLocals]) hc.ip ⟨by simp [Γ14, sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H8)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipParams _ rfl hlk)
      (ip_spec C hok hc.eqv H8 s8 us hden (fun hz => hLE H8 s8 us C.pins.zeroLevel hp08 hden hz)))
    (fun ipb wip s9 H9 hp9 hwip => ?_)
  subst hwip
  have hp89 : H8 <+: H9 := hp9
  have hHH9 : H <+: H9 := (hHH7.trans hp78).trans hp89
  have hp09 : C.H <+: H9 := hp.trans hHH9
  let Γ15 : Env := (rbIP, boolW ipb) :: Γ14
  have hΓ15 : ∀ z, z ∉ rbLocals → Γ15.get z = Γ0.get z := fun z hz => by
    simp only [Γ15]; rw [cnl (by decide) hz]; exact hΓ14 z hz
  -- the block's own universe arguments
  have hbl9 : EBlk H9 ol (lps0.map Enc.idxW) := eblk_mono hblkl hHH9
  refine specR_callNIH (C := ctxH C H9) rbLV fParamLevels plParams [vv rbL] (plBody C) [cellA C ol] (by decide) rfl
    (by simp +decide [ctxLocals, rbLocals]) hc.pl ⟨by simp +decide [Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, sev, Env.get_cons], trivial⟩
    (PostLsH (ctxH C H9)) (fun h w _ _ => w = Enc.idxW h) (fun h w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
      (pl_spec ra C hok hc.pl hc.pf hc.ilp hc.ils lps0 ol hl0len H9 s9 hbl9))
    (fun lvls wlv s10 H10 hp10 hwlv => ?_)
  subst hwlv
  have hp910 : H9 <+: H10 := hp10
  have hHH10 : H <+: H10 := hHH9.trans hp910
  have hp010 : C.H <+: H10 := hp.trans hHH10
  let Γ16 : Env := (rbLV, Enc.idxW lvls) :: Γ15
  have hΓ16 : ∀ z, z ∉ rbLocals → Γ16.get z = Γ0.get z := fun z hz => by
    simp only [Γ16]; rw [cnl (by decide) hz]; exact hΓ15 z hz
  -- the groups
  refine specR_callNIH (C := ctxH C H10) rbG fBlockGroups bgParams [vv rbP, vv rbK, vv rbC, vv rbLV, vv rbNP] (bgBody C)
    [cellA C ob, BitVec.ofNat 64 K, BitVec.ofNat 64 nC, Enc.idxW lvls, BitVec.ofNat 64 nPd] (by decide) rfl
    (by simp +decide [ctxLocals, rbLocals]) hc.bg
    ⟨pk Γ16 hΓ16 rbP (by decide) _ vP,
      by simp +decide [Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons] <;> rfl,
      by simp +decide [Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, sev, Env.get_cons],
      by simp [Γ16, sev, Env.get_cons], pk Γ16 hΓ16 rbNP (by decide) _ vNP, trivial⟩
    (fun gs w s' st => blockGroups ((blk.take K).map (fun (c : IConstantInfo) => c.name)) lvls nPd K
        (((blk.drop K).take nC).map ctorPair) s10 = .ok (gs, s') ∧ PostBG (ctxH C H10) gs w s' st)
    (fun gs w s' H' => gs.length = K ∧ ∃ og, w = cellA C og ∧ PtrsRep C H' og (fun og' cs => CtorsRep C H' og' cs) gs)
    (fun gs w s' st ⟨hr, H', hp', hsr, og, hw, hpr⟩ => ⟨H', hp', ⟨bg_len _ _ _ _ _ _ _ _ hr, og, hw, hpr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu bgParams _ rfl hlk)
      (bg_spec C hok hc.bg hc.bo hc.gf hc.cm hc.sp hc.ga hc.mi hc.ni blk ob K nC nPd lvls (by omega) hlen hnP
        (fun i h1 h2 => h4 i h1 (by omega)) H10 s10 hp010 (indBlk_mono hblk hHH10))))
    (fun gs wg s11 H11 hp11 ⟨hgl, og, hwg, hgs⟩ => ?_)
  subst hwg
  have hp1011 : H10 <+: H11 := hp11
  have hHH11 : H <+: H11 := hHH10.trans hp1011
  have hp011 : C.H <+: H11 := hp.trans hHH11
  let Γ17 : Env := (rbG, cellA C og) :: Γ16
  have hΓ17 : ∀ z, z ∉ rbLocals → Γ17.get z = Γ0.get z := fun z hz => by
    simp only [Γ17]; rw [cnl (by decide) hz]; exact hΓ16 z hz
  have gK17 : sev Γ17 (vv rbK) = some (BitVec.ofNat 64 K) := by
    simp +decide [Γ17, Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons] <;> rfl
  -- the members
  let ms := memberList blk K nIdxs gs
  refine specR_pureBind ms ?_
  refine specR_callNIH (C := ctxH C H11) rbMS fMembersOf moParams [vv rbP, vv rbK, vv rbA, vv rbG] (moBody C)
    [cellA C ob, BitVec.ofNat 64 K, cellA C oa, cellA C og] (by decide) rfl (by simp +decide [ctxLocals, rbLocals]) hc.mo
    ⟨pk Γ17 hΓ17 rbP (by decide) _ vP, gK17,
      by simp +decide [Γ17, Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, sev, Env.get_cons]; rfl,
      by simp [Γ17, sev, Env.get_cons], trivial⟩
    (fun a w s' st => (pure ms : AM (List MemberShape)) s11 = .ok (a, s') ∧ PostMO (ctxH C H11) a w s' st)
    (fun a w s' H' => a = ms ∧ s' = s11 ∧ ∃ om, w = cellA C om ∧ PtrsRep C H' om (fun om' m => MemberRep C H' om' m) a)
    (fun a w s' st ⟨hr, H', hp', hsr, om, hw, hpr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact ⟨H', hp', ⟨hr.1.symm, hr.2.symm, om, hw, hpr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu moParams _ rfl hlk)
      (mo_spec C hok hc.mo hc.mf blk ob K oa og nIdxs gs (by omega) hlen hnl hgl H11 s11 hp011
        (indBlk_mono hblk hHH11)
        (fun i hi => by have := hcells i (by omega); simp only [Nat.add_zero] at this
                        exact get_prefix this ((((hp56.trans hp67).trans hp78).trans hp89).trans hp910 |>.trans hp1011))
        hgs)))
    (fun a wm s12 H12 hp12 ⟨ha, hs12, om, hwm, hms⟩ => ?_)
  subst ha; subst hs12; subst hwm
  have hp1112 : H11 <+: H12 := hp12
  have hHH12 : H <+: H12 := hHH11.trans hp1112
  have hp012 : C.H <+: H12 := hp.trans hHH12
  let Γ18 : Env := (rbMS, cellA C om) :: Γ17
  have hΓ18 : ∀ z, z ∉ rbLocals → Γ18.get z = Γ0.get z := fun z hz => by
    simp only [Γ18]; rw [cnl (by decide) hz]; exact hΓ17 z hz
  -- the recursors
  refine specR_callNIH (C := ctxH C H12) rbRC fRecShapes rhParams [vv rbP, vv rbE, vv rbN, vv rbK] (rhBody C)
    [cellA C ob, BitVec.ofNat 64 E, BitVec.ofNat 64 blk.length, BitVec.ofNat 64 K] (by decide) rfl
    (by simp +decide [ctxLocals, rbLocals]) hc.rh
    ⟨pk Γ18 hΓ18 rbP (by decide) _ vP,
      by simp +decide [Γ18, Γ17, Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, sev, Env.get_cons] <;> rfl,
      by simp +decide [Γ18, Γ17, Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, Γ1, sev, Env.get_cons],
      by simp +decide [Γ18, Γ17, Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, Γ2, sev, Env.get_cons] <;> rfl,
      trivial⟩
    (PostRH (ctxH C H12)) (fun rcs w _ H' => ∃ orc, w = cellA C orc ∧ PtrsRep C H' orc (fun og' r => RecRep C H' og' r) rcs)
    (fun rcs w s' st ⟨H', hp', hsr, orc, hw, hpr⟩ => ⟨H', hp', ⟨orc, hw, hpr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rhParams _ rfl hlk)
      (rh_spec C hok hc.rh hc.rc hc.rt hc.sp hc.ga hc.ni blk ob K E (by omega) (by omega) hlen
        (fun i h1 h2 => h5 i h1 (by omega)) H12 s12 hp012 (indBlk_mono hblk hHH12)))
    (fun recsL wr s13 H13 hp13 ⟨orc, hwr, hrcs⟩ => ?_)
  subst hwr
  have hp1213 : H12 <+: H13 := hp13
  have hHH13 : H <+: H13 := hHH12.trans hp1213
  have hp013 : C.H <+: H13 := hp.trans hHH13
  let Γ19 : Env := (rbRC, cellA C orc) :: Γ18
  have hΓ19 : ∀ z, z ∉ rbLocals → Γ19.get z = Γ0.get z := fun z hz => by
    simp only [Γ19]; rw [cnl (by decide) hz]; exact hΓ18 z hz
  -- the first recursor's universe parameters
  have hoE : E < os.length := by omega
  have hk5 : kindOf blk[E] = 5 := by
    have := h5 E (by omega) (by omega)
    simp only [kindAt, List.getElem?_eq_getElem hEl] at this; simpa using this
  obtain ⟨-, ⟨wrl, hwrl, herl⟩, -⟩ := (hcie E hEl hoE).1
  obtain ⟨orl, rfl, hblr⟩ := enlist_cell (C := C) herl
  let rl := blk[E].toConstantVal.levelParams
  have hqE : (ctxH C H13).H[ob + 1 + E]? = some (cellA C os[E]) := by
    show H13[ob + 1 + E]? = _
    have := hblkp.2 E (by simp; omega); simp at this; exact get_prefix this hHH13
  refine UD.specR_heapLoadI' (C := ctxH C H13) rbQ _ (ob + 1 + E) _ hqE (by simp +decide [ctxLocals, rbLocals])
    (by
      have gP := pk Γ19 hΓ19 rbP (by decide) _ vP
      have gE : sev Γ19 (vv rbE) = some (BitVec.ofNat 64 E) := by
        simp +decide [Γ19, Γ18, Γ17, Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, Γ4, Γ3, sev, Env.get_cons] <;> rfl
      have e : sev Γ19 (.op .add [vv rbP, .op .add [.panop .mul [vv rbE, .const 8], .const 8]]) =
          some (cellA C (ob + 1 + E)) := by
        simp only [sev] at gP gE ⊢; rw [gP, gE]; simp; exact cellA_mulIdx C ob E (by omega)
      exact e) ?_
  have hlr : (ctxH C H13).H[os[E] + 2]? = some (cellA C orl) := by
    show H13[os[E] + 2]? = _; rw [show os[E] + 2 = os[E] + 1 + 1 by omega]; exact get_prefix hwrl hHH13
  have hsQE : ∀ (Γ : Env), Γ.get rbQ = some (cellA C os[E]) → ∀ q, sev Γ (.op .add [vv rbQ,
      .const (BitVec.ofNat 64 (8 * q))]) = some (cellA C (os[E] + q)) := by
    intro Γ hq q; simp only [sev, sev_vv, hq]; simp; exact cellA_plus C _ q
  refine UD.specR_heapLoadI' (C := ctxH C H13) rbLR _ (os[E] + 2) _ hlr (by simp +decide [ctxLocals, rbLocals])
    (hsQE _ (by simp [Env.get_cons]) 2) ?_
  let Γ20 : Env := (rbLR, cellA C orl) :: (rbQ, cellA C os[E]) :: Γ19
  have hΓ20 : ∀ z, z ∉ rbLocals → Γ20.get z = Γ0.get z := fun z hz => by
    simp only [Γ20]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ19 z hz
  have hbr13 : EBlk H13 orl (rl.map Enc.idxW) := eblk_mono hblr hHH13
  have hbl13 : EBlk H13 ol (lps0.map Enc.idxW) := eblk_mono hblkl hHH13
  have hrll : rl.length < 2 ^ 59 := hlp E hEl
  -- large?
  have er : (recT blk[E]).1 = blk[E].toConstantVal := recT_fst hk5
  simp only [er]
  let lgb := (largeT lps0 rl).isSome
  refine specR_pureBind lgb ?_
  refine specR_callNIH (C := ctxH C H13) rbLG fLargeChk lgParams [vv rbLR, vv rbL] lgBody [cellA C orl, cellA C ol]
    (by decide) rfl (by simp +decide [ctxLocals, rbLocals]) hc.lg
    ⟨by simp [Γ20, sev, Env.get_cons],
      by simp +decide [Γ20, Γ19, Γ18, Γ17, Γ16, Γ15, Γ14, Γ13, Γ12, Γ11, Γ10, sev, Env.get_cons], trivial⟩
    (fun b w s' st => (pure lgb : AM Bool) s13 = .ok (b, s') ∧ PostB (ctxH C H13) b w s' st)
    (fun b w s' H' => b = lgb ∧ s' = s13 ∧ w = boolW b)
    (fun b w s' st ⟨hr, H', hp', hw, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact ⟨H', hp', ⟨hr.1.symm, hr.2.symm, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu lgParams _ rfl hlk)
      (lg_spec C hc.lg hc.leg hc.lh rl lps0 orl ol hrll hl0len H13 s13 hp013 hbr13 hbl13)))
    (fun b wl s14 H14 hp14 ⟨hb, hs14, hwl⟩ => ?_)
  subst hb; subst hs14; subst hwl
  have hp1314 : H13 <+: H14 := hp14
  have hHH14 : H <+: H14 := hHH13.trans hp1314
  let Γ21 : Env := (rbLG, boolW lgb) :: Γ20
  have hΓ21 : ∀ z, z ∉ rbLocals → Γ21.get z = Γ0.get z := fun z hz => by
    simp only [Γ21]; rw [cnl (by decide) hz]; exact hΓ20 z hz
  have hms14 : PtrsRep C H14 om (fun om' m => MemberRep C H14 om' m) ms :=
    ptrsRep_mono (hp1213.trans hp1314) (fun _ _ h => memberRep_mono (hp1213.trans hp1314) h) hms
  have hrc14 : PtrsRep C H14 orc (fun og' r => RecRep C H14 og' r) recsL :=
    ptrsRep_mono hp1314 (fun _ _ h => recRep_mono hp1314 h) hrcs
  -- the shape block
  have shape : ∀ (el : NIdx) (lb : Bool) (Γ : Env), (∀ z, z ∉ rbLocals → Γ.get z = Γ0.get z) →
      Γ.get rbMS = some (cellA C om) → Γ.get rbRC = some (cellA C orc) → Γ.get rbEL = some (Enc.idxW el) →
      Γ.get rbS = some (Enc.idxW us) → Γ.get rbIP = some (boolW ipb) →
      SpecR (σ := σ) (Inv (ctxH C H14) s14 Γ [] (ctxLocals ++ rbLocals)) (rbShape C (.const (boolW lb))) s14
        (pure ⟨ms, recsL, nPd, el, us, lb, ipb⟩) (PostRB (ctxH C H)) := by
    intro el lb Γ hΓ gMS gRC gEL gS gIP
    refine specR_alloc7I (C := ctxH C H14) (ctxOK_H hok H14) rbO _ _ _ _ _ _ _ (cellA C om) (cellA C orc)
      (BitVec.ofNat 64 nPd) (Enc.idxW el) (Enc.idxW us) (boolW lb) (boolW ipb) (by simp +decide [ctxLocals, rbLocals])
      (fun v => by simp only [sev, sev_vv, Env.get_cons, show rbMS ≠ rbO by decide, ite_false, gMS])
      (fun v => by simp only [sev, sev_vv, Env.get_cons, show rbRC ≠ rbO by decide, ite_false, gRC])
      (fun v => pk ((rbO, v) :: Γ) (fun z hz => by rw [cnl (by decide) hz]; exact hΓ z hz) rbNP (by decide) _ vNP)
      (fun v => by simp only [sev, sev_vv, Env.get_cons, show rbEL ≠ rbO by decide, ite_false, gEL])
      (fun v => by simp only [sev, sev_vv, Env.get_cons, show rbS ≠ rbO by decide, ite_false, gS])
      (fun v => rfl)
      (fun v => by simp only [sev, sev_vv, Env.get_cons, show rbIP ≠ rbO by decide, ite_false, gIP])
      (fun H15 ws15 hp15 hws15 => ?_)
    have hp1415 : H14 <+: H15 := hp15
    let I7 := img7 H15 ws15 (cellA C om) (cellA C orc) (BitVec.ofNat 64 nPd) (Enc.idxW el) (Enc.idxW us) (boolW lb)
      (boolW ipb)
    have hI7 : H15 <+: I7 := img7_prefix _ _ _ _ _ _ _ _ _ hws15
    have hg := img7_get H15 ws15 (cellA C om) (cellA C orc) (BitVec.ofNat 64 nPd) (Enc.idxW el) (Enc.idxW us) (boolW lb)
      (boolW ipb) hws15
    have hpI : H14 <+: I7 := hp1415.trans hI7
    exact specR_returnI _ (cellA C H15.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨I7,
      hHH14.trans hpI, sr_of_eq ht.sr rfl rfl rfl rfl, H15.length, rfl,
      ⟨om, hg 0 (by decide), ptrsRep_mono hpI (fun _ _ h => memberRep_mono hpI h) hms14⟩,
      ⟨orc, hg 1 (by decide), ptrsRep_mono hpI (fun _ _ h => recRep_mono hpI h) hrc14⟩,
      ⟨hg 2 (by decide), show nPd < 2 ^ 63 by omega⟩, hg 3 (by decide), hg 4 (by decide), hg 5 (by decide), hg 6 (by decide)⟩)
  have gMS : Γ21.get rbMS = some (cellA C om) := by
    simp +decide [Γ21, Γ20, Γ19, Γ18, Env.get_cons]
  have gRC : Γ21.get rbRC = some (cellA C orc) := by simp +decide [Γ21, Γ20, Γ19, Env.get_cons]
  have gS : Γ21.get rbS = some (Enc.idxW us) := by
    simp +decide [Γ21, Γ20, Γ19, Γ18, Γ17, Γ16, Γ15, Γ14, Env.get_cons]
  have gIP : Γ21.get rbIP = some (boolW ipb) := by
    simp +decide [Γ21, Γ20, Γ19, Γ18, Γ17, Γ16, Γ15, Env.get_cons]
  refine specR_ifI _ _ (sev_ne0 (Γ := Γ21) (x := rbLG) (b := lgb) (by simp [Γ21, sev, Env.get_cons]))
    (fun hlg => ?_) (fun hlg => ?_)
  · -- large: the recursor's first parameter
    cases hL : largeT lps0 rl with
    | none => simp [lgb, hL, boolW] at hlg
    | some elim =>
      obtain ⟨rr, hrr⟩ := largeT_some hL
      have hel : (ctxH C H14).H[orl + 1]? = some (Enc.idxW elim) := by
        show H14[orl + 1]? = _
        have := hbr13.2 0 (by simp [hrr]); simp [hrr] at this; exact get_prefix this hp1314
      refine UD.specR_heapLoadI' (C := ctxH C H14) rbEL _ (orl + 1) _ hel (by simp +decide [ctxLocals, rbLocals])
        (by
          have e : sev Γ21 (.op .add [vv rbLR, .const 8]) = some (cellA C (orl + 1)) := by
            simp +decide [Γ21, Γ20, sev, Env.get_cons]; exact cellA_add8 C orl
          exact e) ?_
      simp only [lps0, rl] at hL
      simp only [hL]
      exact shape elim true ((rbEL, Enc.idxW elim) :: Γ21) (fun z hz => by rw [cnl (by decide) hz]; exact hΓ21 z hz)
        (by simp only [Env.get_cons, show rbMS ≠ rbEL by decide, ite_false, gMS])
        (by simp only [Env.get_cons, show rbRC ≠ rbEL by decide, ite_false, gRC]) (by simp [Env.get_cons])
        (by simp only [Env.get_cons, show rbS ≠ rbEL by decide, ite_false, gS])
        (by simp only [Env.get_cons, show rbIP ≠ rbEL by decide, ite_false, gIP])
  · -- small: the anonymous name
    have hL : largeT lps0 rl = none := by
      cases e : largeT lps0 rl with
      | none => rfl
      | some _ => simp [lgb, e, boolW] at hlg
    simp only [lps0, rl] at hL
    simp only [hL]
    refine specR_assignI rbEL (.const (Enc.idxW anonH)) (Enc.idxW anonH) (by simp +decide [ctxLocals, rbLocals]) rfl ?_
    refine specR_fact (fun t ht => internAnon_run ht.sr hA) (fun hrun => ?_)
    refine specR_runBind hrun ?_
    exact shape anonH false ((rbEL, Enc.idxW anonH) :: Γ21) (fun z hz => by rw [cnl (by decide) hz]; exact hΓ21 z hz)
      (by simp only [Env.get_cons, show rbMS ≠ rbEL by decide, ite_false, gMS])
      (by simp only [Env.get_cons, show rbRC ≠ rbEL by decide, ite_false, gRC]) (by simp [Env.get_cons])
      (by simp only [Env.get_cons, show rbS ≠ rbEL by decide, ite_false, gS])
      (by simp only [Env.get_cons, show rbIP ≠ rbEL by decide, ite_false, gIP])

end

end ConPanqueque.T.Ind
