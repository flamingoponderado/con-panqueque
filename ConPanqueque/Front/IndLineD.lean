import ConPanqueque.Front.IndLineC

/-! # The inductive line: one constructor

`ctorBody`: constructor record `J` of the block (its position from `fIndCtorsAt`), its name, type and
level parameters (`cvP`), its name against the type's `ctors[J]` (the block at `ilCB`), its `cidx`
(absent or `J`) and `induct` (absent or naming the type, `ilTh`), its counts (below `2⁵⁵`) and the
twin's `numFields` check against the type's telescope; then its stored constant
`[4, name, lps, type, numParams, numFields, T]` and the pointer to it in slot `J + 2` of the
pointer block at `ilOB`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec scanNatList IndTypeRec IndCtorRec IndRecRec RuleRec scanIndCtors scanIndCtor)

set_option autoImplicit false

variable {σ : Type}

/-- The code the inductive line reads. -/
structure ILCodes (σ : Type) (C : Ctx) : Prop where
  nc : ∀ t : PState σ, t.code = C.code → NnCodes t
  sc : ∀ t : PState σ, t.code = C.code → ScanCodes t
  ic : ∀ t : PState σ, t.code = C.code → Scan.IndCodes t
  cN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one)
  cI : C.code.lookup T.Ind.fIndTele = some ([(T.Ex.pFu, .one), (T.Ex.pH, .one)], T.Ind.iptBody T.Ind.fIndTele, .one)
  cP : C.code.lookup T.Ind.fPiSortTele = some ([(T.Ex.pFu, .one), (T.Ex.pH, .one)], T.Ind.pstBody T.Ind.fPiSortTele, .one)
  cV : C.code.lookup T.Ind.fNvChk = some ([(T.Ex.pH, .one)], T.Ind.nvcBody, .one)
  rulesN : C.code.lookup fRulesN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fRule sM, .one)
  ctorsN : C.code.lookup fIndCtorsN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndCtor sM, .one)
  recsN : C.code.lookup fIndRecsN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndRec sM, .one)
  typesN : C.code.lookup fIndTypesN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndType sM, .one)
  rulesAt : C.code.lookup fRulesAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fRule sR, .one)
  ctorsAt : C.code.lookup fIndCtorsAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fIndCtor sR, .one)
  recsAt : C.code.lookup fIndRecsAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fIndRec sR, .one)
  typesAt : C.code.lookup fIndTypesAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fIndType sR, .one)
  declF : ∀ k, k < 3 → C.code.lookup (fIdF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indDeclSpec indDeclInits (vv (slotName k)), .one)
  typeF : ∀ k, k < 10 → C.code.lookup (fItF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indTypeSpec indTypeInits (vv (slotName k)), .one)
  ctorF : ∀ k, k < 8 → C.code.lookup (fIcF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indCtorSpec indCtorInits (vv (slotName k)), .one)
  recF : ∀ k, k < 10 → C.code.lookup (fIrF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indRecSpec indRecInits (vv (slotName k)), .one)
  ruleF : ∀ k, k < 3 → C.code.lookup (fRuF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun ruleSpec ruleInits (vv (slotName k)), .one)

theorem ILCodes.toH {C : Ctx} (cc : ILCodes σ C) (H : List (BitVec 64)) : ILCodes σ (ctxH C H) :=
  ⟨cc.nc, cc.sc, cc.ic, cc.cN, cc.cI, cc.cP, cc.cV, cc.rulesN, cc.ctorsN, cc.recsN, cc.typesN, cc.rulesAt, cc.ctorsAt,
    cc.recsAt, cc.typesAt, cc.declF, cc.typeF, cc.ctorF, cc.recF, cc.ruleF⟩

def ilJ := ofString "il_j"
def ilQ := ofString "il_q"
def ilOB := ofString "il_ob"
def ilTh := ofString "il_th"
def ilP := ofString "il_p"
def ilCp := ofString "il_cp"
def ilR := ofString "il_r"

def sentW : BitVec 64 := BitVec.ofNat 64 listSentinel
def b55W : BitVec 64 := BitVec.ofNat 64 B55

theorem b55W_toNat : b55W.toNat = B55 := by unfold b55W B55; rfl

def ctorTail (C : Ctx) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (callTo ilA (fIcF 4) [vv kBA, vv kBN, vv ilQ])
  (.ite (.cmp .lower (vv ilA) (.const b55W))
    (.seq (callTo ilB (fIcF 3) [vv kBA, vv kBN, vv ilQ])
    (.ite (.cmp .lower (vv ilB) (.const b55W))
      (.seq (.assign .local ilY (.op .add [vv ilP, vv ilB]))
      (.ite (.cmp .notEqual (vv ilT) (vv ilY)) hang
      (allocWr C ilR [.const 4, vv fy, vv kKA0, vv fz, vv ilA, vv ilB, vv ilTh]
        (.seq (.store (slotE ilOB ilJ 2) (vv ilR)) rest)))) hang)) hang)

def inductChk : ProgHOL 64 :=
  .ite (.cmp .equal (vv ilX) (.const sentW)) (.assign .local ilY (vv ilTh))
    (tblGetP ilY (vv fTN) (vv fCap) (vv ilX) (.ite (.cmp .notEqual (vv ilY) (vv ilTh)) hang .skip))

def ctorBody (C : Ctx) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (callTo ilQ fIndCtorsAt [vv kBA, vv kBN, vv ilCp, vv ilJ])
  (.seq (callTo fU (fIcF 2) [vv kBA, vv kBN, vv ilQ])
  (.seq (callTo fW3 (fIcF 5) [vv kBA, vv kBN, vv ilQ])
  (.seq (callTo fV2 (fIcF 1) [vv kBA, vv kBN, vv ilQ])
  (cvP C
   (.seq (.assign .local ilA (.load .one (slotE ilCB ilJ 1)))
   (.ite (.cmp .notEqual (vv fy) (vv ilA)) hang
   (.seq (callTo ilX (fIcF 6) [vv kBA, vv kBN, vv ilQ])
   (.ite (.op .and [.cmp .notEqual (vv ilX) (.const sentW), .cmp .notEqual (vv ilX) (vv ilJ)]) hang
   (.seq (callTo ilX (fIcF 7) [vv kBA, vv kBN, vv ilQ])
   (.seq inductChk (ctorTail C rest)))))))))))

def ctorMods : List MlS := [ilQ, fU, fW3, fV2, ilA, ilX, ilY, ilB, ilR] ++ cvMods

/-- A constructor record's twin facts at position `j` of a block whose type is `t` (handle `T`), whose
`ctors[j]` has handle `h`. -/
structure CtorOK (st : StateD) (s : AState) (t : IndTypeRec) (T : NIdx) (c : IndCtorRec) (j : Nat) (h : NIdx) :
    Prop where
  nm : st.names.get? c.cv.name = some h
  cidx : c.cidx = none ∨ c.cidx = some j
  ind : ∀ iw, c.induct = some iw → st.names.get? iw = some T
  ty : ∃ ch, st.exprs.get? c.cv.type = some ch ∧
    indPiTeleLen (s.store.nodeCount + 1) ch s = .ok (t.numParams + c.numFields, s) ∧
    ∀ e, denoteE s.store ch = some e → t.numParams + c.numFields = ConLeche.Frontend.indPiTeleLen e
  lps : ∀ x ∈ c.cv.levelParams, (st.names.get? x).isSome
  lpl : c.cv.levelParams.length < B55
  np : c.numParams < B55
  nf : c.numFields < B55
  tl : t.numParams + c.numFields < B55

theorem bw_and (p q : Prop) [Decidable p] [Decidable q] : (bw p &&& bw q) = bw (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bw, hp, hq]

theorem tWords_get {k : IdxKind} (tbl : IdTable (Idx k)) (us : List Nat) (j : Nat) (hj : j < us.length) :
    (tWords tbl us)[j]'(by simpa [tWords] using hj) = Enc.idxW ((tbl.get? us[j]).getD default) := by
  simp [tWords]

theorem cvOfD_eq (st : StateD) (cv : CVRec) (nmh : NIdx) (tyh : EIdx) (hn : st.names.get? cv.name = some nmh)
    (ht : st.exprs.get? cv.type = some tyh) :
    cvOfD st cv = ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩ := by
  simp [cvOfD, hn, ht]

theorem tWords_cvOfD (st : StateD) (cv : CVRec) :
    (cvOfD st cv).levelParams.map Enc.idxW = tWords st.names cv.levelParams := by
  simp [cvOfD, tWords]

theorem lt_b55 {w : BitVec 64} {n : Nat} (hw : w = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) (h : w.toNat < b55W.toNat) :
    n < B55 := by
  rw [hw, b55W_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h; exact h

theorem natW_lt64 (x : Nat) : min x natCap < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)

theorem specR_factI {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} {A : Prop} (h : A → SpecR P c s m R) :
    SpecR (fun t => A ∧ P t) c s m R := fun t ⟨ha, ht⟩ => h ha t ht

theorem ofNat_inj64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h; simp at this; omega

theorem ctorBody_spec {α : Type} (C : Ctx) (hok : CtxOK C) (cc : ILCodes σ C)
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ ctorMods, x ∈ D)
    (st : StateD) (jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b)
    (t : IndTypeRec) (cts : List IndCtorRec) (T : NIdx) (pC eC : USize) (hpC : scanIndCtors b pC = .ok cts eC)
    (J : Nat) (hJ : J < cts.length) (hnC : cts.length < B55) (hnP : t.numParams < B55)
    (cb ob : Nat) (hcb : BlkAt C.H cb (tWords st.names t.ctors)) (hlen : t.ctors.length = cts.length)
    (hslot : ob + 2 + J < C.H.length)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hCp : Γ.get ilCp = some (BitVec.ofNat 64 pC.toNat))
    (hJw : Γ.get ilJ = some (BitVec.ofNat 64 J)) (hCB : Γ.get ilCB = some (cellA C cb))
    (hOB : Γ.get ilOB = some (cellA C ob)) (hTh : Γ.get ilTh = some (Enc.idxW T))
    (hP : Γ.get ilP = some (BitVec.ofNat 64 t.numParams))
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64)
    (hk : ∀ (H' : List (BitVec 64)) (Γ' : Env) (o : Nat),
      (∀ c v, C.H[c]? = some v → c ≠ ob + 2 + J → H'[c]? = some v) → C.H.length ≤ H'.length →
      C.H.length ≤ o → H'[ob + 2 + J]? = some (cellA C o) →
      RCIE C.H.length C H' o (.ctorInfo (cvOfD st cts[J].cv) cts[J].numParams cts[J].numFields T) →
      CtorOK st s t T cts[J] J ((st.names.get? (t.ctors[J]'(by omega))).getD default) →
      (∀ y, y ∉ ctorMods → Γ'.get y = Γ.get y) →
      SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (ctorBody C rest) s m R := by
  have hplat := hbuf.plat
  have hsmall := hbuf.small
  have hpCb : pC.toNat ≤ b.size := Nat.le_of_lt (objListOpen_pos hplat (by rw [← scanIndCtors_objList]; exact hpC))
  unfold ctorBody
  refine specR_scan4 hok bufJ b hbuf ilQ fIndCtorsAt ilCp (vv ilJ) _ pC.toNat J _ (hD ilQ (by simp [ctorMods]))
    cc.ctorsAt hBA hBN hCp (by simpa [sev, vv] using hJw)
    (fun u hb hu l1 l2 l3 l4 => indCtorAt_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pC eC cts hpC J
      (by unfold B55 at hnC; omega) l1 l2 l3 l4) (fun wq hq => ?_)
  obtain ⟨q, e', rfl, hqb, hsq⟩ := hq hJ
  refine specR_scan3 hok bufJ b hbuf fU (fIcF 2) ilQ _ q.toNat _ (hD fU (by simp [ctorMods]))
    (cc.ctorF 2 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indCtorField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 2 (by decide) _ e' hsq)
    (fun w2 hw2 => ?_)
  simp only [IndCtorField] at hw2; subst hw2
  refine specR_scan3 hok bufJ b hbuf fW3 (fIcF 5) ilQ _ q.toNat _ (hD fW3 (by simp [ctorMods]))
    (cc.ctorF 5 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indCtorField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 5 (by decide) _ e' hsq)
    (fun w5 hw5 => ?_)
  simp only [IndCtorField] at hw5; subst hw5
  refine specR_scan3 hok bufJ b hbuf fV2 (fIcF 1) ilQ _ q.toNat _ (hD fV2 (by simp [ctorMods]))
    (cc.ctorF 1 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indCtorField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 1 (by decide) _ e' hsq)
    (fun w1 hw1 => ?_)
  simp only [IndCtorField] at hw1
  refine cvP_spec C hok cc.nc cc.cN cc.cI s _ M D (fun x hx => hD x (by simp [ctorMods, hx])) st jN jE cap bufJ b
    hreln hrele hcap hcapN hbuf cts[J].cv w1 hw1 (by envg; exact hTN) (by envg; exact hTE) (by envg; exact hC)
    (by envg) (by envg) (by envg) (by envg; exact hBA) (by envg; exact hBN) _
    (fun H1 ol Γ1 nmh tyh n hp1 hol hblk hnm hty hlps hlpl hn hrun hden h1y h1z h1T h1K h1k => ?_)
  -- the ctors[J] handle
  have g1 : ∀ y, y ∉ cvMods → y ∉ [fV2, fW3, fU, ilQ] → Γ1.get y = Γ.get y := fun y hy hy' => by
    rw [h1k y hy]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    simp only [ConPanqueque.T.Env.get_cons, ite_eq_right hy'.1, ite_eq_right hy'.2.1, ite_eq_right hy'.2.2.1,
      ite_eq_right hy'.2.2.2]
  have hJc : J < t.ctors.length := by omega
  have hcbJ : (ctxH C H1).H[cb + 1 + J]? = some (Enc.idxW ((st.names.get? t.ctors[J]).getD default)) := by
    have := hcb.2 J (by simpa [tWords] using hJc)
    rw [tWords_get _ _ J hJc] at this
    exact getElem?_prefix hp1 this
  refine specR_heapLoadV ilA (slotE ilCB ilJ 1) (cb + 1 + J) _ hcbJ (hD ilA (by simp [ctorMods]))
    (by rw [show cb + 1 + J = cb + 1 + J from rfl]
        exact sev_slot Γ1 (ctxH C H1) ilCB ilJ cb J 1 (by rw [g1 _ (by decide) (by decide)]; exact hCB)
          (by rw [g1 _ (by decide) (by decide)]; exact hJw) (by unfold B55 at hnC; omega)) ?_
  refine specR_eqGuardI fy ilA (Enc.idxW nmh) (Enc.idxW ((st.names.get? t.ctors[J]).getD default))
    (by envg; exact h1y) (by envg) (fun heq => ?_)
  have hnmJ : nmh = (st.names.get? t.ctors[J]).getD default := Enc.idxW_inj heq
  -- cidx
  refine specR_scan3 (ctxOK_H hok H1) bufJ b (bufOK_prefix hbuf hp1) ilX (fIcF 6) ilQ _ q.toNat _
    (hD ilX (by simp [ctorMods])) (cc.ctorF 6 (by decide)) (by envg; rw [g1 _ (by decide) (by decide)]; exact hBA)
    (by envg; rw [g1 _ (by decide) (by decide)]; exact hBN) (by envg; rw [h1k ilQ (by decide)]; envg)
    (fun u hb hu l1 l2 l3 => indCtorField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 6 (by decide) _ e' hsq)
    (fun w6 hw6 => ?_)
  simp only [IndCtorField] at hw6
  have hX6 : Env.get ((ilX, w6) :: (ilA, Enc.idxW ((st.names.get? t.ctors[J]).getD default)) :: Γ1) ilX = some w6 := by
    envg
  have hJ6 : Env.get ((ilX, w6) :: (ilA, Enc.idxW ((st.names.get? t.ctors[J]).getD default)) :: Γ1) ilJ =
      some (BitVec.ofNat 64 J) := by envg; rw [g1 _ (by decide) (by decide)]; exact hJw
  refine specR_ifI _ (bw (w6 ≠ sentW ∧ w6 ≠ BitVec.ofNat 64 J)) (by
      show (do let x ← sev _ (.cmp .notEqual (vv ilX) (.const sentW))
               let y ← sev _ (.cmp .notEqual (vv ilX) (vv ilJ)); pure (x &&& y)) = _
      rw [sev_ne_c _ ilX w6 sentW hX6, sev_ne_v _ ilX ilJ w6 _ hX6 hJ6]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, bw_and]) (fun _ => specR_hangI) (fun hw => ?_)
  have hcidx : cts[J].cidx = none ∨ cts[J].cidx = some J := by
    have hn := bw_eq0 hw
    cases hc : cts[J].cidx with
    | none => exact Or.inl rfl
    | some ci =>
      rw [hc] at hw6; subst hw6
      have : optWord (some ci) = BitVec.ofNat 64 J :=
        Classical.byContradiction fun hne => hn ⟨optWord_ne ci, hne⟩
      simp only [optWord] at this
      exact Or.inr (by rw [natW_eq_small (by unfold B55 at hnC ⊢; omega) this])
  -- induct
  refine specR_scan3 (ctxOK_H hok H1) bufJ b (bufOK_prefix hbuf hp1) ilX (fIcF 7) ilQ _ q.toNat _
    (hD ilX (by simp [ctorMods])) (cc.ctorF 7 (by decide)) (by envg; rw [g1 _ (by decide) (by decide)]; exact hBA)
    (by envg; rw [g1 _ (by decide) (by decide)]; exact hBN) (by envg; rw [h1k ilQ (by decide)]; envg)
    (fun u hb hu l1 l2 l3 => indCtorField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 7 (by decide) _ e' hsq)
    (fun w7 hw7 => ?_)
  simp only [IndCtorField] at hw7
  let Γ6 : Env := (ilX, w7) :: (ilX, w6) :: (ilA, Enc.idxW ((st.names.get? t.ctors[J]).getD default)) :: Γ1
  let Γ7 : Env := (ilY, Enc.idxW T) :: Γ6
  have g6 : ∀ y, y ∉ ctorMods → Γ6.get y = Γ.get y := fun y hy => by
    simp only [ctorMods, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Γ6, ConPanqueque.T.Env.get_cons, ite_eq_right hy.1.2.2.2.2.2.1, ite_eq_right hy.1.2.2.2.2.1]
    exact g1 y hy.2
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hy.1.2.2.2.1, hy.1.2.2.1, hy.1.2.1, hy.1.1⟩)
  have g7 : ∀ y, y ∉ ctorMods → Γ7.get y = Γ.get y := fun y hy => by
    have : y ≠ ilY := fun e => hy (by rw [e]; simp [ctorMods])
    simp only [Γ7, ConPanqueque.T.Env.get_cons, ite_eq_right this]; exact g6 y hy
  have hTh6 : Γ6.get ilTh = some (Enc.idxW T) := by rw [g6 _ (by decide)]; exact hTh
  refine specR_step (Q := fun u => (∀ iw, cts[J].induct = some iw → st.names.get? iw = some T) ∧
    Inv (ctxH C H1) s Γ7 [] D u) ?_ (specR_factI fun hind => ?_)
  · unfold inductChk
    refine step_ifI _ _ (sev_eq_c' Γ6 ilX w7 sentW (by simp only [Γ6]; envg)) (fun hw => ?_) (fun hw => ?_)
    · have he : w7 = sentW := Classical.byContradiction fun hne => by simp [bw, hne] at hw
      refine step_mono (step_assignI ilY (vv ilTh) (Enc.idxW T) (hD ilY (by simp [ctorMods]))
        (by simp only [sev, vv]; exact hTh6)) (fun u hu => hu) (fun u hu => ⟨fun iw hiw => ?_, hu⟩)
      rw [hiw] at hw7; exact absurd (hw7.symm.trans he) (optWord_ne iw)
    · have hne : w7 ≠ sentW := fun he => by simp [bw, he] at hw
      cases hi : cts[J].induct with
      | none => rw [hi] at hw7; exact absurd hw7 hne
      | some iw =>
        rw [hi] at hw7
        refine step_tblGetI ilY (hD ilY (by simp [ctorMods])) jN cap st.names (tblRel_prefix hreln hp1) hcap
          (vv fTN) (vv fCap) (vv ilX) (by simp only [sev, vv]; rw [g6 _ (by decide)]; exact hTN)
          (by simp only [sev, vv]; rw [g6 _ (by decide)]; exact hC) _ (natW_lt64 iw)
          (by simp only [sev, vv, Γ6]; envg; rw [hw7]; rfl) (fun h hh => ?_)
        refine step_ifI _ _ (sev_ne_v _ ilY ilTh (Enc.idxW h) (Enc.idxW T) (by envg)
          (by envg; exact hTh6)) (fun _ => step_hangI) (fun hw' => ?_)
        have hhT : h = T := Enc.idxW_inj (Classical.byContradiction fun hne => by simp [bw, hne] at hw')
        subst hhT
        refine step_mono step_skipI (fun u hu => hu) (fun u hu => ⟨fun iw' hiw' => ?_, inv_env_mono hu
          (fun x v hx => by
            simp only [Γ7, ConPanqueque.T.Env.get_cons] at hx ⊢
            by_cases e : x = ilY
            · simp only [e, ite_true] at hx ⊢; exact hx
            · simp only [e, ite_false] at hx ⊢; exact hx)⟩)
        simp only [Option.some.injEq] at hiw'; rw [← hiw']
        exact get_capped (tblRel_prefix hreln hp1) hcapN iw h hh
  -- counts and the record
  unfold ctorTail
  refine specR_scan3 (ctxOK_H hok H1) bufJ b (bufOK_prefix hbuf hp1) ilA (fIcF 4) ilQ _ q.toNat _
    (hD ilA (by simp [ctorMods])) (cc.ctorF 4 (by decide)) (by rw [g7 _ (by decide)]; exact hBA)
    (by rw [g7 _ (by decide)]; exact hBN) (by simp only [Γ7, Γ6]; envg; rw [h1k ilQ (by decide)]; envg)
    (fun u hb hu l1 l2 l3 => indCtorField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 4 (by decide) _ e' hsq)
    (fun w4 hw4 => ?_)
  simp only [IndCtorField] at hw4; subst hw4
  refine specR_ltGuardI ilA (Scan.natW cts[J].numParams) b55W (by envg) (fun hl4 => ?_)
  obtain ⟨hnp, hnpw⟩ := natW_small (by rw [b55W_toNat] at hl4; exact hl4)
  refine specR_scan3 (ctxOK_H hok H1) bufJ b (bufOK_prefix hbuf hp1) ilB (fIcF 3) ilQ _ q.toNat _
    (hD ilB (by simp [ctorMods])) (cc.ctorF 3 (by decide)) (by envg; rw [g7 _ (by decide)]; exact hBA)
    (by envg; rw [g7 _ (by decide)]; exact hBN) (by simp only [Γ7, Γ6]; envg; rw [h1k ilQ (by decide)]; envg)
    (fun u hb hu l1 l2 l3 => indCtorField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 3 (by decide) _ e' hsq)
    (fun w3 hw3 => ?_)
  simp only [IndCtorField] at hw3; subst hw3
  refine specR_ltGuardI ilB (Scan.natW cts[J].numFields) b55W (by envg) (fun hl3 => ?_)
  obtain ⟨hnf, hnfw⟩ := natW_small (by rw [b55W_toNat] at hl3; exact hl3)
  rw [hnpw, hnfw]
  unfold B55 at hnP hnp hnf hn
  refine specR_assignI ilY (.op .add [vv ilP, vv ilB]) (BitVec.ofNat 64 (t.numParams + cts[J].numFields))
    (hD ilY (by simp [ctorMods])) (by
      simp only [sev, vv]
      rw [show Env.get ((ilB, BitVec.ofNat 64 cts[J].numFields) :: (ilA, BitVec.ofNat 64 cts[J].numParams) :: Γ7) ilP =
        some (BitVec.ofNat 64 t.numParams) by envg; rw [g7 _ (by decide)]; exact hP]
      simp only [ConPanqueque.T.Env.get_cons, ite_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  refine specR_eqGuardI ilT ilY (BitVec.ofNat 64 n) (BitVec.ofNat 64 (t.numParams + cts[J].numFields))
    (by simp only [Γ7, Γ6]; envg; exact h1T) (by envg) (fun hnn => ?_)
  have hnn' : n = t.numParams + cts[J].numFields := ofNat_inj64 (by omega) (by omega) hnn
  subst hnn'
  -- the record
  have hcv := cvOfD_eq st cts[J].cv nmh tyh hnm hty
  let E : Env := (ilY, BitVec.ofNat 64 (t.numParams + cts[J].numFields)) ::
    (ilB, BitVec.ofNat 64 cts[J].numFields) :: (ilA, BitVec.ofNat 64 cts[J].numParams) :: Γ7
  have gE : ∀ y, y ∉ ctorMods → E.get y = Γ.get y := fun y hy => by
    simp only [ctorMods, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [E, ConPanqueque.T.Env.get_cons, ite_eq_right hy.1.2.2.2.2.2.2.1, ite_eq_right hy.1.2.2.2.2.2.2.2.1,
      ite_eq_right hy.1.2.2.2.2.1]
    have := g7 y (by simp only [ctorMods, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hy)
    exact this
  have hEth : E.get ilTh = some (Enc.idxW T) := by rw [gE _ (by decide)]; exact hTh
  have hEy : E.get fy = some (Enc.idxW nmh) := by simp only [E, Γ7, Γ6]; envg; exact h1y
  have hEz : E.get fz = some (Enc.idxW tyh) := by simp only [E, Γ7, Γ6]; envg; exact h1z
  have hEk : E.get kKA0 = some (cellA C ol) := by simp only [E, Γ7, Γ6]; envg; exact h1K
  refine specR_allocWrI (ctxH C H1) (ctxOK_H hok H1) ilR (hD ilR (by simp [ctorMods]))
    [.const 4, vv fy, vv kKA0, vv fz, vv ilA, vv ilB, vv ilTh]
    [BitVec.ofNat 64 4, Enc.idxW nmh, cellA C ol, Enc.idxW tyh, BitVec.ofNat 64 cts[J].numParams,
      BitVec.ofNat 64 cts[J].numFields, Enc.idxW T] rfl (by simp) (fun v i hi => ?_) (fun H2 r hp2 hr1 hr2 hrw => ?_)
  · have gv : ∀ y, y ≠ ilR → Env.get ((ilR, v) :: E) y = E.get y := fun y h => by
      simp only [ConPanqueque.T.Env.get_cons, ite_eq_right h]
    simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ, List.getD_cons_zero, sev, vv]
    · rfl
    · rw [gv _ (by decide)]; exact hEy
    · rw [gv _ (by decide)]; exact hEk
    · rw [gv _ (by decide)]; exact hEz
    · rw [gv _ (by decide)]; simp only [E]; envg
    · rw [gv _ (by decide)]; simp only [E]; envg
    · rw [gv _ (by decide)]; exact hEth
  have hH12 : H1.length ≤ H2.length := hp2.length_le
  have hCH1 : C.H.length ≤ H1.length := hp1.length_le
  have hr1' : H1.length ≤ r := hr1
  refine specR_heapStoreI (C := ctxH (ctxH C H1) H2) (ctxOK_H hok H2) (slotE ilOB ilJ 2) (vv ilR) (ob + 2 + J)
    (by show ob + 2 + J < H2.length; omega) (cellA C r)
    (sev_slot _ (ctxH (ctxH C H1) H2) ilOB ilJ ob J 2
      (by rw [ConPanqueque.T.Env.get_cons, ite_eq_right (by decide), gE _ (by decide)]; exact hOB)
      (by rw [ConPanqueque.T.Env.get_cons, ite_eq_right (by decide), gE _ (by decide)]; exact hJw)
      (by unfold B55 at hnC; omega))
    (by simp only [sev, vv, ConPanqueque.T.Env.get_cons, ite_true]; rfl) ?_
  have hnmJ' : st.names.get? cts[J].cv.name = some ((st.names.get? t.ctors[J]).getD default) := by
    rw [hnm, hnmJ]
  refine hk (H2.set (ob + 2 + J) (cellA C r)) _ r (fun c v hc hne => ?_) (by simp; omega) (by omega)
    (by simp [List.getElem?_set]; omega) ?_ ⟨hnmJ', hcidx, hind, ⟨tyh, hty, hrun, hden⟩, ?_, hlpl, hnp, hnf, hn⟩
    (fun y hy => by
      rw [ConPanqueque.T.Env.get_cons, ite_eq_right (fun e => hy (by rw [e]; simp [ctorMods]))]; exact gE y hy)
  · rw [List.getElem?_set, ite_eq_right (by omega)]; exact getElem?_prefix (hp1.trans hp2) hc
  · refine rcie_keep (rcie_ctor C.H.length C H2 r ol (cvOfD st cts[J].cv) _ _ T (by omega) hol
      (by omega) (by omega) (fun i hi => ?_) ?_) (keepsAbove_set_lt (by omega) _)
    · rw [hcv]; have := hrw i (by simpa using hi); simpa using this
    · rw [tWords_cvOfD]; exact blkAt_mono hblk hp2
  · intro x hx
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
    rw [← e]; exact hlps j hj

end ConPanqueque.Front
