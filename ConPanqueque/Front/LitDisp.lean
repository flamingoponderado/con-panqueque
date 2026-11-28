import ConPanqueque.Front.LitBig
import ConPanqueque.Front.LitStr
import ConPanqueque.T.Str.LitW

/-! # Literal lines (`strVal`, `natVal`)

A `strVal` line: the plain string scanner gives the body's span, the key `1 :: bytes` is copied from
the buffer into fresh heap cells and interned (`litStrBody`).  A `natVal` line: the quoted-number
scanner gives the closing quote, `readNatSat` the value (capped at `natCap`); a value below the cap
is interned by `litWord`, a larger one hangs (a resource limit of the port).  The twin is
`parseExprEntryD` at `.strVal` / `.natVal`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ExprRec LineRec LinePayload ScanRes byteAt IdTable scanString)

variable {σ : Type}

/-! ## `strVal` -/

/-- `strVal s` at index `i`: `kQ` the string's first byte in the buffer, `kN` its length. -/
def exStrVP (C : Ctx) : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
    (allocP C kKA0 (.shift .lsl (.op .add [vv kN, .const 1]) (.const 3))
      (.seq (.assign .local kKA (.op .add [vv kKA0, .const 8]))
      (.seq (.assign .local kK (.const 0))
      (.seq (.store (vv kKA0) (.const 1))
      (.seq kcLoop
      (.seq (.assign .local kL1 (.op .add [vv kN, .const 1]))
      (.seq (.call (some (some (.local, fh), none)) fInternLitStr [vv kKA0, vv kL1, vv kN])
        (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0))))))))))

theorem exStrV_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcN : C.code.lookup fInternLitStr = some ([(pKeyN, .one), (lEn, .one), (lHn, .one)], litStrBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fx, fh, kKA0, kKA, kK, kC, kS, kW, kJ, kL1], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ q len : Nat) (bs : List UInt8) (hpk : Packed C.H bufJ bs) (hqn : q + len ≤ bs.length)
    (hbl : bs.length < 2 ^ 59) (hbuf : bufJ + bs.length / 8 < C.H.length)
    (i : Nat) (str : String) (hi : i < 2 ^ 64)
    (hstr : str.toByteArray.data.toList = (bs.drop q).take len)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i))
    (hQ : Γ.get kQ = some (BitVec.ofNat 64 q)) (hN : Γ.get kN = some (BitVec.ofNat 64 len))
    (hBA : Γ.get kBA = some (cellA C bufJ)) :
    SpecR (Inv (σ := σ) C s Γ M D) (exStrVP C) s (parseExprEntryD st i (.strVal str)) (ExPost C jE cap st i) := by
  have hlay := hok.heapLay
  unfold exStrVP
  refine specR_tblFreshI fx (hD fx (by simp)) jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fI)
    (by simpa [sev, vv] using hTE) (by simpa [sev, vv] using hC) i hi (by simpa [sev, vv] using hI)
    (fun hic hg => ?_)
  have hm : parseExprEntryD st i (.strVal str) =
      (internE (.lit (.strVal str)) >>= fun h => (pure { st with exprs := st.exprs.insert i h } : AM StateD)) := by
    simp [parseExprEntryD, StateD.freshExpr, IdTable.bound_eq, hg]
  rw [hm]
  -- the key cells
  refine specR_allocI kKA0 (.shift .lsl (.op .add [vv kN, .const 1]) (.const 3)) (len + 1) (by omega)
    (hD kKA0 (by simp)) (fun v => by
      simp only [sev, vv, Env.get_cons, show (kN = kKA0) = False from by decide, show (kN = fx) = False from by decide,
        ite_false, hN, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.map_some, show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, ite_true]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]; omega)
    (fun H' ws hpre' hwl hcapH => ?_)
  have hCH : C.H.length ≤ H'.length := hpre'.length_le
  let o := H'.length
  let C1 := ctxH C (H' ++ ws)
  have hl1 : (H' ++ ws).length = H'.length + (len + 1) := by simp [hwl]
  refine specR_assignI kKA _ (cellA C (o + 1)) (hD kKA (by simp))
    (by simp [sev, vv, Env.get_cons]; exact cellA_add8 C o) ?_
  refine specR_assignI kK (.const 0) 0 (hD kK (by simp)) rfl ?_
  refine specR_heapStoreI (C := C1) (ctxOK_H hok _) (vv kKA0) (.const 1) o (by simp only [C1, ctxH]; omega)
    1 (by simp [sev, vv, Env.get_cons]; rfl) rfl ?_
  let H2 := (H' ++ ws).set o 1
  have hl2 : H2.length = H'.length + (len + 1) := by simp [H2, hl1]
  have hp2 : C.H <+: H2 := prefix_set_ge (hpre'.trans (List.prefix_append _ _)) o hCH _
  let wsb := (bs.drop q).map (fun b => BitVec.ofNat 64 b.toNat)
  have g5 : ∀ y, y ∉ [kK, kKA, kKA0, fx] →
      Env.get ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: Γ) y = Env.get Γ y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Env.get_cons, ite_eq_right hy.1, ite_eq_right hy.2.1, ite_eq_right hy.2.2.1, ite_eq_right hy.2.2.2]
  refine kc_spec (C := ctxH C1 H2) (ctxOK_H hok _) (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp)) bufJ (o + 1) q len bs
    (packed_prefix hpk hp2) hqn (by omega) (by simp only [ctxH]; have := hp2.length_le; omega)
    (by simp only [ctxH]; omega) (by have := hok.heapLay; omega)
    (fun k hk i' hi' => by have := Nat.div_le_div_right (c := 8) (Nat.le_of_lt hi'); omega)
    (by rw [g5 _ (by decide)]; exact hBA)
    (by simp only [Env.get_cons, show (kKA = kK) = False from by decide, ite_false, ite_true]; rfl)
    (by rw [g5 _ (by decide)]; exact hQ)
    (by simp only [Env.get_cons, ite_true]) (by rw [g5 _ (by decide)]; exact hN) ?_
  -- the key is in place
  let H3 := kcH H2 (o + 1) wsb len
  change SpecR (Inv (ctxH (ctxH C1 H2) H3) s (kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) ::
    (fx, 0) :: Γ) H2 bufJ (o + 1) q wsb len) [] D) _ s _ _
  have hsl : str.toByteArray.data.toList.length = len := by rw [hstr]; simp; omega
  have hkl : (Enc.encLit ⟨.strVal str⟩).length = len + 1 := by simp [Enc.encLit, Enc.strW, hsl]
  have hl3 : H3.length = H'.length + (len + 1) := by simp [H3, kcH_length, hl2]
  have hp3 : C.H <+: H3 := prefix_kcH hp2 (o + 1) (by omega) wsb len
  have hkey : ∀ j (hj : j < (Enc.encLit ⟨.strVal str⟩).length), H3[o + j]? = some ((Enc.encLit ⟨.strVal str⟩)[j]) := by
    intro j hj
    rw [hkl] at hj
    simp only [H3]
    rw [kcH_get]
    cases j with
    | zero =>
      rw [ite_eq_right (by omega)]
      simp [H2, Enc.encLit, List.getElem?_set, hl1]
      show H'.length < H'.length + (len + 1); omega
    | succ k =>
      rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
      have hk1 : k < str.toByteArray.data.toList.length := by omega
      simp only [Enc.encLit, List.getElem_cons_succ, Enc.strW, List.getElem_map]
      simp only [wsb, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
        show o + (k + 1) - (o + 1) = k by omega]
      rw [List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.getD_some, Option.some.injEq]
      congr 2
      have := congrArg (fun l => l[k]?) hstr
      simp only [List.getElem?_take, ite_eq_left (show k < len by omega), List.getElem?_drop] at this
      rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem (by omega)] at this
      exact (Option.some.inj this).symm
  have gG : ∀ y, y ∉ [kK, kC, kS, kW, kJ] → y ∉ [kK, kKA, kKA0, fx] →
      Env.get (kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: Γ) H2 bufJ (o + 1) q wsb len) y
        = Env.get Γ y :=
    fun y h1 h2 => by rw [kcG_get _ _ _ _ _ _ y h1 len]; exact g5 y h2
  refine specR_assignI kL1 (.op .add [vv kN, .const 1]) (BitVec.ofNat 64 (len + 1)) (hD kL1 (by simp))
    (by simp only [sev, vv]; rw [gG _ (by decide) (by decide), hN]; simp only [Option.bind_eq_bind,
          Option.bind_some, Option.pure_def]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  have hka0 : Env.get (kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: Γ) H2 bufJ (o + 1) q
      wsb len) kKA0 = some (cellA C o) := by
    rw [kcG_get _ _ _ _ _ _ kKA0 (by decide) len]
    simp only [Env.get_cons, show (kKA0 = kK) = False from by decide, show (kKA0 = kKA) = False from by decide,
      ite_false, ite_true]
  refine specR_callNIA fh fInternLitStr [pKeyN, lEn, lHn] [vv kKA0, vv kL1, vv kN] litStrBody
    [cellA C o, BitVec.ofNat 64 (len + 1), BitVec.ofNat 64 len] (by decide) rfl (hD fh (by simp)) hcN
    ⟨by simp only [sev, vv, Env.get_cons, show (kKA0 = kL1) = False from by decide, ite_false]; exact hka0,
     by simp [sev, vv, Env.get_cons],
     by simp only [sev, vv, Env.get_cons, show (kN = kL1) = False from by decide, ite_false]
        rw [gG _ (by decide) (by decide)]; exact hN, trivial⟩
    (fun a w s' st => internE (.lit (.strVal str)) s = .ok (a, s') ∧ PostE (ctxH (ctxH (ctxH C1 H2) H3) C.H) a w s' st)
    (fun a w s' H' => H' = C.H ∧ internE (.lit (.strVal str)) s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨C.H, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      have hs := litStr_body_spec (σ := σ) ra (ctxH (ctxH C1 H2) H3) (ctxOK_H hok _) s str o C.H hp3
        (by omega) (by rw [hkl]; show o + (len + 1) ≤ H3.length; omega) (by rw [hkl]; omega) hkey
      rw [hkl, hsl] at hs
      exact hs _ (pre_of_lookups hu [pKeyN, lEn, lHn] _ rfl hlk)))
    (fun h w s2 H' ⟨e, hr2, hw⟩ => ?_)
  subst e; subst hw
  have eC : ctxH (ctxH (ctxH C1 H2) H3) C.H = C := ctxH_self C
  rw [eC]
  have gF : ∀ y, y ∉ [fh, kL1] → y ∉ [kK, kC, kS, kW, kJ] → y ∉ [kK, kKA, kKA0, fx] →
      Env.get ((fh, Enc.idxW h) :: (kL1, BitVec.ofNat 64 (len + 1)) ::
        kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: Γ) H2 bufJ (o + 1) q wsb len) y
        = Env.get Γ y := by
    intro y h0 h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h0
    simp only [Env.get_cons, ite_eq_right h0.1, ite_eq_right h0.2]; exact gG y h1 h2
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by decide)]; exact hTE) i hic h
    (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

/-- A `strVal` line: the string scanner gives the closing quote, then `kQ`/`kN` are the body's start
and length. -/
def strVLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo kSE fStr [vv kBA, vv kBN, vv kPos])
    (.seq (.assign .local kQ (.op .add [vv kPos, .const 1]))
      (.seq (.assign .local kN (.op .sub [vv kSE, vv kQ]))
        (capG fI (exStrVP C))))

theorem strVLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcN : C.code.lookup fInternLitStr = some ([(pKeyN, .one), (lEn, .one), (lHn, .one)], litStrBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcS : C.code.lookup fStr = some ([(sB, .one), (sN, .one), (sI, .one)], ssFun, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [kQ, kSE, kN, fx, fh, kKA0, kKA, kK, kC, kS, kW, kJ, kL1], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (str : String) (hr : scanString b pos = .ok str e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (strVLineP C) s (parseExprEntryD st i (.strVal str)) (ExPost C jE cap st i) := by
  have hplat := hbuf.plat
  have hsmall := hbuf.small
  have hpb : pos.toNat < b.size := scanString_lt hplat hr
  unfold strVLineP
  refine specR_retP3 kSE fStr sB sN sI ssFun (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) (hD _ (by simp)) hcS
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hP)
    (fun t callee ht c1 c2 c3 => slotCall (s := s) (D := D) hok hbuf hsc pos ssFun _ (fun u hb hc l1 l2 l3 =>
      ssFun_sound2 u (cellA C bufJ) b hplat hb pos (Nat.le_of_lt hpb) hc.2.2.2.1 l1 l2 l3) t callee _ _ ht c1 c2 c3)
    (fun w3 ⟨ee, hw3, hee, hpe, s', hs', hutf⟩ => ?_)
  have hstr : str = s' := scanString_det hr hs'
  let Γ3 : Env := (kSE, w3) :: Γ
  have g3 : ∀ y, y ≠ kSE → Γ3.get y = Γ.get y := fun y h0 => by simp only [Γ3, Env.get_cons, ite_eq_right h0]
  refine specR_assignI kQ _ (BitVec.ofNat 64 (pos.toNat + 1)) (hD _ (by simp))
    (by simp only [sev, vv]; rw [g3 _ (by decide), hP]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add64]) ?_
  let Γ4 : Env := (kQ, BitVec.ofNat 64 (pos.toNat + 1)) :: Γ3
  refine specR_assignI kN _ (BitVec.ofNat 64 (ee.toNat - (pos.toNat + 1))) (hD _ (by simp))
    (by simp only [sev, vv, Γ4, Γ3, Env.get_cons, ite_eq_right (show kSE ≠ kQ by decide), ite_eq_left, hw3]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]) ?_
  let Γ5 : Env := (kN, BitVec.ofNat 64 (ee.toNat - (pos.toNat + 1))) :: Γ4
  have g5 : ∀ y, y ≠ kN → y ≠ kQ → y ≠ kSE → Γ5.get y = Γ.get y := fun y hn hq hs => by
    simp only [Γ5, Γ4, Env.get_cons, ite_eq_right hn, ite_eq_right hq]; exact g3 y hs
  refine specR_capG fI i (by rw [g5 _ (by decide) (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  have := natCap_lt
  have hp1 : (pos + 1).toNat = pos.toNat + 1 := ConLeche.Frontend.usizeStep b pos ((hplat.lt_iff pos).mpr hpb)
  refine exStrV_spec ra C hok hcN s _ M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    st jE cap hrel hcap bufJ (pos.toNat + 1) (ee.toNat - (pos.toNat + 1)) b.data.toList hbuf.pk
    (by simp; omega) (by simpa using hsmall) (by simpa using hbuf.len) i str (by omega) ?_
    (by rw [g5 _ (by decide) (by decide) (by decide)]; exact hTE)
    (by rw [g5 _ (by decide) (by decide) (by decide)]; exact hC) hI'
    (by simp only [Γ5, Γ4, Env.get_cons, ite_eq_right (show kQ ≠ kN by decide), ite_eq_left])
    (by simp only [Γ5, Env.get_cons, ite_eq_left])
    (by rw [g5 _ (by decide) (by decide) (by decide)]; exact hBA)
  rw [hstr]
  show s'.toUTF8.data.toList = _
  rw [hutf, extract_toList, hp1]

/-! ## `natVal` -/

theorem lt_of_byteAt {b : ByteArray} (hp : Plat b) {i : USize} (h : byteAt b i = 34) : i.toNat < b.size := by
  by_cases hl : i.toNat < b.size
  · exact hl
  · have : byteAt b i = 0 := by
      rw [byteAt_eq hp i]; simp [List.getElem?_eq_none (by simp; omega : b.data.toList.length ≤ i.toNat)]
    rw [this] at h; simp at h

/-- What a successful `scanQuotedNat` gives: the closing quote `c` ends the digit run after `v`. -/
theorem scanQuotedNat_facts {b : ByteArray} (hp : Plat b) {v e : USize} {n : Nat}
    (h : ConLeche.Frontend.scanQuotedNat b v = .ok n e) :
    ∃ c : USize, v.toNat < b.size ∧ c.toNat < b.size ∧ e.toNat = c.toNat + 1 ∧ (v + 1).toNat = v.toNat + 1 ∧
      c.toNat = skipDigitsL b.data.toList (v + 1).toNat ∧ n = ConLeche.Frontend.readNatAt b (v + 1) c := by
  unfold ConLeche.Frontend.scanQuotedNat at h
  by_cases hb : byteAt b v = 34
  · rw [if_neg (by simp [hb])] at h
    have hv := lt_of_byteAt hp hb
    have hv1 : (v + 1).toNat = v.toNat + 1 := ConLeche.Frontend.usizeStep b v ((hp.lt_iff v).mpr hv)
    by_cases hc : (ConLeche.Frontend.skipDigits b (v + 1) == v + 1 ||
        byteAt b (ConLeche.Frontend.skipDigits b (v + 1)) != 34) = true
    · rw [if_pos hc] at h; simp at h
    · rw [if_neg hc] at h
      simp only [ScanRes.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hc
      have hcl := lt_of_byteAt hp hc.2
      refine ⟨_, hv, hcl, ConLeche.Frontend.usizeStep b _ ((hp.lt_iff _).mpr hcl), hv1,
        skipDigits_eq hp _ _ rfl, rfl⟩
  · rw [if_pos (by simp [hb])] at h; simp at h

/-- `natVal n` at index `i`, `n` in `kW` (below the cap): `litWord` interns it. -/
def exNatVP : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
    (.seq (.call (some (some (.local, fh), none)) ConPanqueque.T.Str.fLitW [vv kW])
      (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0))))

theorem exNatV_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcW : C.code.lookup ConPanqueque.T.Str.fLitW =
      some ([(ConPanqueque.T.Str.wV, .one)], ConPanqueque.T.Str.lwBody C, .one))
    (hcB : C.code.lookup ConPanqueque.T.Big.fLitB =
      some ([(ConPanqueque.T.Big.iLx, .one)], ConPanqueque.T.Big.litBlkBody C, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i n : Nat) (hi : i < 2 ^ 64) (hn : n < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hW : Γ.get kW = some (BitVec.ofNat 64 n)) :
    SpecR (Inv (σ := σ) C s Γ M D) exNatVP s (parseExprEntryD st i (.natVal n)) (ExPost C jE cap st i) := by
  unfold exNatVP
  refine specR_exFresh (hD fx (by simp)) st jE cap hrel hcap i hi hTE hC hI (fun hic hg => ?_)
  have hm : parseExprEntryD st i (.natVal n) =
      (internE (.lit (.natVal n)) >>= fun e => (pure { st with exprs := st.exprs.insert i e } : AM StateD)) := by
    simp [parseExprEntryD, StateD.freshExpr, IdTable.bound_eq, hg]
  rw [hm]
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, ite_eq_right h]
  refine ConPanqueque.T.Big.specR_callKH fh ConPanqueque.T.Str.fLitW [ConPanqueque.T.Str.wV] [vv kW]
    (ConPanqueque.T.Str.lwBody C) [BitVec.ofNat 64 n] (by decide) rfl (hD fh (by simp)) hcW
    ⟨by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hW, trivial⟩
    (ConPanqueque.T.Str.lw_spec ra C hok hcB s n hn) (fun a s' H' hp => ?_)
  refine specR_weakenH hp ?_
  have g2 : ∀ y, y ≠ fh → y ≠ fx → Env.get ((fh, Enc.idxW a) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hTE) i hic a
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

/-- A `natVal` line: the quoted-number scanner gives the end, `readNatSat` the value of the digits
between the quotes; a value at the cap hangs. -/
def natVLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo kSE fRecNatVal [vv kBA, vv kBN, vv kPos])
  (.seq (.assign .local kQ (.op .add [vv kPos, .const 1]))
  (.seq (.assign .local kN (.op .sub [vv kSE, .const 1]))
  (.seq (callTo kW fReadNat [vv kBA, vv kQ, vv kN])
  (.ite (.cmp .lower (vv kW) (.const (BitVec.ofNat 64 natCap)))
    (capG fI exNatVP) (bigNatP C)))))

theorem natVLine_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcQ : C.code.lookup fRecNatVal = some ([(sB, .one), (sN, .one), (sI, .one)], qnFun, .one))
    (hcR : C.code.lookup fReadNat = some ([(sB, .one), (sI, .one), (sE, .one)], rnFun, .one))
    (hcW : C.code.lookup ConPanqueque.T.Str.fLitW =
      some ([(ConPanqueque.T.Str.wV, .one)], ConPanqueque.T.Str.lwBody C, .one))
    (hcB : C.code.lookup ConPanqueque.T.Big.fLitB =
      some ([(ConPanqueque.T.Big.iLx, .one)], ConPanqueque.T.Big.litBlkBody C, .one))
    (hcM : C.code.lookup ConPanqueque.T.Big.fMul = some (ConPanqueque.T.Big.mulParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.mulBody C, .one))
    (hcA : C.code.lookup ConPanqueque.T.Big.fAdd = some (ConPanqueque.T.Big.addParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.addBody C, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kSE, kQ, kN, kW, fx, fh, kD2, kM2, kH2, kL2, kX2, kT2, kY2, kP2, kS2], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (n : Nat)
    (hr : ConLeche.Frontend.scanQuotedNat b pos = .ok n e) (i : Nat)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (natVLineP C) s (parseExprEntryD st i (.natVal n)) (ExPost C jE cap st i) := by
  have hplat := hbuf.plat
  have hsmall := hbuf.small
  obtain ⟨c, hvb, hcb, hec, hv1, hcs, hn⟩ := scanQuotedNat_facts hplat hr
  unfold natVLineP
  refine specR_retP3 kSE fRecNatVal sB sN sI qnFun (vv kBA) (vv kBN) (vv kPos) (cellA C bufJ)
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 pos.toNat) _ (by decide) (by decide) (by decide) (hD _ (by simp)) hcQ
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hP)
    (fun t callee ht c1 c2 c3 => slotCall (s := s) (D := D) hok hbuf hsc pos qnFun _ (fun u hb hc l1 l2 l3 =>
      qnFun_sound u (cellA C bufJ) b hplat hb hc.2.1 pos (Nat.le_of_lt hvb) l1 l2 l3) t callee _ _ ht c1 c2 c3)
    (fun w3 ⟨ee, hw3, hee, n', hs'⟩ => ?_)
  have hee' : ee = e := by rw [hr] at hs'; simp only [ScanRes.ok.injEq] at hs'; exact hs'.2.symm
  subst hee'
  let Γ3 : Env := (kSE, w3) :: Γ
  have g3 : ∀ y, y ≠ kSE → Γ3.get y = Γ.get y := fun y h0 => by simp only [Γ3, Env.get_cons, ite_eq_right h0]
  refine specR_assignI kQ _ (BitVec.ofNat 64 (pos.toNat + 1)) (hD _ (by simp))
    (by simp only [sev, vv]; rw [g3 _ (by decide), hP]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add64]) ?_
  let Γ4 : Env := (kQ, BitVec.ofNat 64 (pos.toNat + 1)) :: Γ3
  refine specR_assignI kN _ (BitVec.ofNat 64 c.toNat) (hD _ (by simp))
    (by simp only [sev, vv, Γ4, Γ3, Env.get_cons, ite_eq_right (show kSE ≠ kQ by decide), ite_eq_left, hw3]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
          BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), hec]; simp) ?_
  let Γ5 : Env := (kN, BitVec.ofNat 64 c.toNat) :: Γ4
  have g5 : ∀ y, y ≠ kN → y ≠ kQ → y ≠ kSE → Γ5.get y = Γ.get y := fun y hn hq hs => by
    simp only [Γ5, Γ4, Env.get_cons, ite_eq_right hn, ite_eq_right hq]; exact g3 y hs
  refine specR_retP3 kW fReadNat sB sI sE rnFun (vv kBA) (vv kQ) (vv kN) (cellA C bufJ)
    (BitVec.ofNat 64 (pos.toNat + 1)) (BitVec.ofNat 64 c.toNat) _ (by decide) (by decide) (by decide)
    (hD _ (by simp)) hcR
    (by simp only [sev, vv]; rw [g5 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by simp only [sev, vv, Γ5, Γ4, Env.get_cons, ite_eq_right (show kQ ≠ kN by decide), ite_eq_left])
    (by simp only [sev, vv, Γ5, Env.get_cons, ite_eq_left])
    (fun t callee ht c1 c2 c3 => by
      have hb := bytesAt_congr (t := t)
        (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _))
        (u := callEntryStateHOLFinite t callee) rfl rfl rfl
      exact retP_of_retSpec (rnFun_refines _ (cellA C bufJ) b hplat hb (pos + 1) c (by omega) hcs c1
        c3 (by rw [hv1]; exact c2)) (P := fun w => w = BitVec.ofNat 64 (min n natCap)) (by rw [hn]))
    (fun w4 hw4 => ?_)
  subst hw4
  let Γ6 : Env := (kW, BitVec.ofNat 64 (min n natCap)) :: Γ5
  refine specR_ifI _ _ (sev_lower Γ6 (vv kW) _ (min n natCap) natCap
    (by simp [sev, vv, Γ6, Env.get_cons]) rfl
    (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) natCap_lt) natCap_lt) (fun hw => ?_) (fun hw => ?big)
  case big =>
    have hbig : natCap ≤ n := by
      by_cases h : min n natCap < natCap
      · simp [bw, h] at hw
      · omega
    have hge := skipL_ge isDigitN b.data.toList _ (pos + 1).toNat rfl
    have hall := skipL_all isDigitN b.data.toList _ (pos + 1).toNat rfl
    simp only [skipDigitsL] at hcs
    have g6' : ∀ y, y ≠ kW → y ≠ kN → y ≠ kQ → y ≠ kSE → Γ6.get y = Γ.get y := fun y hw hn hq hs => by
      simp only [Γ6, Env.get_cons, ite_eq_right hw]; exact g5 y hn hq hs
    refine bigNat_spec ra C hok hcR hcM hcA hcB s Γ6 M D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
      st jE cap hrel hcap bufJ b hbuf (pos.toNat + 1) c.toNat (by rw [← hv1]; omega) (by omega)
      (fun k hk a1 a2 => hall k hk (by rw [hv1]; exact a1) (by rw [← hcs]; exact a2)) n
      (by rw [hn, readNatAt_eq hplat (pos + 1) c hcs, hv1]) hbig i
      (by rw [g6' _ (by decide) (by decide) (by decide) (by decide)]; exact hTE)
      (by rw [g6' _ (by decide) (by decide) (by decide) (by decide)]; exact hC)
      (by rw [g6' _ (by decide) (by decide) (by decide) (by decide)]; exact hI)
      (by simp (config := {decide := true}) [Γ6, Γ5, Γ4, Env.get_cons])
      (by simp (config := {decide := true}) [Γ6, Γ5, Env.get_cons])
      (by rw [g6' _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
  have hl : min n natCap < natCap := by
    by_cases h : min n natCap < natCap
    · exact h
    · simp [bw, h] at hw
  have hnc : n < natCap := by omega
  have hmn : min n natCap = n := by omega
  have g6 : ∀ y, y ≠ kW → y ≠ kN → y ≠ kQ → y ≠ kSE → Γ6.get y = Γ.get y := fun y hw hn hq hs => by
    simp only [Γ6, Env.get_cons, ite_eq_right hw]; exact g5 y hn hq hs
  refine specR_capG fI i (by rw [g6 _ (by decide) (by decide) (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  have := natCap_lt
  exact exNatV_spec ra C hok hcW hcB s _ M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp)) st jE cap hrel hcap i n (by omega) (by omega)
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide)]; exact hTE)
    (by rw [g6 _ (by decide) (by decide) (by decide) (by decide)]; exact hC) hI'
    (by simp [Γ6, Env.get_cons, hmn])

/-! ## The line functions and the dispatcher's branches -/

def strVL : List MlS := [kQ, kSE, kN, fx, fh, kKA0, kKA, kK, kC, kS, kW, kJ, kL1]

theorem strVL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ strVL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [strVL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

def natVL : List MlS := [kSE, kQ, kN, kW, fx, fh, kD2, kM2, kH2, kL2, kX2, kT2, kY2, kP2, kS2]

theorem natVL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ natVL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [natVL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

theorem strVCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcN : C.code.lookup fInternLitStr = some ([(pKeyN, .one), (lEn, .one), (lHn, .one)], litStrBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcS : C.code.lookup fStr = some ([(sB, .one), (sN, .one), (sI, .one)], ssFun, .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs)
    (hcap : 8 * cap < 2 ^ 64) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (str : String) (hr : scanString b pos = .ok str e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ strVL)) (strVLineP C) s (parseExprEntryD st i (.strVal str))
      (ExPost C jE cap st i) :=
  strVLine_spec ra C hok hcN hsc hcS s _ [] _
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +decide [strVL, ctxLocals])
    st jE cap hrel hcap bufJ b hbuf pos e str hr i (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_I ..)
    (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..)

theorem natVCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcQ : C.code.lookup fRecNatVal = some ([(sB, .one), (sN, .one), (sI, .one)], qnFun, .one))
    (hcR : C.code.lookup fReadNat = some ([(sB, .one), (sI, .one), (sE, .one)], rnFun, .one))
    (hcW : C.code.lookup ConPanqueque.T.Str.fLitW =
      some ([(ConPanqueque.T.Str.wV, .one)], ConPanqueque.T.Str.lwBody C, .one))
    (hcB : C.code.lookup ConPanqueque.T.Big.fLitB =
      some ([(ConPanqueque.T.Big.iLx, .one)], ConPanqueque.T.Big.litBlkBody C, .one))
    (hcM : C.code.lookup ConPanqueque.T.Big.fMul = some (ConPanqueque.T.Big.mulParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.mulBody C, .one))
    (hcA : C.code.lookup ConPanqueque.T.Big.fAdd = some (ConPanqueque.T.Big.addParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.addBody C, .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs)
    (hcap : 8 * cap < 2 ^ 64) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (n : Nat) (hr : ConLeche.Frontend.scanQuotedNat b pos = .ok n e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ natVL)) (natVLineP C) s (parseExprEntryD st i (.natVal n))
      (ExPost C jE cap st i) :=
  natVLine_spec ra C hok hsc hcQ hcR hcW hcB hcM hcA s _ [] _
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +decide [natVL, ctxLocals])
    st jE cap hrel hcap bufJ b hbuf pos e n hr i (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_I ..)
    (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..)

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

/-- The `strVal` branch. -/
theorem brStrV {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcN : C.code.lookup fInternLitStr = some ([(pKeyN, .one), (lEn, .one), (lHn, .one)], litStrBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcS : C.code.lookup fStr = some ([(sB, .one), (sN, .one), (sI, .one)], ssFun, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue strVL (strVLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 13) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_13 hm hta
  obtain ⟨-, v, e, str, rfl, hws, hsc'⟩ := he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  exact specR_exLineCall kR0 fL strVL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (strVL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (strVCore ra C hok hcN hsc hcS s st jN jL jE cap rb capD hfs.tE hfs.lay.cap8 bufJ b hbuf v e str hsc' idx)
    hk

/-- The `natVal` branch. -/
theorem brNatV {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcQ : C.code.lookup fRecNatVal = some ([(sB, .one), (sN, .one), (sI, .one)], qnFun, .one))
    (hcR : C.code.lookup fReadNat = some ([(sB, .one), (sI, .one), (sE, .one)], rnFun, .one))
    (hcW : C.code.lookup ConPanqueque.T.Str.fLitW =
      some ([(ConPanqueque.T.Str.wV, .one)], ConPanqueque.T.Str.lwBody C, .one))
    (hcB : C.code.lookup ConPanqueque.T.Big.fLitB =
      some ([(ConPanqueque.T.Big.iLx, .one)], ConPanqueque.T.Big.litBlkBody C, .one))
    (hcM : C.code.lookup ConPanqueque.T.Big.fMul = some (ConPanqueque.T.Big.mulParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.mulBody C, .one))
    (hcA : C.code.lookup ConPanqueque.T.Big.fAdd = some (ConPanqueque.T.Big.addParams.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.Big.addBody C, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natVL (natVLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 20) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_20 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanQuotedNat)
    (wrap := fun n => LinePayload.expr (.natVal n)) he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  exact specR_exLineCall kR0 fL natVL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (natVL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (natVCore ra C hok hsc hcQ hcR hcW hcB hcM hcA s st jN jL jE cap rb capD hfs.tE hfs.lay.cap8 bufJ b hbuf v e r' hsc' idx)
    hk

end

end ConPanqueque.Front
