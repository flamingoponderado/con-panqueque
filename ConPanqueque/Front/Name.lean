import ConPanqueque.Front.KeyCopy
import ConPanqueque.T.SubstLsTop
import ConPanqueque.T.Copy

/-! # Name records into the store (`parseNameEntryD`)

A string name `str pre s` at index `i`: the prefix's handle from the name table, the freshness test,
then the key (the prefix handle, then the string's bytes one per word) built in freshly allocated
heap cells, the ported intern, the table write.  The string's bytes are the buffer's from byte `q`
(the scanner's plain string). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable NameRec)

variable {σ : Type}

def kKA0 := ofString "kka0"
def kL1 := ofString "kl1"

theorem frontOK_H {C : Ctx} (hf : FrontOK C) (H : List (BitVec 64)) : FrontOK (ctxH C H) := by
  cases hf; constructor <;> assumption

theorem tblRel_prefix {k : IdxKind} {H H' : List (BitVec 64)} {j cap : Nat} {tbl : IdTable (Idx k)}
    (h : TblRel H j cap tbl) (hp : H <+: H') : TblRel H' j cap tbl := by
  refine ⟨fun i hi => ?_, h.2⟩
  have e := h.1 i hi
  have hl : j + i < H.length := by
    by_cases hl : j + i < H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at e; cases e
  obtain ⟨r, rfl⟩ := hp; rw [List.getElem?_append_left hl]; exact e

theorem packed_prefix {H H' : List (BitVec 64)} {j0 : Nat} {bs : List UInt8} (h : Packed H j0 bs)
    (hp : H <+: H') : Packed H' j0 bs := by
  intro i hi
  obtain ⟨w, hw, hb⟩ := h i hi
  have hl : j0 + i / 8 < H.length := by
    by_cases hl : j0 + i / 8 < H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hw; cases hw
  obtain ⟨r, rfl⟩ := hp; exact ⟨w, by rw [List.getElem?_append_left hl]; exact hw, hb⟩

theorem prefix_set_ge {l L : List (BitVec 64)} (h : l <+: L) (c : Nat) (hc : l.length ≤ c) (w : BitVec 64) :
    l <+: L.set c w := by
  obtain ⟨r, rfl⟩ := h
  refine ⟨r.set (c - l.length) w, ?_⟩
  rw [List.set_append_right _ _ (by omega)]

theorem prefix_kcH {l H : List (BitVec 64)} (h : l <+: H) (o : Nat) (ho : l.length ≤ o) (ws : List (BitVec 64)) :
    ∀ n, l <+: kcH H o ws n
  | 0 => h
  | n + 1 => prefix_set_ge (prefix_kcH h o ho ws n) _ (by omega) _

/-- After a name record: the store represented with the name table's cell written, the rest of
the parse state as it was. -/
def NmPost (C : Ctx) (jN cap : Nat) (st : StateD) (i : Nat) :
    StateD → BitVec 64 → AState → PState σ → Prop :=
  fun st' _ s' t' => ∃ w', SR (ctxH C (C.H.set (jN + i) w')) s' t' ∧
    TblRel (C.H.set (jN + i) w') jN cap st'.names ∧
    st'.levels = st.levels ∧ st'.exprs = st.exprs ∧ st'.decls = st.decls

/-- `str pre s` at index `i`: `fU` the prefix's index, `kQ` the string's first byte in the buffer,
`kN` its length, `kBA` the buffer's address. -/
def nmStrP (C : Ctx) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblFreshP fx (vv fTN) (vv fCap) (vv fI)
      (allocP C kKA0 (.shift .lsl (.op .add [vv kN, .const 1]) (.const 3))
        (.seq (.assign .local kKA (.op .add [vv kKA0, .const 8]))
        (.seq (.assign .local kK (.const 0))
        (.seq (.store (vv kKA0) (vv fy))
        (.seq kcLoop
        (.seq (.assign .local kL1 (.op .add [vv kN, .const 1]))
        (.seq (.call (some (some (.local, fh), none)) fInternNStr [vv kKA0, vv kL1, vv fy, vv kN])
          (tblSetP (vv fTN) (vv fI) (vv fh) (.return (.const 0)))))))))))

theorem nmStr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fx, fy, fh, kKA0, kKA, kK, kC, kS, kW, kJ, kL1], x ∈ D)
    (st : StateD) (jN cap : Nat) (hrel : TblRel C.H jN cap st.names) (hcap : 8 * cap < 2 ^ 64)
    (bufJ q len : Nat) (bs : List UInt8) (hpk : Packed C.H bufJ bs) (hqn : q + len ≤ bs.length)
    (hbl : bs.length < 2 ^ 59) (hbuf : bufJ + bs.length / 8 < C.H.length)
    (i pre : Nat) (str : String) (hi : i < 2 ^ 64) (hpre : pre < 2 ^ 64)
    (hstr : str.toByteArray.data.toList = (bs.drop q).take len)
    (hTN : Γ.get fTN = some (cellA C jN)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 pre))
    (hQ : Γ.get kQ = some (BitVec.ofNat 64 q)) (hN : Γ.get kN = some (BitVec.ofNat 64 len))
    (hBA : Γ.get kBA = some (cellA C bufJ)) :
    SpecR (Inv (σ := σ) C s Γ M D) (nmStrP C) s (parseNameEntryD st i (.str pre str)) (NmPost C jN cap st i) := by
  have hlay := hok.heapLay
  unfold nmStrP
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hrel hcap (vv fTN) (vv fCap) (vv fU)
    (by simpa [sev, vv] using hTN) (by simpa [sev, vv] using hC) pre hpre (by simpa [sev, vv] using hU)
    (fun p hp => ?_)
  have g1 : ∀ y, y ≠ fy → Env.get ((fy, Enc.idxW p) :: (fy, Enc.idxW p + 1) :: Γ) y = Env.get Γ y :=
    fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_tblFreshI fx (hD fx (by simp)) jN cap st.names hrel hcap (vv fTN) (vv fCap) (vv fI)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTN)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) i hi
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hI) (fun hic hg => ?_)
  have hm : parseNameEntryD st i (.str pre str) =
      (internNNode (.str p str) >>= fun h => (pure { st with names := st.names.insert i h } : AM StateD)) := by
    simp [parseNameEntryD, StateD.freshName, StateD.name, IdTable.bound_eq, hg, hp]
  rw [hm]
  -- the key cells
  refine specR_allocI kKA0 (.shift .lsl (.op .add [vv kN, .const 1]) (.const 3)) (len + 1) (by omega)
    (hD kKA0 (by simp)) (fun v => by
      simp only [sev, vv, Env.get_cons, show (kN = kKA0) = False from by decide, show (kN = fx) = False from by decide,
        show (kN = fy) = False from by decide, if_false, hN, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.map_some, show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, if_true]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]; omega)
    (fun H' ws hpre' hwl hcapH => ?_)
  have hCH : C.H.length ≤ H'.length := hpre'.length_le
  let o := H'.length
  let C1 := ctxH C (H' ++ ws)
  have hl1 : (H' ++ ws).length = H'.length + (len + 1) := by simp [hwl]
  have g3 : ∀ y, y ≠ kKA0 → y ≠ fx → y ≠ fy →
      Env.get ((kKA0, cellA C o) :: (fx, 0) :: (fy, Enc.idxW p) :: (fy, Enc.idxW p + 1) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3]
  refine specR_assignI kKA _ (cellA C (o + 1)) (hD kKA (by simp))
    (by simp [sev, vv, Env.get_cons]; exact cellA_add8 C o) ?_
  refine specR_assignI kK (.const 0) 0 (hD kK (by simp)) rfl ?_
  refine specR_heapStoreI (C := C1) (ctxOK_H hok _) (vv kKA0) (vv fy) o (by simp only [C1, ctxH]; omega)
    (Enc.idxW p) (by simp [sev, vv, Env.get_cons]; rfl)
    (by simp [sev, vv, Env.get_cons, show fy ≠ kK from by decide, show fy ≠ kKA from by decide,
          show fy ≠ kKA0 from by decide, show fy ≠ fx from by decide]) ?_
  let H2 := (H' ++ ws).set o (Enc.idxW p)
  have hl2 : H2.length = H'.length + (len + 1) := by simp [H2, hl1]
  have hp2 : C.H <+: H2 := prefix_set_ge (hpre'.trans (List.prefix_append _ _)) o hCH _
  let wsb := (bs.drop q).map (fun b => BitVec.ofNat 64 b.toNat)
  have g5 : ∀ y, y ∉ [kK, kKA, kKA0, fx, fy] →
      Env.get ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: (fy, Enc.idxW p) ::
        (fy, Enc.idxW p + 1) :: Γ) y = Env.get Γ y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Env.get_cons, if_neg hy.1, if_neg hy.2.1, if_neg hy.2.2.1, if_neg hy.2.2.2.1, if_neg hy.2.2.2.2]
  refine kc_spec (C := ctxH C1 H2) (ctxOK_H hok _) (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp)) bufJ (o + 1) q len bs
    (packed_prefix hpk hp2) hqn (by omega) (by simp only [ctxH]; have := hp2.length_le; omega)
    (by simp only [ctxH]; omega) (by have := hok.heapLay; omega)
    (fun k hk i' hi' => by have := Nat.div_le_div_right (c := 8) (Nat.le_of_lt hi'); omega)
    (by rw [g5 _ (by decide)]; exact hBA)
    (by simp only [Env.get_cons, show (kKA = kK) = False from by decide, if_false, if_true]; rfl)
    (by rw [g5 _ (by decide)]; exact hQ)
    (by simp only [Env.get_cons, if_true]) (by rw [g5 _ (by decide)]; exact hN) ?_
  -- the key is in place
  let H3 := kcH H2 (o + 1) wsb len
  change SpecR (Inv (ctxH (ctxH C1 H2) H3) s (kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) ::
    (fx, 0) :: (fy, Enc.idxW p) :: (fy, Enc.idxW p + 1) :: Γ) H2 bufJ (o + 1) q wsb len) [] D) _ s _ _
  have hsl : str.toByteArray.data.toList.length = len := by rw [hstr]; simp; omega
  have hkl : (Enc.encStr ⟨p, str⟩).length = len + 1 := by simp [Enc.encStr, Enc.strW, hsl]
  have hl3 : H3.length = H'.length + (len + 1) := by simp [H3, kcH_length, hl2]
  have hp3 : C.H <+: H3 := prefix_kcH hp2 (o + 1) (by omega) wsb len
  have hkey : ∀ j (hj : j < (Enc.encStr ⟨p, str⟩).length), H3[o + j]? = some ((Enc.encStr ⟨p, str⟩)[j]) := by
    intro j hj
    rw [hkl] at hj
    simp only [H3]
    rw [kcH_get]
    cases j with
    | zero =>
      rw [if_neg (by omega)]
      simp [H2, Enc.encStr, List.getElem?_set, hl1]
      show H'.length < H'.length + (len + 1); omega
    | succ k =>
      rw [if_pos ⟨by omega, by omega, by omega⟩]
      have hk1 : k < str.toByteArray.data.toList.length := by omega
      simp only [Enc.encStr, List.getElem_cons_succ, Enc.strW, List.getElem_map]
      simp only [wsb, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
        show o + (k + 1) - (o + 1) = k by omega]
      rw [List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.getD_some, Option.some.injEq]
      congr 2
      have := congrArg (fun l => l[k]?) hstr
      simp only [List.getElem?_take, if_pos (show k < len by omega), List.getElem?_drop] at this
      rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem (by omega)] at this
      exact (Option.some.inj this).symm
  have gG : ∀ y, y ∉ [kK, kC, kS, kW, kJ] → y ∉ [kK, kKA, kKA0, fx, fy] →
      Env.get (kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: (fy, Enc.idxW p) ::
        (fy, Enc.idxW p + 1) :: Γ) H2 bufJ (o + 1) q wsb len) y = Env.get Γ y :=
    fun y h1 h2 => by rw [kcG_get _ _ _ _ _ _ y h1 len]; exact g5 y h2
  refine specR_assignI kL1 (.op .add [vv kN, .const 1]) (BitVec.ofNat 64 (len + 1)) (hD kL1 (by simp))
    (by simp only [sev, vv]; rw [gG _ (by decide) (by decide), hN]; simp only [Option.bind_eq_bind,
          Option.bind_some, Option.pure_def]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  have hfy : Env.get (kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: (fy, Enc.idxW p) ::
        (fy, Enc.idxW p + 1) :: Γ) H2 bufJ (o + 1) q wsb len) fy = some (Enc.idxW p) := by
    rw [kcG_get _ _ _ _ _ _ fy (by decide) len]
    simp only [Env.get_cons, show (fy = kK) = False from by decide, show (fy = kKA) = False from by decide,
      show (fy = kKA0) = False from by decide, show (fy = fx) = False from by decide, if_false, if_true]
  have hka0 : Env.get (kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: (fy, Enc.idxW p) ::
        (fy, Enc.idxW p + 1) :: Γ) H2 bufJ (o + 1) q wsb len) kKA0 = some (cellA C o) := by
    rw [kcG_get _ _ _ _ _ _ kKA0 (by decide) len]
    simp only [Env.get_cons, show (kKA0 = kK) = False from by decide, show (kKA0 = kKA) = False from by decide,
      if_false, if_true]
  refine specR_callNIA fh fInternNStr [pKeyN, lEn, lEp, lHn] [vv kKA0, vv kL1, vv fy, vv kN] nameStrBody
    [cellA C o, BitVec.ofNat 64 (len + 1), Enc.idxW p, BitVec.ofNat 64 len] (by decide) rfl (hD fh (by simp)) hcN
    ⟨by simp only [sev, vv, Env.get_cons, show (kKA0 = kL1) = False from by decide, if_false]; exact hka0,
     by simp [sev, vv, Env.get_cons],
     by simp only [sev, vv, Env.get_cons, show (fy = kL1) = False from by decide, if_false]; exact hfy,
     by simp only [sev, vv, Env.get_cons, show (kN = kL1) = False from by decide, if_false]
        rw [gG _ (by decide) (by decide)]; exact hN, trivial⟩
    (fun a w s' st => internNNode (.str p str) s = .ok (a, s') ∧ PostNm (ctxH (ctxH (ctxH C1 H2) H3) C.H) a w s' st)
    (fun a w s' H' => H' = C.H ∧ internNNode (.str p str) s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨C.H, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      have hs := nameStr_body_spec (σ := σ) ra (ctxH (ctxH C1 H2) H3) (ctxOK_H hok _) (frontOK_H hf _) s p str o C.H hp3
        (by omega) (by rw [hkl]; show o + (len + 1) ≤ H3.length; omega) (by rw [hkl]; omega) hkey
      rw [hkl, hsl] at hs
      exact hs _ (pre_of_lookups hu [pKeyN, lEn, lEp, lHn] _ rfl hlk)))
    (fun h w s2 H' ⟨e, hr2, hw⟩ => ?_)
  subst e; subst hw
  have eC : ctxH (ctxH (ctxH C1 H2) H3) C.H = C := ctxH_self C
  rw [eC]
  have gF : ∀ y, y ∉ [fh, kL1] → y ∉ [kK, kC, kS, kW, kJ] → y ∉ [kK, kKA, kKA0, fx, fy] →
      Env.get ((fh, Enc.idxW h) :: (kL1, BitVec.ofNat 64 (len + 1)) ::
        kcG ((kK, 0) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: (fx, 0) :: (fy, Enc.idxW p) ::
        (fy, Enc.idxW p + 1) :: Γ) H2 bufJ (o + 1) q wsb len) y = Env.get Γ y := by
    intro y h0 h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h0
    simp only [Env.get_cons, if_neg h0.1, if_neg h0.2]; exact gG y h1 h2
  refine specR_tblSetI hok jN cap st.names hrel hcap (vv fTN) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by decide)]; exact hTN) i hic h
    (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

theorem limbs_zero : Enc.limbs 0 = [] := by rw [Enc.limbs]; simp

theorem limbs_small (n : Nat) (h : n < 2 ^ 64) :
    Enc.limbs n = if n = 0 then [] else [BitVec.ofNat 64 n] := by
  rw [Enc.limbs]
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [h0, dif_neg, if_false, not_false_eq_true]
    rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Enc.limbs]; simp

/-- `num pre n` at index `i`: `fU` the prefix's index, `fV2` the (capped) number. -/
def nmNumP (C : Ctx) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblFreshP fx (vv fTN) (vv fCap) (vv fI)
      (.ite (.cmp .lower (vv fV2) (.const (BitVec.ofNat 64 natCap)))
        (allocP C kKA0 (.const (BitVec.ofNat 64 16))
          (.seq (.store (vv kKA0) (vv fy))
          (.seq (.store (.op .add [vv kKA0, .const 8]) (vv fV2))
          (.seq (.assign .local kL1 (.op .add [.const 1, .cmp .notEqual (vv fV2) (.const 0)]))
          (.seq (.call (some (some (.local, fh), none)) fInternNNum [vv kKA0, vv kL1, vv fy, vv fV2])
            (tblSetP (vv fTN) (vv fI) (vv fh) (.return (.const 0))))))))
        hang))

theorem nmNum_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup fInternNNum = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lNw, .one)], nameNumBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fx, fy, fh, kKA0, kL1], x ∈ D)
    (st : StateD) (jN cap : Nat) (hrel : TblRel C.H jN cap st.names) (hcap : 8 * cap < 2 ^ 64)
    (i pre n : Nat) (hi : i < 2 ^ 64) (hpre : pre < 2 ^ 64)
    (hTN : Γ.get fTN = some (cellA C jN)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 pre))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 (min n natCap))) :
    SpecR (Inv (σ := σ) C s Γ M D) (nmNumP C) s (parseNameEntryD st i (.num pre n)) (NmPost C jN cap st i) := by
  have hlay := hok.heapLay
  unfold nmNumP
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hrel hcap (vv fTN) (vv fCap) (vv fU)
    (by simpa [sev, vv] using hTN) (by simpa [sev, vv] using hC) pre hpre (by simpa [sev, vv] using hU)
    (fun p hp => ?_)
  have g1 : ∀ y, y ≠ fy → Env.get ((fy, Enc.idxW p) :: (fy, Enc.idxW p + 1) :: Γ) y = Env.get Γ y :=
    fun y h => by simp only [Env.get_cons, if_neg h]
  refine specR_tblFreshI fx (hD fx (by simp)) jN cap st.names hrel hcap (vv fTN) (vv fCap) (vv fI)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTN)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) i hi
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hI) (fun hic hg => ?_)
  have g2 : ∀ y, y ≠ fx → y ≠ fy →
      Env.get ((fx, 0) :: (fy, Enc.idxW p) :: (fy, Enc.idxW p + 1) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, if_neg h1, if_neg h2]
  refine specR_ifI _ _ (sev_lower _ (vv fV2) (.const (BitVec.ofNat 64 natCap)) (min n natCap) natCap
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hV) rfl (by simp [natCap]; omega)
    (by simp [natCap])) (fun hw => ?_) (fun _ => specR_hangI)
  have hn : n < natCap := by
    by_cases h : min n natCap < natCap
    · omega
    · simp [bw, h] at hw
  have hmn : min n natCap = n := by omega
  rw [hmn] at hV
  have hm : parseNameEntryD st i (.num pre n) =
      (internNNode (.num p n) >>= fun h => (pure { st with names := st.names.insert i h } : AM StateD)) := by
    simp [parseNameEntryD, StateD.freshName, StateD.name, IdTable.bound_eq, hg, hp]
  rw [hm]
  refine specR_allocI kKA0 (.const (BitVec.ofNat 64 16)) 2 (by omega) (hD kKA0 (by simp)) (fun v => rfl)
    (fun H' ws hpre' hwl hcapH => ?_)
  have hCH : C.H.length ≤ H'.length := hpre'.length_le
  let C1 := ctxH C (H' ++ ws)
  have hl1 : (H' ++ ws).length = H'.length + 2 := by rw [List.length_append, hwl]
  have g3 : ∀ y, y ≠ kKA0 → y ≠ fx → y ≠ fy →
      Env.get ((kKA0, cellA C H'.length) :: (fx, 0) :: (fy, Enc.idxW p) :: (fy, Enc.idxW p + 1) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3]
  refine specR_heapStoreI (C := C1) (ctxOK_H hok _) (vv kKA0) (vv fy) H'.length (by simp only [C1, ctxH]; omega)
    (Enc.idxW p) (by simp [sev, vv, Env.get_cons]; rfl)
    (by simp [sev, vv, Env.get_cons, show fy ≠ kKA0 from by decide, show fy ≠ fx from by decide]) ?_
  let H2 := (H' ++ ws).set H'.length (Enc.idxW p)
  have hl2 : H2.length = H'.length + 2 := by simp [H2, hwl]
  refine specR_heapStoreI (C := ctxH C1 H2) (ctxOK_H hok _) (.op .add [vv kKA0, .const 8]) (vv fV2) (H'.length + 1)
    (by simp only [ctxH]; omega) (BitVec.ofNat 64 n)
    (by simp [sev, vv, Env.get_cons]; exact cellA_add8 C H'.length)
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide)]; exact hV) ?_
  let H3 := H2.set (H'.length + 1) (BitVec.ofNat 64 n)
  have hl3 : H3.length = H'.length + 2 := by simp [H3, H2, hwl]
  have hp3 : C.H <+: H3 := prefix_set_ge (prefix_set_ge (hpre'.trans (List.prefix_append _ _)) _ hCH _) _ (by omega) _
  have hkl : (Enc.encNum ⟨p, n⟩).length = (if n = 0 then 1 else 2) := by
    by_cases h0 : n = 0
    · subst h0; simp [Enc.encNum, limbs_zero]
    · simp [Enc.encNum, limbs_small n (by simp [natCap] at hn; omega), h0]
  refine specR_assignI kL1 _ (BitVec.ofNat 64 (Enc.encNum ⟨p, n⟩).length) (hD kL1 (by simp)) (by
    simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide), hV, hkl]
    by_cases h0 : n = 0
    · subst h0; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : BitVec.ofNat 64 n ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e; simp [natCap] at this hn; omega
      simp only [h0, if_false, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
      simp only [beq_eq_false_iff_ne.mpr this, Bool.not_false, if_true]; rfl) ?_
  have hkey : ∀ j (hj : j < (Enc.encNum ⟨p, n⟩).length), H3[H'.length + j]? = some ((Enc.encNum ⟨p, n⟩)[j]) := by
    intro j hj
    have hj2 : j < 2 := by rw [hkl] at hj; split at hj <;> omega
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · show (H2.set (H'.length + 1) _)[H'.length + 0]? = _
      rw [List.getElem?_set_ne (by omega)]
      show ((H' ++ ws).set H'.length (Enc.idxW p))[H'.length + 0]? = _
      rw [Nat.add_zero, List.getElem?_set_self (by rw [hl1]; omega)]
      simp [Enc.encNum]
    · have h0 : n ≠ 0 := by intro h; rw [hkl, if_pos h] at hj; omega
      show (H2.set (H'.length + 1) _)[H'.length + 1]? = _
      rw [List.getElem?_set_self (by rw [hl2]; omega)]
      simp [Enc.encNum, limbs_small n (by simp [natCap] at hn; omega), h0]
  refine specR_callNIA fh fInternNNum [pKeyN, lEn, lEp, lNw] [vv kKA0, vv kL1, vv fy, vv fV2] nameNumBody
    [cellA C H'.length, BitVec.ofNat 64 (Enc.encNum ⟨p, n⟩).length, Enc.idxW p, (UInt64.ofNat n).toBitVec]
    (by decide) rfl (hD fh (by simp)) hcN
    ⟨by simp [sev, vv, Env.get_cons, show kKA0 ≠ kL1 from by decide],
     by simp [sev, vv, Env.get_cons],
     by simp [sev, vv, Env.get_cons, show fy ≠ kL1 from by decide, show fy ≠ kKA0 from by decide,
          show fy ≠ fx from by decide],
     by simp only [sev, vv]
        rw [Env.get_cons, if_neg (by decide), g3 _ (by decide) (by decide) (by decide), hV]
        congr 1, trivial⟩
    (fun a w s' st => internNNode (.num p n) s = .ok (a, s') ∧ PostNm (ctxH (ctxH (ctxH C1 H2) H3) C.H) a w s' st)
    (fun a w s' H' => H' = C.H ∧ internNNode (.num p n) s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨C.H, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact nameNum_body_spec (σ := σ) ra (ctxH (ctxH C1 H2) H3) (ctxOK_H hok _) (frontOK_H hf _) s p n H'.length C.H
        hp3 (by omega) (by show H'.length + _ ≤ H3.length; rw [hl3, hkl]; split <;> omega)
        (by rw [hkl]; split <;> omega) hkey _ (pre_of_lookups hu [pKeyN, lEn, lEp, lNw] _ rfl hlk)))
    (fun h w s2 H' ⟨e, hr2, hw⟩ => ?_)
  subst e; subst hw
  rw [show ∀ X Y, ctxH (ctxH (ctxH C1 X) Y) C.H = C from fun X Y => ctxH_self C]
  have gF : ∀ y, y ≠ fh → y ≠ kL1 → y ≠ kKA0 → y ≠ fx → y ≠ fy →
      Env.get ((fh, Enc.idxW h) :: (kL1, BitVec.ofNat 64 (Enc.encNum ⟨p, n⟩).length) ::
        (kKA0, cellA C H'.length) :: (fx, 0) :: (fy, Enc.idxW p) :: (fy, Enc.idxW p + 1) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 h4 h5 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  refine specR_tblSetI hok jN cap st.names hrel hcap (vv fTN) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTN) i hic h
    (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

end ConPanqueque.Front
