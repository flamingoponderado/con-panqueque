import ConPanqueque.Front.Steps
import ConPanqueque.T.EIntern2

/-! # `const` expression records into the store

`const n us` at index `i`: the freshness test, the name's handle, then the universe arguments: their
count (`nnFun` until the sentinel), a key of that many heap cells filled with the levels' handles
(`nnFun` for each index, then the level table), the ported `internLs`, the ported `internConst`,
the table write.  The twin is `parseExprEntryD` at `.const`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable ExprRec scanNatList)

variable {σ : Type}

def kX := ofString "kx"
def kY := ofString "ky"
def kG2 := ofString "kgo"
def kBN := ofString "kbn"
def kLs := ofString "kls"

/-- One level of the list: its index from the buffer, its handle, into key cell `kK`. -/
def fillBody : ProgHOL 64 :=
  .seq (callTo kX fNth [vv kBA, vv kBN, vv fV2, vv kK])
    (tblGetP kY (vv fTL) (vv fCap) (vv kX)
      (.seq (.store (.op .add [vv kKA0, .shift .lsl (vv kK) (.const 3)]) (vv kY))
        (.assign .local kK (.op .add [vv kK, .const 1]))))

/-- After the count: the key, the level list, the constant, the table write. -/
def exConstTail (C : Ctx) : ProgHOL 64 :=
  allocP C kKA0 (.shift .lsl (vv kK) (.const 3))
    (.seq (.assign .local kN (vv kK))
    (.seq (.assign .local kK (.const 0))
    (.seq (.while (.cmp .lower (vv kK) (vv kN)) fillBody)
    (.seq (.call (some (some (.local, kLs), none)) fInternLs [vv kKA0, vv kN])
    (.seq (.call (some (some (.local, fh), none)) fInternConst [vv fy, vv kLs])
      (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0))))))))

/-- The key words: each index's handle (a default where the table has none; the loop stops there). -/
def lvWords (st : StateD) (us : List Nat) : List (BitVec 64) :=
  us.map (fun x => Enc.idxW ((st.levels.get? x).getD default))

theorem mapM_level_ok (st : StateD) :
    ∀ (us : List Nat), (∀ j (hj : j < us.length), (st.levels.get? us[j]).isSome) →
      us.mapM st.level = pure (us.map (fun x => (st.levels.get? x).getD default))
  | [], _ => rfl
  | x :: xs, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨hx, hhx⟩ := Option.isSome_iff_exists.mp h0
    have ih := mapM_level_ok st xs (fun j hj => by have := h (j + 1) (by simp; omega); simpa using this)
    simp [List.mapM_cons, StateD.level, hhx, ih]

theorem natCap_lt_sent : natCap < nnSent := by simp [natCap, nnSent]

/-- The input buffer's facts, at the context the frontend starts from. -/
structure BufOK (C : Ctx) (bufJ : Nat) (b : ByteArray) : Prop where
  pk : Packed C.H bufJ b.data.toList
  al : (cellA C bufJ).toNat % 8 = 0
  len : bufJ + b.size / 8 < C.H.length
  plat : Plat b
  small : b.size < 2 ^ 59

/-- The buffer is readable in any state represented at an image that keeps its cells. -/
theorem bufOK_bytes {C : Ctx} (hok : CtxOK C) {bufJ : Nat} {b : ByteArray} (hb : BufOK C bufJ b)
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {H : List (BitVec 64)} {t : PState σ}
    (ht : Inv (ctxH C H) s Γ M D t) (hpk : Packed H bufJ b.data.toList) (hlen : C.H.length ≤ H.length) :
    BytesAt t (cellA C bufJ) b.data.toList := by
  have hHN : H.length ≤ C.HN := inv_heapLen ht
  have hlay := hok.heapLay
  have hlb := hb.len
  refine bytesAt_of_heap ht.sr bufJ _ hpk hb.al ?_
  have : (cellA C bufJ).toNat = C.HB.toNat + 8 * bufJ := by
    unfold cellA; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  show (cellA C bufJ).toNat + _ < _
  rw [this]; simp; omega

theorem lvWords_getD (st : StateD) (us : List Nat) (i : Nat) (hi : i < us.length) :
    (lvWords st us).getD i 0 = Enc.idxW ((st.levels.get? us[i]).getD default) := by
  simp [lvWords, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem packed_kcH {H : List (BitVec 64)} {j0 : Nat} {bs : List UInt8} (h : Packed H j0 bs) (o : Nat)
    (ho : ∀ i, i < bs.length → j0 + i / 8 < o) (ws : List (BitVec 64)) : ∀ n, Packed (kcH H o ws n) j0 bs
  | 0 => h
  | n + 1 => packed_set (packed_kcH h o ho ws n) _ (fun i hi => by have := ho i hi; omega) _

/-- One iteration of the fill loop. -/
theorem fill_step (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (s : AState) (D : List MlS) (hD : ∀ x ∈ [kX, kY, kK], x ∈ D)
    (st : StateD) (jL cap : Nat) (hrel : TblRel C.H jL cap st.levels) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos : USize) (us : List Nat)
    (e0 : USize) (hpos : pos.toNat ≤ b.size) (hs : scanNatList b pos = .ok us e0)
    (H1 : List (BitVec 64)) (hp1 : C.H <+: H1) (o : Nat) (ho : C.H.length ≤ o) (hko : o + us.length ≤ H1.length)
    (i : Nat) (hi : i < us.length) (hk62 : us.length < 2 ^ 61) (Γ : Env)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 pos.toNat)) (hK : Γ.get kK = some (BitVec.ofNat 64 i))
    (hTL : Γ.get fTL = some (cellA C jL)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hKA : Γ.get kKA0 = some (cellA C o)) :
    Step (Inv (σ := σ) (ctxH C (kcH H1 o (lvWords st us) i)) s Γ [] D) fillBody
      (fun t' => (st.levels.get? us[i]).isSome ∧
        Inv (ctxH C (kcH H1 o (lvWords st us) (i + 1))) s
          ((kK, BitVec.ofNat 64 (i + 1)) :: (kY, Enc.idxW ((st.levels.get? us[i]).getD default)) ::
            (kY, Enc.idxW ((st.levels.get? us[i]).getD default) + 1) :: (kX, nnRes us i) :: Γ) [] D t') := by
  have hlay := hok.heapLay
  let ws := lvWords st us
  have hHl : (kcH H1 o ws i).length = H1.length := kcH_length _ _ _ _
  have hpi : C.H <+: kcH H1 o ws i := prefix_kcH hp1 o ho ws i
  have hbl : ∀ i', i' < b.data.toList.length → bufJ + i' / 8 < o := by
    intro i' hi'; have := hbuf.len; have := Nat.div_le_div_right (c := 8) (Nat.le_of_lt hi'); simp at hi' ⊢; omega
  have hpk : Packed (kcH H1 o ws i) bufJ b.data.toList :=
    packed_kcH (packed_prefix hbuf.pk hp1) o hbl ws i
  unfold fillBody
  refine step_seq (step_call4I (C := ctxH C (kcH H1 o ws i)) kX fNth sB sN sI sL nnFun (vv kBA) (vv kBN) (vv fV2)
    (vv kK) (cellA C bufJ) (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 pos.toNat) (BitVec.ofNat 64 i) (nnRes us i)
    (by decide) (hD kX (by simp)) hcN (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN)
    (by simpa [sev, vv] using hV) (by simpa [sev, vv] using hK)
    (fun t callee ht h1 h2 h3 h4 => retSpec_of_retP (nnFun_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b
      hbuf.plat (bytesAt_congr (bufOK_bytes hok hbuf ht hpk (by have := hpi.length_le; omega)) rfl rfl rfl)
      (hnc _ (by show t.code = C.code; exact ht.sr.code)) pos hpos i (by omega) us e0 hs h1 h2 h3 h4))) ?_
  have hnr : nnRes us i = BitVec.ofNat 64 (min us[i] natCap) := by simp [nnRes, hi]
  have g1 : ∀ y, y ≠ kX → Env.get ((kX, nnRes us i) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, if_neg h]
  refine step_tblGetI (C := ctxH C (kcH H1 o ws i)) kY (hD kY (by simp)) jL cap st.levels
    (tblRel_prefix hrel hpi) hcap (vv fTL) (vv fCap) (vv kX)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTL) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC)
    (min us[i] natCap) (by simp [natCap]; omega) (by simp [sev, vv, Env.get_cons, hnr]) (fun h hh => ?_)
  have hlt : us[i] < natCap := by
    by_cases hl : us[i] < natCap
    · exact hl
    · have : min us[i] natCap = natCap := by omega
      rw [this, hrel.2 natCap hcapN] at hh; cases hh
  have hmin : min us[i] natCap = us[i] := by omega
  rw [hmin] at hh
  have hws : ws.getD i 0 = Enc.idxW h := by rw [lvWords_getD st us i hi, hh]; rfl
  have g2 : ∀ y, y ≠ kY → y ≠ kX →
      Env.get ((kY, Enc.idxW h) :: (kY, Enc.idxW h + 1) :: (kX, nnRes us i) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, if_neg h1, if_neg h2]
  refine step_seq (step_heapStoreI (C := ctxH C (kcH H1 o ws i)) (ctxOK_H hok _) _ (vv kY) (o + i)
    (by simp only [ctxH]; omega) (Enc.idxW h)
    (by
      simp only [sev, vv]; rw [g2 _ (by decide) (by decide), hKA, g2 _ (by decide) (by decide), hK]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
        show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, if_true]
      rw [shl3 i (by have := hi; have := hk62; omega), ← cellA_add]; rfl)
    (by simp [sev, vv, Env.get_cons])) ?_
  intro t ht
  rcases step_assignI (C := ctxH C (kcH H1 o ws (i + 1))) kK (.op .add [vv kK, .const 1]) (BitVec.ofNat 64 (i + 1))
    (hD kK (by simp)) (by
      simp only [sev, vv]; rw [g2 _ (by decide) (by decide), hK]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) t
    (by simp only [kcH, hws]; exact ht) with hs' | ⟨hn, hq⟩
  · exact Or.inl hs'
  · refine Or.inr ⟨hn, by rw [hh]; rfl, ?_⟩
    rw [hh]; exact hq

end ConPanqueque.Front
