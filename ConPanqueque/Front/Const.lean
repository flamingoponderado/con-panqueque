import ConPanqueque.Front.Steps
import ConPanqueque.T.EIntern2
import ConPanqueque.T.LoopT

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

/-- The environment facts the tail keeps. -/
def TailEnv (C : Ctx) (Γ0 Γ : Env) : Prop :=
  ∀ y ∈ [fTE, fTL, fCap, fI, fy, fV2, kBA, kBN, kKA0, kN], Env.get Γ y = Env.get Γ0 y

theorem tailEnv_cons {C : Ctx} {Γ0 Γ : Env} (h : TailEnv C Γ0 Γ) (x : MlS) (v : BitVec 64)
    (hx : x ∉ [fTE, fTL, fCap, fI, fy, fV2, kBA, kBN, kKA0, kN]) : TailEnv C Γ0 ((x, v) :: Γ) := by
  intro y hy
  have hne : y ≠ x := fun e => hx (by rw [← e]; exact hy)
  rw [Env.get_cons, if_neg hne]; exact h y hy

theorem exConstTail_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcLs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (hcC : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kKA0, kN, kK, kX, kY, kLs, fh], x ∈ D)
    (st : StateD) (jE jL cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hrell : TblRel C.H jL cap st.levels)
    (hcap : 8 * cap < 2 ^ 64) (hcapN : cap ≤ natCap)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (us : List Nat) (hus : us.length < 2 ^ 60) (wpos : BitVec 64)
    (hlist : us = [] ∨ ∃ (pos : USize) (e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ pos.toNat ≤ b.size ∧
      scanNatList b pos = .ok us e0)
    (i : Nat) (hi : i < 2 ^ 64) (hic : i < cap) (nm : NIdx)
    (hTE : Γ.get fTE = some (cellA C jE)) (hTL : Γ.get fTL = some (cellA C jL))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hI : Γ.get fI = some (BitVec.ofNat 64 i))
    (hy : Γ.get fy = some (Enc.idxW nm)) (hK : Γ.get kK = some (BitVec.ofNat 64 us.length))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hV : Γ.get fV2 = some wpos) :
    SpecR (Inv (σ := σ) C s Γ M D) (exConstTail C) s
      ((us.mapM st.level >>= fun ls => internLsNode ls >>= fun lsh => internConstE nm lsh) >>= fun e =>
        (pure { st with exprs := st.exprs.insert i e } : AM StateD)) (ExPost C jE cap st i) := by
  have hlay := hok.heapLay
  let L := us.length
  let ws := lvWords st us
  unfold exConstTail
  refine specR_allocI kKA0 (.shift .lsl (vv kK) (.const 3)) L (by omega) (hD kKA0 (by simp)) (fun v => by
      simp only [sev, vv, Env.get_cons, show (kK = kKA0) = False from by decide, if_false, hK, Option.map_some,
        show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, if_true]
      rw [shl3 L (by omega)])
    (fun H' wsA hp' hwl hcapH => ?_)
  have hCH : C.H.length ≤ H'.length := hp'.length_le
  let o := H'.length
  let H1 := H' ++ wsA
  have hl1 : H1.length = H'.length + L := by simp [H1, hwl]
  have hp1 : C.H <+: H1 := hp'.trans (List.prefix_append _ _)
  have g0 : ∀ y, y ≠ kKA0 → Env.get ((kKA0, cellA C o) :: Γ) y = Env.get Γ y := fun y h => by
    rw [Env.get_cons, if_neg h]
  refine specR_assignI kN (vv kK) (BitVec.ofNat 64 L) (hD kN (by simp))
    (by simp only [sev, vv]; rw [g0 _ (by decide)]; exact hK) ?_
  refine specR_assignI kK (.const 0) 0 (hD kK (by simp)) rfl ?_
  refine specR_dropMem ?_
  let Γ2 : Env := (kK, 0) :: (kN, BitVec.ofNat 64 L) :: (kKA0, cellA C o) :: Γ
  let m0 : AM StateD := (us.mapM st.level >>= fun ls => internLsNode ls >>= fun lsh => internConstE nm lsh) >>= fun e =>
    (pure { st with exprs := st.exprs.insert i e } : AM StateD)
  let P : LoopPt StateD → Prop := fun p => p.s = s ∧ p.m = m0 ∧ ∃ i', i' ≤ L ∧
    p.C = ctxH C (kcH H1 o ws i') ∧ (∀ j (hj : j < us.length), j < i' → (st.levels.get? us[j]).isSome) ∧
    p.Γ.get kK = some (BitVec.ofNat 64 i') ∧ TailEnv C Γ2 p.Γ
  have hp0 : P ⟨ctxH C (kcH H1 o ws 0), s, Γ2, m0⟩ :=
    ⟨rfl, rfl, 0, by omega, rfl, fun j _ h => absurd h (by omega), by simp [Γ2, Env.get_cons], fun _ _ => rfl⟩
  refine (specR_whileT (σ := σ) (D := D) P ⟨ctxH C (kcH H1 o ws 0), s, Γ2, m0⟩ hp0 ?_ : _)
  intro p ⟨hps, hpm, i', hi', hpC, hall, hpk, hte⟩ _
  have hkN : p.Γ.get kN = some (BitVec.ofNat 64 L) := by
    rw [hte kN (by simp)]; simp [Γ2, Env.get_cons, show kN ≠ kK from by decide]
  refine ⟨_, sev_lower _ (vv kK) (vv kN) i' L (by simpa [sev, vv] using hpk) (by simpa [sev, vv] using hkN)
    (by omega) (by omega), fun hw => ?_, fun hw => ?_⟩
  · -- the loop is done: every level was found
    have hiL : i' = L := by
      by_cases h : i' < L
      · simp [bw, h] at hw
      · omega
    subst hiL
    have hall' : ∀ j (hj : j < us.length), (st.levels.get? us[j]).isSome := fun j hj => hall j hj hj
    let hs := us.map (fun x => (st.levels.get? x).getD default)
    have hmap := mapM_level_ok st us hall'
    have hm0 : m0 = (internLsNode hs >>= fun lsh => internConstE nm lsh >>= fun e =>
        (pure { st with exprs := st.exprs.insert i e } : AM StateD)) := by
      simp only [m0, hmap, pure_bind, bind_assoc]; rfl
    rw [hpC, hps, hpm, hm0]
    let HK := kcH H1 o ws us.length
    have hlK : HK.length = H'.length + us.length := by simp only [HK]; rw [kcH_length]; exact hl1
    have hpK : C.H <+: HK := prefix_kcH hp1 o hCH ws _
    have hkey : ∀ j (hj : j < hs.length), HK[o + j]? = some (Enc.idxW hs[j]) := by
      intro j hj
      have hj' : j < us.length := by simpa [hs] using hj
      simp only [HK]
      rw [kcH_get, if_pos ⟨by omega, by omega, by show o + j < H1.length; omega⟩,
        show o + j - o = j by omega, lvWords_getD st us j hj']
      simp [hs]
    have gΓ2 : ∀ y, y ≠ kK → y ≠ kN → y ≠ kKA0 → Γ2.get y = Γ.get y := fun y h1 h2 h3 => by
      simp only [Γ2, Env.get_cons, if_neg h1, if_neg h2, if_neg h3]
    have look : ∀ y ∈ [fTE, fTL, fCap, fI, fy, fV2, kBA, kBN, kKA0, kN], y ≠ kK → y ≠ kN → y ≠ kKA0 →
        p.Γ.get y = Γ.get y := fun y hy h1 h2 h3 => by rw [hte y hy, gΓ2 y h1 h2 h3]
    have hKA0 : p.Γ.get kKA0 = some (cellA C o) := by
      rw [hte kKA0 (by simp)]; simp [Γ2, Env.get_cons, show kKA0 ≠ kK from by decide, show kKA0 ≠ kN from by decide]
    refine specR_callNIA kLs fInternLs [pKey, lEc] [vv kKA0, vv kN] internLsBody
      [cellA C o, BitVec.ofNat 64 hs.length] (by decide) rfl (hD kLs (by simp)) hcLs
      ⟨by simp only [sev, vv]; exact hKA0, by simp only [sev, vv]; rw [hkN]; simp [hs, L], trivial⟩
      (fun a w s' st' => internLsNode hs s = .ok (a, s') ∧ PostLs (ctxH (ctxH C HK) C.H) a w s' st')
      (fun a w s' H' => H' = C.H ∧ internLsNode hs s = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st' ⟨hr, hw, hsr⟩ => ⟨C.H, ⟨rfl, hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact internLs_body_spec (σ := σ) ra (ctxH C HK) (ctxOK_H hok _) s hs o C.H hpK hCH
          (by show o + hs.length ≤ HK.length; simp [hs]; omega) (by simp [hs]; omega) hkey _
          (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
      (fun lsh w s2 H' ⟨e, hr2, hw⟩ => ?_)
    subst e; subst hw
    rw [show ctxH (ctxH C HK) C.H = C from ctxH_self C]
    have gL : ∀ y, y ≠ kLs → Env.get ((kLs, Enc.idxW lsh) :: p.Γ) y = p.Γ.get y := fun y h => by
      rw [Env.get_cons, if_neg h]
    refine callEN fh fInternConst [lEn, lEus] [vv fy, vv kLs] constBody [Enc.idxW nm, Enc.idxW lsh] (by decide) rfl
      (hD fh (by simp)) hcC
      ⟨by simp only [sev, vv]; rw [gL _ (by decide), look fy (by simp) (by decide) (by decide) (by decide)]; exact hy,
       by simp [sev, vv, Env.get_cons], trivial⟩ (const_body_spec ra C hok s2 nm lsh) (fun h s3 _ => ?_)
    have gF : ∀ y, y ≠ fh → y ≠ kLs → y ∈ [fTE, fTL, fCap, fI, fy, fV2, kBA, kBN, kKA0, kN] → y ≠ kK → y ≠ kN →
        y ≠ kKA0 → Env.get ((fh, Enc.idxW h) :: (kLs, Enc.idxW lsh) :: p.Γ) y = Γ.get y :=
      fun y h1 h2 hy h3 h4 h5 => by
        rw [Env.get_cons, if_neg h1, Env.get_cons, if_neg h2]; exact look y hy h3 h4 h5
    refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
      (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by simp) (by decide) (by decide) (by decide)]; exact hTE)
      i hic h
      (by simp only [sev, vv]; rw [gF _ (by decide) (by decide) (by simp) (by decide) (by decide) (by decide)]; exact hI)
      (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
    exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)
  · -- one more level
    have hiL : i' < L := by
      by_cases h : i' < L
      · exact h
      · simp [bw, h] at hw
    have hne : us ≠ [] := by intro h; simp [L, h] at hiL
    obtain ⟨pos, e0, hwp, hpos, hsl⟩ := hlist.resolve_left hne
    have gΓ2 : ∀ y, y ≠ kK → y ≠ kN → y ≠ kKA0 → Γ2.get y = Γ.get y := fun y h1 h2 h3 => by
      simp only [Γ2, Env.get_cons, if_neg h1, if_neg h2, if_neg h3]
    have look : ∀ y ∈ [fTE, fTL, fCap, fI, fy, fV2, kBA, kBN, kKA0, kN], y ≠ kK → y ≠ kN → y ≠ kKA0 →
        p.Γ.get y = Γ.get y := fun y hy h1 h2 h3 => by rw [hte y hy, gΓ2 y h1 h2 h3]
    rw [hpC, hps]
    refine step_mono (fill_step C hok hnc hcN s D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl|rfl|rfl <;> simp)) st jL cap hrell hcap hcapN
      bufJ b hbuf pos us e0 hpos hsl H1 hp1 o hCH (by show H'.length + us.length ≤ H1.length; omega) i' hiL (by omega) p.Γ
      (by rw [look kBA (by simp) (by decide) (by decide) (by decide)]; exact hBA)
      (by rw [look kBN (by simp) (by decide) (by decide) (by decide)]; exact hBN)
      (by rw [look fV2 (by simp) (by decide) (by decide) (by decide), hV, hwp])
      hpk (by rw [look fTL (by simp) (by decide) (by decide) (by decide)]; exact hTL)
      (by rw [look fCap (by simp) (by decide) (by decide) (by decide)]; exact hC)
      (by rw [hte kKA0 (by simp)]; simp [Γ2, Env.get_cons, show kKA0 ≠ kK from by decide,
            show kKA0 ≠ kN from by decide]))
      (fun t ht => ht) (fun t ⟨hsome, hinv⟩ => ⟨⟨ctxH C (kcH H1 o ws (i' + 1)), s, _, m0⟩,
        ⟨rfl, rfl, i' + 1, by omega, rfl, fun j hj hji => ?_, by simp [Env.get_cons],
          tailEnv_cons (tailEnv_cons (tailEnv_cons (tailEnv_cons hte _ _ (by decide)) _ _ (by decide)) _ _
            (by decide)) _ _ (by decide)⟩, by show m0 s = p.m s; rw [hpm], hinv⟩)
    by_cases hj' : j < i'
    · exact hall j hj hj'
    · have : j = i' := by omega
      subst this; exact hsome

end ConPanqueque.Front
