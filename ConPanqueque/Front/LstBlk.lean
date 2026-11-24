import ConPanqueque.Front.Const

/-! # Lists of table handles into heap cells, generically

The `const` record's fill loop (`Front/Const.lean`), over any table and key base: `fillBodyG fT kb`
reads the `kK`-th index of the list (`nnFun`), its handle from the table at `fT`, and stores it at
cell `kK` from the address in `kb`.  The level-parameter block of a declaration uses it over the
name table. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable scanNatList byteAt)

variable {σ : Type}

def fillBodyG (fT kb : MlS) : ProgHOL 64 :=
  .seq (callTo kX fNth [vv kBA, vv kBN, vv fV2, vv kK])
    (tblGetP kY (vv fT) (vv fCap) (vv kX)
      (.seq (.store (.op .add [vv kb, .shift .lsl (vv kK) (.const 3)]) (vv kY))
        (.assign .local kK (.op .add [vv kK, .const 1]))))

def tWords {k : IdxKind} (tbl : IdTable (Idx k)) (us : List Nat) : List (BitVec 64) :=
  us.map (fun x => Enc.idxW ((tbl.get? x).getD default))

theorem tWords_getD {k : IdxKind} (tbl : IdTable (Idx k)) (us : List Nat) (i : Nat) (hi : i < us.length) :
    (tWords tbl us).getD i 0 = Enc.idxW ((tbl.get? us[i]).getD default) := by
  simp [tWords, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

/-- One iteration of the fill loop. -/
theorem fillG_step {k : IdxKind} (fT kb : MlS) (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (s : AState) (D : List MlS) (hD : ∀ x ∈ [kX, kY, kK], x ∈ D) (hfT : fT ∉ [kX, kY, kK]) (hkb : kb ∉ [kX, kY, kK])
    (tbl : IdTable (Idx k)) (jL cap : Nat) (hrel : TblRel C.H jL cap tbl) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos : USize) (us : List Nat)
    (e0 : USize) (hpos : pos.toNat ≤ b.size) (hs : scanNatList b pos = .ok us e0)
    (H1 : List (BitVec 64)) (hp1 : C.H <+: H1) (o : Nat) (ho : C.H.length ≤ o) (hko : o + us.length ≤ H1.length)
    (i : Nat) (hi : i < us.length) (hk62 : us.length < 2 ^ 61) (Γ : Env)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 pos.toNat)) (hK : Γ.get kK = some (BitVec.ofNat 64 i))
    (hTL : Γ.get fT = some (cellA C jL)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hKA : Γ.get kb = some (cellA C o)) :
    Step (Inv (σ := σ) (ctxH C (kcH H1 o (tWords tbl us) i)) s Γ [] D) (fillBodyG fT kb)
      (fun t' => (tbl.get? us[i]).isSome ∧
        Inv (ctxH C (kcH H1 o (tWords tbl us) (i + 1))) s
          ((kK, BitVec.ofNat 64 (i + 1)) :: (kY, Enc.idxW ((tbl.get? us[i]).getD default)) ::
            (kY, Enc.idxW ((tbl.get? us[i]).getD default) + 1) :: (kX, nnRes us i) :: Γ) [] D t') := by
  have hlay := hok.heapLay
  have hfX : fT ≠ kX := fun e => hfT (by rw [e]; simp)
  have hbX : kb ≠ kX := fun e => hkb (by rw [e]; simp)
  have hbY : kb ≠ kY := fun e => hkb (by rw [e]; simp)
  let ws := tWords tbl us
  have hHl : (kcH H1 o ws i).length = H1.length := kcH_length _ _ _ _
  have hpi : C.H <+: kcH H1 o ws i := prefix_kcH hp1 o ho ws i
  have hbl : ∀ i', i' < b.data.toList.length → bufJ + i' / 8 < o := by
    intro i' hi'; have := hbuf.len; have := Nat.div_le_div_right (c := 8) (Nat.le_of_lt hi'); simp at hi' ⊢; omega
  have hpk : Packed (kcH H1 o ws i) bufJ b.data.toList :=
    packed_kcH (packed_prefix hbuf.pk hp1) o hbl ws i
  unfold fillBodyG
  refine step_seq (step_call4I (C := ctxH C (kcH H1 o ws i)) kX fNth sB sN sI sL nnFun (vv kBA) (vv kBN) (vv fV2)
    (vv kK) (cellA C bufJ) (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 pos.toNat) (BitVec.ofNat 64 i) (nnRes us i)
    (by decide) (hD kX (by simp)) hcN (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN)
    (by simpa [sev, vv] using hV) (by simpa [sev, vv] using hK)
    (fun t callee ht h1 h2 h3 h4 => retSpec_of_retP (nnFun_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b
      hbuf.plat (bytesAt_congr (bufOK_bytes hok hbuf ht hpk (by have := hpi.length_le; omega)) rfl rfl rfl)
      (hnc _ (by show t.code = C.code; exact ht.sr.code)) pos hpos i (by omega) us e0 hs h1 h2 h3 h4))) ?_
  have hnr : nnRes us i = BitVec.ofNat 64 (min us[i] natCap) := by simp [nnRes, hi]
  have g1 : ∀ y, y ≠ kX → Env.get ((kX, nnRes us i) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, if_neg h]
  refine step_tblGetI (C := ctxH C (kcH H1 o ws i)) kY (hD kY (by simp)) jL cap tbl
    (tblRel_prefix hrel hpi) hcap (vv fT) (vv fCap) (vv kX)
    (by simp only [sev, vv]; rw [g1 _ hfX]; exact hTL) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC)
    (min us[i] natCap) (by simp [natCap]; omega) (by simp [sev, vv, Env.get_cons, hnr]) (fun h hh => ?_)
  have hlt : us[i] < natCap := by
    by_cases hl : us[i] < natCap
    · exact hl
    · have : min us[i] natCap = natCap := by omega
      rw [this, hrel.2 natCap hcapN] at hh; cases hh
  have hmin : min us[i] natCap = us[i] := by omega
  rw [hmin] at hh
  have hws : ws.getD i 0 = Enc.idxW h := by rw [tWords_getD tbl us i hi, hh]; rfl
  have g2 : ∀ y, y ≠ kY → y ≠ kX →
      Env.get ((kY, Enc.idxW h) :: (kY, Enc.idxW h + 1) :: (kX, nnRes us i) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, if_neg h1, if_neg h2]
  refine step_seq (step_heapStoreI (C := ctxH C (kcH H1 o ws i)) (ctxOK_H hok _) _ (vv kY) (o + i)
    (by simp only [ctxH]; omega) (Enc.idxW h)
    (by
      simp only [sev, vv]; rw [g2 _ hbY hbX, hKA, g2 _ (by decide) (by decide), hK]
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


/-- The locals the list procedure changes. -/
def lbMods : List MlS := [kK, kG2, kX, kY, kKA0, kKA, kN]

def Keep (Γ Γ' : Env) : Prop := ∀ y, y ∉ lbMods → Env.get Γ' y = Env.get Γ y

theorem keep_cons {Γ Γ' : Env} (h : Keep Γ Γ') (x : MlS) (v : BitVec 64) (hx : x ∈ lbMods) :
    Keep Γ ((x, v) :: Γ') := fun y hy => by
  have : y ≠ x := fun e => hy (by rw [e]; exact hx)
  rw [Env.get_cons, if_neg this]; exact h y hy

/-- The block: allocate `L + 1` cells, the length first, then the handles. -/
def blkTail (C : Ctx) (fT : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C kKA0 (.shift .lsl (.op .add [vv kK, .const 1]) (.const 3))
    (.seq (.store (vv kKA0) (vv kK))
    (.seq (.assign .local kKA (.op .add [vv kKA0, .const 8]))
    (.seq (.assign .local kN (vv kK))
    (.seq (.assign .local kK (.const 0))
    (.seq (.while (.cmp .lower (vv kK) (vv kN)) (fillBodyG fT kKA)) rest)))))

/-- The handles of the list in slot `fV2` (a position, or the sentinel for an empty list), as a block
whose address ends up in `kKA0`; then `rest`. -/
def lstBlkP (C : Ctx) (fT : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local kK (.const 0))
    (.ite (.cmp .equal (vv fV2) (.const (BitVec.ofNat 64 listSentinel)))
      (blkTail C fT rest)
      (.seq (.assign .local kG2 (.const 1))
        (.seq (.while (vv kG2) countBody) (blkTail C fT rest))))

theorem blkTail_spec {k : IdxKind} {α : Type} (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ lbMods, x ∈ D) (fT : MlS) (hfT : fT ∉ lbMods)
    (tbl : IdTable (Idx k)) (jT cap : Nat) (hrel : TblRel C.H jT cap tbl) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (us : List Nat)
    (hus : us.length < 2 ^ 60) (wpos : BitVec 64)
    (hlist : us = [] ∨ ∃ (pos e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ pos.toNat ≤ b.size ∧
      scanNatList b pos = .ok us e0)
    (hT : Γ.get fT = some (cellA C jT)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hV : Γ.get fV2 = some wpos) (hK : Γ.get kK = some (BitVec.ofNat 64 us.length))
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64)
    (hk : ∀ (H' : List (BitVec 64)) (o : Nat) (Γ' : Env), C.H <+: H' → C.H.length ≤ o →
      BlkAt H' o (tWords tbl us) → (∀ j (hj : j < us.length), (tbl.get? us[j]).isSome) →
      Γ'.get kKA0 = some (cellA C o) → Keep Γ Γ' → SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (blkTail C fT rest) s m R := by
  have hlay := hok.heapLay
  let L := us.length
  let ws := tWords tbl us
  have hm : ∀ x ∈ lbMods, x ∈ D := hD
  unfold blkTail
  refine specR_allocI kKA0 (.shift .lsl (.op .add [vv kK, .const 1]) (.const 3)) (L + 1) (by omega)
    (hD kKA0 (by simp [lbMods])) (fun v => by
      simp only [sev, vv, Env.get_cons, show (kK = kKA0) = False from by decide, if_false, hK,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
        show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, if_true]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]; omega)
    (fun H' wsA hp' hwl hcapH => ?_)
  have hCH : C.H.length ≤ H'.length := hp'.length_le
  let o := H'.length
  have hl0 : (H' ++ wsA).length = H'.length + (L + 1) := by simp [hwl]
  have g0 : ∀ y, y ≠ kKA0 → Env.get ((kKA0, cellA C o) :: Γ) y = Env.get Γ y := fun y h => by
    rw [Env.get_cons, if_neg h]
  refine specR_heapStoreI (C := ctxH C (H' ++ wsA)) (ctxOK_H hok _) (vv kKA0) (vv kK) o
    (by simp only [ctxH]; omega) (BitVec.ofNat 64 L) (by simp [sev, vv, Env.get_cons]; rfl)
    (by simp only [sev, vv]; rw [g0 _ (by decide)]; exact hK) ?_
  let H1 := (H' ++ wsA).set o (BitVec.ofNat 64 L)
  have hl1 : H1.length = H'.length + (L + 1) := by simp [H1, hl0]
  have hp1 : C.H <+: H1 := prefix_set_ge (hp'.trans (List.prefix_append _ _)) o hCH _
  refine specR_assignI kKA (.op .add [vv kKA0, .const 8]) (cellA C (o + 1)) (hD kKA (by simp [lbMods]))
    (by simp [sev, vv, Env.get_cons]; exact cellA_add8 C o) ?_
  refine specR_assignI kN (vv kK) (BitVec.ofNat 64 L) (hD kN (by simp [lbMods]))
    (by simp only [sev, vv, Env.get_cons, show (kK = kKA) = False from by decide,
          show (kK = kKA0) = False from by decide, if_false]; exact hK) ?_
  refine specR_assignI kK (.const 0) 0 (hD kK (by simp [lbMods])) rfl ?_
  let Γ5 : Env := (kK, 0) :: (kN, BitVec.ofNat 64 L) :: (kKA, cellA C (o + 1)) :: (kKA0, cellA C o) :: Γ
  have hk5 : Keep Γ Γ5 :=
    keep_cons (keep_cons (keep_cons (keep_cons (fun _ _ => rfl) _ _ (by simp [lbMods])) _ _ (by simp [lbMods]))
      _ _ (by simp [lbMods])) _ _ (by simp [lbMods])
  refine specR_dropMem ?_
  let P : LoopPt α → Prop := fun p => p.s = s ∧ p.m = m ∧ ∃ i', i' ≤ L ∧
    p.C = ctxH C (kcH H1 (o + 1) ws i') ∧ (∀ j (hj : j < us.length), j < i' → (tbl.get? us[j]).isSome) ∧
    p.Γ.get kK = some (BitVec.ofNat 64 i') ∧ p.Γ.get kN = some (BitVec.ofNat 64 L) ∧
    p.Γ.get kKA = some (cellA C (o + 1)) ∧ p.Γ.get kKA0 = some (cellA C o) ∧ Keep Γ p.Γ
  have hp0 : P ⟨ctxH C (kcH H1 (o + 1) ws 0), s, Γ5, m⟩ :=
    ⟨rfl, rfl, 0, by omega, rfl, fun j _ h => absurd h (by omega), by simp [Γ5, Env.get_cons],
      by simp [Γ5, Env.get_cons, show kN ≠ kK from by decide],
      by simp [Γ5, Env.get_cons, show kKA ≠ kK from by decide, show kKA ≠ kN from by decide],
      by simp [Γ5, Env.get_cons, show kKA0 ≠ kK from by decide, show kKA0 ≠ kN from by decide,
        show kKA0 ≠ kKA from by decide], hk5⟩
  refine (specR_whileT (σ := σ) (D := D) P ⟨ctxH C (kcH H1 (o + 1) ws 0), s, Γ5, m⟩ hp0 ?_ : _)
  intro p ⟨hps, hpm, i', hi', hpC, hall, hpk, hpn, hpa, hpa0, hkp⟩ _
  have lk : ∀ y, y ∉ lbMods → p.Γ.get y = Γ.get y := hkp
  refine ⟨_, sev_lower _ (vv kK) (vv kN) i' L (by simpa [sev, vv] using hpk) (by simpa [sev, vv] using hpn)
    (by omega) (by omega), fun hw => ?_, fun hw => ?_⟩
  · -- done: the block is in place
    have hiL : i' = L := by
      by_cases h : i' < L
      · simp [bw, h] at hw
      · omega
    subst hiL
    rw [hpC, hps, hpm]
    refine hk (kcH H1 (o + 1) ws us.length) o p.Γ (prefix_kcH hp1 (o + 1) (by omega) ws _) hCH ⟨?_, ?_⟩
      (fun j hj => hall j hj hj) hpa0 hkp
    · rw [kcH_get, if_neg (by omega)]
      simp [H1, List.getElem?_set, hl0, ws, tWords]
      exact ⟨show H'.length < H'.length + (L + 1) by omega, rfl⟩
    · intro j hj
      have hj' : j < us.length := by simpa [ws, tWords] using hj
      rw [kcH_get, if_pos ⟨by omega, by omega, by show o + 1 + j < H1.length; omega⟩,
        show o + 1 + j - (o + 1) = j by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
  · -- one more handle
    have hiL : i' < L := by
      by_cases h : i' < L
      · exact h
      · simp [bw, h] at hw
    have hne : us ≠ [] := by intro h; simp [L, h] at hiL
    obtain ⟨pos, e0, hwp, hpos, hsl⟩ := hlist.resolve_left hne
    rw [hpC, hps]
    refine step_mono (fillG_step fT kKA C hok hnc hcN s D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl|rfl|rfl <;> simp [lbMods]))
      (fun h => hfT (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl|rfl|rfl <;>
        simp [lbMods])) (by decide)
      tbl jT cap hrel hcap hcapN bufJ b hbuf pos us e0 hpos hsl H1 hp1 (o + 1) (by omega)
      (by show H'.length + 1 + us.length ≤ H1.length; omega) i' hiL (by omega) p.Γ
      (by rw [lk kBA (by decide)]; exact hBA) (by rw [lk kBN (by decide)]; exact hBN)
      (by rw [lk fV2 (by decide), hV, hwp]) hpk (by rw [lk fT hfT]; exact hT) (by rw [lk fCap (by decide)]; exact hC)
      hpa)
      (fun t ht => ht) (fun t ⟨hsome, hinv⟩ => ⟨⟨ctxH C (kcH H1 (o + 1) ws (i' + 1)), s, _, m⟩,
        ⟨rfl, rfl, i' + 1, by omega, rfl, fun j hj hji => ?_, by simp [Env.get_cons],
          by simp [Env.get_cons, show kN ≠ kK from by decide, show kN ≠ kY from by decide,
            show kN ≠ kX from by decide, hpn],
          by simp [Env.get_cons, show kKA ≠ kK from by decide, show kKA ≠ kY from by decide,
            show kKA ≠ kX from by decide, hpa],
          by simp [Env.get_cons, show kKA0 ≠ kK from by decide, show kKA0 ≠ kY from by decide,
            show kKA0 ≠ kX from by decide, hpa0],
          keep_cons (keep_cons (keep_cons (keep_cons hkp _ _ (by simp [lbMods])) _ _ (by simp [lbMods])) _ _
            (by simp [lbMods])) _ _ (by simp [lbMods])⟩, by show m s = p.m s; rw [hpm], hinv⟩)
    by_cases hj' : j < i'
    · exact hall j hj hj'
    · have : j = i' := by omega
      subst this; exact hsome

/-- **A list of table handles as a heap block** (continuation form): the continuation gets the block,
the image it lies in, the table having answered every index, and the locals other than the
procedure's own as they were. -/
theorem lstBlk_spec {k : IdxKind} {α : Type} (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ lbMods, x ∈ D) (fT : MlS) (hfT : fT ∉ lbMods)
    (tbl : IdTable (Idx k)) (jT cap : Nat) (hrel : TblRel C.H jT cap tbl) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (us : List Nat)
    (hus : us.length < 2 ^ 60) (wpos : BitVec 64)
    (hslot : (∃ (pos e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ scanNatList b pos = .ok us e0) ∨
      (us = [] ∧ wpos = BitVec.ofNat 64 listSentinel))
    (hT : Γ.get fT = some (cellA C jT)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hV : Γ.get fV2 = some wpos)
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64)
    (hk : ∀ (H' : List (BitVec 64)) (o : Nat) (Γ' : Env), C.H <+: H' → C.H.length ≤ o →
      BlkAt H' o (tWords tbl us) → (∀ j (hj : j < us.length), (tbl.get? us[j]).isSome) →
      Γ'.get kKA0 = some (cellA C o) → Keep Γ Γ' → SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (lstBlkP C fT rest) s m R := by
  have hplat := hbuf.plat
  have hsmall := hbuf.small
  have hfX : fT ≠ kX := fun e => hfT (by rw [e]; simp [lbMods])
  have hfK : fT ≠ kK := fun e => hfT (by rw [e]; simp [lbMods])
  have hfG : fT ≠ kG2 := fun e => hfT (by rw [e]; simp [lbMods])
  unfold lstBlkP
  refine specR_assignI kK (.const 0) 0 (hD kK (by simp [lbMods])) rfl ?_
  have g1 : ∀ y, y ≠ kK → Env.get ((kK, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, if_neg h]
  have hk1 : Keep Γ ((kK, 0) :: Γ) := keep_cons (fun _ _ => rfl) _ _ (by simp [lbMods])
  have hsent : ∀ (pos : USize) (e0 : USize), scanNatList b pos = .ok us e0 →
      BitVec.ofNat 64 pos.toNat ≠ BitVec.ofNat 64 listSentinel := by
    intro pos e0 hsl e
    have := scanNatList_lt hplat hsl
    have := congrArg BitVec.toNat e
    simp [listSentinel] at this; omega
  -- continuations from a later environment
  have hkK : ∀ Γ', Keep ((kK, 0) :: Γ) Γ' → Keep Γ Γ' := fun Γ' h y hy => by rw [h y hy]; exact hk1 y hy
  refine specR_ifI _ _ (sev_eq_c' _ fV2 wpos (BitVec.ofNat 64 listSentinel)
    (by rw [g1 _ (by decide)]; exact hV)) (fun hw => ?_) (fun hw => ?_)
  · have hw' : wpos = BitVec.ofNat 64 listSentinel := by
      by_cases h : wpos = BitVec.ofNat 64 listSentinel
      · exact h
      · simp [bw, h] at hw
    have hus0 : us = [] := by
      rcases hslot with ⟨pos, e0, hwp, hsl⟩ | ⟨h0, _⟩
      · exact absurd (hwp.symm.trans hw') (hsent pos e0 hsl)
      · exact h0
    subst hus0
    exact blkTail_spec C hok hnc hcN s _ M D hD fT hfT tbl jT cap hrel hcap hcapN bufJ b hbuf [] (by simp) wpos
      (Or.inl rfl) (by rw [g1 _ hfK]; exact hT) (by rw [g1 _ (by decide)]; exact hC)
      (by rw [g1 _ (by decide)]; exact hBA) (by rw [g1 _ (by decide)]; exact hBN)
      (by rw [g1 _ (by decide)]; exact hV) (by simp [Env.get_cons]) rest
      (fun H' o Γ' a1 a2 a3 a4 a5 a6 => hk H' o Γ' a1 a2 a3 a4 a5 (hkK Γ' a6))
  · have hw' : wpos ≠ BitVec.ofNat 64 listSentinel := by intro h; simp [bw, h] at hw
    obtain ⟨pos, e0, hwp, hsl⟩ := hslot.resolve_right (fun ⟨_, h⟩ => hw' h)
    have hpos : pos.toNat ≤ b.size := Nat.le_of_lt (scanNatList_lt hplat hsl)
    let L := us.length
    refine specR_assignI kG2 (.const 1) 1 (hD kG2 (by simp [lbMods])) rfl ?_
    refine specR_dropMem ?_
    let Γ4 : Env := (kG2, 1) :: (kK, 0) :: Γ
    have hk4 : Keep Γ Γ4 := keep_cons hk1 _ _ (by simp [lbMods])
    let P : LoopPt α → Prop := fun p => p.C = C ∧ p.s = s ∧ p.m = m ∧ ∃ c, c ≤ L ∧
      p.Γ.get kK = some (BitVec.ofNat 64 c) ∧
      (p.Γ.get kG2 = some 1 ∨ (p.Γ.get kG2 = some 0 ∧ c = L)) ∧ Keep Γ p.Γ
    have hp0 : P ⟨C, s, Γ4, m⟩ :=
      ⟨rfl, rfl, rfl, 0, by omega, by simp [Γ4, Env.get_cons, show kK ≠ kG2 from by decide],
        Or.inl (by simp [Γ4, Env.get_cons]), hk4⟩
    refine (specR_whileT (σ := σ) (D := D) P ⟨C, s, Γ4, m⟩ hp0 ?_ : _)
    intro p ⟨hpC, hps, hpm, c, hcL, hpk, hpg, hkp⟩ _
    have lk : ∀ y, y ∉ lbMods → p.Γ.get y = Γ.get y := hkp
    rcases hpg with hg1 | ⟨hg0, hcL'⟩
    · refine ⟨1, by simp [sev, vv, hg1], fun h => absurd h (by decide), fun _ => ?_⟩
      rw [hpC, hps]
      refine step_seq (step_call4I (C := C) kX fNth sB sN sI sL nnFun (vv kBA) (vv kBN) (vv fV2) (vv kK)
        (cellA C bufJ) (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 pos.toNat) (BitVec.ofNat 64 c) (nnRes us c)
        (by decide) (hD kX (by simp [lbMods])) hcN
        (by simp only [sev, vv]; rw [lk kBA (by decide)]; exact hBA)
        (by simp only [sev, vv]; rw [lk kBN (by decide)]; exact hBN)
        (by simp only [sev, vv]; rw [lk fV2 (by decide), hV, hwp])
        (by simpa [sev, vv] using hpk)
        (fun t callee ht h1 h2 h3 h4 => retSpec_of_retP (nnFun_sound (callEntryStateHOLFinite t callee) (cellA C bufJ)
          b hplat (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk
            (Nat.le_refl _)) rfl rfl rfl)
          (hnc _ (by show t.code = C.code; exact ht.sr.code)) pos hpos c (by omega) us e0 hsl h1 h2 h3 h4))) ?_
      refine step_ifI _ _ (sev_eq_c' _ kX (nnRes us c) (BitVec.ofNat 64 nnSent) (by simp [Env.get_cons]))
        (fun hw2 => ?_) (fun hw2 => ?_)
      · have hcl : c = L := by
          by_cases h : c < L
          · have : nnRes us c ≠ BitVec.ofNat 64 nnSent := by
              simp only [nnRes, dif_pos (show c < us.length from h)]; intro e
              have := congrArg BitVec.toNat e
              have h2 : min us[c] natCap ≤ natCap := Nat.min_le_right _ _
              have h1 : min us[c] natCap < 2 ^ 64 := Nat.lt_of_le_of_lt h2 (by unfold natCap; decide)
              rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1] at this
              unfold nnSent natCap at this h2; omega
            simp [bw, this] at hw2
          · omega
        intro t ht
        rcases step_assignI (C := C) (Γ := (kX, nnRes us c) :: p.Γ) kG2 (.const 0) 0 (hD kG2 (by simp [lbMods])) rfl
          t ht with hs' | ⟨hn', hq⟩
        · exact Or.inl hs'
        · exact Or.inr ⟨hn', ⟨C, s, _, m⟩, ⟨rfl, rfl, rfl, c, hcL, by simp [Env.get_cons, show kK ≠ kG2 from by decide,
            show kK ≠ kX from by decide, hpk], Or.inr ⟨by simp [Env.get_cons], hcl⟩,
            keep_cons (keep_cons hkp _ _ (by simp [lbMods])) _ _ (by simp [lbMods])⟩,
            by show m s = p.m s; rw [hpm], hq⟩
      · have hcl : c < L := by
          by_cases h : c < L
          · exact h
          · have : nnRes us c = BitVec.ofNat 64 nnSent := by simp [nnRes, show ¬ c < us.length by omega]
            simp [bw, this] at hw2
        intro t ht
        rcases step_assignI (C := C) (Γ := (kX, nnRes us c) :: p.Γ) kK (.op .add [vv kK, .const 1])
          (BitVec.ofNat 64 (c + 1)) (hD kK (by simp [lbMods])) (by
            simp only [sev, vv, Env.get_cons, show (kK = kX) = False from by decide, if_false, hpk,
              Option.bind_eq_bind, Option.bind_some, Option.pure_def]
            congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) t ht with hs' | ⟨hn', hq⟩
        · exact Or.inl hs'
        · exact Or.inr ⟨hn', ⟨C, s, _, m⟩, ⟨rfl, rfl, rfl, c + 1, by omega, by simp [Env.get_cons],
            Or.inl (by simp [Env.get_cons, show kG2 ≠ kK from by decide, show kG2 ≠ kX from by decide, hg1]),
            keep_cons (keep_cons hkp _ _ (by simp [lbMods])) _ _ (by simp [lbMods])⟩,
            by show m s = p.m s; rw [hpm], hq⟩
    · refine ⟨0, by simp [sev, vv, hg0], fun _ => ?_, fun h => absurd rfl h⟩
      subst hcL'
      rw [hpC, hps, hpm]
      exact blkTail_spec C hok hnc hcN s p.Γ [] D hD fT hfT tbl jT cap hrel hcap hcapN bufJ b hbuf us hus wpos
        (Or.inr ⟨pos, e0, hwp, hpos, hsl⟩) (by rw [lk fT hfT]; exact hT) (by rw [lk fCap (by decide)]; exact hC)
        (by rw [lk kBA (by decide)]; exact hBA) (by rw [lk kBN (by decide)]; exact hBN)
        (by rw [lk fV2 (by decide)]; exact hV) hpk rest
        (fun H' o Γ' a1 a2 a3 a4 a5 a6 => hk H' o Γ' a1 a2 a3 a4 a5 (fun y hy => by rw [a6 y hy]; exact hkp y hy))

end ConPanqueque.Front
