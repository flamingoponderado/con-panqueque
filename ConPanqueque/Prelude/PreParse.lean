import ConPanqueque.Prelude.TwinPre
import ConPanqueque.Prelude.Bytes
import ConPanqueque.Front.ParseTop
import ConPanqueque.Prelude.Keep

/-! # The second parse: fresh tables, the registry kept

`initP2`: `initP` without resetting the registry count — the tables are zeroed and re-seeded, the
records already registered stay.  `parseP2 rest`: `initP2`, then the line loop.  `parseP2_spec`: it
refines `feedAll (withPre P (stInit s)) b 0 0` — the twin's parse of `b` from fresh tables with the
records `P` in front (`feedAll_withPre`: the plain parse of `b`, `P` prepended).

`preStoreP rest`: the prelude's words stored from the address in `kBA` (`storesP`), its size in
`kBN`; `bufOK_pre`: then the buffer holds con-leche's built-in prelude bytes. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

def initP2 (rest : ProgHOL 64) : ProgHOL 64 :=
  zeroFillP (.seq (.store (vv fTN) (.const 1))
    (.seq (.store (vv fTL) (.op .add [vv kZL, .const 1])) rest))

theorem declsRel_frame {C : Ctx} {F rb capD : Nat} {H H' : List (BitVec 64)} {decls : Array IDeclaration}
    (h : DeclsRel C F rb capD H decls) (hl : H'.length = H.length) (hc : ∀ c, rb ≤ c → H'[c]? = H[c]?) :
    DeclsRel C F rb capD H' decls := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [hc _ (Nat.le_refl _)]; exact h1, h2, h3, by rw [hl]; exact h4, fun k hk => ?_⟩
  obtain ⟨o, ho, hr⟩ := h5 k hk
  refine ⟨o, by rw [hc _ (by omega)]; exact ho, recEnc_keeps hr (fun c hcF v hv => ?_)⟩
  have : rb ≤ c := by
    have : F ≤ c := hcF
    have := h3; omega
  rw [hc _ this]; exact hv

theorem initP2_spec {α : Type} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : kZ ∈ D)
    (F rb capD jN cap bufJ : Nat) (b : ByteArray)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b) (zl : LIdx) (P : Array IDeclaration) (hdr : DeclsRel C F rb capD C.H P)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hZL : Γ.get kZL = some (Enc.idxW zl))
    (hk : ∀ (Γ' : Env) (H' : List (BitVec 64)), (∀ y, y ≠ kZ → Γ'.get y = Γ.get y) →
      FrontSt C F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b H'
        { names := ConLeche.Frontend.IdTable.singleton default, levels := ConLeche.Frontend.IdTable.singleton zl,
          decls := P } →
      SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (initP2 rest) s m R := by
  have hl := hfl.tE; have hb1 := hfl.buf; have hb2 := hfl.bufF
  have hrbF : rb < F := by omega
  unfold initP2
  refine zeroFill_spec C hok s Γ M D hD jN (3 * cap) (by omega) (by omega) hZb hZn (fun Γ' hag => ?_)
  let K := kcH C.H jN (List.replicate (3 * cap) 0) (3 * cap)
  have hKl : K.length = C.H.length := kcH_length _ _ _ _
  have hKg : ∀ c, K[c]? = if jN ≤ c ∧ c < jN + 3 * cap ∧ c < C.H.length then some 0 else C.H[c]? := by
    intro c; simp only [K]; rw [kcH_get]
    split
    · rename_i h; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, show c - jN < 3 * cap by omega]
    · rfl
  have g : ∀ y, y ≠ kZ → Γ'.get y = Γ.get y := hag
  refine specR_heapStoreI (C := ctxH C K) (ctxOK_ctxH hok) (vv fTN) (.const 1) jN
    (by show jN < K.length; omega) 1 (by simp only [sev, vv]; rw [g _ (by decide)]; exact hTN) rfl ?_
  let K1 := K.set jN 1
  refine specR_heapStoreI (C := ctxH (ctxH C K) K1) (ctxOK_ctxH (ctxOK_ctxH hok)) (vv fTL)
    (.op .add [vv kZL, .const 1]) (jN + cap) (by show jN + cap < K1.length; simp [K1]; omega) (Enc.idxW zl + 1)
    (by simp only [sev, vv]; rw [g _ (by decide)]; exact hTL)
    (by simp only [sev, vv]; rw [g _ (by decide), hZL]; rfl) ?_
  let K2 := K1.set (jN + cap) (Enc.idxW zl + 1)
  have hK2 : ∀ c, K2[c]? = if c = jN + cap then (if c < C.H.length then some (Enc.idxW zl + 1) else none)
      else if c = jN then (if c < C.H.length then some 1 else none) else K[c]? := by
    intro c
    simp only [K2, K1, List.getElem?_set, List.length_set, hKl]
    by_cases h2 : jN + cap = c <;> by_cases h3 : jN = c <;>
      simp [h2, h3, eq_comm] <;> (try omega) <;> simp [show cap ≠ 0 by omega]
  show SpecR (Inv (ctxH C K2) s Γ' [] D) rest s m R
  refine hk Γ' K2 g ⟨⟨hfl, by omega, by omega, hcapN, hcap8, hcapD8⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [hK2, singleton_get]
      by_cases h0 : i = 0
      · subst h0; simp [show jN + 0 ≠ jN + cap by omega, show jN < C.H.length by omega,
          show cap ≠ 0 by omega, tblW, idxW_default]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h0, hKg,
          ite_eq_left ⟨by omega, by omega, by omega⟩]
        rfl
    · rw [singleton_get, ite_eq_right (by omega)]
  · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [hK2, singleton_get]
      by_cases h0 : i = 0
      · subst h0; simp [show jN + cap < C.H.length by omega, tblW]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h0, hKg,
          ite_eq_left ⟨by omega, by omega, by omega⟩]
        rfl
    · rw [singleton_get, ite_eq_right (by omega)]
  · refine ⟨fun i hi => ?_, fun i _ => empty_get i⟩
    rw [hK2, ite_eq_right (by omega), ite_eq_right (by omega), hKg, ite_eq_left ⟨by omega, by omega, by omega⟩,
      empty_get]; rfl
  · refine declsRel_frame hdr (by simp [K2, K1, hKl]) (fun c hc => ?_)
    rw [hK2, ite_eq_right (by omega), ite_eq_right (by omega), hKg, ite_eq_right (by omega)]
  · refine ⟨fun i hi => ?_, hbuf.al, by simp [ctxH, K2, K1, hKl]; exact hbuf.len, hbuf.plat, hbuf.small⟩
    obtain ⟨w, hw, hbw⟩ := hbuf.pk i hi
    refine ⟨w, ?_, hbw⟩
    show K2[bufJ + i / 8]? = some w
    rw [hK2, ite_eq_right (by omega), ite_eq_right (by omega), hKg, ite_eq_right (by omega)]; exact hw

def parseP2 (rest : ProgHOL 64) : ProgHOL 64 :=
  initP2 (.seq (.call (some (some (.local, kR0), none)) fFeed feedArgs0) rest)

/-- The second parse's starting state: fresh tables, the records `P`. -/
def stPre (s : AState) (P : Array IDeclaration) : StateD :=
  { names := ConLeche.Frontend.IdTable.singleton default, levels := ConLeche.Frontend.IdTable.singleton s.pins.zeroLevel,
    decls := P }

theorem stPre_eq (s : AState) (P : Array IDeclaration) : stPre s P = withPre P (stInit s) := by
  simp [stPre, withPre, stInit]

theorem parseP2_spec {β : Type} {k : StateD → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (fc : FrontCodes σ C)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0], x ∈ D)
    (F rb capD jN cap bufJ : Nat) (b : ByteArray)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b) (P : Array IDeclaration) (hdr : DeclsRel C F rb capD C.H P)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (hk : ∀ st' s' H' (Γ'' : Env), feedAll (stPre s P) b 0 0 s = .ok (st', s') →
      (∀ y, y ≠ kZ → y ≠ kR0 → Γ''.get y = Γ.get y) →
      FrontSt C F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' Γ'' [] D) rest s' (k st') R) :
    SpecR (Inv C s Γ M D) (parseP2 rest) s (feedAll (stPre s P) b 0 0 >>= k) R := by
  unfold parseP2
  refine initP2_spec C hok s Γ M D (hD _ (by simp)) F rb capD jN cap bufJ b hfl hcap1 hcapN hcap8 hcapD8 hFH hbuf
    s.pins.zeroLevel P hdr hZb hZn hTN hTL hZL (fun Γ' H' hag hfs => ?_)
  have g : ∀ y, y ≠ kZ → Γ'.get y = Γ.get y := hag
  have hfs' : FrontSt (ctxH C H') F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b (ctxH C H').H (stPre s P) :=
    frontSt_ctxH H' hfs
  refine specR_protoCall (C := ctxH C H') kR0 fFeed feedPs (by decide) feedL feedCore feedArgs0
    (feedVs (ctxH C H') jN (jN + cap) (jN + 2 * cap) cap bufJ b.size rb capD 0 0) rfl (hD _ (by simp)) hcF ?_
    (feedL_none (ctxH C H') jN (jN + cap) (jN + 2 * cap) cap bufJ b.size rb capD 0 0)
    (fun a w s' t => feedAll (stPre s P) b 0 0 s = .ok (a, s') ∧
      FeedPost (ctxH C H') F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b a w s' t)
    (fun _ _ _ _ _ ⟨hr, H'', h1, h2⟩ => ⟨hr, H'', sr_of_eq h1 rfl rfl rfl rfl, h2⟩)
    (specR_run (feedCore_spec ra F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b _ (ctxH C H') 0 (stPre s P) 0 s rfl
      (by simp) (ctxOK_ctxH hok) (frontOK_ctxH hf) (frontCodes_ctxH fc) hcF hfs'))
    (fun st' _ s' H'' => feedAll (stPre s P) b 0 0 s = .ok (st', s') ∧
      FrontSt C F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b H'' st')
    (fun a w s' t ⟨hr, H'', h1, h2⟩ => ⟨H'', ⟨hr, frontSt_of_ctxH h2⟩, h1⟩)
    (fun a w s' H'' ⟨hr, hq⟩ => hk a s' H'' _ hr
      (fun y h1 h2 => by simp only [T.Env.get_cons, ite_eq_right h2]; exact g y h1) hq)
  simp only [EvAll, feedVs, feedArgs0, sev, vv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, trivial⟩
  · rw [g _ (by decide)]; exact hTN
  · rw [g _ (by decide)]; exact hTL
  · rw [g _ (by decide)]; exact hTE
  · rw [g _ (by decide)]; exact hC
  · rw [g _ (by decide)]; exact hBA
  · rw [g _ (by decide)]; exact hBN
  · rw [g _ (by decide)]; exact hRB
  · rw [g _ (by decide)]; exact hCD

theorem pre_es_len (ws : List (BitVec 64)) : 0 + (ws.map (ExpHOL.const : BitVec 64 → ExpHOL 64)).length ≤ ws.length := by
  simp

theorem pre_es_val (Γ : Env) (ws : List (BitVec 64)) : ∀ i (hi : i < (ws.map (ExpHOL.const : BitVec 64 → ExpHOL 64)).length),
    sev Γ (ws.map (ExpHOL.const : BitVec 64 → ExpHOL 64))[i] = some (ws.getD (0 + i) 0) := by
  intro i hi
  have hi' : i < ws.length := by simpa using hi
  simp only [List.getElem_map, sev, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

/-- The prelude's bytes into the buffer at `kBA`, its size into `kBN`. -/
def preStoreP (rest : ProgHOL 64) : ProgHOL 64 :=
  storesP kBA 0 (preWords.map .const) (.seq (.assign .local kBN (.const (BitVec.ofNat 64 preSize))) rest)

/-- The stored prelude is a buffer for the frontend (the words `ws` and the image `K` kept abstract:
unfolding them would evaluate the prelude's words). -/
theorem bufOK_pre (C : Ctx) (H K ws : List (BitVec 64)) (bufJ : Nat) (hws : ws = packW preBytes.data.toList)
    (hwl : ws.length = 1963) (hK : kcH H bufJ ws ws.length = K)
    (hal : (cellA C bufJ).toNat % 8 = 0)
    (hH : bufJ + 1963 < H.length) (hbits : System.Platform.numBits = 64) :
    BufOK (ctxH C K) bufJ preBytes := by
  have hs := preBytes_size
  have hs' : preBytes.size = 15700 := hs
  have hpk : Packed (kcH H bufJ ws ws.length) bufJ preBytes.data.toList := by
    have h1 : bufJ + ws.length ≤ H.length := by omega
    have := packed_packW H bufJ preBytes.data.toList (hws ▸ h1)
    exact hws ▸ this
  have hKl : K.length = H.length := by rw [← hK, kcH_length]
  rw [hK] at hpk
  refine ⟨hpk, hal, ?_, ⟨hbits, by rw [hs']; decide, by rw [hs']; decide⟩, by rw [hs']; decide⟩
  show bufJ + preBytes.size / 8 < K.length
  rw [hKl, hs']; omega

theorem kcH_agree' (H : List (BitVec 64)) (r : Nat) (ws : List (BitVec 64)) (n : Nat) :
    H.length = (kcH H r ws n).length ∧ ∀ c, (c < r ∨ r + n ≤ c) → (kcH H r ws n)[c]? = H[c]? :=
  ⟨(kcH_length _ _ _ _).symm, fun c hc => by rw [kcH_get]; rw [if_neg (by omega)]⟩

/-- The stores, for any word list `ws` that packs the prelude (kept abstract, see `bufOK_pre`). -/
theorem preStore_gen {β : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS}
    (ws : List (BitVec 64)) (hws : ws = packW preBytes.data.toList) (hwl : ws.length = 1963)
    (hDN : kBN ∈ D) (r : Nat) (hkb : Γ.get kBA = some (cellA C r)) (hal : (cellA C r).toNat % 8 = 0)
    (hH : r + 1963 < C.H.length) (h8 : 8 * (r + 1963) < 2 ^ 64) (hbits : System.Platform.numBits = 64)
    {rest : ProgHOL 64} {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ H2 : List (BitVec 64), H2.length = C.H.length → (∀ c, (c < r ∨ r + 1963 ≤ c) → H2[c]? = C.H[c]?) →
      BufOK (ctxH C H2) r preBytes →
      SpecR (Inv (ctxH C H2) s ((kBN, BitVec.ofNat 64 preSize) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (storesP kBA 0 (ws.map .const) (.seq (.assign .local kBN (.const (BitVec.ofNat 64 preSize))) rest))
      s m R := by
  have := storesP_spec (σ := σ) C hok s Γ D kBA r hkb ws (m := m) (R := R)
    (.seq (.assign .local kBN (.const (BitVec.ofNat 64 preSize))) rest) (ws.map .const) 0 C.H (pre_es_len ws)
    (by omega) (by omega) (pre_es_val Γ ws)
  rw [kcH, ctxH_self] at this
  refine this ?_
  rw [show 0 + (ws.map (ExpHOL.const : BitVec 64 → ExpHOL 64)).length = ws.length by simp]
  obtain ⟨hl2, ha2⟩ := kcH_agree' C.H r ws ws.length
  generalize hK2 : kcH C.H r ws ws.length = H2 at hl2 ha2 ⊢
  refine specR_assignI kBN (.const (BitVec.ofNat 64 preSize)) _ hDN rfl ?_
  exact hk H2 hl2.symm (fun c hc => ha2 c (by rw [hwl]; omega))
    (bufOK_pre C C.H H2 ws r hws hwl hK2 hal hH hbits)

/-- **The prelude's bytes stored**: the continuation runs at an image that agrees with the old one
outside the 1963 words from `r` and holds the prelude as a buffer at `r`, with `kBN` its size. -/
theorem preStore_spec {β : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS}
    (hDN : kBN ∈ D) (r : Nat) (hkb : Γ.get kBA = some (cellA C r)) (hal : (cellA C r).toNat % 8 = 0)
    (hH : r + 1963 < C.H.length) (h8 : 8 * (r + 1963) < 2 ^ 64) (hbits : System.Platform.numBits = 64)
    {rest : ProgHOL 64} {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ H2 : List (BitVec 64), H2.length = C.H.length → (∀ c, (c < r ∨ r + 1963 ≤ c) → H2[c]? = C.H[c]?) →
      BufOK (ctxH C H2) r preBytes →
      SpecR (Inv (ctxH C H2) s ((kBN, BitVec.ofNat 64 preSize) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (preStoreP rest) s m R :=
  preStore_gen hok preWords rfl (by rw [preWords_length]; rfl) hDN r hkb hal hH h8 hbits hk

end ConPanqueque.Prelude
