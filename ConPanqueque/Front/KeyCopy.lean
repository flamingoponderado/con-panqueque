import ConPanqueque.Front.NameIntern

/-! # Copying bytes from the input buffer into a key, one word per byte

A name's key (`Enc.encStr`) holds the string's bytes one per word.  `kcLoop` copies `n` bytes of the
buffer (packed, from cell `bufJ`, starting at byte `q`) into heap cells `o, o+1, …`.  Each byte is
extracted from its word with shifts and a mask, so the copy reads the packed buffer little-endian
whatever the machine's byte order is (`byteW`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T

variable {σ : Type}

def kQ := ofString "kq"
def kK := ofString "kk2"
def kJ := ofString "kj"
def kW := ofString "kw"
def kS := ofString "ks"
def kC := ofString "kc"
def kBA := ofString "kba"
def kKA := ofString "kka"
def kN := ofString "kn"

def kcBody : ProgHOL 64 :=
  .seq (.assign .local kJ (.op .add [vv kQ, vv kK]))
  (.seq (.assign .local kW (.load .one (.op .add [vv kBA, .shift .lsl (.shift .lsr (vv kJ) (.const 3)) (.const 3)])))
  (.seq (.assign .local kS (.shift .lsl (.op .and [vv kJ, .const 7]) (.const 3)))
  (.seq (.assign .local kC (.op .and [.shift .lsr (vv kW) (vv kS), .const 255]))
  (.seq (.store (.op .add [vv kKA, .shift .lsl (vv kK) (.const 3)]) (vv kC))
    (.assign .local kK (.op .add [vv kK, .const 1]))))))

def kcLoop : ProgHOL 64 := .while (.cmp .lower (vv kK) (vv kN)) kcBody

/-- `x := *(e)` at a cell of the heap image, as a step. -/
theorem step_heapLoadI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (x : MlS) (e : ExpHOL 64)
    (j : Nat) (hj : j < C.H.length) (hx : x ∈ D) (he : sev Γ e = some (cellA C j)) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .local x (.load .one e)) (Inv C s ((x, C.H[j]) :: Γ) M D) := by
  intro t ht
  obtain ⟨w0, h0⟩ := ht.decl x hx
  rw [ConsLoop.assign_local t x _ C.H[j] w0
    (by have := eval_load_word t _ _ (inv_ev ht he) (heap_cell ht.sr j hj).1
        rw [(heap_cell ht.sr j hj).2] at this; exact this) h0]
  exact Or.inr ⟨rfl, inv_set ht x _⟩

/-- `*(ea) := ev` at a cell of the image, as a step. -/
theorem step_heapStoreI {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (ea ev : ExpHOL 64) (j : Nat) (hj : j < C.H.length) (w : BitVec 64) (hea : sev Γ ea = some (cellA C j))
    (hev : sev Γ ev = some w) :
    Step (Inv (σ := σ) C s Γ M D) (.store ea ev) (Inv (ctxH C (C.H.set j w)) s Γ [] D) := by
  intro t ht
  rw [store_word t ea ev _ w (inv_ev ht hea) (inv_ev ht hev) (heap_cell ht.sr j hj).1]
  exact Or.inr ⟨rfl, sr_heapStore hok ht.sr j hj w, fun y v hy => ht.env y v hy, fun _ _ h => absurd h (by simp),
    ht.decl⟩

/-- The key cells after `i` copies. -/
def kcH (H : List (BitVec 64)) (o : Nat) (ws : List (BitVec 64)) : Nat → List (BitVec 64)
  | 0 => H
  | i + 1 => (kcH H o ws i).set (o + i) (ws.getD i 0)

theorem kcH_length (H : List (BitVec 64)) (o : Nat) (ws : List (BitVec 64)) :
    ∀ i, (kcH H o ws i).length = H.length
  | 0 => rfl
  | i + 1 => by simp [kcH, kcH_length H o ws i]

theorem kcH_get (H : List (BitVec 64)) (o : Nat) (ws : List (BitVec 64)) :
    ∀ i c, (kcH H o ws i)[c]? = if o ≤ c ∧ c < o + i ∧ c < H.length then some (ws.getD (c - o) 0) else H[c]?
  | 0, c => by simp [kcH]; omega
  | i + 1, c => by
    simp only [kcH, List.getElem?_set, kcH_length]
    rw [kcH_get H o ws i c]
    by_cases e : o + i = c
    · subst e; by_cases hl : o + i < H.length <;> simp [hl]
    · simp only [e, if_false]
      by_cases h1 : o ≤ c ∧ c < o + i ∧ c < H.length
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem packed_set {H : List (BitVec 64)} {j0 : Nat} {bs : List UInt8} (h : Packed H j0 bs) (c : Nat)
    (hc : ∀ i, i < bs.length → c ≠ j0 + i / 8) (w : BitVec 64) : Packed (H.set c w) j0 bs := by
  intro i hi
  obtain ⟨w', hw, hb⟩ := h i hi
  exact ⟨w', by rw [List.getElem?_set, if_neg (hc i hi)]; exact hw, hb⟩

theorem env_get_cons5 (Γ : Env) (a b c d e : MlS × BitVec 64) (x : MlS) (h1 : x ≠ a.1) (h2 : x ≠ b.1)
    (h3 : x ≠ c.1) (h4 : x ≠ d.1) (h5 : x ≠ e.1) : Env.get (a :: b :: c :: d :: e :: Γ) x = Env.get Γ x := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d; obtain ⟨e1, e2⟩ := e
  simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- The environment after `i` iterations. -/
def kcG (Γ0 : Env) (H : List (BitVec 64)) (bufJ o q : Nat) (ws : List (BitVec 64)) : Nat → Env
  | 0 => Γ0
  | i + 1 =>
    let j := q + i
    let wv := (kcH H o ws i).getD (bufJ + j / 8) 0
    let sv := (BitVec.ofNat 64 j &&& 7) <<< (3 : Nat)
    (kK, BitVec.ofNat 64 (i + 1)) :: (kC, (wv >>> sv.toNat) &&& 255) :: (kS, sv) :: (kW, wv) ::
      (kJ, BitVec.ofNat 64 j) :: kcG Γ0 H bufJ o q ws i

theorem kcG_get (Γ0 : Env) (H : List (BitVec 64)) (bufJ o q : Nat) (ws : List (BitVec 64)) (x : MlS)
    (hx : x ∉ [kK, kC, kS, kW, kJ]) : ∀ i, Env.get (kcG Γ0 H bufJ o q ws i) x = Env.get Γ0 x
  | 0 => rfl
  | i + 1 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [kcG]
    rw [env_get_cons5 _ _ _ _ _ _ x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2]
    exact kcG_get Γ0 H bufJ o q ws x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2]) i

theorem kcG_k (Γ0 : Env) (H : List (BitVec 64)) (bufJ o q : Nat) (ws : List (BitVec 64))
    (h0 : Env.get Γ0 kK = some 0) : ∀ i, Env.get (kcG Γ0 H bufJ o q ws i) kK = some (BitVec.ofNat 64 i)
  | 0 => h0
  | i + 1 => by simp [kcG, Env.get_cons]

theorem ctxH_self (C : Ctx) : ctxH C C.H = C := by cases C; rfl

theorem ctxH_ctxH (C : Ctx) (H H' : List (BitVec 64)) : ctxH (ctxH C H) H' = ctxH C H' := rfl

/-- **The key copy**: `n` bytes of the buffer from byte `q`, into heap cells `o, …, o + n - 1`. -/
theorem kc_spec {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (hD : ∀ x ∈ [kK, kC, kS, kW, kJ], x ∈ D)
    (bufJ o q n : Nat) (bs : List UInt8) (hpk : Packed C.H bufJ bs) (hqn : q + n ≤ bs.length)
    (hbl : bs.length < 2 ^ 60) (hbuf : bufJ + bs.length / 8 < C.H.length)
    (hko : o + n ≤ C.H.length) (hon : 8 * (o + n) < 2 ^ 64)
    (hdis : ∀ k, k < n → ∀ i, i < bs.length → o + k ≠ bufJ + i / 8)
    (hBA : Γ0.get kBA = some (cellA C bufJ)) (hKA : Γ0.get kKA = some (cellA C o))
    (hQ : Γ0.get kQ = some (BitVec.ofNat 64 q)) (hK0 : Γ0.get kK = some 0)
    (hN : Γ0.get kN = some (BitVec.ofNat 64 n))
    (hr : SpecR (Inv (ctxH C (kcH C.H o ((bs.drop q).map (fun b => BitVec.ofNat 64 b.toNat)) n)) s
      (kcG Γ0 C.H bufJ o q ((bs.drop q).map (fun b => BitVec.ofNat 64 b.toNat)) n) [] D) rest s m R) :
    SpecR (Inv C s Γ0 [] D) (.seq kcLoop rest) s m R := by
  let ws := (bs.drop q).map (fun b => BitVec.ofNat 64 b.toNat)
  have hws : ∀ i (hi : i < n), ws.getD i 0 = BitVec.ofNat 64 (bs[q + i]'(by omega)).toNat := by
    intro i hi
    simp only [ws, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
    rw [List.getElem?_eq_getElem (by omega)]; rfl
  have e0 := ctxH_self C
  rw [← e0]
  unfold kcLoop
  refine specR_forI (K := fun i => ctxH C (kcH C.H o ws i)) (G := kcG Γ0 C.H bufJ o q ws) _ kcBody rest n
    (fun i hi => ⟨_, sev_lower _ (vv kK) (vv kN) i n
      (by simp only [sev, vv]; exact kcG_k Γ0 C.H bufJ o q ws hK0 i)
      (by simp only [sev, vv]; rw [kcG_get Γ0 C.H bufJ o q ws kN (by decide) i]; exact hN)
      (by omega) (by omega), by simp [bw]⟩) (fun i hi => ?_) hr
  -- one iteration
  let j := q + i
  have hj : j < bs.length := by omega
  have hHl : (kcH C.H o ws i).length = C.H.length := kcH_length _ _ _ _
  have hc : bufJ + j / 8 < C.H.length := by have := Nat.div_le_div_right (c := 8) (Nat.le_of_lt hj); omega
  have hcell : (kcH C.H o ws i)[bufJ + j / 8]? = C.H[bufJ + j / 8]? := by
    rw [kcH_get, if_neg]
    intro ⟨h1, h2, _⟩
    exact hdis (bufJ + j / 8 - o) (by omega) j hj (by omega)
  obtain ⟨w, hw, hbw⟩ := hpk j hj
  have hwv : (kcH C.H o ws i).getD (bufJ + j / 8) 0 = w := by
    rw [List.getD_eq_getElem?_getD, hcell, hw]; rfl
  have hget : (kcH C.H o ws i)[bufJ + j / 8]'(by omega) = w := by
    have := hcell; rw [hw, List.getElem?_eq_getElem (by omega)] at this; exact Option.some.inj this
  have hcv : (w >>> ((BitVec.ofNat 64 j &&& 7) <<< (3 : Nat)).toNat) &&& 255 = ws.getD i 0 := by
    rw [and7shl3 j (by omega), byte_extract w (j % 8) (Nat.mod_lt _ (by decide)), hbw, hws i hi]
  have Gi := fun x (hx : x ∉ [kK, kC, kS, kW, kJ]) => kcG_get Γ0 C.H bufJ o q ws x hx i
  have hko' : o + i < C.H.length := by omega
  -- kJ := kQ + kK
  refine step_seq (step_assignI kJ _ (BitVec.ofNat 64 j) (hD kJ (by simp))
    (by simp only [sev, vv, Gi kQ (by decide), hQ, kcG_k Γ0 C.H bufJ o q ws hK0 i, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, Scan.ofNat_add64]; rfl)) ?_
  -- kW := *(kBA + ((kJ >> 3) << 3))
  refine step_seq (step_heapLoadI (C := ctxH C (kcH C.H o ws i)) kW _ (bufJ + j / 8) (by simp only [ctxH]; rw [hHl]; exact hc)
    (hD kW (by simp)) (by
      simp only [sev, vv, Env.get_cons, if_pos, show (kBA = kJ) = False from by decide, if_false,
        Gi kBA (by decide), hBA, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
        show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, if_true]
      rw [shr3shl3 j (by omega), ← cellA_add]; rfl)) ?_
  simp only [ctxH] at hget ⊢
  rw [hget]
  -- kS := (kJ & 7) << 3
  refine step_seq (step_assignI kS _ ((BitVec.ofNat 64 j &&& 7) <<< (3 : Nat)) (hD kS (by simp))
    (by simp [sev, vv, Env.get_cons, show kJ ≠ kW from by decide])) ?_
  -- kC := (kW >> kS) & 255
  refine step_seq (step_assignI kC _ ((w >>> ((BitVec.ofNat 64 j &&& 7) <<< (3 : Nat)).toNat) &&& 255)
    (hD kC (by simp)) (by
      have h8 := and7shl3 j (by omega)
      simp only [sev, vv, Env.get_cons, show (kW = kS) = False from by decide, if_true, if_false,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rw [if_pos (by rw [h8]; omega)]; rfl)) ?_
  -- *(kKA + (kK << 3)) := kC
  refine step_seq (step_heapStoreI (C := ctxH C (kcH C.H o ws i)) (ctxOK_H hok _) _ _ (o + i)
    (by simp only [ctxH]; rw [hHl]; exact hko') (ws.getD i 0)
    (by
      simp only [sev, vv, Env.get_cons, show (kKA = kC) = False from by decide, show (kKA = kS) = False from by decide,
        show (kKA = kW) = False from by decide, show (kKA = kJ) = False from by decide, if_false,
        show (kK = kC) = False from by decide, show (kK = kS) = False from by decide,
        show (kK = kW) = False from by decide, show (kK = kJ) = False from by decide,
        Gi kKA (by decide), hKA, kcG_k Γ0 C.H bufJ o q ws hK0 i, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.map_some, show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide,
        if_true]
      rw [shl3 i (by omega), ← cellA_add]; rfl)
    (by simp only [sev, vv, Env.get_cons, if_true]; rw [hcv])) ?_
  -- kK := kK + 1
  intro t ht
  rcases step_assignI (C := ctxH C (kcH C.H o ws (i + 1)))
    (Γ := (kC, (w >>> ((BitVec.ofNat 64 j &&& 7) <<< (3 : Nat)).toNat) &&& 255) ::
      (kS, (BitVec.ofNat 64 j &&& 7) <<< (3 : Nat)) :: (kW, w) :: (kJ, BitVec.ofNat 64 j) ::
      kcG Γ0 C.H bufJ o q ws i) kK (.op .add [vv kK, .const 1]) (BitVec.ofNat 64 (i + 1)) (hD kK (by simp))
    (by
      simp only [sev, vv, Env.get_cons, show (kK = kC) = False from by decide, show (kK = kS) = False from by decide,
        show (kK = kW) = False from by decide, show (kK = kJ) = False from by decide, if_false,
        kcG_k Γ0 C.H bufJ o q ws hK0 i, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) t ht with hs | ⟨hn, hq⟩
  · exact Or.inl hs
  · refine Or.inr ⟨hn, ?_⟩
    have hwv' : (kcH C.H o ws i).getD (bufJ + (q + i) / 8) 0 = w := hwv
    try simp only [kcG]
    simp only [hwv']
    exact hq

end ConPanqueque.Front
