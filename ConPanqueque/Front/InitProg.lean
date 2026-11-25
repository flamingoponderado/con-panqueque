import ConPanqueque.Front.InitTwin

/-! # The frontend's initial state

`initP`: zero the three tables (contiguous from `jN`), bind index 0 of the name table to the zero
name handle and index 0 of the level table to the pinned zero level, and set the registry count to
0.  `initP_spec`: the result is `FrontSt` for `stInit s`, the state `StateD.init` returns after the
pins. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

/-- The pinned zero level's handle word. -/
def kZL := ofString "kzl"

def initP (rest : ProgHOL 64) : ProgHOL 64 :=
  zeroFillP (.seq (.store (vv fTN) (.const 1))
    (.seq (.store (vv fTL) (.op .add [vv kZL, .const 1])) (.seq (.store (vv kRB) (.const 0)) rest)))

theorem idxW_default : Enc.idxW (default : NIdx) = 0 := rfl

theorem singleton_get {α : Type} (x : α) (i : Nat) :
    (ConLeche.Frontend.IdTable.singleton x).get? i = if i = 0 then some x else none := by
  by_cases h : i = 0
  · subst h; simp [ConLeche.Frontend.IdTable.singleton, ConLeche.Frontend.IdTable.get?]
  · simp [ConLeche.Frontend.IdTable.singleton, ConLeche.Frontend.IdTable.get?, h]

theorem empty_get {α : Type} (i : Nat) : ({} : ConLeche.Frontend.IdTable α).get? i = none := by
  simp [ConLeche.Frontend.IdTable.get?]

theorem initP_spec {α : Type} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : kZ ∈ D)
    (F rb capD jN cap bufJ : Nat) (b : ByteArray)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b) (zl : LIdx)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hRB : Γ.get kRB = some (cellA C rb)) (hZL : Γ.get kZL = some (Enc.idxW zl))
    (hk : ∀ (Γ' : Env) (H' : List (BitVec 64)), (∀ y, y ≠ kZ → Γ'.get y = Γ.get y) →
      FrontSt C F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b H'
        { names := ConLeche.Frontend.IdTable.singleton default, levels := ConLeche.Frontend.IdTable.singleton zl } →
      SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (initP rest) s m R := by
  have hl := hfl.tE; have hb1 := hfl.buf; have hb2 := hfl.bufF
  have hrbF : rb < F := by omega
  unfold initP
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
  refine specR_heapStoreI (C := ctxH (ctxH (ctxH C K) K1) K2) (ctxOK_ctxH (ctxOK_ctxH (ctxOK_ctxH hok))) (vv kRB)
    (.const 0) rb (by show rb < K2.length; simp [K2, K1]; omega) 0
    (by simp only [sev, vv]; rw [g _ (by decide)]; exact hRB) rfl ?_
  let K3 := K2.set rb 0
  have hK3 : ∀ c, K3[c]? = if c = rb then (if c < C.H.length then some 0 else none)
      else if c = jN + cap then (if c < C.H.length then some (Enc.idxW zl + 1) else none)
      else if c = jN then (if c < C.H.length then some 1 else none) else K[c]? := by
    intro c
    simp only [K3, K2, K1, List.getElem?_set, List.length_set, hKl]
    by_cases h1 : rb = c <;> by_cases h2 : jN + cap = c <;> by_cases h3 : jN = c <;>
      simp [h1, h2, h3, eq_comm] <;> (try omega) <;> simp [show cap ≠ 0 by omega]
  refine hk Γ' K3 g ⟨⟨hfl, by omega, by omega, hcapN, hcap8, hcapD8⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [hK3, singleton_get]
      by_cases h0 : i = 0
      · subst h0; simp [show jN ≠ rb by omega, show jN + 0 ≠ jN + cap by omega, show jN < C.H.length by omega,
          show cap ≠ 0 by omega, tblW, idxW_default]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h0, hKg, ite_eq_left ⟨by omega, by omega, by omega⟩]
        rfl
    · rw [singleton_get, ite_eq_right (by omega)]
  · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [hK3, singleton_get]
      by_cases h0 : i = 0
      · subst h0; simp [show jN + cap ≠ rb by omega, show jN + cap < C.H.length by omega, tblW]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h0, hKg, ite_eq_left ⟨by omega, by omega, by omega⟩]
        rfl
    · rw [singleton_get, ite_eq_right (by omega)]
  · refine ⟨fun i hi => ?_, fun i _ => empty_get i⟩
    rw [hK3, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hKg, ite_eq_left ⟨by omega, by omega, by omega⟩,
      empty_get]; rfl
  · refine ⟨?_, by simp, by omega, by simp [K3, K2, K1, hKl]; omega, fun k hk => by simp at hk⟩
    rw [hK3, ite_eq_left rfl, ite_eq_left (by omega)]; rfl
  · refine ⟨fun i hi => ?_, hbuf.al, by simp [ctxH, K3, K2, K1, hKl]; exact hbuf.len, hbuf.plat, hbuf.small⟩
    obtain ⟨w, hw, hbw⟩ := hbuf.pk i hi
    refine ⟨w, ?_, hbw⟩
    show K3[bufJ + i / 8]? = some w
    rw [hK3, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hKg, ite_eq_right (by omega)]; exact hw

end ConPanqueque.Front
