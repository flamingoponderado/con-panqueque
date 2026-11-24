import ConPanqueque.Front.ParseTwin

/-! # The parse: init, then the line loop from the buffer's start

`parseP rest`: `initP`, then `kR0 := feed(…, 0, 0)`, then `rest`.  `parseP_spec`: the continuation
runs at `FrontSt` of some image for the state `feedAll (stInit s) b 0 0` ends in. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

def feedArgs0 : List (ExpHOL 64) :=
  [vv fTN, vv fTL, vv fTE, vv fCap, vv kBA, vv kBN, vv kRB, vv kCapD, .const 0, .const 0]

def parseP (rest : ProgHOL 64) : ProgHOL 64 :=
  initP (.seq (.call (some (some (.local, kR0), none)) fFeed feedArgs0) rest)

theorem parseP_spec {β : Type} {k : StateD → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (fc : FrontCodes σ C)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0], x ∈ D)
    (F rb capD jN cap bufJ : Nat) (b : ByteArray)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (hk : ∀ st' s' H' (Γ'' : Env), feedAll (stInit s) b 0 0 s = .ok (st', s') →
      (∀ y, y ≠ kZ → y ≠ kR0 → Γ''.get y = Γ.get y) →
      FrontSt C F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' Γ'' [] D) rest s' (k st') R) :
    SpecR (Inv C s Γ M D) (parseP rest) s (feedAll (stInit s) b 0 0 >>= k) R := by
  unfold parseP
  refine initP_spec C hok s Γ M D (hD _ (by simp)) F rb capD jN cap bufJ b hfl hcap1 hcapN hcap8 hcapD8 hFH hbuf
    s.pins.zeroLevel hZb hZn hTN hTL hRB hZL (fun Γ' H' hag hfs => ?_)
  have g : ∀ y, y ≠ kZ → Γ'.get y = Γ.get y := hag
  have hfs' : FrontSt (ctxH C H') F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b (ctxH C H').H (stInit s) :=
    frontSt_ctxH H' hfs
  refine specR_protoCall (C := ctxH C H') kR0 fFeed feedPs (by decide) feedL feedCore feedArgs0
    (feedVs (ctxH C H') jN (jN + cap) (jN + 2 * cap) cap bufJ b.size rb capD 0 0) rfl (hD _ (by simp)) hcF ?_
    (feedL_none (ctxH C H') jN (jN + cap) (jN + 2 * cap) cap bufJ b.size rb capD 0 0)
    (fun a w s' t => feedAll (stInit s) b 0 0 s = .ok (a, s') ∧
      FeedPost (ctxH C H') F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b a w s' t)
    (fun _ _ _ _ _ ⟨hr, H'', h1, h2⟩ => ⟨hr, H'', sr_of_eq h1 rfl rfl rfl rfl, h2⟩)
    (specR_run (feedCore_spec ra F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b _ (ctxH C H') 0 (stInit s) 0 s rfl
      (by simp) (ctxOK_ctxH hok) (frontOK_ctxH hf) (frontCodes_ctxH fc) hcF hfs'))
    (fun st' _ s' H'' => feedAll (stInit s) b 0 0 s = .ok (st', s') ∧
      FrontSt C F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b H'' st')
    (fun a w s' t ⟨hr, H'', h1, h2⟩ => ⟨H'', ⟨hr, frontSt_of_ctxH h2⟩, h1⟩)
    (fun a w s' H'' ⟨hr, hq⟩ => hk a s' H'' _ hr
      (fun y h1 h2 => by simp only [Env.get_cons, if_neg h2]; exact g y h1) hq)
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

end ConPanqueque.Front
