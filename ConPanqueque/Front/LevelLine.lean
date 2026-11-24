import ConPanqueque.Front.NameLine

/-! # Single-number lines and level lines

`bvar`, `sort`, `succ`, `param`: the number is the line's payload slot (capped); both it and the
index are guarded below the cap.  `max`/`imax`: the payload is the list `[a, d]`'s position, read
twice by the k-th-element scanner. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ScanRes LevelRec scanNatList)

variable {σ : Type}

/-- A line whose number is in `fU`: both guards, then the procedure. -/
def natLineP (P : ProgHOL 64) : ProgHOL 64 := capG fI (capG fU P)

theorem natLine_spec {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {P : ProgHOL 64}
    {R : α → BitVec 64 → AState → PState σ → Prop} (i u : Nat) (m : AM α)
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hU : Γ.get fU = some (BitVec.ofNat 64 (min u natCap)))
    (hP : i < natCap → u < natCap → Γ.get fI = some (BitVec.ofNat 64 i) → Γ.get fU = some (BitVec.ofNat 64 u) →
      SpecR (Inv C s Γ M D) P s m R) :
    SpecR (Inv C s Γ M D) (natLineP P) s m R :=
  specR_capG fI i hI (fun hi hI' => specR_capG fU u hU (fun hu hU' => hP hi hu hI' hU'))

/-- A `max`/`imax` line: the list's two elements to `fU` and `fV2`. -/
def lvPairLineP (f : MlS) : ProgHOL 64 :=
  .seq (callTo fU fNth [vv kBA, vv kBN, vv kPos, .const 0])
    (.seq (callTo fV2 fNth [vv kBA, vv kBN, vv kPos, .const 1])
      (capG fI (capG fU (capG fV2 (lvBinP f)))))

theorem lvPairLine_spec {α : Type} (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (f : MlS) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fU, fV2], x ∈ D)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize) (a d i : Nat)
    (hs : scanNatList b pos = .ok [a, d] e) {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (hspec : ∀ Γ' : Env, i < natCap → a < natCap → d < natCap → Γ'.get fI = some (BitVec.ofNat 64 i) →
      Γ'.get fU = some (BitVec.ofNat 64 a) → Γ'.get fV2 = some (BitVec.ofNat 64 d) →
      (∀ y, y ≠ fU → y ≠ fV2 → Γ'.get y = Γ.get y) → SpecR (Inv C s Γ' M D) (lvBinP f) s m R)
    (hI : Γ.get fI = some (BitVec.ofNat 64 (min i natCap)))
    (hP : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv (σ := σ) C s Γ M D) (lvPairLineP f) s m R := by
  have hplat := hbuf.plat
  have hpos : pos.toNat ≤ b.size := Nat.le_of_lt (scanNatList_lt hplat hs)
  have nth : ∀ (Δ : Env) (x : MlS) (k : Nat), k < 2 → x ∈ D →
      Δ.get kBA = some (cellA C bufJ) → Δ.get kBN = some (BitVec.ofNat 64 b.size) →
      Δ.get kPos = some (BitVec.ofNat 64 pos.toNat) →
      Step (Inv (σ := σ) C s Δ M D) (callTo x fNth [vv kBA, vv kBN, vv kPos, .const (BitVec.ofNat 64 k)])
        (Inv C s ((x, nnRes [a, d] k) :: Δ) M D) :=
    fun Δ x k hk hx h1 h2 h3 =>
      step_call4I (C := C) x fNth sB sN sI sL nnFun (vv kBA) (vv kBN) (vv kPos) (.const (BitVec.ofNat 64 k))
        (cellA C bufJ) (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 pos.toNat) (BitVec.ofNat 64 k) (nnRes [a, d] k)
        (by decide) hx hcN (by simpa [sev, vv] using h1) (by simpa [sev, vv] using h2) (by simpa [sev, vv] using h3) rfl
        (fun t callee ht c1 c2 c3 c4 => retSpec_of_retP (nnFun_sound (callEntryStateHOLFinite t callee) (cellA C bufJ)
          b hplat (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk
            (Nat.le_refl _)) rfl rfl rfl)
          (hnc _ (by show t.code = C.code; exact ht.sr.code)) pos hpos k (by omega) [a, d] e hs c1 c2 c3 c4))
  unfold lvPairLineP
  refine specR_step (nth Γ fU 0 (by decide) (hD _ (by simp)) hBA hBN hP) ?_
  have g1 : ∀ y, y ≠ fU → Env.get ((fU, nnRes [a, d] 0) :: Γ) y = Γ.get y := fun y h => by
    simp only [Env.get_cons, if_neg h]
  refine specR_step (nth _ fV2 1 (by decide) (hD _ (by simp)) (by rw [g1 _ (by decide)]; exact hBA)
    (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hP)) ?_
  let Γ2 : Env := (fV2, nnRes [a, d] 1) :: (fU, nnRes [a, d] 0) :: Γ
  have g2 : ∀ y, y ≠ fV2 → y ≠ fU → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, if_neg h, if_neg h']
  refine specR_capG fI i (by rw [g2 _ (by decide) (by decide)]; exact hI) (fun hiN hI' => ?_)
  refine specR_capG fU a (by simp only [Γ2, Env.get_cons, if_neg (show fU ≠ fV2 by decide), if_pos]; rfl)
    (fun haN hU' => ?_)
  refine specR_capG fV2 d (by simp only [Γ2, Env.get_cons, if_pos]; rfl) (fun hdN hV' => ?_)
  exact hspec Γ2 hiN haN hdN hI' hU' hV' (fun y h h' => g2 y h' h)

end ConPanqueque.Front
