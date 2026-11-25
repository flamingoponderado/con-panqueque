import ConPanqueque.Front.PlTag
import ConPanqueque.Front.Dispatch

/-! # The scan phase of the dispatcher

Four calls of the line scanner at the line's start, for the tag, the payload slot, the index and the
next position.  Each call is specified on its own (`lineFun_spec`), but all see the one record
`scanLineFwd b i` gives, so their words fit together (`ScanOut`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (LineRec LinePayload ScanRes scanLineFwd)

variable {σ : Type}

/-- The line's start. -/
def kLI := ofString "kli"
def fLnPl := ofString "lnpl"
def fLnS0 := ofString "lns0"
def fLnIx := ofString "lnix"
def fLnNx := ofString "lnnx"

/-- What the four words say about the line. -/
def ScanOut (b : ByteArray) (rec : LineRec) (next : USize) (wt ws wi wn : BitVec 64) : Prop :=
  wt = BitVec.ofNat 64 (plTag (recPl rec)) ∧ wn = BitVec.ofNat 64 next.toNat ∧
  (rec ≠ .blank → PlOK b wt ws (recPl rec) ∧
    ∃ j0 ik idx j', lineEnd j0 ik idx (recPl rec) = .ok rec j' ∧ wi = BitVec.ofNat 64 (min idx natCap))

theorem lineOut_rec {b : ByteArray} {i : USize} {rec : LineRec} {next : USize} (hs : scanLineFwd b i = .ok rec next)
    {u : PanSemStateFiniteExact 64 σ} (h : LineOut b i u) :
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 next.toNat))) ∧
    ((rec = .blank ∧ u.locals.lookup sPl = some (.val (.word 0))) ∨
     (rec ≠ .blank ∧ ∃ (ik : UInt8) (idx : Nat) (wpl ws0 : BitVec 64) (j0 j' : USize),
        u.locals.lookup sIdx = some (.val (.word (BitVec.ofNat 64 (min idx natCap)))) ∧
        u.locals.lookup sPl = some (.val (.word wpl)) ∧
        u.locals.lookup (slotName 0) = some (.val (.word ws0)) ∧ PlOK b wpl ws0 (recPl rec) ∧
        lineEnd j0 ik idx (recPl rec) = .ok rec j')) := by
  obtain ⟨rec', next', hs', hI, hc⟩ := h
  rw [hs] at hs'; simp only [ScanRes.ok.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'
  refine ⟨hI, ?_⟩
  rcases hc with ⟨hb, hp, -⟩ | ⟨ik, idx, pl, wpl, ws0, j0, j', h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨hb, hp⟩
  · have hpl := lineEnd_pl h6; subst hpl
    refine Or.inr ⟨fun hb => ?_, ik, idx, wpl, ws0, j0, j', h2, h3, h4, h5, h6⟩
    subst hb; simp [recPl, lineEnd] at h6

theorem lk_word {u : PanSemStateFiniteExact 64 σ} {x : MlS} {w w' : BitVec 64}
    (h : u.locals.lookup x = some (.val (.word w))) (h' : u.locals.lookup x = some (.val (.word w'))) : w = w' := by
  rw [h] at h'; simpa using h'

/-- The scan phase. -/
theorem specR_scanPhase {α : Type} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (C : Ctx) (hok : CtxOK C) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b)
    (hlc : ∀ t : PState σ, t.code = C.code → LineCodes t)
    (hc1 : C.code.lookup fLnPl = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun sPl, .one))
    (hc2 : C.code.lookup fLnS0 = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun (slotName 0), .one))
    (hc3 : C.code.lookup fLnIx = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun sIdx, .one))
    (hc4 : C.code.lookup fLnNx = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun sI, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kTg, kS0, kIx, kNx], x ∈ D)
    (i : USize) (hi : i.toNat ≤ b.size) (rec : LineRec) (next : USize) (hs : scanLineFwd b i = .ok rec next)
    (hLI : Γ.get kLI = some (BitVec.ofNat 64 i.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hk : ∀ wt ws wi wn, ScanOut b rec next wt ws wi wn →
      SpecR (Inv C s ((kNx, wn) :: (kIx, wi) :: (kS0, ws) :: (kTg, wt) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D)
      (.seq (callTo kTg fLnPl [vv kBA, vv kBN, vv kLI]) (.seq (callTo kS0 fLnS0 [vv kBA, vv kBN, vv kLI])
        (.seq (callTo kIx fLnIx [vv kBA, vv kBN, vv kLI]) (.seq (callTo kNx fLnNx [vv kBA, vv kBN, vv kLI]) rest))))
      s m R := by
  have hplat := hbuf.plat
  have lc : ∀ (Δ : Env) (x f y : MlS) (rest' : ProgHOL 64), x ∈ D → y ∈ [sI, sPl, sIK, sIdx, slotName 0] →
      C.code.lookup f = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun y, .one) →
      Δ.get kBA = some (cellA C bufJ) → Δ.get kBN = some (BitVec.ofNat 64 b.size) →
      Δ.get kLI = some (BitVec.ofNat 64 i.toNat) →
      (∀ w, (∃ u : PanSemStateFiniteExact 64 σ, LineOut b i u ∧ u.locals.lookup y = some (.val (.word w))) →
        SpecR (Inv C s ((x, w) :: Δ) M D) rest' s m R) →
      SpecR (Inv C s Δ M D) (.seq (callTo x f [vv kBA, vv kBN, vv kLI]) rest') s m R :=
    fun Δ x f y rest' hx hy hcf h1 h2 h3 hk' =>
      specR_retP3 x f sB sN sI _ (vv kBA) (vv kBN) (vv kLI) (cellA C bufJ) (BitVec.ofNat 64 b.size)
        (BitVec.ofNat 64 i.toNat) _ (by decide) (by decide) (by decide) hx hcf
        (by simpa [sev, vv] using h1) (by simpa [sev, vv] using h2) (by simpa [sev, vv] using h3)
        (fun t callee ht c1 c2 c3 => lineFun_spec (callEntryStateHOLFinite t callee) (cellA C bufJ) b hplat
          (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk
            (Nat.le_refl _)) rfl rfl rfl)
          (hlc _ (by show t.code = C.code; exact ht.sr.code)) i hi y hy c1 c2 c3) hk'
  refine lc Γ kTg fLnPl sPl _ (hD _ (by simp)) (by simp) hc1 hBA hBN hLI (fun wt ⟨u1, ho1, hl1⟩ => ?_)
  have g1 : ∀ y, y ≠ kTg → Env.get ((kTg, wt) :: Γ) y = Γ.get y := fun y h => by simp only [Env.get_cons, ite_eq_right h]
  refine lc _ kS0 fLnS0 (slotName 0) _ (hD _ (by simp)) (by simp) hc2 (by rw [g1 _ (by decide)]; exact hBA)
    (by rw [g1 _ (by decide)]; exact hBN) (by rw [g1 _ (by decide)]; exact hLI) (fun ws ⟨u2, ho2, hl2⟩ => ?_)
  let Γ2 : Env := (kS0, ws) :: (kTg, wt) :: Γ
  have g2 : ∀ y, y ≠ kS0 → y ≠ kTg → Γ2.get y = Γ.get y := fun y h h' => by
    simp only [Γ2, Env.get_cons, ite_eq_right h, ite_eq_right h']
  refine lc Γ2 kIx fLnIx sIdx _ (hD _ (by simp)) (by simp) hc3 (by rw [g2 _ (by decide) (by decide)]; exact hBA)
    (by rw [g2 _ (by decide) (by decide)]; exact hBN) (by rw [g2 _ (by decide) (by decide)]; exact hLI)
    (fun wi ⟨u3, ho3, hl3⟩ => ?_)
  let Γ3 : Env := (kIx, wi) :: Γ2
  have g3 : ∀ y, y ≠ kIx → y ≠ kS0 → y ≠ kTg → Γ3.get y = Γ.get y := fun y h0 h h' => by
    simp only [Γ3, Env.get_cons, ite_eq_right h0]; exact g2 y h h'
  refine lc Γ3 kNx fLnNx sI _ (hD _ (by simp)) (by simp) hc4 (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hLI) (fun wn ⟨u4, ho4, hl4⟩ => ?_)
  refine hk wt ws wi wn ⟨?_, ?_, fun hnb => ?_⟩
  · rcases (lineOut_rec hs ho1).2 with ⟨hb, hp⟩ | ⟨hnb, ik, idx, wpl, ws0, j0, j', -, hp, -, hpl, -⟩
    · subst hb; exact (lk_word hl1 hp)
    · rw [lk_word hl1 hp]; exact plOK_tag_eq hpl
  · exact (lk_word hl4 (lineOut_rec hs ho4).1)
  · have ht1 : wt = BitVec.ofNat 64 (plTag (recPl rec)) := by
      rcases (lineOut_rec hs ho1).2 with ⟨hb, -⟩ | ⟨-, ik, idx, wpl, ws0, j0, j', -, hp, -, hpl, -⟩
      · exact absurd hb hnb
      · rw [lk_word hl1 hp]; exact plOK_tag_eq hpl
    rcases (lineOut_rec hs ho2).2 with ⟨hb, -⟩ | ⟨-, ik2, idx2, wpl2, ws2, j02, j2', -, hp2, hs2, hpl2, -⟩
    · exact absurd hb hnb
    rcases (lineOut_rec hs ho3).2 with ⟨hb, -⟩ | ⟨-, ik3, idx3, wpl3, ws3, j03, j3', hi3, -, -, -, hle3⟩
    · exact absurd hb hnb
    refine ⟨?_, j03, ik3, idx3, j3', hle3, lk_word hl3 hi3⟩
    rw [lk_word hl2 hs2, ht1, ← plOK_tag_eq hpl2]; exact hpl2

end ConPanqueque.Front
