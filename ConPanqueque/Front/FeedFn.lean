import ConPanqueque.Front.Feed

/-! # The line loop as a recursive function

`feed(tables, buffer, registry, i, n)`: past the buffer's end it returns; otherwise it applies the
line at `i` (`applyLineP`), returns if that was the last line (`next = 0`), and otherwise calls
itself at the next line.  `feedCore_spec`, by induction on the bytes left: the function refines
`feedAll`, ending at `FrontSt` of some image. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (scanLineFwd ScanRes)

variable {σ : Type}

def kR1 := ofString "kr1"
def fFeed := ofString "feed"
def feedPs : List MlS := [fTN, fTL, fTE, fCap, kBA, kBN, kRB, kCapD, kLI, kLn]
def feedL : List MlS := [kTg, kS0, kIx, kNx, kR0, kR1]

def afterLineP : ProgHOL 64 :=
  .ite (.cmp .equal (vv kNx) (.const 0)) (.return (.const 0))
    (.ite (.cmp .lower (vv kLI) (vv kNx))
      (.seq (.call (some (some (.local, kR1), none)) fFeed
          [vv fTN, vv fTL, vv fTE, vv fCap, vv kBA, vv kBN, vv kRB, vv kCapD, vv kNx, .op .add [vv kLn, .const 1]])
        (.return (vv kR1)))
      hang)

def feedCore : ProgHOL 64 :=
  .ite (.cmp .lower (vv kLI) (vv kBN)) (applyLineP afterLineP) (.return (.const 0))

def feedVs (C : Ctx) (jN jL jE cap bufJ bsz rb capD i n : Nat) : List (BitVec 64) :=
  [cellA C jN, cellA C jL, cellA C jE, BitVec.ofNat 64 cap, cellA C bufJ, BitVec.ofNat 64 bsz, cellA C rb,
    BitVec.ofNat 64 capD, BitVec.ofNat 64 i, BitVec.ofNat 64 n]

/-- A scan error: the first scanner call cannot return. -/
theorem specR_scanErr {α : Type} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (C : Ctx) (hok : CtxOK C) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b)
    (hlc : ∀ t : PState σ, t.code = C.code → LineCodes t)
    (hc1 : C.code.lookup fLnPl = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun sPl, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : kTg ∈ D)
    (i : USize) (hi : i.toNat ≤ b.size) (er : ConLeche.Frontend.ScanErr) (hs : scanLineFwd b i = .err er)
    (hLI : Γ.get kLI = some (BitVec.ofNat 64 i.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size)) :
    SpecR (Inv C s Γ M D) (.seq (callTo kTg fLnPl [vv kBA, vv kBN, vv kLI]) rest) s m R :=
  specR_retP3 kTg fLnPl sB sN sI _ (vv kBA) (vv kBN) (vv kLI) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 i.toNat) _ (by decide) (by decide) (by decide) hD hc1
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hLI)
    (fun t callee ht c1 c2 c3 => lineFun_spec (callEntryStateHOLFinite t callee) (cellA C bufJ) b hbuf.plat
      (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk
        (Nat.le_refl _)) rfl rfl rfl)
      (hlc _ (by show t.code = C.code; exact ht.sr.code)) i hi sPl (by simp) c1 c2 c3)
    (fun w ⟨u, ⟨rec, next, hs', _⟩, _⟩ => by rw [hs] at hs'; cases hs')

abbrev feedEnv (C : Ctx) (jN jL jE cap bufJ bsz rb capD i n : Nat) : Env :=
  ctxEnv C ++ feedPs.zip (feedVs C jN jL jE cap bufJ bsz rb capD i n)

section
variable (C : Ctx) (jN jL jE cap bufJ bsz rb capD i n : Nat)
theorem feedEnv_TN : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get fTN = some (cellA C jN) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_TL : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get fTL = some (cellA C jL) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_TE : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get fTE = some (cellA C jE) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_Cap : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get fCap = some (BitVec.ofNat 64 cap) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_BA : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get kBA = some (cellA C bufJ) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_BN : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get kBN = some (BitVec.ofNat 64 bsz) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_RB : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get kRB = some (cellA C rb) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_CD : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get kCapD = some (BitVec.ofNat 64 capD) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_LI : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get kLI = some (BitVec.ofNat 64 i) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedEnv_Ln : (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get kLn = some (BitVec.ofNat 64 n) := by
  simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
theorem feedL_none : ∀ y, y ∈ feedL → (feedEnv C jN jL jE cap bufJ bsz rb capD i n).get y = none := by
  intro y hy; simp only [feedL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [feedEnv, ctxEnv, feedPs, feedVs, Env.get]
end

/-- Where the loop ends: `FrontSt` of some image. -/
def FeedPost (C : Ctx) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) :
    StateD → BitVec 64 → AState → PState σ → Prop :=
  fun st' _ s' t' => ∃ H', SR (ctxH C H') s' t' ∧ FrontSt C F rb capD jN jL jE cap bufJ b H' st'


theorem usize_lt64 (i : USize) : i.toNat < 2 ^ 64 := by
  have := i.toNat_lt_size; simp [USize.size_eq_two_pow] at this
  rcases System.Platform.numBits_eq with h | h <;> rw [h] at this <;> omega

theorem ctxOK_ctxH {C : Ctx} {H : List (BitVec 64)} (h : CtxOK C) : CtxOK (ctxH C H) := by
  cases C; cases h; constructor <;> assumption
theorem frontOK_ctxH {C : Ctx} {H : List (BitVec 64)} (h : FrontOK C) : FrontOK (ctxH C H) := by
  cases C; cases h; constructor <;> assumption
theorem frontCodes_ctxH {C : Ctx} {H : List (BitVec 64)} (h : FrontCodes σ C) : FrontCodes σ (ctxH C H) :=
  ⟨h.hsc, h.hnc, h.hhc, h.hlc, h.cNth, h.cSafe, h.cHintV, h.cStr, h.cApp, h.cLam, h.cAll, h.cLet, h.cProj, h.cLs, h.cConst, h.cBVar, h.cSort, h.cSucc, h.cParam, h.cMax, h.cImax, h.cNNum, h.cNStr, h.fApp, h.fLam, h.fAll, h.fLet, h.fProj, h.fConst, h.fNum, h.fStrN, h.fThm, h.fOpq, h.fDef, h.cLnPl, h.cLnS0, h.cLnIx, h.cLnNx, h.l1, h.l2, h.l3, h.l4, h.l5, h.l6, h.l7, h.l8, h.l9, h.l10, h.l11, h.l12, h.l14, h.l15, h.l16, h.l18, h.l19⟩

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray} {H : List (BitVec 64)} {st : StateD}
theorem frontSt_ctxH {C : Ctx} (H0 : List (BitVec 64)) (h : FrontSt C F rb capD jN jL jE cap bufJ b H st) :
    FrontSt (ctxH C H0) F rb capD jN jL jE cap bufJ b H st := by
  cases C; exact ⟨h.lay, h.tN, h.tL, h.tE, h.dr, h.buf⟩
theorem frontSt_of_ctxH {C : Ctx} {H0 : List (BitVec 64)} (h : FrontSt (ctxH C H0) F rb capD jN jL jE cap bufJ b H st) :
    FrontSt C F rb capD jN jL jE cap bufJ b H st := by
  cases C; exact ⟨h.lay, h.tN, h.tL, h.tE, h.dr, h.buf⟩
end

/-- **The line loop refines `feedAll`.** -/
theorem feedCore_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (F rb capD jN jL jE cap bufJ : Nat)
    (b : ByteArray) :
    ∀ msr (C : Ctx) (i : USize) (st : StateD) (n : Nat) (s : AState), b.size - i.toNat = msr → n ≤ i.toNat →
      CtxOK C → FrontOK C → FrontCodes σ C →
      C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one) →
      FrontSt C F rb capD jN jL jE cap bufJ b C.H st →
      SpecR (Inv (σ := σ) C s (feedEnv C jN jL jE cap bufJ b.size rb capD i.toNat n) [] (ctxLocals ++ feedL))
        feedCore s (feedAll st b i n) (FeedPost C F rb capD jN jL jE cap bufJ b) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | ind msr ih =>
    intro C i st n s hm hn hok hf fc hcF hfs
    have hi64 := usize_lt64 i
    have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
    have hsz := hbuf.small
    unfold feedCore
    refine specR_ifI _ _ (sev_lower _ (vv kLI) (vv kBN) i.toNat b.size (by simpa [sev, vv] using feedEnv_LI ..)
      (by simpa [sev, vv] using feedEnv_BN ..) hi64 (by omega)) (fun hw => ?_) (fun hw => ?_)
    · have hlt : i.toNat < b.size := by
        by_cases e : i.toNat < b.size
        · exact e
        · simp [bw, e] at hw
      have hiu : i < b.usize := (hbuf.plat.lt_iff i).mpr hlt
      rw [feedAll, dif_pos hiu]
      cases hsc : scanLineFwd b i with
      | err er =>
        simp only
        unfold applyLineP
        exact specR_scanErr C hok bufJ b hbuf fc.hlc fc.cLnPl s _ [] _ (by simp [feedL]) i (by omega) er hsc
          (feedEnv_LI ..) (feedEnv_BA ..) (feedEnv_BN ..)
      | ok r j =>
        simp only
        refine applyLine_spec ra C hok hf fc s _ [] _ (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [feedL]) st hfs i (by omega) r j hsc n (by omega)
          (feedEnv_LI ..) (feedEnv_Ln ..) (feedEnv_TN ..) (feedEnv_TL ..) (feedEnv_TE ..) (feedEnv_Cap ..)
          (feedEnv_BA ..) (feedEnv_BN ..) (feedEnv_RB ..) (feedEnv_CD ..) (fun st' s' H' Γ' hf' hag hnx => ?_)
        have look : ∀ y, y ∉ [kTg, kS0, kIx, kNx, kR0] → Γ'.get y =
            (feedEnv C jN jL jE cap bufJ b.size rb capD i.toNat n).get y := hag
        simp only
        unfold afterLineP
        have hj64 := usize_lt64 j
        refine specR_ifI _ _ (sev_eq_c' Γ' kNx _ 0 hnx) (fun h0 => ?_) (fun h0 => ?_)
        · have hj0 : (j == 0) = true := by
            have e := congrArg BitVec.toNat (bw_eq_ne h0); simp only [BitVec.toNat_ofNat] at e
            rw [Nat.mod_eq_of_lt hj64] at e
            simp only [beq_iff_eq]; exact USize.toNat_inj.mp (by simpa using e)
          rw [if_pos hj0]
          exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨H', sr_of_eq ht.sr rfl rfl rfl rfl, hf'⟩)
        · have hj0 : ¬ (j == 0) = true := by
            intro e; simp only [beq_iff_eq] at e; subst e; simp [bw] at h0
          rw [if_neg hj0]
          refine specR_ifI _ _ (sev_lower Γ' (vv kLI) (vv kNx) i.toNat j.toNat
            (by simp only [sev, vv]; rw [look _ (by decide)]; exact feedEnv_LI ..) (by simpa [sev, vv] using hnx)
            hi64 hj64) (fun hw2 => ?_) (fun _ => specR_hangI)
          have hij : i.toNat < j.toNat := by
            by_cases e : i.toNat < j.toNat
            · exact e
            · simp [bw, e] at hw2
          have hiju : i < j := USize.lt_iff_toNat_lt.mpr hij
          rw [dif_pos hiju, ← bind_pure (feedAll st' b j (n + 1))]
          refine specR_protoCall (C := ctxH C H') kR1 fFeed feedPs (by decide) feedL feedCore _
            (feedVs (ctxH C H') jN jL jE cap bufJ b.size rb capD j.toNat (n + 1)) rfl (by simp [feedL]) hcF ?_
            (feedL_none (ctxH C H') jN jL jE cap bufJ b.size rb capD j.toNat (n + 1))
            (FeedPost (ctxH C H') F rb capD jN jL jE cap bufJ b)
            (fun _ _ _ _ _ ⟨H'', h1, h2⟩ => ⟨H'', sr_of_eq h1 rfl rfl rfl rfl, h2⟩)
            (ih _ (by omega) (ctxH C H') j st' (n + 1) s' rfl (by omega) (ctxOK_ctxH hok) (frontOK_ctxH hf) (frontCodes_ctxH fc) hcF (frontSt_ctxH H' hf'))
            (fun _ _ _ H'' => FrontSt C F rb capD jN jL jE cap bufJ b H'' _)
            (fun a w s'' t ⟨H'', h1, h2⟩ => ⟨H'', frontSt_of_ctxH h2, h1⟩)
            (fun a w s'' H'' hq => specR_returnI (vv kR1) w (by simp [sev, vv, Env.get_cons])
              (fun t ht => ⟨H'', sr_of_eq ht.sr rfl rfl rfl rfl, hq⟩))
          simp only [EvAll, feedVs, sev, vv]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnx, ?_, trivial⟩
          · rw [look _ (by decide)]; exact feedEnv_TN ..
          · rw [look _ (by decide)]; exact feedEnv_TL ..
          · rw [look _ (by decide)]; exact feedEnv_TE ..
          · rw [look _ (by decide)]; exact feedEnv_Cap ..
          · rw [look _ (by decide)]; exact feedEnv_BA ..
          · rw [look _ (by decide)]; exact feedEnv_BN ..
          · rw [look _ (by decide)]; exact feedEnv_RB ..
          · rw [look _ (by decide)]; exact feedEnv_CD ..
          · rw [look _ (by decide), feedEnv_Ln]
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add64]
    · have hge : ¬ i < b.usize := by
        intro h
        have : i.toNat < b.size := (hbuf.plat.lt_iff i).mp h
        simp [bw, this] at hw
      rw [feedAll, dif_neg hge]
      exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨C.H, by rw [ctxH_self]; exact sr_of_eq ht.sr rfl rfl rfl rfl, hfs⟩)

end ConPanqueque.Front
