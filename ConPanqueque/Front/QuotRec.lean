import ConPanqueque.Front.AxiomRec
import ConPanqueque.Scan.QuotKind

/-! # A quotient record in the value heap

A `#QUOT` line: name and type through the tables, the kind string classified (`fQKind`; any other string
hangs, where the twin fails), then the five-cell record of kind `6` whose fifth cell is the kind's number
(`type` 1, `ctor` 2, `lift` 3, `ind` 4). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec DeclRec HintsRec scanNatList scanString scanHints)

set_option autoImplicit false

variable {σ : Type}

/-- The kind a number names. -/
def qkOfNat : Nat → ConLeche.QuotKind
  | 1 => .type
  | 2 => .ctor
  | 3 => .lift
  | _ => .ind

theorem processQuot_ok (st : StateD) (cv : CVRec) (kind : String) (k : Nat) (hk : quotKindOf kind = some k)
    (nmh : NIdx) (tyh : EIdx)
    (hnm : st.names.get? cv.name = some nmh) (hty : st.exprs.get? cv.type = some tyh)
    (hlps : ∀ j (hj : j < cv.levelParams.length), (st.names.get? cv.levelParams[j]).isSome) :
    processLineCoreD st (.quot cv kind) =
      pure (.inl { st with decls := st.decls.push (.quotDecl (qkOfNat k)
        ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩) }) := by
  have hm := mapM_name_ok st cv.levelParams hlps
  unfold quotKindOf at hk
  split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;>
    simp [processLineCoreD, parseCVD, StateD.name, getDeclD, StateD.expr, hnm, hty, hm, pushDecl, qkOfNat]

/-- A quotient record: name and type, the kind classified, the record. -/
def qtVd (C : Ctx) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblGetP fz (vv fTE) (vv fCap) (vv fW3)
      (.ite (.cmp .equal (vv kSf) (.const (BitVec.ofNat 64 listSentinel))) hang
        (.seq (callTo kT fQKind [vv kBA, vv kBN, vv kSf])
          (.seq (.assign .local kVh (.op .sub [vv kT, vv kSf])) (vdTail C 6)))))

/-- The record's fifth cell: a kind's number. -/
def qkNum : ConLeche.QuotKind → Nat
  | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4 | .sound => 5

theorem qkNum_ofNat {x : String} {k : Nat} (h : quotKindOf x = some k) : qkNum (qkOfNat k) = k := by
  unfold quotKindOf at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem qtVd_spec (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcK : C.code.lookup fQKind = some ([(sB, .one), (sN, .one), (sI, .one)], qkFun, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fy, fz, kVh, kT, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (cv : CVRec) (kind : String) (hus : cv.levelParams.length < 2 ^ 59) (wpos wsf : BitVec 64)
    (hslot : (∃ (pos e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ scanNatList b pos = .ok cv.levelParams e0) ∨
      (cv.levelParams = [] ∧ wpos = BitVec.ofNat 64 listSentinel))
    (hss : (∃ (p e : USize), wsf = BitVec.ofNat 64 p.toNat ∧ scanString b p = .ok kind e) ∨
      (kind = "" ∧ wsf = BitVec.ofNat 64 listSentinel))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hU : Γ.get fU = some (BitVec.ofNat 64 (min cv.name natCap)))
    (hW : Γ.get fW3 = some (BitVec.ofNat 64 (min cv.type natCap)))
    (hV : Γ.get fV2 = some wpos) (hSf : Γ.get kSf = some wsf)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (qtVd C) s (processLineCoreD st (.quot cv kind))
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hplat := hbuf.plat
  have hNC : min cv.name natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hTC : min cv.type natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  unfold qtVd
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv fU)
    (by simpa [sev, vv] using hTN) (by simpa [sev, vv] using hC) _ hNC (by simpa [sev, vv] using hU)
    (fun nmh hnm => ?_)
  have hnm' := get_capped hreln hcapN _ nmh hnm
  have g1 : ∀ y, y ≠ fy → Env.get ((fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ) y = Env.get Γ y :=
    fun y h => by simp only [Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fz (hD fz (by simp)) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv fW3)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTE) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC)
    _ hTC (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hW) (fun tyh hty => ?_)
  have hty' := get_capped hrele hcapN _ tyh hty
  let Γ2 : Env := (fz, Enc.idxW tyh) :: (fz, Enc.idxW tyh + 1) :: (fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ
  have g2 : ∀ y, y ≠ fz → y ≠ fy → Env.get Γ2 y = Env.get Γ y := fun y h1 h2 => by
    simp only [Γ2, Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  refine specR_ifI _ _ (sev_eq_c' Γ2 kSf wsf (BitVec.ofNat 64 listSentinel)
    (by rw [g2 _ (by decide) (by decide)]; exact hSf)) (fun _ => specR_hangI) (fun hw => ?_)
  have hw' : wsf ≠ BitVec.ofNat 64 listSentinel := by intro h; simp [bw, h] at hw
  obtain ⟨psf, esf, hwsf, hsf⟩ := hss.resolve_right (fun ⟨_, h⟩ => hw' h)
  have hpsf : psf.toNat ≤ b.size := Nat.le_of_lt (scanString_lt hplat hsf)
  have hbt : ∀ (t : PState σ) (Δ : Env) (M' : Mem), Inv C s Δ M' D t → BytesAt t (cellA C bufJ) b.data.toList :=
    fun t Δ M' ht => bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)
  refine specR_retP3 kT fQKind sB sN sI qkFun (vv kBA) (vv kBN) (vv kSf) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 psf.toNat) (fun w => ∃ k, quotKindOf kind = some k ∧ w = BitVec.ofNat 64 (psf.toNat + k))
    (by decide) (by decide) (by decide) (hD kT (by simp)) hcK
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hBA)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hBN)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide), hSf, hwsf])
    (fun t callee ht h1 h2 h3 => qkFun_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hplat
      (bytesAt_congr (t := t) (hbt t _ _ ht) rfl rfl rfl) psf hpsf kind esf hsf h1 h2 h3) (fun wt ⟨k, hk, hwt⟩ => ?_)
  have hk4 : k ≤ 4 := by unfold quotKindOf at hk; split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk <;> omega
  have hroom := hplat.room
  let Γ3 : Env := (kT, wt) :: Γ2
  have g3 : ∀ y, y ≠ kT → y ≠ fz → y ≠ fy → Env.get Γ3 y = Env.get Γ y := fun y h0 h1 h2 => by
    simp only [Γ3, Env.get_cons, ite_eq_right h0]; exact g2 y h1 h2
  have e1 : Γ3.get kT = some wt := by simp [Γ3, Env.get_cons]
  have e2 : Γ3.get kSf = some wsf := by rw [g3 _ (by decide) (by decide) (by decide)]; exact hSf
  refine specR_assignI kVh (.op .sub [vv kT, vv kSf]) (BitVec.ofNat 64 k) (hD kVh (by simp)) (by
    have hs : sev Γ3 (.op .sub [vv kT, vv kSf]) = some (wt - wsf) := by
      show (do let x ← sev Γ3 (vv kT); let y ← sev Γ3 (vv kSf); pure (x - y)) = _
      simp only [sev, vv, e1, e2]; rfl
    rw [hs, hwt, hwsf]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have h1 : psf.toNat + k < 2 ^ 64 := by omega
    have h2 : psf.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    omega) ?_
  let Γ4 : Env := (kVh, BitVec.ofNat 64 k) :: Γ3
  have g4 : ∀ y, y ≠ kVh → y ≠ kT → y ≠ fz → y ≠ fy → Env.get Γ4 y = Env.get Γ y := fun y h h0 h1 h2 => by
    simp only [Γ4, Env.get_cons, ite_eq_right h]; exact g3 y h0 h1 h2
  refine vdTail_spec C hok hnc hcN s Γ4 M D (fun x hx => hD x (by simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))
    st F rb capD jN jL jE cap bufJ b hlay hreln hcap hcapN hbuf hdr hcapD cv.levelParams hus wpos hslot 6
    (Enc.idxW nmh) (Enc.idxW tyh) (BitVec.ofNat 64 k)
    (fun lpsH => .quotDecl (qkOfNat k) ⟨nmh, lpsH, tyh⟩)
    (fun H r o hr ho h0 h1 h2 h3 h4 hb =>
      ⟨hr, h0, ⟨o, ho, by simpa using h1, by simpa using h2, by simpa using h3, hb, by simpa using hus⟩,
        by rw [h4]; congr 2; exact (qkNum_ofNat hk).symm⟩)
    (fun hall => processQuot_ok st cv kind k hk nmh tyh hnm' hty' hall)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hC)
    (by simp only [Γ4, Γ3, Γ2, Env.get_cons, ite_eq_right (show fy ≠ kVh by decide), ite_eq_right (show fy ≠ kT by decide),
          ite_eq_right (show fy ≠ fz by decide), ite_eq_left])
    (by simp only [Γ4, Γ3, Γ2, Env.get_cons, ite_eq_right (show fz ≠ kVh by decide), ite_eq_right (show fz ≠ kT by decide),
          ite_eq_left])
    (by simp [Γ4])
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hV)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hCD)

end ConPanqueque.Front
