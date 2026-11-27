import ConPanqueque.Front.IndLineD
import ConPanqueque.Front.LineCall

/-! # The inductive line: the constructor loop

`indCtorLoop(…, J, …)`: constructor `J` (`ctorBody`), then itself at `J + 1`, until `J` reaches the
count.  `ctorCore_spec` by induction on the constructors left. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec scanNatList IndTypeRec IndCtorRec IndRecRec RuleRec scanIndCtors scanIndCtor)

set_option autoImplicit false

variable {σ : Type}

theorem prefix_of_agree {A B : List (BitVec 64)} (hl : A.length ≤ B.length)
    (h : ∀ c, c < A.length → B[c]? = A[c]?) : A <+: B := by
  refine ⟨B.drop A.length, ?_⟩
  apply List.ext_getElem?
  intro c
  by_cases hc : c < A.length
  · rw [List.getElem?_append_left hc]; exact (h c hc).symm
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]; congr 1; omega

def fCtorLoop := ofString "indCtorLoop"
def ilZ := ofString "il_z"

def ctorPs : List MlS := [kBA, kBN, fTN, fTE, fCap, ilCp, ilJ, ilNc, ilCB, ilOB, ilTh, ilP]
def ctorL : List MlS := ilZ :: ctorMods

def ctorArgs (eJ : ExpHOL 64) : List (ExpHOL 64) :=
  [vv kBA, vv kBN, vv fTN, vv fTE, vv fCap, vv ilCp, eJ, vv ilNc, vv ilCB, vv ilOB, vv ilTh, vv ilP]

def ctorCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv ilJ) (vv ilNc))
    (ctorBody C (.seq (.call (some (some (.local, ilZ), none)) fCtorLoop (ctorArgs (.op .add [vv ilJ, .const 1])))
      (.return (vv ilZ))))
    (.return (.const 0))

def ctorVals (C : Ctx) (bufJ bsz jN jE cap pC J nC cb ob : Nat) (T : NIdx) (nP : Nat) : List (BitVec 64) :=
  [cellA C bufJ, BitVec.ofNat 64 bsz, cellA C jN, cellA C jE, BitVec.ofNat 64 cap, BitVec.ofNat 64 pC,
    BitVec.ofNat 64 J, BitVec.ofNat 64 nC, cellA C cb, cellA C ob, Enc.idxW T, BitVec.ofNat 64 nP]

section
variable (C : Ctx) (bufJ bsz jN jE cap pC J nC cb ob : Nat) (T : NIdx) (nP : Nat)

abbrev ctorEnv : Env := ctxEnv C ++ ctorPs.zip (ctorVals C bufJ bsz jN jE cap pC J nC cb ob T nP)

theorem ctorEnv_get :
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get kBA = some (cellA C bufJ) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get kBN = some (BitVec.ofNat 64 bsz) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get fTN = some (cellA C jN) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get fTE = some (cellA C jE) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get fCap = some (BitVec.ofNat 64 cap) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get ilCp = some (BitVec.ofNat 64 pC) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get ilJ = some (BitVec.ofNat 64 J) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get ilNc = some (BitVec.ofNat 64 nC) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get ilCB = some (cellA C cb) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get ilOB = some (cellA C ob) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get ilTh = some (Enc.idxW T) ∧
    (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get ilP = some (BitVec.ofNat 64 nP) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp +decide [ctorEnv, ctxEnv, ctorPs, ctorVals, Env.get]

theorem ctorL_none : ∀ y, y ∈ ctorL → (ctorEnv C bufJ bsz jN jE cap pC J nC cb ob T nP).get y = none :=
  Knot.params_none C ctorL ctorPs _ (by decide) (by decide)

end

/-- After the loop from `J`: the twin unchanged, an image that keeps every cell outside slots
`J + 2 …` of the pointer block, and constructors `J …` stored with their twin facts. -/
def CtorFacts (C : Ctx) (s : AState) (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (T : NIdx)
    (ob X J : Nat) (H' : List (BitVec 64)) : Prop :=
  C.H.length ≤ H'.length ∧
    (∀ c v, C.H[c]? = some v → (c < ob + 2 + J ∨ X ≤ c) → H'[c]? = some v) ∧
    ∀ j (hj : J ≤ j) (hjn : j < cts.length), ∃ o, X ≤ o ∧ H'[ob + 2 + j]? = some (cellA C o) ∧
      RCIE X C H' o (.ctorInfo (cvOfD st cts[j].cv) cts[j].numParams cts[j].numFields T) ∧
      CtorOK st s t T cts[j] j ((st.names.get? (t.ctors.getD j 0)).getD default)

def CtorPost (C : Ctx) (s : AState) (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (T : NIdx)
    (ob X J : Nat) : Unit → BitVec 64 → AState → PState σ → Prop :=
  fun _ _ s' u => s' = s ∧ ∃ H', SR (ctxH C H') s u ∧ CtorFacts C s st t cts T ob X J H'

theorem ctorCore_spec (C0 : Ctx) (hok : CtxOK C0) (cc : ILCodes σ C0)
    (hcL : C0.code.lookup fCtorLoop = some (ctorPs.map (fun p => (p, ShapeHOL.one)), prologue ctorL (ctorCore C0), .one))
    (s : AState) (st : StateD) (jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C0.H jN cap st.names) (hrele : TblRel C0.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C0 bufJ b)
    (t : IndTypeRec) (cts : List IndCtorRec) (T : NIdx) (pC eC : USize) (hpC : scanIndCtors b pC = .ok cts eC)
    (hnC : cts.length < B55) (hnP : t.numParams < B55) (hlen : t.ctors.length = cts.length)
    (cb ob : Nat) (hob : C0.H.length ≤ ob) (hcbX : ob + cts.length + 3 ≤ cb) :
    ∀ n J (H : List (BitVec 64)), cts.length - J = n → J ≤ cts.length → C0.H <+: H →
      BlkAt H cb (tWords st.names t.ctors) → ob + cts.length + 3 ≤ H.length →
      SpecR (Inv (σ := σ) (ctxH C0 H) s (ctorEnv (ctxH C0 H) bufJ b.size jN jE cap pC.toNat J cts.length cb ob T
          t.numParams) [] (ctxLocals ++ ctorL)) (ctorCore C0) s (pure ())
        (CtorPost (ctxH C0 H) s st t cts T ob (ob + cts.length + 3) J) := by
  intro n
  induction n with
  | zero =>
    intro J H hn hJ hp hcb hX
    have hJ' : J = cts.length := by omega
    subst hJ'
    obtain ⟨-, -, -, -, -, -, gJ, gN, -⟩ := ctorEnv_get (ctxH C0 H) bufJ b.size jN jE cap pC.toNat cts.length
      cts.length cb ob T t.numParams
    unfold ctorCore
    refine specR_ifI _ _ (sev_lower_nat _ ilJ ilNc _ _ gJ gN (by unfold B55 at hnC; omega) (by unfold B55 at hnC; omega))
      (fun hw => absurd (bw_ne0 hw) (Nat.lt_irrefl _)) (fun _ => ?_)
    exact specR_returnI (.const 0) 0 rfl (fun u hu => ⟨rfl, H, sr_of_eq hu.sr rfl rfl rfl rfl, Nat.le_refl _,
      fun c v hc _ => hc, fun j hj hjn => absurd hjn (by omega)⟩)
  | succ n ih =>
    intro J H hn hJ hp hcb hX
    have hJn : J < cts.length := by omega
    obtain ⟨gBA, gBN, gTN, gTE, gC, gCp, gJ, gN, gCB, gOB, gTh, gP⟩ := ctorEnv_get (ctxH C0 H) bufJ b.size jN jE cap
      pC.toNat J cts.length cb ob T t.numParams
    unfold ctorCore
    refine specR_ifI _ _ (sev_lower_nat _ ilJ ilNc _ _ gJ gN (by unfold B55 at hnC; omega) (by unfold B55 at hnC; omega))
      (fun _ => ?_) (fun hw => absurd hJn (bw_eq0 hw))
    have hD : ∀ x ∈ ctorMods, x ∈ ctxLocals ++ ctorL := fun x hx => by simp [ctorL, hx]
    refine ctorBody_spec (ctxH C0 H) (ctxOK_H hok H) (cc.toH H) s _ [] _ hD st jN jE cap bufJ b (tblRel_prefix hreln hp)
      (tblRel_prefix hrele hp) hcap hcapN (bufOK_prefix hbuf hp) t cts T pC eC hpC J hJn hnC hnP cb ob hcb hlen
      (by show ob + 2 + J < H.length; omega) gBA gBN gTN gTE gC gCp gJ gCB gOB gTh gP _ (fun H1 Γ' o hpres hlen1 ho hslot hrc hcok hΓ => ?_)
    have hpres1 : ∀ c v, H[c]? = some v → c ≠ ob + 2 + J → H1[c]? = some v := hpres
    have hp1 : C0.H <+: H1 := prefix_of_agree (by have := hp.length_le; simp only [ctxH] at hlen1; omega)
      (fun c hc => by
        have hv : H[c]? = C0.H[c]? := by obtain ⟨r, hr⟩ := hp; rw [← hr, List.getElem?_append_left hc]
        obtain ⟨v, hv'⟩ : ∃ v, C0.H[c]? = some v := ⟨C0.H[c], List.getElem?_eq_getElem hc⟩
        rw [hv', hpres1 c v (by rw [hv, hv']) (by omega)])
    have hk1 : KeepsAbove (ob + cts.length + 3) H H1 := fun c hc v hv => hpres1 c v hv (by omega)
    have look : ∀ y, y ∉ ctorMods → Γ'.get y =
        (ctorEnv (ctxH C0 H) bufJ b.size jN jE cap pC.toNat J cts.length cb ob T t.numParams).get y := hΓ
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) rfl ?_
    refine specR_protoCall (C := ctxH (ctxH C0 H) H1) ilZ fCtorLoop ctorPs (by decide) ctorL (ctorCore C0)
      (ctorArgs (.op .add [vv ilJ, .const 1]))
      (ctorVals (ctxH C0 H1) bufJ b.size jN jE cap pC.toNat (J + 1) cts.length cb ob T t.numParams) rfl
      (by simp [ctorL]) hcL ?_
      (ctorL_none (ctxH C0 H1) bufJ b.size jN jE cap pC.toNat (J + 1) cts.length cb ob T t.numParams)
      (CtorPost (ctxH C0 H1) s st t cts T ob (ob + cts.length + 3) (J + 1))
      (fun _ _ _ _ _ ⟨h0, H'', h1, h2⟩ => ⟨h0, H'', sr_of_eq h1 rfl rfl rfl rfl, h2⟩)
      (ih (J + 1) H1 (by omega) (by omega) hp1 (blkAt_keep hk1 hcb (by omega)) (by simp only [ctxH] at hlen1; omega))
      (fun _ _ s'' H'' => s'' = s ∧ CtorFacts (ctxH C0 H1) s st t cts T ob (ob + cts.length + 3) (J + 1) H'')
      (fun a w s'' u ⟨h0, H'', h1, h2⟩ => ⟨H'', ⟨h0, h2⟩, by rw [h0]; exact h1⟩) ?_
    · simp only [EvAll, ctorArgs, ctorVals, sev, vv]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · rw [look _ (by decide)]; exact gBA
      · rw [look _ (by decide)]; exact gBN
      · rw [look _ (by decide)]; exact gTN
      · rw [look _ (by decide)]; exact gTE
      · rw [look _ (by decide)]; exact gC
      · rw [look _ (by decide)]; exact gCp
      · rw [look _ (by decide), gJ]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
      · rw [look _ (by decide)]; exact gN
      · rw [look _ (by decide)]; exact gCB
      · rw [look _ (by decide)]; exact gOB
      · rw [look _ (by decide)]; exact gTh
      · rw [look _ (by decide)]; exact gP
    · intro a w s'' H'' ⟨h0, hl2, hpres2, hall2⟩
      subst h0
      refine specR_returnI (vv ilZ) w (by simp [sev, vv, ConPanqueque.T.Env.get_cons]) (fun u hu => ?_)
      have hl1 : H.length ≤ H1.length := hlen1
      have hl2' : H1.length ≤ H''.length := hl2
      have hpres2' : ∀ c v, H1[c]? = some v → (c < ob + 2 + (J + 1) ∨ ob + cts.length + 3 ≤ c) → H''[c]? = some v :=
        hpres2
      refine ⟨rfl, H'', sr_of_eq hu.sr rfl rfl rfl rfl, by show H.length ≤ H''.length; omega,
        fun c v hc hcr => hpres2' c v (hpres1 c v hc (by omega)) (by omega), fun j hj hjn => ?_⟩
      by_cases e : j = J
      · subst e
        have hJc : j < t.ctors.length := by omega
        refine ⟨o, by have : ob + cts.length + 3 ≤ H.length := hX; have : H.length ≤ o := ho; omega,
          hpres2' _ _ hslot (by omega), rcie_keep (rcie_mono hrc (by show ob + cts.length + 3 ≤ H.length; omega))
            (fun c hc v hv => hpres2' c v hv (Or.inr hc)), ?_⟩
        rw [show t.ctors.getD j 0 = t.ctors[j] by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJc]]
        exact hcok
      · exact hall2 j (by omega) hjn
end ConPanqueque.Front
