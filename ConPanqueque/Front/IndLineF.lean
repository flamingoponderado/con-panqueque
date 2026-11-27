import ConPanqueque.Front.IndLineE

/-! # The inductive line: the recursor's rules

`ruleBody`: rule `J` of the recursor (its position from `fRulesAt`), its constructor name and right-hand
side through the tables, its field count (below `2⁵⁵`); the rule `[ctor, nfields, 0, 0, 0, rhs]` and
the pointer to it in slot `J + 1` of the rule block at `ilRP`.  `indRuleLoop` repeats it. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec IndTypeRec IndCtorRec IndRecRec RuleRec scanRules scanRule)

set_option autoImplicit false

variable {σ : Type}

def ilRl := ofString "il_rl"
def ilNu := ofString "il_nu"
def ilRP := ofString "il_rp"
def fRuleLoop := ofString "indRuleLoop"

def ruleBody (C : Ctx) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (callTo ilQ fRulesAt [vv kBA, vv kBN, vv ilRl, vv ilJ])
  (.seq (callTo ilX (fRuF 0) [vv kBA, vv kBN, vv ilQ])
  (tblGetP ilY (vv fTN) (vv fCap) (vv ilX)
  (.seq (callTo ilA (fRuF 1) [vv kBA, vv kBN, vv ilQ])
  (.ite (.cmp .lower (vv ilA) (.const b55W))
    (.seq (callTo ilX (fRuF 2) [vv kBA, vv kBN, vv ilQ])
    (tblGetP ilB (vv fTE) (vv fCap) (vv ilX)
    (allocWr C ilR [vv ilY, vv ilA, .const 0, .const 0, .const 0, vv ilB]
      (.seq (.store (slotE ilRP ilJ 1) (vv ilR)) rest)))) hang))))

def ruleMods : List MlS := [ilQ, ilX, ilY, ilA, ilB, ilR]

/-- A rule's twin facts. -/
structure RuleOK (st : StateD) (ru : RuleRec) : Prop where
  ctor : (st.names.get? ru.ctor).isSome
  rhs : (st.exprs.get? ru.rhs).isSome
  nf : ru.nfields < B55

theorem ruleBody_spec {α : Type} (C : Ctx) (hok : CtxOK C) (cc : ILCodes σ C)
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ ruleMods, x ∈ D)
    (st : StateD) (jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b)
    (rus : List RuleRec) (pR eR : USize) (hpR : scanRules b pR = .ok rus eR)
    (J : Nat) (hJ : J < rus.length) (hnU : rus.length < B55) (rp : Nat) (hslot : rp + 1 + J < C.H.length)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hRl : Γ.get ilRl = some (BitVec.ofNat 64 pR.toNat))
    (hJw : Γ.get ilJ = some (BitVec.ofNat 64 J)) (hRP : Γ.get ilRP = some (cellA C rp))
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64)
    (hk : ∀ (H' : List (BitVec 64)) (Γ' : Env) (o : Nat),
      (∀ c v, C.H[c]? = some v → c ≠ rp + 1 + J → H'[c]? = some v) → C.H.length ≤ H'.length →
      C.H.length ≤ o → H'[rp + 1 + J]? = some (cellA C o) →
      RRule C.H.length C H' o (ruleOfD st rus[J]) → RuleOK st rus[J] →
      (∀ y, y ∉ ruleMods → Γ'.get y = Γ.get y) →
      SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (ruleBody C rest) s m R := by
  have hplat := hbuf.plat
  have hpRb : pR.toNat ≤ b.size := Nat.le_of_lt (objListOpen_pos hplat (by rw [← scanRules_objList]; exact hpR))
  unfold ruleBody
  refine specR_scan4 hok bufJ b hbuf ilQ fRulesAt ilRl (vv ilJ) _ pR.toNat J _ (hD ilQ (by simp [ruleMods]))
    cc.rulesAt hBA hBN hRl (by simpa [sev, vv] using hJw)
    (fun u hb hu l1 l2 l3 l4 => ruleAt_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pR eR rus hpR J
      (by unfold B55 at hnU; omega) l1 l2 l3 l4) (fun wq hq => ?_)
  obtain ⟨q, e', rfl, hqb, hsq⟩ := hq hJ
  refine specR_scan3 hok bufJ b hbuf ilX (fRuF 0) ilQ _ q.toNat _ (hD ilX (by simp [ruleMods]))
    (cc.ruleF 0 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => ruleField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 0 (by decide) _ e' hsq)
    (fun w0 hw0 => ?_)
  simp only [RuleField] at hw0; subst hw0
  refine specR_tblGetI ilY (hD ilY (by simp [ruleMods])) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv ilX)
    (by simp only [sev, vv]; envg; exact hTN) (by simp only [sev, vv]; envg; exact hC) _ (natW_lt64 _)
    (by simp only [sev, vv]; envg; rfl) (fun hc hhc => ?_)
  have hc' := get_capped hreln hcapN _ hc hhc
  refine specR_scan3 hok bufJ b hbuf ilA (fRuF 1) ilQ _ q.toNat _ (hD ilA (by simp [ruleMods]))
    (cc.ruleF 1 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => ruleField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 1 (by decide) _ e' hsq)
    (fun w1 hw1 => ?_)
  simp only [RuleField] at hw1; subst hw1
  refine specR_ltGuardI ilA (Scan.natW rus[J].nfields) b55W (by envg) (fun hl1 => ?_)
  obtain ⟨hnf, hnfw⟩ := natW_small (by rw [b55W_toNat] at hl1; exact hl1)
  refine specR_scan3 hok bufJ b hbuf ilX (fRuF 2) ilQ _ q.toNat _ (hD ilX (by simp [ruleMods]))
    (cc.ruleF 2 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => ruleField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 2 (by decide) _ e' hsq)
    (fun w2 hw2 => ?_)
  simp only [RuleField] at hw2; subst hw2
  refine specR_tblGetI ilB (hD ilB (by simp [ruleMods])) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv ilX)
    (by simp only [sev, vv]; envg; exact hTE) (by simp only [sev, vv]; envg; exact hC) _ (natW_lt64 _)
    (by simp only [sev, vv]; envg; rfl) (fun hr hhr => ?_)
  have hr' := get_capped hrele hcapN _ hr hhr
  rw [hnfw]
  have hru : ruleOfD st rus[J] = ⟨hc, rus[J].nfields, .plain, hr⟩ := by simp [ruleOfD, hc', hr']
  refine specR_allocWrI C hok ilR (hD ilR (by simp [ruleMods])) [vv ilY, vv ilA, .const 0, .const 0, .const 0, vv ilB]
    [Enc.idxW hc, BitVec.ofNat 64 rus[J].nfields, 0, 0, 0, Enc.idxW hr] rfl (by simp)
    (fun v i hi => ?_) (fun H2 r hp2 hr1 hr2 hrw => ?_)
  · simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ, List.getD_cons_zero, sev, vv] <;>
    first | rfl | envg
  have gE : ∀ y, y ∉ ruleMods → Env.get ((ilR, cellA C r) :: (ilB, Enc.idxW hr) :: (ilB, Enc.idxW hr + 1) ::
      (ilX, Scan.natW rus[J].rhs) :: (ilA, BitVec.ofNat 64 rus[J].nfields) :: (ilY, Enc.idxW hc) ::
      (ilY, Enc.idxW hc + 1) :: (ilX, Scan.natW rus[J].ctor) :: (ilQ, BitVec.ofNat 64 q.toNat) :: Γ) y = Γ.get y :=
    fun y hy => by
      simp only [ruleMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp only [ConPanqueque.T.Env.get_cons, ite_eq_right hy.1, ite_eq_right hy.2.1, ite_eq_right hy.2.2.1,
        ite_eq_right hy.2.2.2.1, ite_eq_right hy.2.2.2.2.1, ite_eq_right hy.2.2.2.2.2]
  refine specR_heapStoreI (C := ctxH C H2) (ctxOK_H hok H2) (slotE ilRP ilJ 1) (vv ilR) (rp + 1 + J)
    (by show rp + 1 + J < H2.length; have := hp2.length_le; omega) (cellA C r)
    (sev_slot _ (ctxH C H2) ilRP ilJ rp J 1 (by rw [gE _ (by decide)]; exact hRP)
      (by rw [gE _ (by decide)]; exact hJw) (by unfold B55 at hnU; omega))
    (by simp only [sev, vv, ConPanqueque.T.Env.get_cons, ite_true]) ?_
  have hr1' : C.H.length ≤ r := hr1
  refine hk (H2.set (rp + 1 + J) (cellA C r)) _ r (fun c v hc0 hne => ?_) (by simp; have := hp2.length_le; omega)
    (by omega) (by simp [List.getElem?_set]; have := hp2.length_le; omega) ?_ ⟨by rw [hc']; rfl, by rw [hr']; rfl, hnf⟩
    (fun y hy => gE y hy)
  · rw [List.getElem?_set, ite_eq_right (by omega)]; exact getElem?_prefix hp2 hc0
  · refine rrule_keep (rrule_of C.H.length C H2 r (ruleOfD st rus[J]) (by omega) (by rw [hru])
      (by rw [hru]; unfold B55 at hnf; simp only; omega) (fun i hi => ?_)) (keepsAbove_set_lt (by omega) _)
    rw [hru]; have := hrw i (by simpa using hi); simpa using this

def ruleArgs (eJ : ExpHOL 64) : List (ExpHOL 64) :=
  [vv kBA, vv kBN, vv fTN, vv fTE, vv fCap, vv ilRl, eJ, vv ilNu, vv ilRP]

def rulePs : List MlS := [kBA, kBN, fTN, fTE, fCap, ilRl, ilJ, ilNu, ilRP]
def ruleL : List MlS := ilZ :: ruleMods

def ruleCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv ilJ) (vv ilNu))
    (ruleBody C (.seq (.call (some (some (.local, ilZ), none)) fRuleLoop (ruleArgs (.op .add [vv ilJ, .const 1])))
      (.return (vv ilZ))))
    (.return (.const 0))

def ruleVals (C : Ctx) (bufJ bsz jN jE cap pR J nU rp : Nat) : List (BitVec 64) :=
  [cellA C bufJ, BitVec.ofNat 64 bsz, cellA C jN, cellA C jE, BitVec.ofNat 64 cap, BitVec.ofNat 64 pR,
    BitVec.ofNat 64 J, BitVec.ofNat 64 nU, cellA C rp]

section
variable (C : Ctx) (bufJ bsz jN jE cap pR J nU rp : Nat)

abbrev ruleEnv : Env := ctxEnv C ++ rulePs.zip (ruleVals C bufJ bsz jN jE cap pR J nU rp)

theorem ruleEnv_get :
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get kBA = some (cellA C bufJ) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get kBN = some (BitVec.ofNat 64 bsz) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get fTN = some (cellA C jN) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get fTE = some (cellA C jE) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get fCap = some (BitVec.ofNat 64 cap) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get ilRl = some (BitVec.ofNat 64 pR) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get ilJ = some (BitVec.ofNat 64 J) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get ilNu = some (BitVec.ofNat 64 nU) ∧
    (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get ilRP = some (cellA C rp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp +decide [ruleEnv, ctxEnv, rulePs, ruleVals, Env.get]

theorem ruleL_none : ∀ y, y ∈ ruleL → (ruleEnv C bufJ bsz jN jE cap pR J nU rp).get y = none :=
  Knot.params_none C ruleL rulePs _ (by decide) (by decide)

end

def RuleFacts (C : Ctx) (st : StateD) (rus : List RuleRec) (rp X J : Nat) (H' : List (BitVec 64)) : Prop :=
  C.H.length ≤ H'.length ∧
    (∀ c v, C.H[c]? = some v → (c < rp + 1 + J ∨ X ≤ c) → H'[c]? = some v) ∧
    ∀ j (hj : J ≤ j) (hjn : j < rus.length), ∃ o, X ≤ o ∧ H'[rp + 1 + j]? = some (cellA C o) ∧
      RRule X C H' o (ruleOfD st rus[j]) ∧ RuleOK st rus[j]

def RulePost (C : Ctx) (s : AState) (st : StateD) (rus : List RuleRec) (rp X J : Nat) :
    Unit → BitVec 64 → AState → PState σ → Prop :=
  fun _ _ s' u => s' = s ∧ ∃ H', SR (ctxH C H') s u ∧ RuleFacts C st rus rp X J H'

theorem ruleCore_spec (C0 : Ctx) (hok : CtxOK C0) (cc : ILCodes σ C0)
    (hcL : C0.code.lookup fRuleLoop = some (rulePs.map (fun p => (p, ShapeHOL.one)), prologue ruleL (ruleCore C0), .one))
    (s : AState) (st : StateD) (jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C0.H jN cap st.names) (hrele : TblRel C0.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C0 bufJ b)
    (rus : List RuleRec) (pR eR : USize) (hpR : scanRules b pR = .ok rus eR) (hnU : rus.length < B55)
    (rp : Nat) (hrp : C0.H.length ≤ rp) :
    ∀ n J (H : List (BitVec 64)), rus.length - J = n → J ≤ rus.length → C0.H <+: H →
      rp + rus.length + 1 ≤ H.length →
      SpecR (Inv (σ := σ) (ctxH C0 H) s (ruleEnv (ctxH C0 H) bufJ b.size jN jE cap pR.toNat J rus.length rp) []
          (ctxLocals ++ ruleL)) (ruleCore C0) s (pure ())
        (RulePost (ctxH C0 H) s st rus rp (rp + rus.length + 1) J) := by
  intro n
  induction n with
  | zero =>
    intro J H hn hJ hp hX
    have hJ' : J = rus.length := by omega
    subst hJ'
    obtain ⟨-, -, -, -, -, -, gJ, gN, -⟩ := ruleEnv_get (ctxH C0 H) bufJ b.size jN jE cap pR.toNat rus.length
      rus.length rp
    unfold ruleCore
    refine specR_ifI _ _ (sev_lower_nat _ ilJ ilNu _ _ gJ gN (by unfold B55 at hnU; omega) (by unfold B55 at hnU; omega))
      (fun hw => absurd (bw_ne0 hw) (Nat.lt_irrefl _)) (fun _ => ?_)
    exact specR_returnI (.const 0) 0 rfl (fun u hu => ⟨rfl, H, sr_of_eq hu.sr rfl rfl rfl rfl, Nat.le_refl _,
      fun c v hc _ => hc, fun j hj hjn => absurd hjn (by omega)⟩)
  | succ n ih =>
    intro J H hn hJ hp hX
    have hJn : J < rus.length := by omega
    obtain ⟨gBA, gBN, gTN, gTE, gC, gRl, gJ, gN, gRP⟩ := ruleEnv_get (ctxH C0 H) bufJ b.size jN jE cap
      pR.toNat J rus.length rp
    unfold ruleCore
    refine specR_ifI _ _ (sev_lower_nat _ ilJ ilNu _ _ gJ gN (by unfold B55 at hnU; omega) (by unfold B55 at hnU; omega))
      (fun _ => ?_) (fun hw => absurd hJn (bw_eq0 hw))
    have hD : ∀ x ∈ ruleMods, x ∈ ctxLocals ++ ruleL := fun x hx => by simp [ruleL, hx]
    refine ruleBody_spec (ctxH C0 H) (ctxOK_H hok H) (cc.toH H) s _ [] _ hD st jN jE cap bufJ b (tblRel_prefix hreln hp)
      (tblRel_prefix hrele hp) hcap hcapN (bufOK_prefix hbuf hp) rus pR eR hpR J hJn hnU rp (by show rp + 1 + J < H.length; omega)
      gBA gBN gTN gTE gC gRl gJ gRP _ (fun H1 Γ' o hpres hlen1 ho hslot hrr hrok hΓ => ?_)
    have hpres1 : ∀ c v, H[c]? = some v → c ≠ rp + 1 + J → H1[c]? = some v := hpres
    have hp1 : C0.H <+: H1 := prefix_of_agree (by have := hp.length_le; simp only [ctxH] at hlen1; omega)
      (fun c hc => by
        have hv : H[c]? = C0.H[c]? := by obtain ⟨r, hr⟩ := hp; rw [← hr, List.getElem?_append_left hc]
        obtain ⟨v, hv'⟩ : ∃ v, C0.H[c]? = some v := ⟨C0.H[c], List.getElem?_eq_getElem hc⟩
        rw [hv', hpres1 c v (by rw [hv, hv']) (by omega)])
    have look : ∀ y, y ∉ ruleMods → Γ'.get y =
        (ruleEnv (ctxH C0 H) bufJ b.size jN jE cap pR.toNat J rus.length rp).get y := hΓ
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) rfl ?_
    refine specR_protoCall (C := ctxH (ctxH C0 H) H1) ilZ fRuleLoop rulePs (by decide) ruleL (ruleCore C0)
      (ruleArgs (.op .add [vv ilJ, .const 1]))
      (ruleVals (ctxH C0 H1) bufJ b.size jN jE cap pR.toNat (J + 1) rus.length rp) rfl
      (by simp [ruleL]) hcL ?_
      (ruleL_none (ctxH C0 H1) bufJ b.size jN jE cap pR.toNat (J + 1) rus.length rp)
      (RulePost (ctxH C0 H1) s st rus rp (rp + rus.length + 1) (J + 1))
      (fun _ _ _ _ _ ⟨h0, H'', h1, h2⟩ => ⟨h0, H'', sr_of_eq h1 rfl rfl rfl rfl, h2⟩)
      (ih (J + 1) H1 (by omega) (by omega) hp1 (by simp only [ctxH] at hlen1; omega))
      (fun _ _ s'' H'' => s'' = s ∧ RuleFacts (ctxH C0 H1) st rus rp (rp + rus.length + 1) (J + 1) H'')
      (fun a w s'' u ⟨h0, H'', h1, h2⟩ => ⟨H'', ⟨h0, h2⟩, by rw [h0]; exact h1⟩) ?_
    · simp only [EvAll, ruleArgs, ruleVals, sev, vv]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · rw [look _ (by decide)]; exact gBA
      · rw [look _ (by decide)]; exact gBN
      · rw [look _ (by decide)]; exact gTN
      · rw [look _ (by decide)]; exact gTE
      · rw [look _ (by decide)]; exact gC
      · rw [look _ (by decide)]; exact gRl
      · rw [look _ (by decide), gJ]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
      · rw [look _ (by decide)]; exact gN
      · rw [look _ (by decide)]; exact gRP
    · intro a w s'' H'' ⟨h0, hl2, hpres2, hall2⟩
      subst h0
      refine specR_returnI (vv ilZ) w (by simp [sev, vv, ConPanqueque.T.Env.get_cons]) (fun u hu => ?_)
      have hl1 : H.length ≤ H1.length := hlen1
      have hl2' : H1.length ≤ H''.length := hl2
      have hpres2' : ∀ c v, H1[c]? = some v → (c < rp + 1 + (J + 1) ∨ rp + rus.length + 1 ≤ c) →
          H''[c]? = some v := hpres2
      refine ⟨rfl, H'', sr_of_eq hu.sr rfl rfl rfl rfl, by show H.length ≤ H''.length; omega,
        fun c v hc hcr => hpres2' c v (hpres1 c v hc (by omega)) (by omega), fun j hj hjn => ?_⟩
      by_cases e : j = J
      · subst e
        refine ⟨o, by have : rp + rus.length + 1 ≤ H.length := hX; have : H.length ≤ o := ho; omega,
          hpres2' _ _ hslot (by omega), ?_, hrok⟩
        intro H3 hk3
        exact hrr H3 (fun c hc v hv => by
          have hc' : H.length ≤ c := hc
          have : rp + rus.length + 1 ≤ H.length := hX
          exact hk3 c (by omega) v (hpres2' c v hv (Or.inr (by omega))))
      · exact hall2 j (by omega) hjn
end ConPanqueque.Front
