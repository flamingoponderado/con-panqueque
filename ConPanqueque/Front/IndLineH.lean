import ConPanqueque.Front.IndLineG

/-! # The inductive line: the recursor record's checks -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec IndTypeRec IndCtorRec IndRecRec RuleRec scanRules scanRule scanIndRec)

set_option autoImplicit false

variable {σ : Type}

theorem optW_cases (o : Option Nat) (K : Nat) (hK : ∀ n, o = some n → n < K) (hK64 : K < 2 ^ 63) (y : Nat) (hy : y < 2 ^ 63)
    (h : ¬ (ConPanqueque.T.Ind.optW o ≠ 0 ∧ ConPanqueque.T.Ind.optW o ≠ BitVec.ofNat 64 (y + 1))) : ∀ n, o = some n → n = y := by
  intro n hn; subst hn
  have hnK := hK n rfl
  simp only [ConPanqueque.T.Ind.optW] at h
  have hne : BitVec.ofNat 64 (n + 1) ≠ 0 := by
    intro e; have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; simp at this
  have : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 (y + 1) := Classical.byContradiction fun e => h ⟨hne, e⟩
  have := ofNat_inj64 (by omega) (by omega) this; omega

theorem recP_spec {α : Type} (C0 : Ctx) (hok : CtxOK C0) (cc : ILCodes σ C0)
    (hrL : C0.code.lookup fRuleLoop = some (rulePs.map (fun p => (p, ShapeHOL.one)), prologue ruleL (ruleCore C0), .one))
    (s : AState) (Γ : Env) (D : List MlS) (hD : ∀ x ∈ recMods, x ∈ D)
    (st : StateD) (F rb capD jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C0.H jN cap st.names) (hrele : TblRel C0.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C0 bufJ b)
    (hdr : DeclsRel C0 F rb capD C0.H st.decls) (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (T : NIdx) (tyh : EIdx) (qR eR : USize)
    (hqR : qR.toNat ≤ b.size) (hsR : scanIndRec b qR = .ok r eR)
    (hnP : t.numParams < B55) (hnC : cts.length < B55)
    (hlpT : t.cv.levelParams.length < B55) (hlpC : ∀ c ∈ cts, c.cv.levelParams.length < B55)
    (H : List (BitVec 64)) (hp0 : C0.H <+: H) (ob : Nat) (hob : C0.H.length ≤ ob)
    (hX : ob + cts.length + 3 ≤ H.length)
    (hob0 : H[ob]? = some (BitVec.ofNat 64 (cts.length + 2))) (os : List Nat) (hosl : os.length = cts.length + 1)
    (hos : ∀ i (hi : i < os.length), H[ob + 1 + i]? = some (cellA C0 os[i]))
    (hhead : ∀ i (hi : i < (indHead st t cts T).length) (ho : i < os.length),
      RCIE (ob + cts.length + 3) C0 H os[i] (indHead st t cts T)[i])
    (hBA : Γ.get kBA = some (cellA C0 bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hTN : Γ.get fTN = some (cellA C0 jN)) (hTE : Γ.get fTE = some (cellA C0 jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hRB : Γ.get kRB = some (cellA C0 rb))
    (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hRq : Γ.get ilRq = some (BitVec.ofNat 64 qR.toNat)) (hP : Γ.get ilP = some (BitVec.ofNat 64 t.numParams))
    (hNc : Γ.get ilNc = some (BitVec.ofNat 64 cts.length)) (hOB : Γ.get ilOB = some (cellA C0 ob))
    (hTy : Γ.get ilTy = some (Enc.idxW tyh))
    (hfd : ConPanqueque.Bridge.IsFrontDecl C0.pins (.indDecl (indBlockD st t cts r T) t.numParams))
    {m : AM (StateD ⊕ RecordVerdict)}
    (hm : RecTwin st s t cts r tyh →
      m s = (pure (.inl { st with decls := st.decls.push (.indDecl (indBlockD st t cts r T) t.numParams) }) :
        AM (StateD ⊕ RecordVerdict)) s) :
    SpecR (Inv (σ := σ) (ctxH C0 H) s Γ [] D) (recP C0) s m
      (fun a w s' t' => DeclPost C0 F rb capD C0.H st (.indDecl (indBlockD st t cts r T) t.numParams) a w s' t' ∧
        RecTwin st s t cts r tyh) := by
  have hplat := hbuf.plat
  have hokc := ctxOK_H hok H
  have hbufc := bufOK_prefix hbuf hp0
  have hsm := hbuf.small
  unfold recP
  refine specR_scan3 hokc bufJ b hbufc fU (fIrF 3) ilRq _ qR.toNat _ (hD fU (by simp [recMods])) (cc.recF 3 (by decide))
    hBA hBN hRq
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 3 (by decide) _ eR hsR)
    (fun w3 hw3 => ?_)
  simp only [IndRecField] at hw3; subst hw3
  refine specR_scan3 hokc bufJ b hbufc fW3 (fIrF 9) ilRq _ qR.toNat _ (hD fW3 (by simp [recMods])) (cc.recF 9 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg; exact hRq)
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 9 (by decide) _ eR hsR)
    (fun w9 hw9 => ?_)
  simp only [IndRecField] at hw9; subst hw9
  refine specR_scan3 hokc bufJ b hbufc fV2 (fIrF 2) ilRq _ qR.toNat _ (hD fV2 (by simp [recMods])) (cc.recF 2 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg; exact hRq)
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 2 (by decide) _ eR hsR)
    (fun w2 hw2 => ?_)
  simp only [IndRecField] at hw2
  refine cvP_spec (ctxH C0 H) hokc cc.nc cc.cN cc.cI s _ [] D (fun x hx => hD x (by simp [recMods, hx])) st jN jE cap
    bufJ b (tblRel_prefix hreln hp0) (tblRel_prefix hrele hp0) hcap hcapN hbufc r.cv w2 hw2
    (by envg; exact hTN) (by envg; exact hTE) (by envg; exact hC) (by envg) (by envg) (by envg)
    (by envg; exact hBA) (by envg; exact hBN) _
    (fun Hc ol Γ1 rn rty n hpc hol hblk hrn hrty hlps hlpl hn hrun hden h1y h1z h1T h1K h1k => ?_)
  have g1 : ∀ y, y ∉ cvMods → y ∉ [fV2, fW3, fU] → Γ1.get y = Γ.get y := fun y hy hy' => by
    rw [h1k y hy]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    simp only [ConPanqueque.T.Env.get_cons, ite_eq_right hy'.1, ite_eq_right hy'.2.1, ite_eq_right hy'.2.2]
  have hpc' : H <+: Hc := hpc
  refine ConPanqueque.T.Ind.specR_nvcI (ctxH (ctxH C0 H) Hc) cc.cV ilX fy rn (hD ilX (by simp [recMods])) h1y
    (fun H2 wv hp2 hview => ?_)
  have hp2' : Hc <+: H2 := hp2
  have hokc2 := ctxOK_H hok H2
  have hbufc2 := bufOK_prefix hbuf (hp0.trans (hpc'.trans hp2'))
  have gg : ∀ y, y ∉ cvMods → y ∉ [ilX, fV2, fW3, fU] → Env.get ((ilX, wv) :: Γ1) y = Γ.get y := fun y hy hy' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    rw [ConPanqueque.T.Env.get_cons, ite_eq_right hy'.1]
    exact g1 y hy (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hy'.2)
  refine specR_scan3 hokc2 bufJ b hbufc2 ilA (fIrF 7) ilRq _ qR.toNat _ (hD ilA (by simp [recMods]))
    (cc.recF 7 (by decide)) ((gg _ (by decide) (by decide)).trans hBA) ((gg _ (by decide) (by decide)).trans hBN)
    ((gg _ (by decide) (by decide)).trans hRq)
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 7 (by decide) _ eR hsR)
    (fun w7 hw7 => ?_)
  simp only [IndRecField] at hw7; subst hw7
  refine specR_eqGuardI ilA ilP (Scan.natW r.numParams) (BitVec.ofNat 64 t.numParams) (by envg)
    (by envg; exact (gg _ (by decide) (by decide)).trans hP) (fun he7 => ?_)
  have hrp : r.numParams = t.numParams := natW_eq_small hnP he7
  refine specR_scan3 hokc2 bufJ b hbufc2 ilA (fIrF 6) ilRq _ qR.toNat _ (hD ilA (by simp [recMods]))
    (cc.recF 6 (by decide)) (by envg; exact (gg _ (by decide) (by decide)).trans hBA)
    (by envg; exact (gg _ (by decide) (by decide)).trans hBN) (by envg; exact (gg _ (by decide) (by decide)).trans hRq)
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 6 (by decide) _ eR hsR)
    (fun w6 hw6 => ?_)
  simp only [IndRecField] at hw6; subst hw6
  refine specR_eqcGuardI ilA (Scan.natW r.numMotives) 1 (by envg) (fun he6 => ?_)
  have hrm : r.numMotives = 1 := natW_eq_small (by unfold B55; decide) he6
  refine specR_scan3 hokc2 bufJ b hbufc2 ilA (fIrF 5) ilRq _ qR.toNat _ (hD ilA (by simp [recMods]))
    (cc.recF 5 (by decide)) (by envg; exact (gg _ (by decide) (by decide)).trans hBA)
    (by envg; exact (gg _ (by decide) (by decide)).trans hBN) (by envg; exact (gg _ (by decide) (by decide)).trans hRq)
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 5 (by decide) _ eR hsR)
    (fun w5 hw5 => ?_)
  simp only [IndRecField] at hw5; subst hw5
  refine specR_eqGuardI ilA ilNc (Scan.natW r.numMinors) (BitVec.ofNat 64 cts.length) (by envg)
    (by envg; exact (gg _ (by decide) (by decide)).trans hNc) (fun he5 => ?_)
  have hrmin : r.numMinors = cts.length := natW_eq_small hnC he5
  refine specR_scan3 hokc2 bufJ b hbufc2 ilD (fIrF 4) ilRq _ qR.toNat _ (hD ilD (by simp [recMods]))
    (cc.recF 4 (by decide)) (by envg; exact (gg _ (by decide) (by decide)).trans hBA)
    (by envg; exact (gg _ (by decide) (by decide)).trans hBN) (by envg; exact (gg _ (by decide) (by decide)).trans hRq)
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 4 (by decide) _ eR hsR)
    (fun w4 hw4 => ?_)
  simp only [IndRecField] at hw4; subst hw4
  refine specR_ltGuardI ilD (Scan.natW r.numIndices) b55W (by envg) (fun hl4 => ?_)
  obtain ⟨hni, hniw⟩ := natW_small (by rw [b55W_toNat] at hl4; exact hl4)
  rw [hniw]
  refine ConPanqueque.T.Ind.specR_pstI (ctxH (ctxH C0 H) H2) cc.cP ilX ilTy tyh B55 (by unfold B55; decide)
    (hD ilX (by simp [recMods])) (by envg; exact (gg _ (by decide) (by decide)).trans hTy)
    (fun o H3 hp3 hoK hrun3 hden3 => ?_)
  have hp3' : H2 <+: H3 := hp3
  unfold B55 at hnP hni hnC
  refine specR_assignI ilY (.op .add [.op .add [vv ilP, vv ilD], .const 1])
    (BitVec.ofNat 64 (t.numParams + r.numIndices + 1)) (hD ilY (by simp [recMods])) (by
      simp only [sev, vv]; envg; rw [(g1 _ (by decide) (by decide)).trans hP]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  have hX0 : Env.get ((ilY, BitVec.ofNat 64 (t.numParams + r.numIndices + 1)) :: (ilX, ConPanqueque.T.Ind.optW o) ::
      (ilD, BitVec.ofNat 64 r.numIndices) :: (ilA, Scan.natW r.numMinors) :: (ilA, Scan.natW r.numMotives) ::
      (ilA, Scan.natW r.numParams) :: (ilX, wv) :: Γ1) ilX = some (ConPanqueque.T.Ind.optW o) := by envg
  have hY0 : Env.get ((ilY, BitVec.ofNat 64 (t.numParams + r.numIndices + 1)) :: (ilX, ConPanqueque.T.Ind.optW o) ::
      (ilD, BitVec.ofNat 64 r.numIndices) :: (ilA, Scan.natW r.numMinors) :: (ilA, Scan.natW r.numMotives) ::
      (ilA, Scan.natW r.numParams) :: (ilX, wv) :: Γ1) ilY = some (BitVec.ofNat 64 (t.numParams + r.numIndices + 1)) := by
    envg
  refine specR_ifI _ (bw (ConPanqueque.T.Ind.optW o ≠ 0 ∧ ConPanqueque.T.Ind.optW o ≠
      BitVec.ofNat 64 (t.numParams + r.numIndices + 1))) (by
      show (do let x ← sev _ (.cmp .notEqual (vv ilX) (.const 0))
               let y ← sev _ (.cmp .notEqual (vv ilX) (vv ilY)); pure (x &&& y)) = _
      rw [sev_ne_c _ ilX _ 0 hX0, sev_ne_v _ ilX ilY _ _ hX0 hY0]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, bw_and]) (fun _ => specR_hangI) (fun hw => ?_)
  have hidx := optW_cases o B55 hoK (by unfold B55; decide) (t.numParams + r.numIndices) (by omega) (bw_eq0 hw)
  have twin : (∀ ru ∈ r.rules, RuleOK st ru) → r.rules.length < B55 →
      r.numParams + r.numMotives + r.numMinors + r.numIndices < 2 ^ 56 → RecTwin st s t cts r tyh := fun hr hnu hmi =>
    ⟨⟨rn, hrn, hview⟩, hrp, hrm, hrmin, ⟨o, hrun3, fun k hk => (hidx k hk).symm⟩, fun ru hru => ⟨(hr ru hru).ctor,
      (hr ru hru).rhs⟩, fun x hx => by obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx; rw [← e]; exact hlps j hj,
      by unfold B55; omega, hnu, fun ru hru => (hr ru hru).nf, hlpl, ⟨rty, n, hrty, hn, hden⟩, hmi⟩
  have gq : ∀ y, y ∉ cvMods → y ∉ [ilY, ilX, ilD, ilA, fV2, fW3, fU] →
      Env.get ((ilY, BitVec.ofNat 64 (t.numParams + r.numIndices + 1)) :: (ilX, ConPanqueque.T.Ind.optW o) ::
      (ilD, BitVec.ofNat 64 r.numIndices) :: (ilA, Scan.natW r.numMinors) :: (ilA, Scan.natW r.numMotives) ::
      (ilA, Scan.natW r.numParams) :: (ilX, wv) :: Γ1) y = Γ.get y := fun y hy hy' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    simp only [ConPanqueque.T.Env.get_cons, ite_eq_right hy'.1, ite_eq_right hy'.2.1, ite_eq_right hy'.2.2.1,
      ite_eq_right hy'.2.2.2.1]
    exact g1 y hy (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hy'.2.2.2.2)
  refine specR_mono (recRules_spec (α := Unit) C0 hok cc hrL s _ D hD st F rb capD jN jE cap bufJ b hreln hrele hcap hcapN hbuf
    hdr hcapD t cts r T qR eR hqR hsR hnP hnC hrp hrm hrmin hni hlpT hlpC hlpl H H3 hp0 (hpc'.trans (hp2'.trans hp3'))
    ob hob hX hob0 os hosl hos hhead rn rty hrn hrty ol hol (blkAt_mono hblk (hp2'.trans hp3'))
    ((gq _ (by decide) (by decide)).trans hBA) ((gq _ (by decide) (by decide)).trans hBN)
    ((gq _ (by decide) (by decide)).trans hTN) ((gq _ (by decide) (by decide)).trans hTE)
    ((gq _ (by decide) (by decide)).trans hC) ((gq _ (by decide) (by decide)).trans hRB)
    ((gq _ (by decide) (by decide)).trans hCD) ((gq _ (by decide) (by decide)).trans hRq)
    ((gq _ (by decide) (by decide)).trans hP) ((gq _ (by decide) (by decide)).trans hNc)
    ((gq _ (by decide) (by decide)).trans hOB) (by envg) (by envg; exact h1y) (by envg; exact h1z)
    (by envg; exact h1K) hfd (fun hr hnu hmi => hm (twin hr hnu hmi))) (fun u hu => hu)
    (fun a w s' u ⟨h1, hr, hnu, hmi⟩ => ⟨h1, twin hr hnu hmi⟩)

end ConPanqueque.Front
