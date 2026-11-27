import ConPanqueque.Front.FoldCall

/-! # The whole program: parse, then fold; and its verdict

`mainP`: `parseP foldCallP`.  `main_spec`: it refines the twin's parse-then-fold.  `front_verdict`:
**when the program returns, con-leche parses the input and its pure checker accepts the parsed
declarations** — the acceptance half of "the same verdict", from a pinned starting state. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.T.Decl

variable {σ : Type}

def mainP : ProgHOL 64 := parseP foldCallP

theorem declsRel_value {C : Ctx} {F rb capD : Nat} {H : List (BitVec 64)} {ds : Array IDeclaration}
    (h : DeclsRel C F rb capD H ds) : ∀ d ∈ ds.toList, ConPanqueque.Bridge.IsFrontDecl C.pins d := by
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨o, -, hr⟩ := h.2.2.2.2 k (by simpa using hk)
  simp only [Array.getElem_toList] at hr ⊢
  cases hx : ds[k] <;> rw [hx] at hr <;> first | trivial | exact hr.elim | exact hr.2.2.2.2 | exact hr.1

set_option maxRecDepth 8000 in
theorem foldCodes_ctxH {mode : ConLeche.CheckMode} {C : Ctx} (hc : FoldCodes mode C) (H : List (BitVec 64)) :
    FoldCodes mode (ctxH C H) := by ctx_tr hc

section
variable {F rb capD jN cap bufJ : Nat} {b : ByteArray}

/-- What the whole program's return says about the twin. -/
def MainPost (s : AState) (b : ByteArray) (pins : List INatOpPinSet) :
    IFEnv → BitVec 64 → AState → PState σ → Prop :=
  fun a _ s'' _ => ∃ st' s', feedAll (stInit s) b 0 0 s = .ok (st', s') ∧
    (∀ d ∈ st'.decls.toList, ConPanqueque.Bridge.IsFrontDecl s'.pins d) ∧
    checkDeclsPure .verified pins st'.decls.toList s' = .ok (a, s'')

theorem main_spec (pins : List INatOpPinSet) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (hA : denoteN s.store.ns default = some .anonymous)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0, kN0, kR1], x ∈ D)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ ConPanqueque.Scan.natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel)) :
    SpecR (Inv (σ := σ) C s Γ M D) mainP s (feedAll (stInit s) b 0 0 >>= fun st' => checkDeclsPure .verified pins st'.decls.toList)
      (MainPost s b pins) := by
  have hsz : b.size < USize.size := by
    have := hbuf.small
    simp only [USize.size_eq_two_pow, hbuf.plat.bits]; omega
  unfold mainP
  refine specR_atEntry fun t0 ht0 => ?_
  have hp0 : s.pins = C.pins := ht0.sr.pins
  refine parseP_spec ra C hok hf fc hcF s Γ M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl <;> simp)) F rb capD jN cap bufJ b hfl hcap1 hcapN
    hcap8 hcapD8 hFH hbuf hZb hZn hTN hTL hTE hC hBA hBN hRB hCD hZL (fun st' s' H' Γ'' hrun hag hfs => ?_)
  obtain ⟨hstep, -, rc, -, hden⟩ := parse_twin hst hoff hpo hsz hrun
  have hval : ∀ d ∈ st'.decls.toList, ConPanqueque.Bridge.IsFrontDecl s'.pins d := by
    rw [hstep.pins, hp0]; exact declsRel_value hfs.dr
  have hd : ∀ k (hk : k < st'.decls.size), (denoteDecl s'.store st'.decls[k]).isSome :=
    fun k hk => denoteDecls_isSome hden _ (by simp)
  have hlen : st'.decls.size < 2 ^ 62 := by have := hfs.dr.2.1; omega
  refine specR_mono (specR_run (foldCall_spec pins ra (ctxH C H') (ctxOK_ctxH hok) (foldCodes_ctxH hc H') (by ctx_tr hf)
    hs hpl hfe s' (ConRon.Bridge.denoteN_ext hA hstep.ext) Γ'' D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl <;> simp)) st'
    (frontSt_ctxH H' hfs) hd hlen (by rw [hag _ (by decide) (by decide)]; exact hRB))) (fun t ht => ht)
    (fun a w s'' t ⟨hm, _⟩ => ⟨st', s', hrun, hval, hm⟩)

/-- **The verdict**: when the program returns, con-leche's parse of the input succeeds and its
pure checker accepts the declarations. -/
theorem front_verdict (pins : List INatOpPinSet) (pinsP : List ConLeche.NatOpPinSet)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s) (hpp : PersPins s)
    (hpins : PinsDenote s.store pins pinsP) (hA : denoteN s.store.ns default = some .anonymous)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0, kN0, kR1], x ∈ D)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ ConPanqueque.Scan.natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (t : PState σ) (ht : Inv C s Γ M D t) :
    Stop (evaluateHOLFiniteState t mainP).1 ∨
      ((∃ w, (evaluateHOLFiniteState t mainP).1 = some (.returned (.val (.word w)))) ∧
        ∃ rc, ConLeche.Frontend.parseBytes b = .ok rc ∧
          ∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') pinsP rc.decls.toList
            = .ok (ConLeche.streamEnv rc.decls.toList)) := by
  have hsz : b.size < USize.size := by
    have := hbuf.small
    simp only [USize.size_eq_two_pow, hbuf.plat.bits]; omega
  rcases main_spec pins ra C hok hf fc hc hs hpl hfe hcF s hst hoff hpo hA Γ M D hD hfl hcap1 hcapN hcap8 hcapD8 hFH
      hbuf hZb hZn hTN hTL hTE hC hBA hBN hRB hCD hZL t ht with hstop | ⟨w, hw, a, s'', -, st', s', hrun, hval, hm⟩
  · exact Or.inl hstop
  refine Or.inr ⟨⟨w, hw⟩, ?_⟩
  obtain ⟨hstep, -, rc, hrc, hden⟩ := parse_twin hst hoff hpo hsz hrun
  refine ⟨rc, hrc, ?_⟩
  exact ConPanqueque.Bridge.seq_bridge' hstep.ok (hpo.mono hstep.ext hstep.pins) (hpp.mono hstep.pins)
    (PinsDenote.mono hstep.ext _ _ hpins) hden
    (fun pd h => ConPanqueque.Bridge.isChecked_of_front (hpo.mono hstep.ext hstep.pins) (hval pd h)) hm

end

end ConPanqueque.Front
