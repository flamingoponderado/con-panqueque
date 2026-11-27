import ConPanqueque.Start.Forbid
import ConPanqueque.Front.Main

/-! # The program with the forbidden-name pass

`mainP2`: parse, the forbidden-name pass over the parsed registry, then the fold.  `main_spec2` and
`front_verdict2`: `main_spec`/`front_verdict` with the pass's conclusion added — no parsed record's
name word is one of the given environment cells' words. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front ConPanqueque.T ConPanqueque.T.Decl

variable {σ : Type}

/-- The cells the pass compares against: the 52 pinned names, the 16 reserved names, `Bool.rec`. -/
def cellsF : List Nat := (List.range 52).map (64 + ·) ++ (List.range 16).map (122 + ·) ++ [138]

def mainP2 : ProgHOL 64 := parseP (forbidP cellsF foldCallP)

section
variable {F rb capD jN cap bufJ : Nat} {b : ByteArray}

def MainPost2 (s : AState) (b : ByteArray) (pins : List INatOpPinSet) (EH : List (BitVec 64)) :
    IFEnv → BitVec 64 → AState → PState σ → Prop :=
  fun a _ s'' _ => ∃ st' s', feedAll (stInit s) b 0 0 s = .ok (st', s') ∧
    (∀ d ∈ st'.decls.toList, ConPanqueque.Bridge.IsFrontDecl s'.pins d) ∧
    checkDeclsPure .verified pins st'.decls.toList s' = .ok (a, s'') ∧
    ∀ k (hk : k < st'.decls.size), ∀ j ∈ cellsF, EH[j]? ≠ some (recNameW st'.decls[k])

theorem main_spec2 (pins : List INatOpPinSet) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (hEB : ∀ j, ecell C j = ecb j) (hcells : ∀ j ∈ cellsF, ∃ w, C.EH[j]? = some w)
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0, kN0, kR1], x ∈ D) (hDF : ∀ x ∈ forbidVars, x ∈ D)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ ConPanqueque.Scan.natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel)) :
    SpecR (Inv (σ := σ) C s Γ M D) mainP2 s (feedAll (stInit s) b 0 0 >>= fun st' => checkDeclsPure .verified pins st'.decls.toList)
      (MainPost2 s b pins C.EH) := by
  have hsz : b.size < USize.size := by
    have := hbuf.small
    simp only [USize.size_eq_two_pow, hbuf.plat.bits]; omega
  unfold mainP2
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
  have hRB'' : Γ''.get kRB = some (cellA (ctxH C H') rb) := by rw [hag _ (by decide) (by decide)]; exact hRB
  refine forbid_spec (C := ctxH C H') hEB hDF hfs.dr hcapD8 hRB'' cellsF hcells (fun Γ' hag' hforb => ?_)
  refine specR_mono (specR_run (foldCall_spec pins ra (ctxH C H') (ctxOK_ctxH hok) (foldCodes_ctxH hc H') hs hpl hfe
    s' Γ' D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl <;> simp)) st'
    (frontSt_ctxH H' hfs) hd hlen (by rw [hag' _ (by decide)]; exact hRB''))) (fun t ht => ht)
    (fun a w s'' t ⟨hm, _⟩ => ⟨st', s', hrun, hval, hm, hforb⟩)

end

end ConPanqueque.Start
