import ConPanqueque.Prelude.Cap
import ConPanqueque.Prelude.OverPass
import ConPanqueque.Prelude.HoistPass
import ConPanqueque.Prelude.Final

/-! # The program after the stream's parse: the prelude, the passes, the fold

`preludeP capM`: save the stream's record count in `kNQ`; store the built-in prelude's bytes over
the input buffer; size the tables for them; parse them into the same registry (`parseP2`); the
override pass (`overP`); the hoist check (`hoistP`); the fold (`foldCallP`) over the second
registry.  `mainP3 capM := parseP (preludeP capM)`.

`main_spec3`: `mainP3` refines the twin's stream parse, prelude parse and fold, with the passes'
facts.  `front_verdict3`: when it returns, con-leche parses the input, its built-in prelude parses,
and its pure fold accepts the input prepared with it. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Start

variable {σ : Type}

def preludeP (capM : Nat) : ProgHOL 64 :=
  .seq (.assign .local kNQ (.load .one (vv kRB)))
  (preStoreP (capP capM (parseP2 (overP (hoistP foldCallP)))))

def mainP3 (capM : Nat) : ProgHOL 64 := parseP (preludeP capM)

/-- The folded records: the prelude (`decls` from `nq`), then the stream records (`decls` below
`nq`) the override pass keeps. -/
def joinedI (nq : Nat) (decls : Array IDeclaration) : Array IDeclaration :=
  (decls.toList.drop nq ++ (decls.toList.take nq).filter (keepW ((decls.toList.drop nq).map keyOf))).toArray

theorem stPre_pins {s s' : AState} (h : s'.pins = s.pins) (P : Array IDeclaration) : stPre s' P = stPre s P := by
  simp [stPre, h]

theorem kcH_agree (H : List (BitVec 64)) (r : Nat) (ws : List (BitVec 64)) (n : Nat) :
    Agree r (r + n) H (kcH H r ws n) :=
  ⟨kcH_length _ _ _ _, fun c hc => by rw [kcH_get]; rw [if_neg (by omega)]⟩

/-- The twin's run of the program after the read. -/
def twin3 (s0 : AState) (b : ByteArray) : AM IFEnv :=
  feedAll (stInit s0) b 0 0 >>= fun stQ => feedAll (stPre s0 stQ.decls) preBytes 0 0 >>= fun st2 =>
    checkDeclsPure .verified [] (joinedI stQ.decls.size st2.decls).toList

/-- What the program's return says about the twin. -/
def Post3 (s0 : AState) (b : ByteArray) : IFEnv → BitVec 64 → AState → PState σ → Prop :=
  fun a _ s3 _ => ∃ stQ s1 st2 s2, feedAll (stInit s0) b 0 0 s0 = .ok (stQ, s1) ∧
    feedAll (stPre s0 stQ.decls) preBytes 0 0 s1 = .ok (st2, s2) ∧
    OverW (st2.decls.toList.take stQ.decls.size) (st2.decls.toList.drop stQ.decls.size) ∧
    HoistW s0.pins.names (joinedI stQ.decls.size st2.decls).toList ∧
    (∀ d ∈ (joinedI stQ.decls.size st2.decls).toList, ConPanqueque.Bridge.IsFrontDecl s2.pins d) ∧
    checkDeclsPure .verified [] (joinedI stQ.decls.size st2.decls).toList s2 = .ok (a, s3)

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Start

variable {σ : Type}

/-- The locals the program after the read needs. -/
def rest3Vars : List MlS := [kZ, kR0, kN0, kR1, fCap, kZn, fTL, fTE, kBN, kNQ, kRB] ++ ovVars ++ hsVars

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem main_spec3 (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (hEB : ∀ j, ecell C j = ecb j)
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (hpp : PersPins s) (hpins : PinsDenote s.store [] []) (hA : denoteN s.store.ns default = some .anonymous)
    (hb : PinBlock C.EH s.pins)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ rest3Vars, x ∈ D)
    {F rb capD jN cap j0 capM : Nat} {b : ByteArray}
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap (j0 + 1) b) (hcap1 : 1 ≤ cap)
    (hcapN : cap ≤ ConPanqueque.Scan.natCap) (hcap8 : 8 * cap < 2 ^ 64)
    (hcapM1 : 1 ≤ capM) (hcapMr : jN + 3 * capM ≤ rb) (hcapMN : capM ≤ ConPanqueque.Scan.natCap)
    (hlayP : j0 + 4096 + 2 + capD ≤ F) (hcapD8 : 8 * (j0 + 4096 + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C (j0 + 1) b)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C (j0 + 1))) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel)) (hRA : Γ.get kRA = some (cellA C j0))
    (hal2 : (cellA C (j0 + 4096 + 1 + capD)).toNat % 8 = 0) :
    SpecR (Inv (σ := σ) C s Γ M D) (mainP3 capM) s (twin3 s b) (Post3 s b) := by
  have hsz : b.size < USize.size := by
    have := hbuf.small
    simp only [USize.size_eq_two_pow, hbuf.plat.bits]; omega
  have hD' : ∀ x, x ∈ rest3Vars → x ∈ D := hD
  have hb1 := hfl.buf
  unfold mainP3 twin3
  refine specR_atEntry fun t0 ht0 => ?_
  have hp0 : s.pins = C.pins := ht0.sr.pins
  refine parseP_spec ra C hok hf fc hcF s Γ M D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> simp [rest3Vars]))
    F rb capD jN cap (j0 + 1) b hfl hcap1 hcapN hcap8 (by omega) hFH hbuf hZb hZn hTN hTL hTE hC hBA hBN hRB hCD hZL
    (fun stQ s1 H1 Γ1 hrun1 hag1 hfs1 => ?_)
  obtain ⟨hstep1, -, rc, -, hden1⟩ := parse_twin hst hoff hpo hsz hrun1
  have hp1 : s1.pins = s.pins := hstep1.pins
  have g1 : ∀ y, y ≠ kZ → y ≠ kR0 → Γ1.get y = Γ.get y := hag1
  -- the stream's record count
  have hdr1 := hfs1.dr
  unfold preludeP
  refine specR_loadW kNQ (vv kRB) rb _ (hdr1.1 : (ctxH C H1).H[rb]? = _) (hD' _ (by simp [rest3Vars]))
    (by simp only [sev, vv]; rw [g1 _ (by decide) (by decide)]; exact hRB) ?_
  let nq := stQ.decls.size
  -- the prelude's bytes
  let Γ2 : Env := (kNQ, BitVec.ofNat 64 nq) :: Γ1
  have g2 : ∀ y, y ≠ kZ → y ≠ kR0 → y ≠ kNQ → Γ2.get y = Γ.get y := by
    intro y h1 h2 h3; simp only [Γ2, T.Env.get_cons, h3, ite_false]; exact g1 y h1 h2
  have hBA2 : Γ2.get kBA = some (cellA (ctxH C H1) (j0 + 1)) := by
    rw [g2 _ (by decide) (by decide) (by decide)]; exact hBA
  have hFH1 : F ≤ H1.length := hdr1.2.2.2.1
  have hrb1 : rb + 1 + capD ≤ j0 + 1 := hfl.buf
  refine preStore_spec (C := ctxH C H1) (ctxOK_ctxH hok) (hD' _ (by simp [rest3Vars])) (j0 + 1) hBA2 hbuf.al
    (by show j0 + 1 + 1963 < H1.length; omega) (by omega) hbuf.plat.bits (fun H2 hl2 ha2 hbufP => ?_)
  have hA2 : Agree (j0 + 1) (j0 + 1 + 1963) H1 H2 := ⟨hl2, ha2⟩
  have hH2 : H2.length = H1.length := hA2.1
  let Γ3 : Env := (kBN, BitVec.ofNat 64 preSize) :: Γ2
  have g3 : ∀ y, y ≠ kZ → y ≠ kR0 → y ≠ kNQ → y ≠ kBN → Γ3.get y = Γ.get y := by
    intro y h1 h2 h3 h4; simp only [Γ3, T.Env.get_cons, h4, ite_false]; exact g2 y h1 h2 h3
  -- the tables for the prelude
  refine capP_spec (C := ctxH (ctxH C H1) H2) (fun x hx => hD' x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [rest3Vars])) capM preSize jN (by decide) hcapM1
    (by have := hcapD8; omega) (by simp (config := {decide := true}) [Γ3, T.Env.get_cons])
    (by rw [g3 _ (by decide) (by decide) (by decide) (by decide)]; exact hTN) (fun Γ4 hag4 hC4 hZn4 hTL4 hTE4 => ?_)
  let cap' := capOf capM preSize
  have hcap'1 : 1 ≤ cap' := by simp only [cap', capOf]; split <;> omega
  have hcap'M : cap' ≤ capM := by simp only [cap', capOf]; split <;> omega
  have g4 : ∀ y, y ≠ kZ → y ≠ kR0 → y ≠ kNQ → y ≠ kBN → y ∉ [fCap, kZn, fTL, fTE] → Γ4.get y = Γ.get y :=
    fun y h1 h2 h3 h4 h5 => (hag4 y h5).trans (g3 y h1 h2 h3 h4)
  have hbs := preBytes_size
  have hflP : FrontLay F rb capD jN (jN + cap') (jN + 2 * cap') cap' (j0 + 1) preBytes :=
    ⟨by omega, by omega, by omega, hrb1, by rw [hbs]; simp [preSize]; omega⟩
  have hdrP : DeclsRel (ctxH (ctxH C H1) H2) F rb capD (ctxH (ctxH C H1) H2).H stQ.decls :=
    declsRel_agree hdr1 hA2 hrb1 (by omega)
  have ePre : stPre s1 stQ.decls = stPre s stQ.decls := stPre_pins hp1 _
  rw [← ePre]
  refine parseP2_spec ra (ctxH (ctxH C H1) H2) (ctxOK_ctxH (ctxOK_ctxH hok)) (frontOK_ctxH (frontOK_ctxH hf))
    (frontCodes_ctxH (frontCodes_ctxH fc)) hcF s1 Γ4 [] D (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> simp [rest3Vars]))
    F rb capD jN cap' (j0 + 1) preBytes hflP hcap'1 (by omega) (by omega) (by omega) (by show F ≤ H2.length; omega)
    hbufP stQ.decls hdrP
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hZb) hZn4
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTN) hTL4 hTE4 hC4
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [hag4 _ (by decide), hbs]; simp (config := {decide := true}) [Γ3, T.Env.get_cons])
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hCD)
    (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide), hp1]; exact hZL)
    (fun st2 s2 H3 Γ5 hrun2 hag5 hfs2 => ?_)
  -- the prelude's parse, on the twin
  rw [ePre] at hrun2
  obtain ⟨stP, hrunP, est2⟩ := feedAll_withPre stQ.decls preBytes _ 0 (stInit s1) 0 s1 s2 st2 rfl
    (by rw [← stPre_eq, stPre_pins hp1]; exact hrun2)
  have hsz2 : st2.decls.size = nq + stP.decls.size := by rw [est2]; simp [withPre, stInit, nq]
  have g5 : ∀ y, y ≠ kZ → y ≠ kR0 → y ≠ kNQ → y ≠ kBN → y ∉ [fCap, kZn, fTL, fTE] → Γ5.get y = Γ.get y :=
    fun y h1 h2 h3 h4 h5 => (hag5 y h1 h2).trans (g4 y h1 h2 h3 h4 h5)
  have hNQ5 : Γ5.get kNQ = some (BitVec.ofNat 64 nq) := by
    rw [hag5 _ (by decide) (by decide), hag4 _ (by decide)]; simp (config := {decide := true}) [Γ3, Γ2, T.Env.get_cons]
  let C3 := ctxH (ctxH (ctxH C H1) H2) H3
  have hC3 : C3 = ctxH C H3 := rfl
  -- the override pass
  refine overP_spec (C := C3) (ctxOK_ctxH (ctxOK_ctxH (ctxOK_ctxH hok)))
    (fun x hx => hD' x (by simp [rest3Vars, hx])) (hD' _ (by simp [rest3Vars])) (j0 := j0) (nq := nq)
    hfs2.dr (by omega) (by omega) (by omega) hcapD8
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRB) hNQ5
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRA)
    (fun H4 Γ6 hA4 hag6 hRB6 hOW hdr4 => ?_)
  -- the hoist check
  have hEB4 : ∀ j, ecell (ctxH C3 H4) j = ecb j := fun j => hEB j
  have hb4 : PinBlock (ctxH C3 H4).EH s.pins := hb
  refine hoistP_spec (C := ctxH C3 H4) (fun x hx => hD' x (by simp [rest3Vars, hx])) hdr4 hcapD8 hRB6 hEB4 hb4
    hpo.ready (fun Γ7 hag7 hHW => ?_)
  -- the fold, over the second registry
  let L := joinedI nq st2.decls
  obtain ⟨hstep2, -, rP, -, hdenP⟩ := parse_twin hstep1.ok (by rw [hstep1.scratch]; exact hoff)
    (hpo.mono hstep1.ext hstep1.pins) (by rw [hbs]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size) hrunP
  have hp2 : s2.pins = s.pins := hstep2.pins.trans hp1
  have hst12 := hstep1.trans hstep2
  have hpo2 : PinsOK s2 := hpo.mono hst12.ext hp2
  have hpp2 : PersPins s2 := hpp.mono hp2
  have hpins2 : PinsDenote s2.store [] [] := PinsDenote.mono hst12.ext _ _ hpins
  have hwf2 : StoreWF s2.store := hstep2.ok.wf
  have hdecls2 : st2.decls = stQ.decls ++ stP.decls := by rw [est2]; try simp [withPre, stInit]
  have htake : st2.decls.toList.take nq = stQ.decls.toList := by rw [hdecls2]; simp [nq]
  have hdrop : st2.decls.toList.drop nq = stP.decls.toList := by rw [hdecls2]; simp [nq]
  have hOW' : OverW stQ.decls.toList stP.decls.toList := by rw [← htake, ← hdrop]; exact hOW
  have hQ2 : denoteDecls s2.store stQ.decls.toList = some rc.decls.toList := ConRon.Bridge.Frontend.denoteDecls_ext hstep2.ext _ _ hden1
  have hLd : denoteDecls s2.store L.toList =
      some (rP.decls.toList ++ rc.decls.toList.filter (keep rP.decls.toList)) := by
    show denoteDecls s2.store (st2.decls.toList.drop nq ++ (st2.decls.toList.take nq).filter
      (keepW ((st2.decls.toList.drop nq).map keyOf))) = _
    rw [htake, hdrop]
    exact ConRon.Bridge.Frontend.denoteDecls_append hdenP (denoteDecls_keep hwf2 hQ2 hdenP hOW')
  have hd : ∀ k (hk : k < L.size), (denoteDecl s2.store L[k]).isSome :=
    fun k hk => denoteDecls_isSome hLd _ (by simp)
  have hlen : L.size < 2 ^ 62 := by
    have h1 : L.size ≤ capD := hdr4.2.1
    have := hcapD8; omega
  let st3 : StateD := { st2 with decls := L }
  have hA4' : ∀ c, c < j0 + 4096 → H4[c]? = H3[c]? := fun c hc => hA4.2 c (Or.inl hc)
  have htbl : ∀ {k : IdxKind} {j : Nat} {tbl : ConLeche.Frontend.IdTable (Idx k)}, TblRel H3 j cap' tbl →
      j + cap' ≤ j0 + 4096 → TblRel H4 j cap' tbl :=
    fun h hj => ⟨fun i hi => by rw [hA4' _ (by omega)]; exact h.1 i hi, h.2⟩
  have hfs3 : FrontSt (ctxH C3 H4) F (j0 + 4096) capD jN (jN + cap') (jN + 2 * cap') cap' (j0 + 4096 + 1 + capD)
      ByteArray.empty (ctxH C3 H4).H st3 := by
    refine ⟨⟨⟨by omega, by omega, by omega, Nat.le_refl _, by simp; omega⟩, by omega, by omega, by omega, by omega,
      by omega⟩, htbl hfs2.tN (by omega), htbl hfs2.tL (by omega), htbl hfs2.tE (by omega), hdr4, ?_⟩
    refine ⟨fun i hi => absurd hi (by simp), hal2, ?_, ⟨hbuf.plat.bits, by simp, by simp⟩, by simp⟩
    show j0 + 4096 + 1 + capD + 0 / 8 < H4.length
    have hF4 : F ≤ H4.length := by rw [hA4.1]; exact hfs2.dr.2.2.2.1
    have e0 : ByteArray.empty.size = 0 := rfl
    exact Nat.lt_of_lt_of_le (by omega) hF4
  have hval : ∀ d ∈ L.toList, ConPanqueque.Bridge.IsFrontDecl s2.pins d := by
    rw [hp2, hp0]; exact declsRel_value hdr4
  have hokC : CtxOK (ctxH C3 H4) := ctxOK_ctxH (ctxOK_ctxH (ctxOK_ctxH (ctxOK_ctxH hok)))
  have hcC : FoldCodes .verified (ctxH C3 H4) :=
    foldCodes_ctxH (foldCodes_ctxH (foldCodes_ctxH (foldCodes_ctxH hc H1) H2) H3) H4
  have hfC : FrontOK (ctxH C3 H4) := frontOK_ctxH (frontOK_ctxH (frontOK_ctxH (frontOK_ctxH hf)))
  have hsC : (ctxH C3 H4).side = false := hs
  have hplC : (ctxH C3 H4).saved = none := hpl
  have hfeC : (ctxH C3 H4).fe = feStart (ctxH C3 H4).pins := hfe
  have hA2' : denoteN s2.store.ns default = some .anonymous := ConRon.Bridge.denoteN_ext hA hst12.ext
  have hDC : ∀ x ∈ [kN0, kR1], x ∈ D := fun x hx => hD' x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> simp [rest3Vars])
  have hRB7 : Γ7.get kRB = some (cellA (ctxH C3 H4) (j0 + 4096)) := by rw [hag7 _ (by decide)]; exact hRB6
  have hFC := foldCall_spec (σ := σ) [] ra (ctxH C3 H4) hokC hcC hfC hsC hplC hfeC s2 hA2' Γ7 D hDC
    st3 hfs3 hd hlen hRB7 hpo2 hpp2 [] hpins2
  refine specR_mono (specR_run hFC) (fun t ht => ht)
    (fun a w s3 t ⟨hm, _⟩ => ⟨stQ, s1, st2, s2, hrun1, hrun2, hOW, hHW, hval, hm⟩)

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Start

variable {σ : Type}

/-- The verdict the program's return carries: con-leche parses the input, its built-in prelude
parses, and its pure fold accepts the input prepared with that prelude. -/
def Verdict3 (b : ByteArray) : Prop :=
  ∃ rc, ConLeche.Frontend.parseBytes b = .ok rc ∧ ∃ pre, ConLeche.Frontend.builtinPreludeE = .ok pre ∧
    ∃ E, ConLeche.PureRun [] (ConLeche.Frontend.preparePrelude pre rc.decls).toList ConLeche.Env.empty E

/-- **From the twin's run to con-leche's verdict.** -/
theorem post3_verdict {s : AState} (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (hpp : PersPins s) (hpins : PinsDenote s.store [] []) {b : ByteArray} (hsz : b.size < USize.size)
    {a : IFEnv} {w : BitVec 64} {s3 : AState} {t : PState σ} (h : Post3 s b a w s3 t) : Verdict3 b := by
  obtain ⟨stQ, s1, st2, s2, hrun1, hrun2, hOW, hHW, hval, hm⟩ := h
  obtain ⟨hstep1, -, rc, hrc, hden1⟩ := parse_twin hst hoff hpo hsz hrun1
  have hp1 : s1.pins = s.pins := hstep1.pins
  obtain ⟨stP, hrunP, est2⟩ := feedAll_withPre stQ.decls preBytes _ 0 (stInit s1) 0 s1 s2 st2 rfl
    (by rw [← stPre_eq, stPre_pins hp1]; exact hrun2)
  have hbs := preBytes_size
  obtain ⟨hstep2, -, rP, hrP, hdenP⟩ := parse_twin hstep1.ok (by rw [hstep1.scratch]; exact hoff)
    (hpo.mono hstep1.ext hstep1.pins) (by rw [hbs]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size) hrunP
  have hp2 : s2.pins = s.pins := hstep2.pins.trans hp1
  have hst12 := hstep1.trans hstep2
  have hpo2 : PinsOK s2 := hpo.mono hst12.ext hp2
  have hwf2 : StoreWF s2.store := hstep2.ok.wf
  let nq := stQ.decls.size
  have hdecls2 : st2.decls = stQ.decls ++ stP.decls := by rw [est2]; try simp [withPre, stInit]
  have htake : st2.decls.toList.take nq = stQ.decls.toList := by rw [hdecls2]; simp [nq]
  have hdrop : st2.decls.toList.drop nq = stP.decls.toList := by rw [hdecls2]; simp [nq]
  have hOW' : OverW stQ.decls.toList stP.decls.toList := by rw [← htake, ← hdrop]; exact hOW
  have hQ2 : denoteDecls s2.store stQ.decls.toList = some rc.decls.toList := ConRon.Bridge.Frontend.denoteDecls_ext hstep2.ext _ _ hden1
  have eL : (joinedI nq st2.decls).toList =
      stP.decls.toList ++ stQ.decls.toList.filter (keepW (stP.decls.toList.map keyOf)) := by
    simp only [joinedI, List.toList_toArray]; rw [htake, hdrop]
  have hLd : denoteDecls s2.store (stP.decls.toList ++ stQ.decls.toList.filter (keepW (stP.decls.toList.map keyOf))) =
      some (rP.decls.toList ++ rc.decls.toList.filter (keep rP.decls.toList)) :=
    ConRon.Bridge.Frontend.denoteDecls_append hdenP (denoteDecls_keep hwf2 hQ2 hdenP hOW')
  rw [eL] at hHW hval hm
  have hacc := ConPanqueque.Bridge.seq_bridge' hstep2.ok hpo2 (hpp.mono hp2) (PinsDenote.mono hst12.ext _ _ hpins) hLd
    (fun pd h => ConPanqueque.Bridge.isChecked_of_front hpo2 (hval pd h)) hm
  refine ⟨rc, hrc, final_verdict hwf2 (by rw [← hp2]; exact hpo2.names) hrP hQ2 hdenP hOW' hHW hLd hacc⟩

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Start

variable {σ : Type}

/-- The program after the read: the length guard, the stream's tables, then `mainP3`. -/
def restP3 (capM : Nat) : ProgHOL 64 :=
  .seq (.assign .local kBN (.load .one (vv kRA)))
    (.ite (.cmp .lower (vv kBN) (vv kRM))
      (.seq (.assign .local kBA (.op .add [vv kRA, .const 8])) (capP capM (mainP3 capM))) hang)

/-- **The program after the read**, against the twin's run on the input the read's bytes carry. -/
theorem rest_spec3 (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (hEB : ∀ j, ecell C j = ecb j)
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (hpp : PersPins s) (hpins : PinsDenote s.store [] []) (hA : denoteN s.store.ns default = some .anonymous)
    (hb : PinBlock C.EH s.pins)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ rest3Vars ++ [kBA], x ∈ D)
    (rb capD jN capM j0 Lw : Nat)
    (hcapM1 : 1 ≤ capM) (hcapMr : jN + 3 * capM ≤ rb) (hcapMN : capM ≤ ConPanqueque.Scan.natCap)
    (hbuf0 : rb + 1 + capD ≤ j0 + 1) (hLw : 4096 + 2 + capD ≤ Lw) (hcells : j0 + Lw ≤ C.H.length)
    (hL16 : 16 ≤ 8 * Lw) (h59 : 8 * Lw < 2 ^ 59)
    (hal : (cellA C j0).toNat % 8 = 0) (hov : (cellA C j0).toNat + 8 * Lw + 8 < 2 ^ 64)
    (hbits : System.Platform.numBits = 64) (hcapD8 : 8 * (j0 + 4096 + 1 + capD) < 2 ^ 64)
    (hal2 : (cellA C (j0 + 4096 + 1 + capD)).toNat % 8 = 0)
    (hZb : Γ.get kZb = some (cellA C jN)) (hTN : Γ.get fTN = some (cellA C jN))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (hRA : Γ.get kRA = some (cellA C j0)) (hRM : Γ.get kRM = some (BitVec.ofNat 64 (8 * Lw - 16)))
    (nb : List (BitVec 8)) (hl : nb.length = 8 * Lw) (Hb : List (BitVec 64)) (hHb : Hb.length = C.H.length)
    (hH : C.H = writeH Hb (cellA C j0) j0 0 nb) :
    SpecR (Inv (σ := σ) C s Γ M D) (restP3 capM) s (twin3 s (inputOf nb (leNat (nb.take 8))))
      (Post3 s (inputOf nb (leNat (nb.take 8)))) := by
  have hD' : ∀ x, x ∈ rest3Vars ++ [kBA] → x ∈ D := hD
  have hj0 : j0 < C.H.length := by omega
  unfold restP3
  refine specR_heapLoadI kBN (vv kRA) j0 hj0 (hD' _ (by simp [rest3Vars])) (by simpa [sev, vv] using hRA) ?_
  let w := C.H[j0]
  have hwv : w.toNat = leNat (nb.take 8) := by
    have := header_value Hb (cellA C j0) j0 hal nb (by omega) (by rw [hHb]; omega) (by omega)
    rw [← hH, List.getElem?_eq_getElem hj0, Option.getD_some] at this; exact this
  have hw : w = BitVec.ofNat 64 w.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine specR_ifI _ _ (sev_lower _ (vv kBN) (vv kRM) w.toNat (8 * Lw - 16)
    (by simp (config := {decide := true}) only [sev, vv, T.Env.get_cons, ite_true]; exact congrArg some hw)
    (by simp only [sev, vv]; rw [get_cons_ne _ _ _ _ (by decide)]; exact hRM) w.isLt (by omega))
    (fun h1 => ?_) (fun _ => specR_hangI)
  have hgd : w.toNat < 8 * Lw - 16 := bw_ne0' h1
  refine specR_assignI kBA (.op .add [vv kRA, .const 8]) (cellA C (j0 + 1)) (hD' _ (by simp)) (by
      simp only [sev, vv]; rw [get_cons_ne _ _ _ _ (by decide), hRA]
      rw [show cellA C (j0 + 1) = cellA C j0 + BitVec.ofNat 64 (8 * 1) from cellA_add C j0 1]; rfl) ?_
  let n := w.toNat
  let b := inputOf nb n
  have hbsz : b.size = n := inputOf_size nb _ (by omega)
  have hbuf : BufOK C (j0 + 1) b := by
    have := bufOK_of_read (ctxH C Hb) j0 Lw hal (by show j0 + Lw ≤ Hb.length; omega)
      (by simp only [cellA_ctxH]; omega) h59 hbits nb hl n
      (by omega)
    rw [show ctxH (ctxH C Hb) (writeH (ctxH C Hb).H (cellA (ctxH C Hb) j0) j0 0 nb) = C from by
      rw [ctxH_ctxH]; show ctxH C (writeH Hb (cellA C j0) j0 0 nb) = C; rw [← hH, ctxH_self]] at this
    exact this
  refine capP_spec (C := C) (fun x hx => hD' x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [rest3Vars]))
    capM n jN (by omega) hcapM1 (by have := hcapD8; omega)
    (by rw [get_cons_ne _ _ _ _ (by decide)]; simp (config := {decide := true}) [T.Env.get_cons]; exact hw)
    (by rw [get_cons_ne _ _ _ _ (by decide), get_cons_ne _ _ _ _ (by decide)]; exact hTN)
    (fun Γ4 hag4 hC4 hZn4 hTL4 hTE4 => ?_)
  let cap := capOf capM n
  have hcap1 : 1 ≤ cap := by simp only [cap, capOf]; split <;> omega
  have hcapM : cap ≤ capM := by simp only [cap, capOf]; split <;> omega
  have g4 : ∀ y, y ∉ [fCap, kZn, fTL, fTE] → y ≠ kBA → y ≠ kBN → Γ4.get y = Γ.get y := by
    intro y h1 h2 h3; rw [hag4 y h1]; simp (config := {decide := true}) [T.Env.get_cons, h2, h3]
  rw [show leNat (nb.take 8) = n from hwv.symm]
  exact main_spec3 ra C hok hf fc hc hs hpl hfe hcF hEB s hst hoff hpo hpp hpins hA hb Γ4 M D
    (fun x hx => hD' x (List.mem_append_left _ hx))
    (F := j0 + Lw) (cap := cap) (j0 := j0) (capM := capM) ⟨by omega, by omega, by omega, hbuf0, by rw [hbsz]; omega⟩ hcap1
    (by omega) (by omega) hcapM1 hcapMr hcapMN (by omega) hcapD8 (by omega) hbuf
    (by rw [g4 _ (by decide) (by decide) (by decide)]; exact hZb) hZn4
    (by rw [g4 _ (by decide) (by decide) (by decide)]; exact hTN) hTL4 hTE4 hC4
    (by rw [hag4 _ (by decide)]; simp (config := {decide := true}) [T.Env.get_cons])
    (by rw [hag4 _ (by decide), hbsz]; simp (config := {decide := true}) [T.Env.get_cons]; exact hw)
    (by rw [g4 _ (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g4 _ (by decide) (by decide) (by decide)]; exact hCD)
    (by rw [g4 _ (by decide) (by decide) (by decide)]; exact hZL)
    (by rw [g4 _ (by decide) (by decide) (by decide)]; exact hRA) hal2

end ConPanqueque.Prelude
