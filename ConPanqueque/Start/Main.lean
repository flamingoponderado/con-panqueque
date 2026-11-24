import ConPanqueque.Start.PinPhase
import ConPanqueque.Start.Rest
import ConPanqueque.Code.Top

/-! # The whole program from the harness's start

`mainBody`: declare the locals, store the initial image, read the input, run the pin phase, set
the frontend's locals, then parse and check (`restP`).  `main_verdict`: from a harness start (a
zeroed region, the globals as declared, little-endian), if the program returns, its trace records
the read of bytes `nb`, con-leche parses the input they carry, and con-leche's checker accepts the
declarations. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Code ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front ConPanqueque.Scan

variable {σ : Type}

set_option maxRecDepth 100000

/-- The concrete code table, at the concrete layout. -/
noncomputable def Cg : Ctx := C1 (codeMap []) [] [] P0
noncomputable def codeT : Code := codeMap (codeEntries Cg)

theorem codeEntries_C1 (H EH : List (BitVec 64)) (P : Pins) : codeEntries (C1 codeT H EH P) = codeEntries Cg := rfl

theorem code_C1 (H EH : List (BitVec 64)) (P : Pins) :
    (C1 codeT H EH P).code = codeMap (codeEntries (C1 codeT H EH P)) := by rw [codeEntries_C1]; rfl

theorem pinCodes_T : PinCodes codeT := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [codeT, codeMap_lookup]; rfl)

/-- Declare each local (initially 0). -/
def decsZ : List MlS → ProgHOL 64 → ProgHOL 64
  | [], body => body
  | x :: xs, body => .dec x .one (.const 0) (decsZ xs body)

theorem decsZ_eval (body : ProgHOL 64) : ∀ (xs : List MlS) (t : PanSemStateFiniteExact 64 σ),
    ∃ (t' : PanSemStateFiniteExact 64 σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      t'.memory = t.memory ∧ t'.memaddrs = t.memaddrs ∧ t'.globals = t.globals ∧ t'.code = t.code ∧
      t'.be = t.be ∧ (∀ x ∈ xs, ∃ w, t'.locals.lookup x = some (.val (.word w))) ∧
      (∀ y, y ∉ xs → t'.locals.lookup y = t.locals.lookup y) ∧
      evaluateHOLFiniteState t (decsZ xs body) =
        ((evaluateHOLFiniteState t' body).1, { (evaluateHOLFiniteState t' body).2 with locals := L })
  | [], t => ⟨t, (evaluateHOLFiniteState t body).2.locals, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by simp),
      fun _ _ => rfl, by simp [decsZ]⟩
  | x :: xs, t => by
    obtain ⟨L1, e1⟩ := dec_word' t x (.const 0) 0 (decsZ xs body) (by simp [evalHOLExact])
    obtain ⟨t', L, h1, h2, h3, h4, h5, h6, h7, e⟩ := decsZ_eval body xs (setVarHOLFinite x (.val (.word 0)) t)
    refine ⟨t', L1, h1, h2, h3, h4, h5, fun y hy => ?_, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · by_cases hyx : y ∈ xs
        · exact h6 y hyx
        · exact ⟨0, by rw [h7 y hyx, lookup_setVar_same]⟩
      · exact h6 y hy
    · simp only [List.mem_cons, not_or] at hy
      rw [h7 y hy.2, lookup_setVar_other _ _ hy.1]
    · simp only [decsZ]; rw [e1, e]

def mainLocals : List MlS :=
  [kZ, kR0, kN0, kR1, kBN, kBA, kZb, kZn, fTN, fTL, fTE, fCap, kRB, kCapD, kZL, kRA, kRL, kRM, vPn, vKa, vPb, vRs]

/-- An empty code map (the program text depends on a context only through its layout). -/
def emptyCode : Code := ⟨fun _ => none, ⟨[], fun _ h => absurd rfl h⟩⟩

/-- The context the program text is generated at. -/
def Cprog : Ctx := Cb emptyCode [] EH0

/-- A value-heap cell's address. -/
def cA (j : Nat) : BitVec 64 := BitVec.ofNat 64 (base + H0) + BitVec.ofNat 64 (8 * j)

theorem cellA_C1 (code : Code) (H EH : List (BitVec 64)) (P : Pins) (j : Nat) : cellA (C1 code H EH P) j = cA j := rfl
theorem cellA_Cb (code : Code) (H EH : List (BitVec 64)) (j : Nat) : cellA (Cb code H EH) j = cA j := rfl

/-- The frontend's locals: its three tables, the registry, the zero level, the length bound. -/
def frontAssigns (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local kZb (.const (cA 0)))
  (.seq (.assign .local kZn (.const (BitVec.ofNat 64 (3 * capF))))
  (.seq (.assign .local fTN (.const (cA 0)))
  (.seq (.assign .local fTL (.const (cA capF)))
  (.seq (.assign .local fTE (.const (cA (2 * capF))))
  (.seq (.assign .local fCap (.const (BitVec.ofNat 64 capF)))
  (.seq (.assign .local kRB (.const (cA rbF)))
  (.seq (.assign .local kCapD (.const (BitVec.ofNat 64 capD)))
  (.seq (.assign .local kZL (.const 0))
  (.seq (.assign .local kRM (.const (BitVec.ofNat 64 (8 * Lw - 16))))
    rest)))))))))

/-- The body after the declarations. -/
def mainCore : ProgHOL 64 :=
  .seq (storesP initL)
  (.seq (.assign .local kRA (.const (cA j0F)))
  (.seq (.assign .local kRL (.const (BitVec.ofNat 64 (8 * Lw))))
  (.seq (.extCall fRead (.const 0) (.const 0) (vv kRA) (vv kRL))
    (pinsP Cprog (frontAssigns restP)))))

def mainBody : ProgHOL 64 := decsZ mainLocals mainCore

theorem pinsP_Cb (code code' : Code) (H EH H' EH' : List (BitVec 64)) (r : ProgHOL 64) :
    pinsP (Cb code H EH) r = pinsP (Cb code' H' EH') r := by
  unfold pinsP
  have eA := envAllocP_congr (C := Cb code H EH) (C' := Cb code' H' EH') rfl rfl
  have eN := namesP_congr (C := Cb code H EH) (C' := Cb code' H' EH') rfl rfl
  have eL := allocP_congr (C := Cb code H EH) (C' := Cb code' H' EH') rfl rfl
  rw [eA, eA, eN, eN, eL]

theorem initL_dom : ∀ p ∈ initL, p.1.toNat % 8 = 0 ∧ base ≤ p.1.toNat ∧ p.1.toNat < base + SZ := by
  decide +kernel

/-- The verdict the program's return carries. -/
def Verdict (nb : List (BitVec 8)) : Prop :=
  ∃ rc, ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc ∧
    ∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') [] rc.decls.toList
      = .ok (ConLeche.streamEnv rc.decls.toList)

set_option maxHeartbeats 4000000 in
/-- The body after the declarations. -/
theorem core_verdict (ra : ConPanqueque.Hash.RuntimeAssumptions) (hbits : System.Platform.numBits = 64)
    (t : PState σ) (hm : InitMem t) (hg : InitGlobals t codeT) (hbe : t.be = false)
    (hloc : ∀ x ∈ mainLocals, ∃ w, t.locals.lookup x = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t mainCore).1 ∨
      ((∃ w, (evaluateHOLFiniteState t mainCore).1 = some (.returned (.val (.word w)))) ∧
        ∃ nb bs : List (BitVec 8), nb.length = 8 * Lw ∧
          ⟨.extCall fRead, [], bs.zip nb⟩ ∈ (evaluateHOLFiniteState t mainCore).2.ffi.ioEvents ∧ Verdict nb) := by
  have hD : ∀ x ∈ mainLocals, x ∈ mainLocals := fun x h => h
  unfold mainCore
  -- the initial image
  generalize hR1 : (ProgHOL.seq (.assign .local kRA (.const (cA j0F)))
    (.seq (.assign .local kRL (.const (BitVec.ofNat 64 (8 * Lw))))
    (.seq (.extCall fRead (.const 0) (.const 0) (vv kRA) (vv kRL))
      (pinsP Cprog (frontAssigns restP))))) = R1
  have e0 : evaluateHOLFiniteState t (.seq (storesP initL) R1) = evaluateHOLFiniteState (tI t) R1 :=
    seq_normal _ (storesP_spec initL t (fun p hp => (hm.zero p.1 (initL_dom p hp).1 (initL_dom p hp).2.1
      (initL_dom p hp).2.2).1))
  rw [e0, ← hR1]
  have hinv0 : Inv (C0 codeT) (sBoot P0) [] [] mainLocals (tI t) :=
    ⟨sr_init hm codeT hg, fun x v h => absurd h (by simp [T.Env.get]), fun _ _ h => absurd h (by simp),
      fun x hx => hloc x hx⟩
  -- the buffer's address and size
  obtain ⟨wa, hwa⟩ := hloc kRA (by decide)
  obtain ⟨wl, hwl⟩ := hloc kRL (by decide)
  let t1 := setVarHOLFinite kRA (.val (.word (cA j0F))) (tI t)
  let t2 := setVarHOLFinite kRL (.val (.word (BitVec.ofNat 64 (8 * Lw)))) t1
  have ea1 : evaluateHOLFiniteState (tI t) (.assign .local kRA (.const (cA j0F))) = (none, t1) :=
    ConsLoop.assign_local _ _ _ _ wa (by simp [evalHOLExact]) hwa
  have ea2 : evaluateHOLFiniteState t1 (.assign .local kRL (.const (BitVec.ofNat 64 (8 * Lw)))) = (none, t2) :=
    ConsLoop.assign_local _ _ _ _ wl (by simp [evalHOLExact])
      (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hwl)
  rw [seq_normal _ ea1, seq_normal _ ea2]
  let Γ2 : Env := [(kRL, BitVec.ofNat 64 (8 * Lw)), (kRA, cA j0F)]
  have hinv2 : Inv (C0 codeT) (sBoot P0) Γ2 [] mainLocals t2 := inv_set (inv_set hinv0 kRA _) kRL _
  have hbe2 : t2.be = false := hbe
  -- the read
  have hal : (cellA (C0 codeT) j0F).toNat % 8 = 0 := by
    show (cA j0F).toNat % 8 = 0; simp only [cA]; addr_tac'
  have hov : (cellA (C0 codeT) j0F).toNat + 8 * Lw + 8 < 2 ^ 64 := by
    show (cA j0F).toNat + 8 * Lw + 8 < 2 ^ 64; simp only [cA]; addr_tac'
  have hcells : j0F + Lw ≤ (C0 codeT).H.length := by
    show j0F + Lw ≤ Himg.length; rw [Himg_length]; simp [NH]
  rcases read_step (C0 codeT) (ctxOK_init codeT) (sBoot P0) Γ2 [] mainLocals j0F Lw fRead hal hcells (by omega)
      (by simp [Γ2, T.Env.get_cons]; rfl) (by simp [Γ2, T.Env.get_cons]) fRead_ne t2 hinv2 hbe2 with
    hs3 | ⟨hn3, nb, bs, hl, hio, hinv3⟩
  · exact Or.inl (seq_stop _ _ _ hs3)
  generalize ht3 : (evaluateHOLFiniteState t2 (.extCall fRead (.const 0) (.const 0) (vv kRA) (vv kRL))).2 = t3
    at hio hinv3
  rw [seq_normal (s := t2) (s₁ := t3) _ (by rw [← hn3, ← ht3])]
  let H' := writeH Himg (cA j0F) j0F 0 nb
  have hinv3' : Inv (Cb codeT H' EH0) (sBoot P0) Γ2 [] mainLocals t3 := hinv3
  rw [show Cprog = Cb emptyCode [] EH0 from rfl, pinsP_Cb emptyCode codeT [] EH0 H' EH0]
  have hmono := evaluateHOLFiniteState_ioEvents_mono (pinsP (Cb codeT H' EH0) (frontAssigns restP)) t3 _ _ rfl
  have hev : (⟨.extCall fRead, [], bs.zip nb⟩ : _) ∈ t3.ffi.ioEvents := by rw [hio]; simp
  -- the frontend's locals and the rest, after the pins
  have hk : ∀ sP (EH' : List (BitVec 64)) (Γ' : Env), internReservedPins (sBoot P0) = .ok ((), sP) →
      PinBlock EH' sP.pins → sP.pins.zeroLevel = default →
      (∀ y, y ∉ [vPn, vKa, vPb, vRs] → Γ'.get y = Γ2.get y) →
      SpecR (σ := σ) (Inv (C1 codeT H' EH' sP.pins) sP Γ' [] mainLocals) (frontAssigns restP) sP
        ((fun _ => (pure () : AM Unit)) ()) (fun _ _ _ _ => Verdict nb) := by
    intro sP EH' Γ' hrun hb hz hag
    obtain ⟨hokP, -, hpo, hpp, hoff, -, -⟩ := internReservedPins_run (boot_ok P0).1 (boot_ok P0).2.1 hrun
    let C := C1 codeT H' EH' sP.pins
    have hC : C.code = codeMap (codeEntries C) := code_C1 _ _ _
    unfold frontAssigns
    refine specR_assignI kZb _ (cA 0) (by decide) rfl ?_
    refine specR_assignI kZn _ (BitVec.ofNat 64 (3 * capF)) (by decide) rfl ?_
    refine specR_assignI fTN _ (cA 0) (by decide) rfl ?_
    refine specR_assignI fTL _ (cA capF) (by decide) rfl ?_
    refine specR_assignI fTE _ (cA (2 * capF)) (by decide) rfl ?_
    refine specR_assignI fCap _ (BitVec.ofNat 64 capF) (by decide) rfl ?_
    refine specR_assignI kRB _ (cA rbF) (by decide) rfl ?_
    refine specR_assignI kCapD _ (BitVec.ofNat 64 capD) (by decide) rfl ?_
    refine specR_assignI kZL _ 0 (by decide) rfl ?_
    refine specR_assignI kRM _ (BitVec.ofNat 64 (8 * Lw - 16)) (by decide) rfl ?_
    intro tf htf
    have gRA : Γ'.get kRA = some (cA j0F) := by rw [hag _ (by decide)]; decide
    have gRL : Γ'.get kRL = some (BitVec.ofNat 64 (8 * Lw)) := by rw [hag _ (by decide)]; decide
    rcases rest_verdict [] [] ra C (ctxOK_C1 _ _ _ _ hb) (frontOK_C1 _ _ _ _) (front_ok σ C hC) (fold_ok C hC) rfl rfl rfl
        (feed_ok C hC) sP hokP hoff hpo hpp trivial _ [] mainLocals (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        rbF capD 0 capF j0F Lw (by simp [rbF]) (by simp [j0F]; omega) Himg (by rw [Himg_length]; simp [NH])
        (by simp [Lw]) (by simp [Lw]) hal (by show (cA j0F).toNat + 8 * Lw + 8 < 2 ^ 64; exact hov) hbits
        (by simp [capF]) (by simp [capF, natCap]) (by simp [capF]) (by simp [rbF, capF, capD])
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons])
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons])
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons])
        (by simp (config := {decide := true}) [T.Env.get_cons, hz])
        (by simp (config := {decide := true}) [T.Env.get_cons]; rw [gRA]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons]; exact gRL)
        (by simp (config := {decide := true}) [T.Env.get_cons])
        nb hl rfl tf htf with hs | ⟨⟨w, hret⟩, hv⟩
    · exact Or.inl hs
    · exact Or.inr ⟨w, hret, (), sP, rfl, hv⟩
  -- the pins
  rcases pins_spec (σ := σ) ra codeT pinCodes_T mainLocals (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (rest := frontAssigns restP) (R := fun _ _ _ _ => Verdict nb) H' (sBoot P0) Γ2 [] (fun _ => pure ())
      hk t3 hinv3' with hs4 | ⟨w, hret, -, -, -, hv⟩
  · exact Or.inl hs4
  · exact Or.inr ⟨⟨w, hret⟩, nb, bs, hl, hmono.subset hev, hv⟩

/-- **The whole program's verdict.**  From the harness's start (the region zeroed, the globals as
declared, little-endian), if `main`'s body returns, its FFI trace records the read of bytes `nb`,
con-leche parses the input they carry (length header first), and con-leche's checker accepts the
declarations.  Assumed: the Lean runtime's hashes are their reference models (`ra`), and con-leche
runs on a 64-bit platform (`hbits`). -/
theorem main_verdict (ra : ConPanqueque.Hash.RuntimeAssumptions) (hbits : System.Platform.numBits = 64)
    (t : PState σ) (hm : InitMem t) (hg : InitGlobals t codeT) (hbe : t.be = false) :
    Stop (evaluateHOLFiniteState t mainBody).1 ∨
      ((∃ w, (evaluateHOLFiniteState t mainBody).1 = some (.returned (.val (.word w)))) ∧
        ∃ nb bs : List (BitVec 8), nb.length = 8 * Lw ∧
          ⟨.extCall fRead, [], bs.zip nb⟩ ∈ (evaluateHOLFiniteState t mainBody).2.ffi.ioEvents ∧ Verdict nb) := by
  obtain ⟨t', L, h1, h2, h3, h4, h5, h6, -, e⟩ := decsZ_eval mainCore mainLocals t
  unfold mainBody
  rw [e]
  have hm' : InitMem t' := ⟨fun a hal hb1 hb2 => by rw [h1, h2]; exact hm.zero a hal hb1 hb2⟩
  have hg' : InitGlobals t' codeT := by
    obtain ⟨c, d, n1, n2, n3, n4, k, ht, eo, lit, et⟩ := hg
    exact ⟨by rw [h4]; exact c, by rw [h3]; exact d, by rw [h3]; exact n1, by rw [h3]; exact n2, by rw [h3]; exact n3,
      by rw [h3]; exact n4, by rw [h3]; exact k, by rw [h3]; exact ht, by rw [h3]; exact eo, by rw [h3]; exact lit,
      by rw [h3]; exact et⟩
  exact core_verdict ra hbits t' hm' hg' (by rw [h5]; exact hbe) h6

end ConPanqueque.Start
