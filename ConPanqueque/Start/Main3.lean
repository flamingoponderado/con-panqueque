import ConPanqueque.Start.Rest2
import ConPanqueque.Start.Main
import ConLeche.Verify.Frontend.Chunks
import ConPanqueque.Start.BasisPhase
import ConPanqueque.Code.Basis

/-! # The whole program with the forbidden-name pass

`mainCore2`: as `mainCore`, with `Bool.rec` interned before the pin phase (its handle kept in
`vBr`), stored into environment cell 138 after it, and `restP2` (parse, the pass, the fold) as the
rest.  `main_verdict2`: if it returns, the read input parses, con-leche's pure checker accepts it,
and every declaration is a value record at a name outside `FN`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Code ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front ConPanqueque.Scan

variable {σ : Type}

set_option maxRecDepth 100000

def vBr := ofString "pbr"

theorem pinBlock_agree {EH EH' : List (BitVec 64)} {P : Pins} (h : PinBlock EH P) (hr : P.reserved.length ≤ 16)
    (hag : ∀ j, j < 138 → EH'[j]? = EH[j]?) : PinBlock EH' P where
  size := h.size
  names i hi := by
    have : i < 52 := by have := h.size; simp [pinCount] at this; omega
    rw [hag _ (by omega)]; exact h.names i hi
  us := by rw [hag _ (by omega)]; exact h.us
  z := by rw [hag _ (by omega)]; exact h.z
  s1 := by rw [hag _ (by omega)]; exact h.s1
  mx := ⟨by rw [hag _ (by omega)]; exact h.mx.1, h.mx.2⟩
  ptr := by rw [hag _ (by omega)]; exact h.ptr
  cnt := by rw [hag _ (by omega)]; exact h.cnt
  res i hi := by rw [hag _ (by omega)]; exact h.res i hi

def mainLocals2 : List MlS := mainLocals ++ forbidVars ++ [vBr] ++ [ocA, ocB, ocC, ocD] ++ basisLocals

def boolRecCs : List String := ["Bool", "rec"]

/-- The body after the declarations. -/
def mainCore2 : ProgHOL 64 :=
  .seq (storesP initL)
  (.seq (.assign .local kRA (.const (cA j0F)))
  (.seq (.assign .local kRL (.const (BitVec.ofNat 64 (8 * Lw))))
  (.seq (.extCall fRead (.const 0) (.const 0) (vv kRA) (vv kRL))
    (nameP Cprog boolRecCs
      (.seq (.assign .local vBr (vv vPn))
      (pinsP Cprog
        (envAllocP Cprog vPb (.const (BitVec.ofNat 64 8))
          (.seq (.store (vv vPb) (vv vBr)) (offCheckP Cprog (ConPanqueque.T.Lit.basisP Cprog ConPanqueque.T.Lit.basisKinds (frontAssigns (restP2 capF))))))))))))

def mainBody2 : ProgHOL 64 := decsZ mainLocals2 mainCore2

/-- The verdict the program's return carries, with the pass. -/
def Verdict2 (nb : List (BitVec 8)) : Prop :=
  ∃ rc, ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc ∧
    (∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') [] rc.decls.toList
      = .ok (ConLeche.streamEnv rc.decls.toList)) ∧
    ∀ d ∈ rc.decls.toList, ∃ n, ConPanqueque.Pipeline.recName d = some n ∧ n ∉ FN

theorem writeH_append (A B : List (BitVec 64)) (A0 : BitVec 64) (j0 : Nat) : ∀ (a : Nat) (xs : List (BitVec 8)),
    (∀ b, a ≤ b → b < a + xs.length → j0 + b / 8 < A.length) →
    writeH (A ++ B) A0 j0 a xs = writeH A A0 j0 a xs ++ B
  | _, [], _ => rfl
  | a, x :: xs, h => by
    have ih := writeH_append A B A0 j0 (a + 1) xs (fun b h1 h2 => h b (by omega) (by simp; omega))
    have hi : j0 + a / 8 < (writeH A A0 j0 (a + 1) xs).length := by
      rw [writeH_length]; exact h a (Nat.le_refl _) (by simp)
    simp only [writeH, ih]
    rw [List.getElem?_append_left hi, List.set_append_left _ _ hi]

set_option maxHeartbeats 4000000 in
/-- The body after the declarations. -/
theorem core_verdict2 (ra : ConPanqueque.Hash.RuntimeAssumptions) (hbits : System.Platform.numBits = 64)
    (t : PState σ) (hm : InitMem t) (hg : InitGlobals t codeT) (hbe : t.be = false)
    (hloc : ∀ x ∈ mainLocals2, ∃ w, t.locals.lookup x = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t mainCore2).1 ∨
      ((∃ w, (evaluateHOLFiniteState t mainCore2).1 = some (.returned (.val (.word w)))) ∧
        ∃ nb bs : List (BitVec 8), nb.length = 8 * Lw ∧
          ⟨.extCall fRead, [], bs.zip nb⟩ ∈ (evaluateHOLFiniteState t mainCore2).2.ffi.ioEvents ∧ Verdict2 nb) := by
  have hD : ∀ x ∈ mainLocals2, x ∈ mainLocals2 := fun x h => h
  unfold mainCore2
  -- the initial image
  generalize hR1 : (ProgHOL.seq (.assign .local kRA (.const (cA j0F)))
    (.seq (.assign .local kRL (.const (BitVec.ofNat 64 (8 * Lw))))
    (.seq (.extCall fRead (.const 0) (.const 0) (vv kRA) (vv kRL))
      (nameP Cprog boolRecCs
        (.seq (.assign .local vBr (vv vPn))
        (pinsP Cprog (envAllocP Cprog vPb (.const (BitVec.ofNat 64 8))
          (.seq (.store (vv vPb) (vv vBr)) (offCheckP Cprog (ConPanqueque.T.Lit.basisP Cprog ConPanqueque.T.Lit.basisKinds (frontAssigns (restP2 capF)))))))))))) = R1
  have e0 : evaluateHOLFiniteState t (.seq (storesP initL) R1) = evaluateHOLFiniteState (tI t) R1 :=
    seq_normal _ (storesP_spec initL t (fun p hp => (hm.zero p.1 (initL_dom p hp).1 (initL_dom p hp).2.1
      (initL_dom p hp).2.2).1))
  rw [e0, ← hR1]
  have hinv0 : Inv (C0 codeT) (sBoot P0) [] [] mainLocals2 (tI t) :=
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
  have hinv2 : Inv (C0 codeT) (sBoot P0) Γ2 [] mainLocals2 t2 := inv_set (inv_set hinv0 kRA _) kRL _
  have hbe2 : t2.be = false := hbe
  -- the read
  have hal : (cellA (C0 codeT) j0F).toNat % 8 = 0 := by
    show (cA j0F).toNat % 8 = 0; simp only [cA]; addr_tac'
  have hov : (cellA (C0 codeT) j0F).toNat + 8 * Lw + 8 < 2 ^ 64 := by
    show (cA j0F).toNat + 8 * Lw + 8 < 2 ^ 64; simp only [cA]; addr_tac'
  have hcells : j0F + Lw ≤ (C0 codeT).H.length := by
    show j0F + Lw ≤ Himg.length; rw [Himg_length]; simp [NH]
  rcases read_step (C0 codeT) (ctxOK_init codeT) (sBoot P0) Γ2 [] mainLocals2 j0F Lw fRead hal hcells (by omega)
      (by simp [Γ2, T.Env.get_cons]; rfl) (by simp [Γ2, T.Env.get_cons]) fRead_ne t2 hinv2 hbe2 with
    hs3 | ⟨hn3, nb, bs, hl, hio, hinv3⟩
  · exact Or.inl (seq_stop _ _ _ hs3)
  generalize ht3 : (evaluateHOLFiniteState t2 (.extCall fRead (.const 0) (.const 0) (vv kRA) (vv kRL))).2 = t3
    at hio hinv3
  rw [seq_normal (s := t2) (s₁ := t3) _ (by rw [← hn3, ← ht3])]
  let H' := writeH Himg (cA j0F) j0F 0 nb
  have hinv3' : Inv (Cb codeT H' EH0) (sBoot P0) Γ2 [] mainLocals2 t3 := hinv3
  rw [show Cprog = Cb emptyCode [] EH0 from rfl,
    nameP_congr (C := Cb emptyCode [] EH0) (C' := Cb codeT H' EH0) rfl rfl]
  have hmono := evaluateHOLFiniteState_ioEvents_mono (nameP (Cb codeT H' EH0) boolRecCs
    (.seq (.assign .local vBr (vv vPn)) (pinsP Cprog (envAllocP Cprog vPb (.const (BitVec.ofNat 64 8))
      (.seq (.store (vv vPb) (vv vBr)) (offCheckP Cprog (ConPanqueque.T.Lit.basisP Cprog ConPanqueque.T.Lit.basisKinds (frontAssigns (restP2 capF))))))))) t3 _ _ rfl
  have hev : (⟨.extCall fRead, [], bs.zip nb⟩ : _) ∈ t3.ffi.ioEvents := by rw [hio]; simp
  -- after the pins: the `Bool.rec` cell, the frontend's locals, the rest
  have hk2 : ∀ (bh : NIdx) (s1 : AState) (Γ1 : Env), StateOK s1 → s1.store.scratchOn = false →
      denoteN s1.store.ns default = some .anonymous →
      denoteN s1.store.ns bh = some boolRecName → PersN bh → Γ1.get vBr = some (Enc.idxW bh) →
      (∀ y, y ∉ [vPn, vKa, vBr] → Γ1.get y = Γ2.get y) →
      ∀ sP (EH' : List (BitVec 64)) (Γ' : Env), internReservedPins s1 = .ok ((), sP) →
      PinBlock EH' sP.pins → sP.pins.zeroLevel = default → EH'.length = 138 →
      (∀ y, y ∉ [vPn, vKa, vPb, vRs] → Γ'.get y = Γ1.get y) →
      SpecR (σ := σ) (Inv (C1 codeT H' EH' sP.pins) sP Γ' [] mainLocals2)
        (envAllocP Cprog vPb (.const (BitVec.ofNat 64 8)) (.seq (.store (vv vPb) (vv vBr)) (offCheckP Cprog (ConPanqueque.T.Lit.basisP Cprog ConPanqueque.T.Lit.basisKinds (frontAssigns (restP2 capF))))))
        sP (ConPanqueque.T.Lit.basisTwin ConPanqueque.T.Lit.basisKinds >>= fun _ => (pure () : AM Unit))
        (fun _ _ _ _ => Verdict2 nb) := by
    intro bh s1 Γ1 hok1 hoff1 hA1 hbd1 hbp hbr hag1 sP EH' Γ' hrun hb hz hlen hag
    obtain ⟨hokP, hextP, hpo, hpp, hoff, -, -⟩ := internReservedPins_run hok1 hoff1 hrun
    have hr16 : sP.pins.reserved.length ≤ 16 := by
      rw [(denoteNL_get hpo.reserved).1, reserved_length]
    rw [envAllocP_congr (C := Cprog) (C' := C1 codeT H' EH' sP.pins) rfl rfl]
    refine specR_envAllocI vPb _ 1 (by decide) (hD _ (by decide)) (fun v => rfl) (fun ws hws hroom => ?_)
    show SpecR (Inv (C1 codeT H' (EH' ++ ws) sP.pins) sP _ [] mainLocals2) _ sP _ _
    have hag2 : ∀ j, j < 138 → (EH' ++ ws)[j]? = EH'[j]? := fun j hj => List.getElem?_append_left (by omega)
    have hb2 := pinBlock_agree hb hr16 hag2
    have hl2 : (EH' ++ ws).length = 139 := by simp [hlen, hws]
    refine specR_envStoreI (ctxOK_C1 _ _ _ _ hb2) (vv vPb) (vv vBr) 138 (by rw [C1_EH, hl2]; omega) (Enc.idxW bh)
      (by simp only [sev, vv, T.Env.get_cons, ite_true, C1_EH, hlen]; rfl)
      (by simp only [sev, vv, T.Env.get_cons, show vBr ≠ vPb by decide, ite_false]
          rw [hag _ (by decide), hbr]) ?_
    show SpecR (Inv (C1 codeT H' ((EH' ++ ws).set 138 (Enc.idxW bh)) sP.pins) sP _ [] mainLocals2) _ sP _ _
    let EH3 := (EH' ++ ws).set 138 (Enc.idxW bh)
    have hb3 : PinBlock EH3 sP.pins := pinBlock_agree hb2 hr16 (fun j hj => by
      simp only [EH3]; rw [List.getElem?_set, ite_eq_right (by omega)])
    have hB3 : EH3[138]? = some (Enc.idxW bh) := List.getElem?_set_self (by omega)
    have hbdP : denoteN sP.store.ns bh = some boolRecName := denoteN_ext hbd1 hextP
    let C := C1 codeT H' EH3 sP.pins
    have hC : C.code = codeMap (codeEntries C) := code_C1 _ _ _
    have hag' : ∀ y, y ∉ [vPn, vKa, vPb, vRs, vBr] → T.Env.get ((vPb, ecell (C1 codeT H' EH' sP.pins) EH'.length) :: Γ') y
        = Γ2.get y := by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp only [T.Env.get_cons, ite_eq_right hy.2.2.1]
      rw [hag y (by simp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1]), hag1 y (by simp [hy.1, hy.2.1, hy.2.2.2.2])]
    -- the scratch tier off, then the pinned blocks interned
    refine specR_offCheckI (C := C) ⟨by decide, by decide, by decide, by decide⟩ (fun hoffA => ?_)
    rw [show ConPanqueque.T.Lit.basisP Cprog = ConPanqueque.T.Lit.basisP C from by
      funext ks r; exact basisP_congr (C := Cprog) (C' := C) rfl rfl ks r]
    have G : ConPanqueque.T.Lit.GenEnv C mainLocals2 12 :=
      ⟨ctxOK_C1 _ _ _ _ hb3, frontOK_C1 _ _ _ _, (boot_ok P0).2.2.1, ecodes_ok C hC, by decide, by decide,
        fun c hc j hj => List.mem_append_right _ (gv_mem_basisLocals hc hj)⟩
    rw [show C = ctxH C C.H from (ctxH_self C).symm]
    refine ConPanqueque.T.Lit.basisP_spec ra G _ C.H _ _ [] sP (fun s' Γ4 H'' hpH ag4 hrun => ?_)
    obtain ⟨hist, hoff', -, -⟩ := ConPanqueque.T.Lit.basisTwin_step _ hokP hoffA hrun
    have hpins' : s'.pins = sP.pins := hist.pins
    have hokP' := hist.ok
    have hpo' : PinsOK s' := hpo.mono hist.ext hist.pins
    have hpp' : PersPins s' := hpp.mono hist.pins
    have hb3' : PinBlock EH3 s'.pins := by rw [hpins']; exact hb3
    have hbd' : denoteN s'.store.ns bh = some boolRecName := denoteN_ext hbdP hist.ext
    obtain ⟨extra, hextra⟩ := hpH
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
    have g4 : ∀ y, y ≠ vPn → y ≠ vKa → (∀ c j, 0 ≤ j → y ≠ ConPanqueque.T.Lit.gv c j) →
        Γ4.get y = T.Env.get ((ocD, 0) :: (ocC, 0) :: (ocB, 0) :: (ocA, 0) ::
          (vPb, ecell (C1 codeT H' EH' sP.pins) EH'.length) :: Γ') y :=
      fun y h1 h2 h3 => ag4 y h3 h1 h2
    have gvNe : ∀ (m : MlS), m.explode.head? ≠ some (BitVec.ofNat 8 'g'.toNat) → ∀ c j, 0 ≤ j → m ≠ ConPanqueque.T.Lit.gv c j :=
      fun m hm c j _ e => ConPanqueque.T.Lit.gv_ne_of hm e.symm
    have gRA : Γ4.get kRA = some (cA j0F) := by
      rw [g4 kRA (by decide) (by decide) (gvNe _ (by simp [kRA, ofString]))]
      simp (config := {decide := true}) only [T.Env.get_cons, ite_false]
      rw [hag _ (by decide), hag1 _ (by decide)]; decide
    have gRL : Γ4.get kRL = some (BitVec.ofNat 64 (8 * Lw)) := by
      rw [g4 kRL (by decide) (by decide) (gvNe _ (by simp [kRL, ofString]))]
      simp (config := {decide := true}) only [T.Env.get_cons, ite_false]
      rw [hag _ (by decide), hag1 _ (by decide)]; decide
    have hHimg : (ctxH C H'').H = writeH (Himg ++ extra) (cellA (ctxH C H'') j0F) j0F 0 nb := by
      show H'' = _
      rw [← hextra]
      exact (writeH_append Himg extra (cA j0F) j0F 0 nb (fun b _ hb => by
        rw [Himg_length]; simp [NH]; rw [hl] at hb; omega)).symm
    rcases rest_verdict2 [] [] ra (ctxH C H'') (ctxOK_H (ctxOK_C1 _ _ _ _ hb3) H'') (by ctx_tr (frontOK_C1 codeT H' EH3 sP.pins))
        (frontCodes_ctxH (front_ok σ C hC)) (foldCodes_ctxH (fold_ok C hC) H'') rfl rfl rfl
        (fun _ => rfl) (feed_ok C hC) s' hokP' hoff'.1 hpo' hpp' trivial
        (ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteN_ext hA1 hextP) hist.ext) hb3' bh hB3 hbd' hbp _ [] mainLocals2 (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (fun x hx => by
          simp only [forbidVars, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        rbF capD 0 capF j0F Lw (by simp [rbF]) (by simp [j0F]; omega) (Himg ++ extra)
        (by simp only [List.length_append]; rw [Himg_length]; simp [NH])
        (by simp [Lw]) (by simp [Lw]) hal (by show (cA j0F).toNat + 8 * Lw + 8 < 2 ^ 64; exact hov) hbits
        (by simp [capF]) (by simp [capF, natCap]) (by simp [capF]) (by simp [rbF, capF, capD])
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons])
        (by simp (config := {decide := true}) [T.Env.get_cons, hpins', hz])
        (by simp (config := {decide := true}) [T.Env.get_cons]; rw [gRA]; rfl)
        (by simp (config := {decide := true}) [T.Env.get_cons]; exact gRL)
        (by simp (config := {decide := true}) [T.Env.get_cons])
        nb hl hHimg tf htf with hs | ⟨⟨w, hret⟩, hv⟩
    · exact Or.inl hs
    · exact Or.inr ⟨w, hret, (), s', rfl, hv⟩
  -- `Bool.rec`, then the pins
  have hk1 : ∀ (bh : NIdx) (s1 : AState) (Γ1 : Env), (∀ y, y ≠ vPn → y ≠ vKa → Γ1.get y = Γ2.get y) →
      Γ1.get vPn = some (Enc.idxW bh) → internName boolRecName (sBoot P0) = .ok (bh, s1) →
      SpecR (σ := σ) (Inv (Cb codeT H' EH0) s1 Γ1 [] mainLocals2)
        (.seq (.assign .local vBr (vv vPn)) (pinsP Cprog (envAllocP Cprog vPb (.const (BitVec.ofNat 64 8))
          (.seq (.store (vv vPb) (vv vBr)) (offCheckP Cprog (ConPanqueque.T.Lit.basisP Cprog ConPanqueque.T.Lit.basisKinds (frontAssigns (restP2 capF)))))))) s1
        ((fun _ => internReservedPins >>= fun _ =>
          ConPanqueque.T.Lit.basisTwin ConPanqueque.T.Lit.basisKinds >>= fun _ => (pure () : AM Unit)) bh)
        (fun _ _ _ _ => Verdict2 nb) := by
    intro bh s1 Γ1 hag1 hpn hr
    obtain ⟨st1, hden1⟩ := ConRon.Bridge.Frontend.internName_sstep (boot_ok P0).1 hr
    have hoff1 : s1.store.scratchOn = false := by rw [st1.scratch]; exact (boot_ok P0).2.1
    have hbp := ConRon.Bridge.Frontend.PersN_of_denote st1.ok.wf hoff1 hden1
    refine specR_assignI vBr (vv vPn) (Enc.idxW bh) (hD _ (by decide)) (by simpa [sev, vv] using hpn) ?_
    rw [show Cprog = Cb emptyCode [] EH0 from rfl, pinsP_Cb emptyCode codeT [] EH0 H' EH0]
    refine pins_spec ra codeT pinCodes_T mainLocals2 (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> decide) H' s1 _ []
      (fun _ => ConPanqueque.T.Lit.basisTwin ConPanqueque.T.Lit.basisKinds >>= fun _ => pure ())
      (fun sP EH' Γ' hrun hb hz hlen hag => hk2 bh s1 _ st1.ok hoff1
        (ConRon.Bridge.denoteN_ext (boot_ok P0).2.2.1 st1.ext) hden1 hbp (by simp [T.Env.get_cons])
        (fun y hy => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          simp only [T.Env.get_cons, ite_eq_right hy.2.2]; exact hag1 y hy.1 hy.2.1) sP EH' Γ' hrun hb hz hlen hag)
  rcases name_spec ra (Cb codeT H' EH0) (ctxOK_Cb codeT H' EH0 (fun _ _ => rfl)) (frontOK_Cb codeT H' EH0)
      pinCodes_T.nstr mainLocals2 (hD _ (by decide)) (hD _ (by decide)) boolRecName boolRecCs (by decide)
      (fun c hc => by simp only [boolRecCs, List.mem_cons, List.not_mem_nil, or_false] at hc
                      rcases hc with rfl | rfl <;> decide) (sBoot P0) (boot_ok P0).1 (boot_ok P0).2.2.1 Γ2 [] _ hk1 t3 hinv3' with
    hs4 | ⟨w, hret, -, -, -, hv⟩
  · exact Or.inl hs4
  · exact Or.inr ⟨⟨w, hret⟩, nb, bs, hl, hmono.subset hev, hv⟩

/-- **The whole program's verdict, with the pass.** -/
theorem main_verdict2 (ra : ConPanqueque.Hash.RuntimeAssumptions) (hbits : System.Platform.numBits = 64)
    (t : PState σ) (hm : InitMem t) (hg : InitGlobals t codeT) (hbe : t.be = false) :
    Stop (evaluateHOLFiniteState t mainBody2).1 ∨
      ((∃ w, (evaluateHOLFiniteState t mainBody2).1 = some (.returned (.val (.word w)))) ∧
        ∃ nb bs : List (BitVec 8), nb.length = 8 * Lw ∧
          ⟨.extCall fRead, [], bs.zip nb⟩ ∈ (evaluateHOLFiniteState t mainBody2).2.ffi.ioEvents ∧ Verdict2 nb) := by
  obtain ⟨t', L, h1, h2, h3, h4, h5, h6, -, e⟩ := decsZ_eval mainCore2 mainLocals2 t
  unfold mainBody2
  rw [e]
  have hm' : InitMem t' := ⟨fun a hal hb1 hb2 => by rw [h1, h2]; exact hm.zero a hal hb1 hb2⟩
  have hg' : InitGlobals t' codeT := by
    obtain ⟨c, d, n1, n2, n3, n4, k, ht, eo, lit, et⟩ := hg
    exact ⟨by rw [h4]; exact c, by rw [h3]; exact d, by rw [h3]; exact n1, by rw [h3]; exact n2, by rw [h3]; exact n3,
      by rw [h3]; exact n4, by rw [h3]; exact k, by rw [h3]; exact ht, by rw [h3]; exact eo, by rw [h3]; exact lit,
      by rw [h3]; exact et⟩
  exact core_verdict2 ra hbits t' hm' hg' (by rw [h5]; exact hbe) h6

-- `main_pipeline`/`main_pipeline_chunks` (an arbitrary prelude under `PreludeOK`) are superseded by
-- `main_pipeline_prelude` (`ConPanqueque/Start/Main4.lean`), at con-leche's own built-in prelude.

end ConPanqueque.Start
