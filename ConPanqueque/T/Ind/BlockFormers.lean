import ConPanqueque.T.Ind.EnvRules

/-!
# The block's formers and constructors in the environment heap

`cnFill`: a member's constructor names (its `CtorsRep` pair block) into a value-heap block, `memberNamesFill`'s
twin; the former's capability record is written with them (`fmBody`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl

def cnL := ofString "cn_l"
def cnD := ofString "cn_d"
def cnI := ofString "cn_i"
def cnK := ofString "cn_k"
def cnX := ofString "cn_x"
def cnY := ofString "cn_y"
def cnZ := ofString "cn_z"
def cnR := ofString "cn_r"
def fCnFill := ofString "ctorNamesFill"

def cnParams : List MlS := [cnL, cnD, cnI, cnK]
def cnLocals : List MlS := [cnX, cnY, cnZ, cnR]

/-- The constructors' names (pair block at `cnL`, from `cnI`) into the block at `cnD`. -/
def cnBody : ProgHOL 64 := prologue cnLocals
  (.ite (.cmp .lower (vv cnI) (vv cnK))
    (.seq (.assign .local cnX (.load .one (.op .add [vv cnL, .op .add [.panop .mul [vv cnI, .const 16], .const 8]])))
    (.seq (.assign .local cnY (vv cnX))
    (.seq (.assign .local cnZ (.load .one (vv cnY)))
    (.seq (.store (.op .add [vv cnD, .op .add [.panop .mul [vv cnI, .const 8], .const 8]]) (vv cnZ))
    (.seq (.call (some (some (.local, cnR), none)) fCnFill [vv cnL, vv cnD, .op .add [vv cnI, .const 1], vv cnK])
      (.return (.const 0)))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- The names from position `i` on, past the frozen prefix `Hc`. -/
def PostCN (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (cs : List (IConstantVal × Nat)) (i : Nat) (_ : Unit) (_ : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧
    ∀ j (hj : j < cs.length), i ≤ j → H'[o + 1 + j]? = some (Enc.idxW cs[j].1.name)

theorem postCN_locals (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (cs : List (IConstantVal × Nat)) (i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCN C Hc o cs i a w s' st → PostCN C Hc o cs i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem cn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnLocals → (ctxEnv C ++ cnParams.zip vals).get x = none :=
  Knot.params_none C cnLocals cnParams vals (by decide) (by decide)

/-- **The member-names fill** from position `i`. -/
theorem cn_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fCnFill = some (cnParams.map (fun p => (p, ShapeHOL.one)), cnBody, .one))
    (cs : List (IConstantVal × Nat)) (om o : Nat) (H0 : List (BitVec 64)) (hms : CtorsRep C H0 om cs) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), cs.length - i = k → i ≤ cs.length → H0 <+: Hc →
      Hc.length ≤ o + 1 + i → Hc <+: H → o + 1 + cs.length ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (cnParams.zip [cellA C om, cellA C o, BitVec.ofNat 64 i,
        BitVec.ofNat 64 cs.length])) cnBody s (pure ()) (PostCN C Hc o cs i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi h0 hHc hp hl
    refine specR_prologue (postCN_locals _ _ _ _ _) (cn_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, cnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc s hk hi h0 hHc hp hl
    have hil : i < cs.length := by omega
    refine specR_prologue (postCN_locals _ _ _ _ _) (cn_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨oc, h1, hcv, -⟩ := hms.2 i hil
    have h1b := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix h1 h0H)).1
    refine UD.specR_heapLoadI' (C := ctxH C H) cnX _ (om + 1 + 2 * i) _ (ConPanqueque.T.Decl.get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, cnParams, ctxEnv]; exact cellA_mul16 C om i (by omega)) ?_
    refine specR_assignI cnY (vv cnX) (cellA C oc) (by decide) (by simp [Env.get]) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnZ _ oc _ (ConPanqueque.T.Decl.get_prefix hcv.1 h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hj : o + 1 + i < (ctxH C H).H.length := by show o + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_H hok H) _ (vv cnZ) (o + 1 + i) hj (Enc.idxW cs[i].1.name)
      (by simp +decide [sev, Env.get_cons, Env.get, cnParams, ctxEnv]; exact cellA_mulIdx C o i (by omega))
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H.set (o + 1 + i) (Enc.idxW cs[i].1.name))) _ _ _ _) _ _ _ _
    generalize hB : H.set (o + 1 + i) (Enc.idxW cs[i].1.name) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[o + 1 + i]? = some (Enc.idxW cs[i].1.name) := by rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hp
    let Hc' := B.take (o + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIG (C := ctxH C B) cnR fCnFill cnParams [vv cnL, vv cnD, .op .add [vv cnI, .const 1], vv cnK]
      cnBody [cellA C om, cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cnParams, ctxEnv], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostCN C Hc' o cs (i + 1) a w s' st)
      (fun a w s' H' => s' = s ∧ Hc' <+: H' ∧
        ∀ j (hj : j < cs.length), i + 1 ≤ j → H'[o + 1 + j]? = some (Enc.idxW cs[j].1.name))
      (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) B Hc' s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega) _
          (pre_of_lookups hu cnParams _ rfl hlk)))
      (fun a w s' H' ⟨hs', hp', hc'⟩ => ?_)
    subst hs'
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
      rcases Nat.lt_or_ge i j with h | h
      · exact hc' j hj (by omega)
      · have e : j = i := by omega
        subst e
        have := ConPanqueque.T.Decl.get_prefix (show Hc'[o + 1 + j]? = some (Enc.idxW cs[j].1.name) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'
        exact this⟩)

end

/-- `blockCapsAt`'s record at a present member, uniformly. -/
def capsOf (p : BlockShape) (ms : MemberShape) (isRec : Bool) (nz : Bool) : IIndCaps :=
  { eta := (ms.ctors.length == 1 && ms.nIdx == 0 && !isRec), all := p.memberNames, nparams := p.nP, nIdx := ms.nIdx,
    ctors := ms.ctors.map (·.1.name), neverZero := nz }

theorem blockCapsAt_eq (p : BlockShape) (i : Nat) (isRec : Bool) (ms : MemberShape) (hmi : p.members[i]? = some ms) :
    blockCapsAt p i isRec = (formerZ ms.declared >>= fun z => pure (capsOf p ms isRec z.isNever)) := by
  unfold blockCapsAt memberNeverZero
  simp only [hmi, bind_assoc, pure_bind]
  congr 1; funext z
  rcases hc : ms.ctors with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · simp [capsOf, hc]
  · simp only [capsOf, hc, List.length_singleton, List.map_cons, List.map_nil]
    congr 2
    by_cases hn : ms.nIdx = 0 <;> cases isRec <;> simp [hn]
  · simp [capsOf, hc]

def fmM := ofString "fm_m"
def fmIr := ofString "fm_ir"
def fmAll := ofString "fm_all"
def fmNp := ofString "fm_np"
def fmDc := ofString "fm_dc"
def fmNi := ofString "fm_ni"
def fmL := ofString "fm_l"
def fmNc := ofString "fm_nc"
def fmNz := ofString "fm_nz"
def fmE := ofString "fm_e"
def fmV := ofString "fm_v"
def fmX := ofString "fm_x"
def fmB := ofString "fm_b"
def fmR := ofString "fm_r"
def fmO := ofString "fm_o"
def fFormerRec := ofString "formerRecW"

def fmParams : List MlS := [fmM, fmIr, fmAll, fmNp, fmNz]
def fmLocals : List MlS := [fmDc, fmNi, fmL, fmNc, fmE, fmV, fmX, fmB, fmR, fmO]

/-- A former's environment record (member at `fmM`, the block's recursiveness, its names' environment block, its
parameter count, its sort's never-zero bit). -/
def fmBody (C : Ctx) : ProgHOL 64 := prologue fmLocals
  (.seq (.assign .local fmDc (.load .one (.op .add [vv fmM, .const 8])))
  (.seq (.assign .local fmNi (.load .one (.op .add [vv fmM, .const 16])))
  (.seq (.assign .local fmL (.load .one (.op .add [vv fmM, .const 24])))
  (.seq (.assign .local fmNc (.load .one (vv fmL)))
  (guardP fmNc 58
  (.seq (.assign .local fmE (.op .and [.cmp .equal (vv fmNc) (.const 1),
    .op .and [.cmp .equal (vv fmNi) (.const 0), .cmp .equal (vv fmIr) (.const 0)]]))
  (allocP C fmV (.shift .lsl (.op .add [vv fmNc, .const 1]) (.const 3))
  (.seq (.store (vv fmV) (vv fmNc))
  (.seq (.call (some (some (.local, fmX), none)) fCnFill [vv fmL, vv fmV, .const 0, vv fmNc])
  (envBlkP C fmB fmV fmNc fmX
  (.seq (.call (some (some (.local, fmO), none)) fConstRec
    [vv fmDc, .const 3, vv fmE, vv fmAll, vv fmNp, vv fmNi, vv fmB, vv fmNz])
    (.return (vv fmO)))))))))))))

section
variable {σ : Type}

/-- A fresh constant record, past the value heap and the environment heap, at any later state. -/
def PostFM (C : Ctx) (ci : IConstantInfo) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' EH o, C.H <+: H' ∧ C.EH <+: EH ∧ C.EH.length ≤ o ∧ w = ecell C o ∧ CIE C.EB EH o ci ∧
    SR (ctxE (ctxH C H') EH) s' st

theorem postFM_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostFM C a w s' st → PostFM C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', EH, o, h1, h2, h3, h4, h5, h6⟩ => ⟨H', EH, o, h1, h2, h3, h4, h5, sr_of_eq h6 rfl rfl rfl rfl⟩

theorem fm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fmLocals → (ctxEnv C ++ fmParams.zip vals).get x = none :=
  Knot.params_none C fmLocals fmParams vals (by decide) (by decide)

theorem eta_word (a b : Nat) (r : Bool) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((if BitVec.ofNat 64 a = 1#64 then 1#64 else 0#64) &&&
      ((if BitVec.ofNat 64 b = 0#64 then 1#64 else 0#64) &&& if boolW r = 0#64 then 1#64 else 0#64)) =
      boolW (a == 1 && b == 0 && !r) := by
  have e1 : (BitVec.ofNat 64 a = 1#64) ↔ a = 1 := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro h; subst h; rfl
  have e2 : (BitVec.ofNat 64 b = 0#64) ↔ b = 0 := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro h; subst h; rfl
  by_cases h1 : a = 1 <;> by_cases h2 : b = 0 <;> cases r <;> simp [e1, e2, h1, h2, boolW]

/-- **A former's record**, its capabilities `blockCapsAt`'s. -/
theorem fm_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcn : C.code.lookup fCnFill = some (cnParams.map (fun p => (p, ShapeHOL.one)), cnBody, .one))
    (hcw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one))
    (p : BlockShape) (ms : MemberShape) (om : Nat)
    (hmr : MemberRep C C.H om ms) (isRec : Bool) (wAll : BitVec 64) (hall : ENList C.EB C.EH wAll p.memberNames)
    (hnp : p.nP < 2 ^ 63) (hni : ms.nIdx < 2 ^ 63) (hlps : ms.declared.levelParams.length < 2 ^ 60) (nz : Bool)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (fmParams.zip [cellA C om, boolW isRec, wAll, BitVec.ofNat 64 p.nP, boolW nz])) (fmBody C) s
      (pure (IConstantInfo.indInfo ms.declared (capsOf p ms isRec nz))) (PostFM C) := by
  refine specR_prologue (postFM_locals _) (fm_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : C.H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  obtain ⟨-, ⟨od, hod, hcv⟩, hnI, ⟨ol, hol, hcs⟩⟩ := hmr
  refine UD.specR_heapLoadI' (C := C) fmDc _ (om + 1) _ hod (by decide)
    (by simp +decide [sev, Env.get, fmParams, ctxEnv]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := C) fmNi _ (om + 2) _ hnI (by decide)
    (by simp +decide [sev, Env.get, fmParams, ctxEnv]; exact cellA_add_ofNat C om 2) ?_
  refine UD.specR_heapLoadI' (C := C) fmL _ (om + 3) _ hol (by decide)
    (by simp +decide [sev, Env.get, fmParams, ctxEnv]; exact cellA_add_ofNat C om 3) ?_
  refine UD.specR_heapLoadI' (C := C) fmNc _ ol _ hcs.1 (by decide) (by simp +decide [Env.get] <;> rfl) ?_
  have hcl : ms.ctors.length < 2 ^ 61 := by
    rcases Nat.lt_or_ge 0 ms.ctors.length with h | h
    · obtain ⟨oc, h1, -⟩ := hcs.2 (ms.ctors.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1).1; omega
    · omega
  refine specR_guardI fmNc ms.ctors.length 58 (by decide) (by simp [Env.get]) (by omega) (fun hc58 => ?_)
  have hp1' : C.H <+: C.H := List.prefix_refl _
  refine specR_assignI fmE _ (boolW (ms.ctors.length == 1 && ms.nIdx == 0 && !isRec)) (by decide)
    (by
      simp +decide only [sev, sev_vv, Env.get, Env.get_cons, fmParams, ctxEnv, ite_true, ite_false, List.zip,
        List.append, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      simp +decide [Env.get, fmParams, ctxEnv]
      exact eta_word ms.ctors.length ms.nIdx isRec (by omega) hni) ?_
  -- the constructor names, copied
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
  have hHN1' : C.H.length ≤ C.HN := hHN1
  refine specR_allocI (C := ctxH C C.H) fmV _ (ms.ctors.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : C.H <+: H2 := hp2
  have hq0 : H2.length < (ctxH (ctxH C C.H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv fmV) (vv fmNc) H2.length hq0 (BitVec.ofNat 64 ms.ctors.length)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 ms.ctors.length))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 ms.ctors.length) = B
  have hBlen : B.length = H2.length + (ms.ctors.length + 1) := by rw [← hB]; simp [hws]
  have hB0 : B[H2.length]? = some (BitVec.ofNat 64 ms.ctors.length) := by
    rw [← hB, List.getElem?_set_self (by simp; omega)]
  have hpB : H2 <+: B := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc := B.take (H2.length + 1)
  have hpc : H2 <+: Hc := by
    refine prefix_of_get? (by simp [Hc]; omega) (fun j hj => ?_)
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
  refine specR_pureBind () ?_
  refine specR_callNIG (C := ctxH C B) fmX fCnFill cnParams [vv fmL, vv fmV, .const 0, vv fmNc] cnBody
    [cellA C ol, cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.ctors.length] (by decide) rfl (by decide) hcn
    ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, rfl, by simp +decide [sev, Env.get],
      trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostCN C Hc H2.length ms.ctors 0 a w s' st)
    (fun a w s' H' => s' = s ∧ Hc <+: H' ∧
      ∀ j (hj : j < ms.ctors.length), 0 ≤ j → H'[H2.length + 1 + j]? = some (Enc.idxW ms.ctors[j].1.name))
    (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact cn_spec C hok hcn ms.ctors ol H2.length C.H hcs _ 0 B Hc s rfl (Nat.zero_le _)
        ((hp1'.trans hp2').trans hpc) (by simp [Hc]) (List.take_prefix _ _) (by omega) _
        (pre_of_lookups hu cnParams _ rfl hlk)))
    (fun a w s' H3 ⟨hs', hp3, hc3⟩ => ?_)
  subst s'
  have hpH3 : C.H <+: H3 := ((hp1'.trans hp2').trans hpc).trans hp3
  let ns : List (BitVec 64) := (ms.ctors.map (·.1.name)).map Enc.idxW
  have hnsl : ns.length = ms.ctors.length := by simp [ns]
  have hbns : BlkAt H3 H2.length ns := by
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hnsl]
      exact ConPanqueque.T.Decl.get_prefix (show Hc[H2.length]? = _ by
        simp only [Hc]; rw [List.getElem?_take_of_lt (by omega)]; exact hB0) hp3
    · have := hc3 j (by omega) (Nat.zero_le _)
      simpa [ns] using this
  refine specR_envBlkI (ctxOK_H hok H3) hcp fmB fmV fmNc fmX H2.length ns hbns (by omega) (by decide) (by decide)
    (by decide) (by decide) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, hnsl])
    (fun EH1 w5 hpe1 hebn => ?_)
  -- the record
  have hok4 : CtxOK (ctxE (ctxH C H3) EH1) := ctxOK_E (ctxOK_H hok H3) hpe1
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ =>
    (pure (IConstantInfo.indInfo ms.declared (capsOf p ms isRec nz)) : AM _)) (by simp) ?_
  refine specR_callNC (C := ctxE (ctxH C H3) EH1) fmO fConstRec cwParams
    [vv fmDc, .const 3, vv fmE, vv fmAll, vv fmNp, vv fmNi, vv fmB, vv fmNz] (cwBody C)
    [cellA C od, 3, boolW (ms.ctors.length == 1 && ms.nIdx == 0 && !isRec), wAll, BitVec.ofNat 64 p.nP,
      BitVec.ofNat 64 ms.nIdx, ecell C C.EH.length, boolW nz]
    (by decide) rfl (by decide) hcw
    ⟨by simp +decide [sev, Env.get], rfl, by simp +decide [sev, Env.get],
      by simp +decide [sev, Env.get, fmParams, ctxEnv], by simp +decide [sev, Env.get, fmParams, ctxEnv],
      by simp +decide [sev, Env.get, fmParams, ctxEnv], by simp +decide [sev, Env.get] <;> rfl,
      by simp +decide [sev, Env.get, fmParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧
      PostCW (ctxE (ctxH C H3) EH1) ms.declared 3 [boolW (ms.ctors.length == 1 && ms.nIdx == 0 && !isRec), wAll,
        BitVec.ofNat 64 p.nP, BitVec.ofNat 64 ms.nIdx, ecell C C.EH.length, boolW nz] s a w s' st)
    (fun a w s' C' => s' = s ∧ ∃ EH2 o, C' = ctxE (ctxH C H3) EH2 ∧ EH1 <+: EH2 ∧ EH1.length ≤ o ∧ w = ecell C o ∧
      CVE C.EB EH2 (o + 1) ms.declared ∧ EH2[o]? = some 3 ∧
      (∀ j (hj : j < 6), EH2[o + 4 + j]? = some ([boolW (ms.ctors.length == 1 && ms.nIdx == 0 && !isRec), wAll,
        BitVec.ofNat 64 p.nP, BitVec.ofNat 64 ms.nIdx, ecell C C.EH.length, boolW nz] : List (BitVec 64))[j]))
    (fun a w s' st ⟨hr, h0, EH2, o, h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨_, ⟨pure_run_unit _ _ _ hr, EH2, o, rfl, h1, h2, h3, h4, h5, fun j hj => h6 j (by simpa using hj)⟩,
        by rw [pure_run_unit _ _ _ hr]; exact h7⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact cw_spec (ctxE (ctxH C H3) EH1) hok4 hcp ms.declared od (cvRep_mono hpH3 hcv) hlps 3 _ _ _ _ _ _ s _
        (pre_of_lookups hu cwParams _ rfl hlk)))
    (fun _ w6 s3 C3 ⟨hs3, EH2, o, eC3, hpe2, hol2, hw6, hcve, htg, hfs⟩ => ?_)
  subst eC3 hw6; subst s3
  have hl1 : C.EH.length ≤ EH1.length := hpe1.length_le
  have hol' : EH1.length ≤ o := hol2
  exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨H3, EH2, o, hpH3, hpe1.trans hpe2, by omega, rfl,
      ⟨hcve, htg, hfs 0 (by decide),
        ⟨wAll, hfs 1 (by decide), enlist_mono (hpe1.trans hpe2) hall⟩,
        ⟨hfs 2 (by decide), hnp⟩, ⟨hfs 3 (by decide), hni⟩,
        ⟨ecell C C.EH.length, hfs 4 (by decide), C.EH.length, rfl, by
          have h : EBlk EH2 C.EH.length ns := eblk_mono hebn hpe2
          simpa [ns, capsOf, List.map_map] using h⟩,
        hfs 5 (by decide)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The twin's block constants, effects first -/

/-- The formers' records from never-zero bits. -/
def formersOf (p : BlockShape) (isRec : Bool) (ms : List MemberShape) (nzs : List Bool) : List IConstantInfo :=
  (ms.zip nzs).map fun a => .indInfo a.1.declared (capsOf p a.1 isRec a.2)

theorem blockFormers_go (p : BlockShape) (isRec : Bool) :
    ∀ (l : List MemberShape) (k : Nat), l = p.members.drop k →
      ((l.map (·.declared)).zipIdx k).mapM (fun (a : IConstantVal × Nat) => do
          pure (IConstantInfo.indInfo a.1 (← blockCapsAt p a.2 isRec))) =
        (l.mapM fun ms => formerZ ms.declared >>= fun z => pure z.isNever) >>= fun nzs =>
          pure (formersOf p isRec l nzs)
  | [], k, _ => by simp [formersOf]
  | ms :: l, k, hl => by
    have hk : p.members[k]? = some ms := by
      have := congrArg List.head? hl
      simp [List.head?_drop] at this; exact this.symm
    have hl' : l = p.members.drop (k + 1) := by
      have := congrArg List.tail hl
      simpa [List.tail_drop] using this
    simp only [List.map_cons, List.zipIdx_cons, List.mapM_cons, bind_assoc, pure_bind]
    rw [blockCapsAt_eq p k isRec ms hk, bind_assoc]
    congr 1; funext z
    simp only [pure_bind]
    rw [blockFormers_go p isRec l (k + 1) hl']
    simp only [bind_assoc, pure_bind]
    rfl

theorem blockFormers_eq (p : BlockShape) (isRec : Bool) :
    blockFormers p isRec = (p.members.mapM fun ms => formerZ ms.declared >>= fun z => pure z.isNever) >>= fun nzs =>
      pure (formersOf p isRec p.members nzs) := by
  unfold blockFormers
  exact blockFormers_go p isRec p.members 0 (by simp)

/-- The recursors' records from their firing modes. -/
def recsOf (rcs : List RecShape) (fs : List IRecRuleFire) : List IConstantInfo :=
  (rcs.zip fs).map fun a => .recInfo a.1.cvR a.1.mI a.1.rP a.1.isK (a.1.rules.map ({ · with fire := a.2 }))

theorem blockRecs_eq (p : BlockShape) : ∀ rcs : List RecShape,
    blockRecs p rcs = (rcs.mapM (recFire p)) >>= fun fs => pure (recsOf rcs fs)
  | [] => by simp [blockRecs, recsOf]
  | rc :: rest => by
    simp only [blockRecs, List.mapM_cons, bind_assoc, pure_bind]
    congr 1; funext f
    rw [blockRecs_eq p rest]
    simp only [bind_assoc, pure_bind]
    rfl

end ConPanqueque.T.Ind
