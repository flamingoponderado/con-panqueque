import ConPanqueque.T.Ind.BlockIsRec
import ConPanqueque.T.Ind.SumCtor
import ConPanqueque.T.Decl.NameNodup

/-!
# The constructors' names distinct

`cnfBody`: the constructors' names (a `CtorsRep` block) into a fresh block; `cnnBody`: that block's
`nameNodup`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl

def cnfQ := ofString "cnf_q"
def cnfD := ofString "cnf_d"
def cnfI := ofString "cnf_i"
def cnfK := ofString "cnf_k"
def cnfX := ofString "cnf_x"
def cnfY := ofString "cnf_y"
def cnfR := ofString "cnf_r"
def fCnFillN := ofString "ctorNamesFill"

def cnfParams : List MlS := [cnfQ, cnfD, cnfI, cnfK]
def cnfLocals : List MlS := [cnfX, cnfY, cnfR]

/-- The constructors' names (a `CtorsRep` block at `cnfQ`, from `cnfI`) into the block at `cnfD`. -/
def cnfBody : ProgHOL 64 := prologue cnfLocals
  (.ite (.cmp .lower (vv cnfI) (vv cnfK))
    (.seq (.assign .local cnfX (.load .one (.op .add [vv cnfQ, .op .add [.panop .mul [vv cnfI, .const 16], .const 8]])))
    (.seq (.assign .local cnfY (.load .one (vv cnfX)))
    (.seq (.store (.op .add [vv cnfD, .op .add [.panop .mul [vv cnfI, .const 8], .const 8]]) (vv cnfY))
    (.seq (.call (some (some (.local, cnfR), none)) fCnFillN [vv cnfQ, vv cnfD, .op .add [vv cnfI, .const 1], vv cnfK])
      (.return (.const 0))))))
    (.return (.const 0)))

def cnnQ := ofString "cnn_q"
def cnnK := ofString "cnn_k"
def cnnNb := ofString "cnn_nb"
def cnnX := ofString "cnn_x"
def cnnR := ofString "cnn_r"
def fCnn := ofString "ctorNamesNodup"

def cnnParams : List MlS := [cnnQ, cnnK]
def cnnLocals : List MlS := [cnnNb, cnnX, cnnR]

/-- `nameNodup` of the constructors' names (a `CtorsRep` block at `cnnQ` of `cnnK` constructors). -/
def cnnBody (C : Ctx) : ProgHOL 64 := prologue cnnLocals
  (guardP cnnK 58
  (allocP C cnnNb (.shift .lsl (.op .add [vv cnnK, .const 1]) (.const 3))
  (.seq (.store (vv cnnNb) (vv cnnK))
  (.seq (.call (some (some (.local, cnnX), none)) fCnFillN [vv cnnQ, vv cnnNb, .const 0, vv cnnK])
  (.seq (.call (some (some (.local, cnnR), none)) fNdg [vv cnnNb, .const 0, vv cnnK])
    (.return (vv cnnR)))))))

structure CNNCodes (C : Ctx) : Prop where
  fill : C.code.lookup fCnFillN = some (cnfParams.map (fun p => (p, ShapeHOL.one)), cnfBody, .one)
  ndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  ndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
  self : C.code.lookup fCnn = some (cnnParams.map (fun p => (p, ShapeHOL.one)), cnnBody C, .one)

section
variable {σ : Type}

/-- The names from position `i` on, past the frozen prefix `Hc`. -/
def PostCNF (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (ms : List (IConstantVal × Nat)) (i : Nat) (_ : Unit) (_ : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧
    ∀ j (hj : j < ms.length), i ≤ j → H'[o + 1 + j]? = some (Enc.idxW ms[j].1.name)

theorem postCNF_locals (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (ms : List (IConstantVal × Nat)) (i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCNF C Hc o ms i a w s' st → PostCNF C Hc o ms i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem cnf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnfLocals → (ctxEnv C ++ cnfParams.zip vals).get x = none :=
  Knot.params_none C cnfLocals cnfParams vals (by decide) (by decide)

/-- **The constructor-names fill** from position `i`. -/
theorem cnf_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fCnFillN = some (cnfParams.map (fun p => (p, ShapeHOL.one)), cnfBody, .one))
    (ms : List (IConstantVal × Nat)) (om o : Nat) (H0 : List (BitVec 64)) (hms : CtorsRep C H0 om ms) (hcl : ms.length < 2 ^ 58) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length → H0 <+: Hc →
      Hc.length ≤ o + 1 + i → Hc <+: H → o + 1 + ms.length ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (cnfParams.zip [cellA C om, cellA C o, BitVec.ofNat 64 i,
        BitVec.ofNat 64 ms.length])) cnfBody s (pure ()) (PostCNF C Hc o ms i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi h0 hHc hp hl
    refine specR_prologue (postCNF_locals _ _ _ _ _) (cnf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, cnfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc s hk hi h0 hHc hp hl
    have hil : i < ms.length := by omega
    refine specR_prologue (postCNF_locals _ _ _ _ _) (cnf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cnfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨oc, h1, hcv, -⟩ := hms.2 i hil
    refine UD.specR_heapLoadI' (C := ctxH C H) cnfX _ (om + 1 + 2 * i) _ (ConPanqueque.T.Decl.get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, cnfParams, ctxEnv]; exact cellA_pair1 C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnfY _ oc _ (ConPanqueque.T.Decl.get_prefix hcv.1 h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hj : o + 1 + i < (ctxH C H).H.length := by show o + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_H hok H) _ (vv cnfY) (o + 1 + i) hj (Enc.idxW ms[i].1.name)
      (by simp +decide [sev, Env.get_cons, Env.get, cnfParams, ctxEnv]; exact cellA_mulIdx C o i (by omega))
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H.set (o + 1 + i) (Enc.idxW ms[i].1.name))) _ _ _ _) _ _ _ _
    generalize hB : H.set (o + 1 + i) (Enc.idxW ms[i].1.name) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[o + 1 + i]? = some (Enc.idxW ms[i].1.name) := by rw [← hB, List.getElem?_set_self (by omega)]
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
    refine specR_callNIG (C := ctxH C B) cnfR fCnFillN cnfParams [vv cnfQ, vv cnfD, .op .add [vv cnfI, .const 1], vv cnfK]
      cnfBody [cellA C om, cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cnfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnfParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cnfParams, ctxEnv], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostCNF C Hc' o ms (i + 1) a w s' st)
      (fun a w s' H' => s' = s ∧ Hc' <+: H' ∧
        ∀ j (hj : j < ms.length), i + 1 ≤ j → H'[o + 1 + j]? = some (Enc.idxW ms[j].1.name))
      (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) B Hc' s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega) _
          (pre_of_lookups hu cnfParams _ rfl hlk)))
      (fun a w s' H' ⟨hs', hp', hc'⟩ => ?_)
    subst hs'
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
      rcases Nat.lt_or_ge i j with h | h
      · exact hc' j hj (by omega)
      · have e : j = i := by omega
        subst e
        have := ConPanqueque.T.Decl.get_prefix (show Hc'[o + 1 + j]? = some (Enc.idxW ms[j].1.name) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'
        exact this⟩)


theorem cnn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnnLocals → (ctxEnv C ++ cnnParams.zip vals).get x = none :=
  Knot.params_none C cnnLocals cnnParams vals (by decide) (by decide)

/-- **`nameNodup` of the constructors' names** at the block's members. -/
theorem cnn_spec (C : Ctx) (hok : CtxOK C) (hc : CNNCodes C)
    (cs : List (IConstantVal × Nat)) (om : Nat) (hms : CtorsRep C C.H om cs) (hcl : cs.length < 2 ^ 58)
    (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (cnnParams.zip [cellA C om, BitVec.ofNat 64 cs.length])) (cnnBody C) s
      (pure (nameNodup (cs.map (·.1.name)))) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (cnn_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  refine specR_guardI cnnK cs.length 58 (by decide) (by simp +decide [Env.get, cnnParams, ctxEnv]) (by omega)
    (fun hm58 => ?_)
  refine specR_allocI (C := ctxH C H) cnnNb _ (cs.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get_cons, Env.get, cnnParams, ctxEnv]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : H <+: H2 := hp2
  have hq0 : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv cnnNb) (vv cnnK) H2.length hq0 (BitVec.ofNat 64 cs.length)
    (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons, Env.get, cnnParams, ctxEnv]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 cs.length))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 cs.length) = B
  have hBlen : B.length = H2.length + (cs.length + 1) := by rw [← hB]; simp [hws]
  have hpB : H2 <+: B := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc := B.take (H2.length + 1)
  have hpc : H2 <+: Hc := by
    refine prefix_of_get? (by simp [Hc]; omega) (fun j hj => ?_)
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
  refine specR_pureBind () ?_
  refine specR_callNIG (C := ctxH C B) cnnX fCnFillN cnfParams [vv cnnQ, vv cnnNb, .const 0, vv cnnK] cnfBody
    [cellA C om, cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 cs.length] (by decide) rfl (by decide) hc.fill
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cnnParams, ctxEnv], by simp +decide [sev, Env.get_cons]; rfl, rfl,
      by simp +decide [sev, Env.get_cons, Env.get, cnnParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostCNF C Hc H2.length cs 0 a w s' st)
    (fun a w s' H' => s' = s ∧ Hc <+: H' ∧
      ∀ j (hj : j < cs.length), 0 ≤ j → H'[H2.length + 1 + j]? = some (Enc.idxW cs[j].1.name))
    (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact cnf_spec C hok hc.fill cs om H2.length C.H hms hcl _ 0 B Hc s rfl (Nat.zero_le _)
        (hp.trans (hp2'.trans hpc)) (by simp [Hc]) (List.take_prefix _ _) (by omega) _
        (pre_of_lookups hu cnfParams _ rfl hlk)))
    (fun a w s' H3 ⟨hs', hp3, hc3⟩ => ?_)
  subst s'
  have hp3' : H <+: H3 := hp2'.trans (hpc.trans hp3)
  have hns : BlkAt H3 H2.length ((cs.map (·.1.name)).map Enc.idxW) := by
    refine ⟨?_, fun j hj => ?_⟩
    · have h0 : B[H2.length]? = some (BitVec.ofNat 64 cs.length) := by
        rw [← hB, List.getElem?_set_self (by simp; omega)]
      have h0' : Hc[H2.length]? = some (BitVec.ofNat 64 cs.length) := by
        simp only [Hc]; rw [List.getElem?_take_of_lt (by omega)]; exact h0
      simpa using ConPanqueque.T.Decl.get_prefix h0' hp3
    · simp only [List.length_map] at hj
      simp only [List.map_map, List.getElem_map, Function.comp]
      exact hc3 j hj (Nat.zero_le _)
  refine specR_congr (m' := (pure (nameNodup ((cs.map (·.1.name)).drop 0)) : AM Bool) >>= fun r => pure r)
    (by rw [List.drop_zero, bind_pure]) ?_
  refine specR_callNIH (C := ctxH C H3) cnnR fNdg ndgParams [vv cnnNb, .const 0, vv cnnK] ndgBody
    [cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 (cs.map (·.1.name)).length] (by decide) rfl (by decide) hc.ndg
    ⟨by simp +decide [sev, Env.get_cons]; rfl, rfl,
      by simp +decide [sev, Env.get_cons, Env.get, cnnParams, ctxEnv], trivial⟩
    (PostB (ctxH C H3)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
      (ndg_spec C hc.ndh hc.ndg (cs.map (fun x => x.1.name)) H2.length (by simp; omega) _ 0 H3 s (hp.trans hp3')
        hns rfl (Nat.zero_le _)))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  have hp4' : H3 <+: H4 := hp4
  exact specR_returnI _ _ (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H4, hp3'.trans hp4', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
