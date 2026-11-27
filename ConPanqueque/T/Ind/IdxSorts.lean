import ConPanqueque.T.Ind.CheckPos

/-!
# `checkBlockIdxSorts` (single-member blocks)

The member's telescope opened at variables from `0`, its index binders (the opened variables past the
parameters, `drop nP` through `appendBlock` onto an empty block) checked by `checkStructFieldSortsI` (a
proposition-sorted block, no bound).  A telescope that does not open, or opens to fewer than `nP` variables,
hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def bisMs := ofString "bis_ms"
def bisNP := ofString "bis_np"
def bisSr := ofString "bis_sr"
def bisP0 := ofString "bis_p0"
def bisQ := ofString "bis_q"
def bisNi := ofString "bis_ni"
def bisTy := ofString "bis_ty"
def bisX := ofString "bis_x"
def bisFv := ofString "bis_fv"
def bisL := ofString "bis_l"
def bisE0 := ofString "bis_e0"
def bisD := ofString "bis_d"
def bisE1 := ofString "bis_e1"
def bisU := ofString "bis_u"
def fBis := ofString "checkBlockIdxSorts"

def bisParams : List MlS := [bisMs, bisNP, bisSr]
def bisLocals : List MlS := [bisP0, bisQ, bisNi, bisTy, bisX, bisFv, bisL, bisE0, bisD, bisE1, bisU]

def bisBody (C : Ctx) : ProgHOL 64 := prologue bisLocals
  (.seq (.assign .local bisP0 (.load .one (.op .add [vv bisMs, .const 8])))
  (.seq (.assign .local bisQ (.load .one (vv bisP0)))
  (.seq (.assign .local bisNi (.load .one (.op .add [vv bisP0, .const 16])))
  (.seq (.assign .local bisTy (.load .one (.op .add [vv bisQ, .const 16])))
  (.seq (.call (some (some (.local, bisX), none)) fOpenFvars [.op .add [vv bisNP, vv bisNi], vv bisTy, .const 0])
  (.ite (.cmp .equal (vv bisX) (.const 0)) hang
  (.seq (.assign .local bisFv (.load .one (vv bisX)))
  (.seq (.assign .local bisL (.load .one (vv bisFv)))
  (.ite (.cmp .equal (vv bisL) (.op .add [vv bisNP, vv bisNi]))
    (alloc1 C bisE0 (.const 0)
    (.seq (.call (some (some (.local, bisD), none)) fCat [vv bisE0, vv bisFv, vv bisNP])
    (alloc1 C bisE1 (.const 0)
    (.seq (.call (some (some (.local, bisU), none)) fFieldSorts
        [vv bisD, vv bisE1, .const 0, vv bisSr, vv bisNP, .const 1, .const 0, vv bisNi])
      (.return (.const 0))))))
    hang)))))))))

theorem bis_eadd (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

structure BISCodes (C : Ctx) : Prop where
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  cat : CatCodes C
  fs : FSCodes C
  self : C.code.lookup fBis = some (bisParams.map (fun p => (p, ShapeHOL.one)), bisBody C, .one)

section
variable {σ : Type}

theorem bis_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bisLocals → (ctxEnv C ++ bisParams.zip vals).get x = none :=
  Knot.params_none C bisLocals bisParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`checkBlockIdxSorts`** at one member, whose record the cell at `om + 1` points to. -/
theorem bis_spec1 (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : BISCodes C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (p : BlockShape) (ms0 : MemberShape) (om : Nat)
    (hslot : ∃ o0, C.H[om + 1]? = some (cellA C o0) ∧ MemberRep C C.H o0 ms0) (lsr : ConLeche.Level)
    (hSd : denoteL C.St.ls p.resSort = some lsr)
    (hnP : p.nP < 2 ^ 56) (hni : ms0.nIdx < 2 ^ 56) (s : AState) :
    SpecR (σ := σ) (Pre C s (bisParams.zip [cellA C om, BitVec.ofNat 64 p.nP, Enc.idxW p.resSort])) (bisBody C) s
      (checkBlockIdxSorts mode C.fe p [ms0]) (Decl.PostU C) := by
  refine specR_prologue (Decl.postU_locals _) (bis_none _ _) ?_
  obtain ⟨o0, ho0, hrep⟩ := hslot
  obtain ⟨⟨oc, hoc, hcv⟩, -, hnI, -⟩ := hrep
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine UD.specR_heapLoadI' (C := ctxH C C.H) bisP0 _ (om + 1) _ ho0 (by decide)
    (by simp +decide [sev, Env.get, bisParams, ctxEnv]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) bisQ (vv bisP0) o0 _ hoc (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) bisNi _ (o0 + 2) _ hnI (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C o0 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) bisTy _ (oc + 2) _ hcv.2.2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
  simp only [checkBlockIdxSorts, bind_assoc]
  refine specR_callNIH (C := ctxH C C.H) bisX fOpenFvars ofParams [.op .add [vv bisNP, vv bisNi], vv bisTy, .const 0]
    (ofBody C) [BitVec.ofNat 64 (p.nP + ms0.nIdx), Enc.idxW ms0.cvT.type, BitVec.ofNat 64 0] (by decide) rfl
    (by decide) hc.ofc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, bisParams, ctxEnv]; exact bis_eadd p.nP ms0.nIdx,
      by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostOF (ctxH C C.H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op (p.nP + ms0.nIdx) ms0.cvT.type 0 (by omega) (by omega) C.H hp0 s))
    (fun o w s2 H2 hp2 ⟨hn, hsm⟩ => ?_)
  have hp2' : C.H <+: H2 := hp2
  rcases o with _ | ⟨fvs, e'⟩
  · have e0 := hn rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, oa, rfl, hob, hoe, hfb⟩ := hsm fvs e' rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol : ob < H2.length := (List.getElem?_eq_some_iff.mp hob).1
  have hHN' : H2.length ≤ C.HN := hHN
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [unwrapOr, pure_bind]
  refine UD.specR_heapLoadI' (C := ctxH C H2) bisFv (vv bisX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfl : H2[oa]? = some (BitVec.ofNat 64 fvs.length) := by simpa using hfb.1
  refine UD.specR_heapLoadI' (C := ctxH C H2) bisL (vv bisFv) oa _ hfl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfvl : fvs.length < 2 ^ 63 := by
    rcases Nat.eq_zero_or_pos fvs.length with h0 | hpos
    · omega
    · have h1 := hfb.2 (fvs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      have hlay := hok.heapLay
      omega
  by_cases hge : fvs.length = p.nP + ms0.nIdx
  swap
  · have hneq : BitVec.ofNat 64 fvs.length ≠ BitVec.ofNat 64 (p.nP + ms0.nIdx) := fun h => hge (by
      have := congrArg BitVec.toNat h; simp at this; omega)
    exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, bisParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bis_eadd]; exact hneq) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, bisParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bis_eadd, hge]) (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_alloc1I (ctxOK_H hok H2) bisE0 (.const 0) 0 (by decide) (fun _ => rfl) (fun H3 ws3 hp3 hws3 => ?_)
  have g3 : ((H3 ++ ws3).set H3.length 0)[H3.length]? = some 0 := by simp [List.getElem?_set, hws3]
  have hp3' : H2 <+: _ := (hp3 : H2 <+: H3).trans (img1_prefix H3 ws3 0 hws3)
  have he0 : BlkAt ((H3 ++ ws3).set H3.length 0) H3.length ([] : List (BitVec 64)) :=
    ⟨by simpa using g3, fun i hi => by simp at hi⟩
  refine specR_callPure (C := ctxH C _) bisD fCat catParams [vv bisE0, vv bisFv, vv bisNP] catBody
    [cellA C H3.length, cellA C oa, BitVec.ofNat 64 p.nP] ([] ++ (fvs.map Enc.idxW).drop p.nP) (by decide) rfl
    (by decide) hc.cat.self
    ⟨by simp [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, bisParams, ctxEnv], trivial⟩
    (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s2 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C hok hc.cat (fvs.map Enc.idxW) oa (by simp; omega) _ p.nP [] H3.length _ s2 rfl
        (by simp; omega) he0 (blkAt_mono hfb hp3')))
    (fun w H4 hp4 ⟨o4, hw4, hb4⟩ => ?_)
  subst hw4
  have hp4' : _ <+: H4 := hp4
  have hdb : BlkAt H4 o4 ((fvs.drop p.nP).map Enc.idxW) := by simpa [List.map_drop] using hb4
  refine specR_alloc1I (ctxOK_H hok H4) bisE1 (.const 0) 0 (by decide) (fun _ => rfl) (fun H5 ws5 hp5 hws5 => ?_)
  have g5 : ((H5 ++ ws5).set H5.length 0)[H5.length]? = some 0 := by simp [List.getElem?_set, hws5]
  have hp5' : H4 <+: _ := (hp5 : H4 <+: H5).trans (img1_prefix H5 ws5 0 hws5)
  have he1 : BlkAt ((H5 ++ ws5).set H5.length 0) H5.length (([] : List EIdx).map Enc.idxW) :=
    ⟨by simpa using g5, fun i hi => by simp at hi⟩
  have hpC5 : C.H <+: ((H5 ++ ws5).set H5.length 0) := ((hp2'.trans hp3').trans hp4').trans hp5'
  refine specR_callNIH (C := ctxH C _) bisU fFieldSorts fsParams
    [vv bisD, vv bisE1, .const 0, vv bisSr, vv bisNP, .const 1, .const 0, vv bisNi] (fsBody C)
    [cellA C o4, cellA C H5.length, BitVec.ofNat 64 0, Enc.idxW p.resSort, BitVec.ofNat 64 p.nP, boolW true,
      boolW false, BitVec.ofNat 64 ms0.nIdx] (by decide) rfl (by decide) hc.fs.self
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, rfl,
      (by simp +decide [sev, Env.get_cons, Env.get, bisParams, ctxEnv]),
      (by simp +decide [sev, Env.get_cons, Env.get, bisParams, ctxEnv]), rfl, rfl,
      by simp +decide [sev, Env.get_cons], trivial⟩
    (Decl.PostU (ctxH C _)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fsParams _ rfl hlk)
      (fs_spec mode ra C hok hs hk hac hc.fs heqS true false p.resSort lsr hSd p.nP (fvs.drop p.nP) [] 0 (by simp)
        o4 H5.length ms0.nIdx _ s2 (by omega) hpC5 (blkAt_mono hdb hp5') he1))
    (fun r w s4 H6 hp6 _ => ?_)
  have hp6' : _ <+: H6 := hp6
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H6, hpC5.trans hp6', sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`checkBlockIdxSorts`** on a single-member block. -/
theorem bis_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : BISCodes C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (p : BlockShape) (ms0 : MemberShape) (hms : p.members = [ms0]) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) [ms0]) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls p.resSort = some lsr)
    (hnP : p.nP < 2 ^ 56) (hni : ms0.nIdx < 2 ^ 56) (s : AState) :
    SpecR (σ := σ) (Pre C s (bisParams.zip [cellA C om, BitVec.ofNat 64 p.nP, Enc.idxW p.resSort])) (bisBody C) s
      (checkBlockIdxSorts mode C.fe p p.members) (Decl.PostU C) := by
  rw [hms]
  obtain ⟨o0, ho0, hrep⟩ := hM.2 0 (by simp)
  exact bis_spec1 mode ra C hok hs hk hac hc heqS p ms0 om ⟨o0, by simpa using ho0, by simpa using hrep⟩ lsr hSd hnP hni s

end

end ConPanqueque.T.Ind
