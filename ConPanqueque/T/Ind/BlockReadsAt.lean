import ConPanqueque.T.Ind.BlockTable2

/-!
# `blockReadsAt` assembled

`ccBody`: the block's constructor count (the table's length needs it before any entry is written).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl

def ccMs := ofString "cc_ms"
def ccI := ofString "cc_i"
def ccK := ofString "cc_k"
def ccA := ofString "cc_a"
def ccO := ofString "cc_o"
def ccL := ofString "cc_l"
def ccNc := ofString "cc_nc"
def ccR := ofString "cc_r"
def fCtorCount := ofString "ctorCount"

def ccParams : List MlS := [ccMs, ccI, ccK, ccA]
def ccLocals : List MlS := [ccO, ccL, ccNc, ccR]

def ccBody : ProgHOL 64 := prologue ccLocals
  (.ite (.cmp .lower (vv ccI) (vv ccK))
    (.seq (.assign .local ccO (.load .one (.op .add [vv ccMs, .op .add [.panop .mul [vv ccI, .const 8], .const 8]])))
    (.seq (.assign .local ccL (.load .one (.op .add [vv ccO, .const 24])))
    (.seq (.assign .local ccNc (.load .one (vv ccL)))
    (.seq (.call (some (some (.local, ccR), none)) fCtorCount
      [vv ccMs, .op .add [vv ccI, .const 1], vv ccK, .op .add [vv ccA, vv ccNc]])
      (.return (vv ccR))))))
    (.return (vv ccA)))

theorem membersCtors_length (np : Nat) (ms : List MemberShape) :
    (membersCtors np ms).length = (ms.map (·.ctors.length)).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [membersCtors, ctorsOf] at ih ⊢ <;> omega

section
variable {σ : Type}

theorem cc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ccLocals → (ctxEnv C ++ ccParams.zip vals).get x = none :=
  Knot.params_none C ccLocals ccParams vals (by decide) (by decide)

/-- **`ctorCount`**: `a` plus the constructor counts from member `i`. -/
theorem cc_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fCtorCount = some (ccParams.map (fun p => (p, ShapeHOL.one)), ccBody, .one))
    (ms : List MemberShape) (om : Nat) (hms : PtrsRep C C.H om (MemberRep C C.H) ms) :
    ∀ k i a (H : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length → C.H <+: H →
      a + ((ms.drop i).map (·.ctors.length)).sum < 2 ^ 64 →
      SpecR (Pre (σ := σ) (ctxH C H) s (ccParams.zip [cellA C om, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length,
        BitVec.ofNat 64 a])) ccBody s (pure ())
        (fun _ w s' st => s' = s ∧ w = BitVec.ofNat 64 (a + ((ms.drop i).map (·.ctors.length)).sum) ∧
          ∃ H', H <+: H' ∧ SR (ctxH C H') s st) := by
  intro k
  induction k with
  | zero =>
    intro i a H s hk hi hp ha
    refine specR_prologue (fun _ _ _ _ _ ⟨h1, h2, H', hp', hs⟩ => ⟨h1, h2, H', hp', sr_of_eq hs rfl rfl rfl rfl⟩)
      (cc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hml : ms.length < 2 ^ 61 := by
      have h0 := (List.getElem?_eq_some_iff.mp (get_prefix hms.1 hp)).1
      rcases Nat.lt_or_ge 0 ms.length with h | h
      · obtain ⟨oc, h1, -⟩ := hms.2 (ms.length - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp (get_prefix h1 hp)).1; omega
      · omega
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, ccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ (BitVec.ofNat 64 a) (by simp +decide [Env.get, ccParams, ctxEnv])
      (fun t ht => ⟨rfl, by simp, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i a H s hk hi hp ha
    have hil : i < ms.length := by omega
    refine specR_prologue (fun _ _ _ _ _ ⟨h1, h2, H', hp', hs⟩ => ⟨h1, h2, H', hp', sr_of_eq hs rfl rfl rfl rfl⟩)
      (cc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hml : ms.length < 2 ^ 61 := by
      obtain ⟨oc, h1, -⟩ := hms.2 (ms.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp (get_prefix h1 hp)).1; omega
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oi, h1, hmr⟩ := hms.2 i hil
    obtain ⟨-, -, -, ⟨ol, hol, hcs⟩⟩ := hmr
    refine UD.specR_heapLoadI' (C := ctxH C H) ccO _ (om + 1 + i) _ (get_prefix h1 hp) (by decide)
      (by simp +decide [sev, Env.get, ccParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ccL _ (oi + 3) _ (get_prefix hol hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oi 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ccNc _ ol _ (get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hsum : ((ms.drop i).map (·.ctors.length)).sum = ms[i].ctors.length + ((ms.drop (i + 1)).map (·.ctors.length)).sum := by
      rw [List.drop_eq_getElem_cons hil, List.map_cons, List.sum_cons]
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ccR fCtorCount ccParams
      [vv ccMs, .op .add [vv ccI, .const 1], vv ccK, .op .add [vv ccA, vv ccNc]] ccBody
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length, BitVec.ofNat 64 (a + ms[i].ctors.length)]
      (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get, ccParams, ctxEnv], by simp +decide [sev, Env.get, ccParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get, ccParams, ctxEnv],
        by simp +decide [sev, Env.get, ccParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat], trivial⟩
      (fun _ w s' st => s' = s ∧ w = BitVec.ofNat 64 (a + ms[i].ctors.length + ((ms.drop (i + 1)).map (·.ctors.length)).sum) ∧
          ∃ H', H <+: H' ∧ SR (ctxH C H') s st)
      (fun _ w s' H' => s' = s ∧ w = BitVec.ofNat 64 (a + ms[i].ctors.length + ((ms.drop (i + 1)).map (·.ctors.length)).sum))
      (fun _ w s' st ⟨h1, h2, H', hp', hs⟩ => ⟨H', hp', ⟨h1, h2⟩, by subst h1; exact hs⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccParams _ rfl hlk)
        (ih (i + 1) (a + ms[i].ctors.length) H s (by omega) (by omega) hp (by omega)))
      (fun _ w s1 H1 hp1 ⟨hs1, hw⟩ => ?_)
    subst hw; subst s1
    exact specR_returnI _ (BitVec.ofNat 64 (a + ms[i].ctors.length + ((ms.drop (i + 1)).map (·.ctors.length)).sum))
      (by simp [Env.get])
      (fun t ht => ⟨rfl, by rw [hsum]; congr 1; omega, H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The twin, effects first -/

theorem blockReadsAt_eq (fe : IFEnv) (p : BlockShape) :
    blockReadsAt fe p = (do
      let isRec ← blockIsRec p
      let nzs ← p.members.mapM fun ms => formerZ ms.declared >>= fun z => pure z.isNever
      let fs1 ← p.recs.mapM (recFire p)
      let fs2 ← p.recs.mapM (recFire p)
      let cs := formersOf p isRec p.members nzs ++ membersCtors p.nP p.members ++ recsOf p.recs fs1
      let ok ← recsRead (consBlockRecsTemp cs fe []).1 (recsOf p.recs fs2)
      pure (ok, ((consBlockRecsTemp cs fe []).2.foldr (fun (x : NIdx × Option IConstantInfo) acc => acc.popTemp x.1 x.2)
        (consBlockRecsTemp cs fe []).1).setFlags fe.natLit fe.strLit)) := by
  unfold blockReadsAt blockConstants
  simp only [blockFormers_eq, blockRecs_eq, blockCtors_eq, bind_assoc, pure_bind]

/-! ## The program -/

def brS := ofString "br_s"
def brOm := ofString "br_om"
def brK := ofString "br_k"
def brOr := ofString "br_or"
def brNr := ofString "br_nr"
def brNp := ofString "br_np"
def brIr := ofString "br_ir"
def brNz := ofString "br_nz"
def brX2 := ofString "br_x2"
def brF1 := ofString "br_f1"
def brF2 := ofString "br_f2"
def brNc := ofString "br_nc"
def brNb := ofString "br_nb"
def brX1 := ofString "br_x1"
def brAll := ofString "br_all"
def brR1 := ofString "br_r1"
def brN := ofString "br_n"
def brT := ofString "br_t"
def brX3 := ofString "br_x3"
def brX4 := ofString "br_x4"
def brX5 := ofString "br_x5"
def brD := ofString "br_d"
def brX6 := ofString "br_x6"
def brOk := ofString "br_ok"
def fBlockReadsAt := ofString "blockReadsAt"

def brParams : List MlS := [brS]
def brLocals : List MlS := [brOm, brK, brOr, brNr, brNp, brIr, brNz, brX2, brF1, brF2, brNc, brNb, brX1, brAll, brR1,
  brN, brT, brX3, brX4, brX5, brD, brX6, brOk]

/-- `blockReadsAt` at the shape `brS`: phase A (recursiveness, never-zero bits, both firing-mode runs, the
constructor count), then phase B (the names' environment block, the block table, the recursors' block), then
`recsRead` through the table. -/
def brBody (C : Ctx) : ProgHOL 64 := prologue brLocals
  (.seq (.assign .local brOm (.load .one (vv brS)))
  (.seq (.assign .local brK (.load .one (vv brOm)))
  (.seq (.assign .local brOr (.load .one (.op .add [vv brS, .const 8])))
  (.seq (.assign .local brNr (.load .one (vv brOr)))
  (.seq (.assign .local brNp (.load .one (.op .add [vv brS, .const 16])))
  (guardP brK 58 (guardP brNr 58
  (.seq (.call (some (some (.local, brIr), none)) fBlockIsRec [vv brOm, vv brK])
  (allocP C brNz (.shift .lsl (.op .add [vv brK, .const 1]) (.const 3))
  (.seq (.store (vv brNz) (vv brK))
  (.seq (.call (some (some (.local, brX2), none)) fZfFill [vv brOm, vv brNz, .const 0, vv brK])
  (.seq (.call (some (some (.local, brF1), none)) fFfFill [vv brOr, .const 0, vv brNr, vv brK])
  (.seq (.call (some (some (.local, brF2), none)) fFfFill [vv brOr, .const 0, vv brNr, vv brK])
  (.seq (.call (some (some (.local, brNc), none)) fCtorCount [vv brOm, .const 0, vv brK, .const 0])
  (guardP brNc 58
  (allocP C brNb (.shift .lsl (.op .add [vv brK, .const 1]) (.const 3))
  (.seq (.store (vv brNb) (vv brK))
  (.seq (.call (some (some (.local, brX1), none)) fNmFill [vv brOm, vv brNb, .const 0, vv brK])
  (envBlkP C brAll brNb brK brR1
  (.seq (.assign .local brN (.op .add [.op .add [vv brK, vv brNc], vv brNr]))
  (allocP C brT (.shift .lsl (.op .add [.shift .lsl (vv brN) (.const 1), .const 1]) (.const 3))
  (.seq (.store (vv brT) (vv brN))
  (.seq (.call (some (some (.local, brX3), none)) fTfFill
    [vv brOm, vv brNz, vv brT, .const 0, .const 0, vv brK, vv brIr, vv brAll, vv brNp])
  (.seq (.call (some (some (.local, brX4), none)) fTmFill [vv brOm, vv brT, vv brK, .const 0, vv brK, vv brNp])
  (.seq (.call (some (some (.local, brX5), none)) fTqFill
    [vv brOr, vv brF1, vv brT, .op .add [vv brK, vv brNc], .const 0, vv brNr])
  (allocP C brD (.shift .lsl (.op .add [vv brNr, .const 1]) (.const 3))
  (.seq (.store (vv brD) (vv brNr))
  (.seq (.call (some (some (.local, brX6), none)) fTxFill [vv brOr, vv brF2, vv brD, .const 0, vv brNr])
  (.seq (.call (some (some (.local, brOk), none)) fRecsRead [vv brT, vv brD, .const 0])
    (.return (vv brOk)))))))))))))))))))))))))))))))

/-! ## Facts the assembly needs -/

theorem exists_list_of_forall {P : Nat → Nat → Prop} : ∀ n : Nat, (∀ j, j < n → ∃ o, P j o) →
    ∃ os : List Nat, os.length = n ∧ ∀ j, j < n → P j (os.getD j 0)
  | 0, _ => ⟨[], rfl, fun j hj => absurd hj (by omega)⟩
  | n + 1, h => by
    obtain ⟨os, hl, hos⟩ := exists_list_of_forall n (fun j hj => h j (by omega))
    obtain ⟨o, ho⟩ := h n (by omega)
    refine ⟨os ++ [o], by simp [hl], fun j hj => ?_⟩
    rcases Nat.lt_or_ge j n with h' | h'
    · have : (os ++ [o]).getD j 0 = os.getD j 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < os.length by omega)]
      rw [this]; exact hos j h'
    · have e : j = n := by omega
      subst e
      have : (os ++ [o]).getD j 0 = o := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show os.length ≤ j by omega), hl]
      rw [this]; exact ho

/-- A constant's own data denote (the parts of `ConstDen` a block constant needs). -/
def CVDen (cv : IConstantVal) (st : EStore) : Prop :=
  (∀ n ∈ cv.levelParams, (denoteN st.ns n).isSome = true) ∧ (denoteE st cv.type).isSome = true ∧
    cv.levelParams.length + 1 < 2 ^ 60

theorem cvDen_ext {cv : IConstantVal} {st st' : EStore} (h : CVDen cv st) (hx : Ext st st') : CVDen cv st' :=
  ⟨fun n hn => denoteN_isSome_ext hx (h.1 n hn), denoteE_isSome_ext hx h.2.1, h.2.2⟩

/-- The block constants' `ConstDen` clauses. -/
def BlockDen (cs : List IConstantInfo) (st : EStore) : Prop :=
  ∀ ci ∈ cs, CVDen ci.toConstantVal st ∧ (∀ cv v hint, ci = .defnInfo cv v hint → (denoteE st v).isSome = true) ∧
    (∀ cv caps, ci = .indInfo cv caps → caps.nparams + caps.nIdx < 2 ^ 63)

theorem constDen_bfLook {es : List (NIdx × Nat × IConstantInfo)} {fe : IFEnv} {fe' : IFEnv} {st : EStore}
    (hfe : ∀ n, fe'.find? n = bfLook es fe n) (hd : ConstDen fe st) (hb : BlockDen (es.map (·.2.2)) st) :
    ConstDen fe' st := by
  intro c ci hc
  rw [hfe] at hc
  unfold bfLook at hc
  cases hf : es.reverse.find? (fun e => e.1 == c) with
  | none => rw [hf] at hc; exact hd c ci hc
  | some e =>
    rw [hf] at hc
    cases hc
    have hm : e ∈ es := List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
    obtain ⟨h1, h2, h3⟩ := hb e.2.2 (List.mem_map.mpr ⟨e, hm, rfl⟩)
    exact ⟨h1.1, h1.2.1, h1.2.2, h2, h3⟩

end ConPanqueque.T.Ind
