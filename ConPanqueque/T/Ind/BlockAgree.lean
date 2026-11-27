import ConPanqueque.T.Ind.BlockTeles

/-!
# `checkBlockAgree` at any number of members

`cagBody(om, i, n, nP, ty0, s0, lst)`: for member `i` (its sort the head of the linked list `lst`, `SLink`):
member 0's type and member `i`'s opened at `nP` fresh variables (`openPisAtFvarsF`), the two telescopes of equal
length, member 0's domains (`fvarTypeDs`, into a block), member `i`'s domains defeq to them (`checkStructDomsAt`,
whose successful runs are `checkBlockDomsAt`'s: `cbd_of_csd`), the sort equal to member 0's (`lvlEq?` answering
`some true`; anything else hangs), then itself at `i + 1`. `cag_spec` refines
`checkBlockAgree mode fe nP cv0 s0 rs` for the tele loop's `rs` (`PostCTL`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## The twin: `checkStructDomsAt` succeeds only where `checkBlockDomsAt` does -/

theorem am_bindInv {α β : Type} {m : AM α} {k : α → AM β} {s : AState} {a : β} {s' : AState}
    (h : (m >>= k) s = .ok (a, s')) : ∃ b s1, m s = .ok (b, s1) ∧ k b s1 = .ok (a, s') := by
  simp only [bind, StateT.bind] at h
  cases hm : m s with
  | error e => rw [hm] at h; cases h
  | ok p => obtain ⟨b, s1⟩ := p; rw [hm] at h; exact ⟨b, s1, rfl, h⟩

theorem am_bindRun {α β : Type} {x : AM α} {f : α → AM β} {s s1 : AState} {a : α} (h : x s = .ok (a, s1)) :
    (x >>= f) s = f a s1 := by simp only [bind, StateT.bind, h]; rfl

theorem am_bind_okMono {α β : Type} {m1 m2 : AM α} {k : α → AM β}
    (h : ∀ s a s', m2 s = .ok (a, s') → m1 s = .ok (a, s')) :
    ∀ s b s', (m2 >>= k) s = .ok (b, s') → (m1 >>= k) s = .ok (b, s') := by
  intro s b s' h2
  obtain ⟨a, s1, h1, h2⟩ := am_bindInv h2
  rw [am_bindRun (h s a s1 h1)]; exact h2

theorem cbd_of_csd (mode : ConLeche.CheckMode) (fe : IFEnv) (off : Nat) (fvs doms : List EIdx) :
    ∀ j s a s', checkStructDomsAt mode fe off fvs doms j s = .ok (a, s') →
      checkBlockDomsAt mode fe off fvs doms j s = .ok (a, s') := by
  intro j
  induction j with
  | zero => intro s a s' h; exact h
  | succ j ih =>
    intro s a s' h
    simp only [checkStructDomsAt, checkBlockDomsAt] at h ⊢
    rcases hx : fvs[j]? with _ | x
    · simp only [hx, unwrapOr] at h; cases h
    rcases hy : doms[j]? with _ | y
    · simp only [hx, hy, unwrapOr, pure_bind] at h; cases h
    simp only [hx, hy, unwrapOr, pure_bind] at h ⊢
    obtain ⟨t, s1, h1, h2⟩ := am_bindInv h
    rw [am_bindRun h1]
    obtain ⟨b, s2, h3, h4⟩ := am_bindInv h2
    rw [am_bindRun h3]
    cases b
    · simp at h4; cases h4
    · simp only [↓reduceIte] at h4 ⊢
      exact ih _ _ _ h4

/-- A spec for a twin with fewer successful runs is a spec for one with more. -/
theorem specR_okMonoA {σ α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m m' : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (hm : ∀ a s', m' s = .ok (a, s') → m s = .ok (a, s'))
    (h : SpecR P c s m' R) : SpecR P c s m R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a, s', hm', hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', hm a s' hm', hq⟩

/-! ## The loop -/

def cagOm := ofString "cag_om"
def cagI := ofString "cag_i"
def cagN := ofString "cag_n"
def cagNP := ofString "cag_np"
def cagTy0 := ofString "cag_ty0"
def cagS0 := ofString "cag_s0"
def cagLst := ofString "cag_lst"
def cagA := ofString "cag_a"
def cagMi := ofString "cag_mi"
def cagOc := ofString "cag_oc"
def cagTy := ofString "cag_ty"
def cagB := ofString "cag_b"
def cagFa0 := ofString "cag_fa0"
def cagFa := ofString "cag_fa"
def cagL0 := ofString "cag_l0"
def cagLa := ofString "cag_la"
def cagDm := ofString "cag_dm"
def cagX := ofString "cag_x"
def cagSv := ofString "cag_sv"
def cagO := ofString "cag_o"
def cagNx := ofString "cag_nx"
def fCag := ofString "checkBlockAgreeAll"

def cagParams : List MlS := [cagOm, cagI, cagN, cagNP, cagTy0, cagS0, cagLst]
def cagLocals : List MlS := [cagA, cagMi, cagOc, cagTy, cagB, cagFa0, cagFa, cagL0, cagLa, cagDm, cagX, cagSv, cagO,
  cagNx]

def cagBody (C : Ctx) : ProgHOL 64 := prologue cagLocals
  (.ite (.cmp .lower (vv cagI) (vv cagN))
    (.seq (.call (some (some (.local, cagA), none)) fOpenFvars [vv cagNP, vv cagTy0, .const 0])
    (.ite (.cmp .equal (vv cagA) (.const 0)) hang
    (.seq (.assign .local cagMi (.load .one (.op .add [vv cagOm, .op .add [.panop .mul [vv cagI, .const 8], .const 8]])))
    (.seq (.assign .local cagOc (.load .one (vv cagMi)))
    (.seq (.assign .local cagTy (.load .one (.op .add [vv cagOc, .const 16])))
    (.seq (.call (some (some (.local, cagB), none)) fOpenFvars [vv cagNP, vv cagTy, .const 0])
    (.ite (.cmp .equal (vv cagB) (.const 0)) hang
    (.seq (.assign .local cagFa0 (.load .one (vv cagA)))
    (.seq (.assign .local cagFa (.load .one (vv cagB)))
    (.seq (.assign .local cagL0 (.load .one (vv cagFa0)))
    (.seq (.assign .local cagLa (.load .one (vv cagFa)))
    (.ite (.cmp .notEqual (vv cagLa) (vv cagL0)) hang
    (guardP cagL0 56
    (allocP C cagDm (.shift .lsl (.op .add [vv cagL0, .const 1]) (.const 3))
    (.seq (.store (vv cagDm) (vv cagL0))
    (.seq (.call (some (some (.local, cagX), none)) fFtdFill [vv cagFa0, .op .add [vv cagDm, .const 8], .const 0, vv cagL0])
    (.seq (.call (some (some (.local, cagX), none)) fSdoms [vv cagFa, vv cagDm, .const 0, vv cagNP])
    (.seq (.assign .local cagSv (.load .one (vv cagLst)))
    (.seq (.call (some (some (.local, cagO), none)) LLeq.fEqv [vv cagSv, vv cagS0])
    (.ite (.cmp .equal (vv cagO) (.const 2))
      (.seq (.assign .local cagNx (.load .one (.op .add [vv cagLst, .const 8])))
      (.seq (.call (some (some (.local, cagX), none)) fCag
          [vv cagOm, .op .add [vv cagI, .const 1], vv cagN, vv cagNP, vv cagTy0, vv cagS0, vv cagNx])
        (.return (.const 0))))
      hang))))))))))))))))))))
    (.return (.const 0)))

structure CAGCodes (C : Ctx) : Prop where
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  ftf : C.code.lookup fFtdFill = some (ftfParams.map (fun p => (p, ShapeHOL.one)), ftfBody, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  sd : C.code.lookup fSdoms = some (sdParams.map (fun p => (p, ShapeHOL.one)), sdBody, .one)
  eqv : C.code.lookup LLeq.fEqv = some ([LEq.pLa, LEq.pLb].map (fun p => (p, ShapeHOL.one)), LLeq.eqvBody, .one)
  self : C.code.lookup fCag = some (cagParams.map (fun p => (p, ShapeHOL.one)), cagBody C, .one)

section
variable {σ : Type}

theorem cag_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cagLocals → (ctxEnv C ++ cagParams.zip vals).get x = none :=
  Knot.params_none C cagLocals cagParams vals (by decide) (by decide)

set_option maxHeartbeats 32000000 in
/-- **`checkBlockAgree`** over the tele loop's list from member `i` on. -/
theorem cag_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : CAGCodes C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (p : BlockShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (hml : p.members.length < 2 ^ 58) (hnP : p.nP < 2 ^ 56) (cv0 : IConstantVal) (s0 : LIdx) (l0 : ConLeche.Level)
    (hs0 : denoteL C.St.ls s0 = some l0) :
    ∀ (rs : List (IConstantVal × LIdx)) i (H : List (BitVec 64)) (s : AState) (w : BitVec 64),
      rs.map Prod.fst = (p.members.drop i).map (·.cvT) → i ≤ p.members.length → C.H <+: H →
      SLink C.HB H w (rs.map Prod.snd) → (∀ x ∈ rs, ∃ l, denoteL C.St.ls x.2 = some l) →
      SpecR (σ := σ) (Pre (ctxH C H) s (cagParams.zip [cellA C om, BitVec.ofNat 64 i,
        BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP, Enc.idxW cv0.type, Enc.idxW s0, w])) (cagBody C) s
        (checkBlockAgree mode C.fe p.nP cv0 s0 rs) (Decl.PostU (ctxH C H)) := by
  intro rs
  induction rs with
  | nil =>
    intro i H s w hmap hi hp hL hD
    have hin : i = p.members.length := by
      rcases Nat.lt_or_ge i p.members.length with h | h
      · rw [List.drop_eq_getElem_cons h] at hmap; simp at hmap; omega
      · omega
    subst hin
    refine specR_prologue (Decl.postU_locals _) (cag_none _ _) ?_
    have hlw := nd_lt_iff p.members.length p.members.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cagParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons x rest ih =>
    intro i H s w hmap hi hp hL hD
    obtain ⟨cv, sv⟩ := x
    have hin : i < p.members.length := by
      rcases Nat.lt_or_ge i p.members.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hmap; simp at hmap
    rw [List.drop_eq_getElem_cons hin] at hmap
    simp only [List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hcv, hmap'⟩ := hmap
    subst hcv
    obtain ⟨o1, w1, hw, ho1, ho1n, hL'⟩ := hL
    subst hw
    refine specR_prologue (Decl.postU_locals _) (cag_none _ _) ?_
    have hlw := nd_lt_iff i p.members.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cagParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [checkBlockAgree]
    have hlay := hok.heapLay
    -- member 0's telescope
    refine specR_callNIH (C := ctxH C H) cagA fOpenFvars ofParams [vv cagNP, vv cagTy0, .const 0] (ofBody C)
      [BitVec.ofNat 64 p.nP, Enc.idxW cv0.type, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ofc
      ⟨by simp +decide [sev, Env.get, cagParams, ctxEnv], by simp +decide [sev, Env.get, cagParams, ctxEnv], rfl, trivial⟩
      (PostOF (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
        w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
        (of_spec ra C hok hc.op p.nP cv0.type 0 (by omega) (by omega) H hp s))
      (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
    have hp1' : H <+: H1 := hp1
    rcases o with _ | ⟨fvs0, e0⟩
    · have e := hn rfl
      subst e
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨ob0, oa0, rfl, hob0, -, hfb0⟩ := hsm fvs0 e0 rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hne0 : cellA C ob0 ≠ 0 :=
      cellA_ne0 C hok ob0 (by have := (List.getElem?_eq_some_iff.mp hob0).1; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne0)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [unwrapOr, pure_bind]
    -- member i's telescope
    obtain ⟨oi, hoi, hrep⟩ := hM.2 i hin
    obtain ⟨⟨oc, hoc, hcv⟩, -, -, -⟩ := hrep
    have hpC1 : C.H <+: H1 := hp.trans hp1'
    refine UD.specR_heapLoadI' (C := ctxH C H1) cagMi _ (om + 1 + i) _ (get_prefix hoi hpC1) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) cagOc (vv cagMi) oi _ (get_prefix hoc hpC1) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) cagTy _ (oc + 2) _ (get_prefix hcv.2.2 hpC1) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
    refine specR_callNIH (C := ctxH C H1) cagB fOpenFvars ofParams [vv cagNP, vv cagTy, .const 0] (ofBody C)
      [BitVec.ofNat 64 p.nP, Enc.idxW p.members[i].cvT.type, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ofc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (PostOF (ctxH C H1)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
        w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
        (of_spec ra C hok hc.op p.nP p.members[i].cvT.type 0 (by omega) (by omega) H1 hpC1 s1))
      (fun o w s2 H2 hp2 ⟨hn, hsm⟩ => ?_)
    have hp2' : H1 <+: H2 := hp2
    rcases o with _ | ⟨fvs, e1⟩
    · have e := hn rfl
      subst e
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨ob, oa, rfl, hob, -, hfb⟩ := hsm fvs e1 rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN2 => ?_)
    have hHN2' : H2.length ≤ C.HN := hHN2
    have hne : cellA C ob ≠ 0 :=
      cellA_ne0 C hok ob (by have := (List.getElem?_eq_some_iff.mp hob).1; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [unwrapOr, pure_bind]
    have hfb0' := blkAt_mono hfb0 hp2'
    refine UD.specR_heapLoadI' (C := ctxH C H2) cagFa0 (vv cagA) ob0 _ (get_prefix hob0 hp2') (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) cagFa (vv cagB) ob _ hob (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) cagL0 (vv cagFa0) oa0 _ hfb0'.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) cagLa (vv cagFa) oa _ hfb.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hl0b := blkAt_len_le hfb0'
    have hlb := blkAt_len_le hfb
    simp only [List.length_map] at hl0b hlb
    by_cases hlen : fvs.length = fvs0.length
    swap
    · refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        intro e; apply hlen; have := congrArg BitVec.toNat e; simp at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this)
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlen])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [hlen, beq_self_eq_true, ↓reduceIte, pure_bind]
    refine specR_guardI cagL0 fvs0.length 56 (by decide) (by simp +decide [Env.get_cons]) (by omega) (fun hl56 => ?_)
    -- member 0's domains, into a block
    refine specR_allocI (C := ctxH C H2) cagDm _ (fvs0.length + 1) (by omega) (by decide) (fun v => ?_)
      (fun H3 ws3 hp3 hws3 hroom3 => ?_)
    · simp +decide [sev, Env.get_cons]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hp3' : H2 <+: H3 := hp3
    have hq3 : H3.length < (ctxH (ctxH C H2) (H3 ++ ws3)).H.length := by
      show H3.length < (H3 ++ ws3).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv cagDm) (vv cagL0) H3.length hq3 (BitVec.ofNat 64 fvs0.length)
      (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C ((H3 ++ ws3).set H3.length (BitVec.ofNat 64 fvs0.length))) _ _ _ _) _ _ _ _
    generalize hB3 : (H3 ++ ws3).set H3.length (BitVec.ofNat 64 fvs0.length) = B3
    have hB3len : B3.length = H3.length + (fvs0.length + 1) := by rw [← hB3]; simp [hws3]
    have hpB3 : H3 <+: B3 := by
      refine prefix_of_get? (by omega) (fun j hj => ?_)
      rw [← hB3, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
    let Hc3 := B3.take (H3.length + 1)
    have hpc3 : H3 <+: Hc3 := by
      refine prefix_of_get? (by simp [Hc3]; omega) (fun j hj => ?_)
      simp only [Hc3]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hpB3
    have hc3 : Hc3[H3.length]? = some (BitVec.ofNat 64 fvs0.length) := by
      simp only [Hc3]; rw [List.getElem?_take_of_lt (by omega), ← hB3, List.getElem?_set_self (by simp; omega)]
    have hHc3 : Hc3.length = H3.length + 1 := by simp [Hc3]; omega
    refine specR_callNIG (C := ctxH C B3) cagX fFtdFill ftfParams
      [vv cagFa0, .op .add [vv cagDm, .const 8], .const 0, vv cagL0] ftfBody
      [cellA C oa0, cellA C (H3.length + 1), BitVec.ofNat 64 0, BitVec.ofNat 64 fvs0.length] (by decide) rfl
      (by decide) hc.ftf
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; exact cellA_add8 C H3.length, rfl,
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostFTF C Hc3 B3.length (H3.length + 1) 0 fvs0.length)
      (fun us _ _ H' => Hc3 <+: H' ∧ us.length = fvs0.length ∧
        ∀ j (hj : j < us.length), H'[H3.length + 1 + j]? = some (Enc.idxW us[j]))
      (fun us w s' st ⟨H', hp', _, hsr, h1, h2⟩ => ⟨H', ⟨hp', by omega, fun j hj => by simpa using h2 j hj⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ftfParams _ rfl hlk)
        (ftf_spec C hok hc.ftf hc.fvt fvs0 oa0 (H3.length + 1) (by omega) _ 0 Hc3 B3 s2
          (blkAt_mono hfb0' (hp3'.trans hpc3)) (List.take_prefix _ _) (by omega) (by omega) rfl (Nat.zero_le _)))
      (fun us w s4 H4 ⟨hp4, hul, hus⟩ => ?_)
    have hdoms : BlkAt H4 H3.length (us.map Enc.idxW) := by
      refine ⟨by simpa [hul] using get_prefix hc3 hp4, fun j hj => ?_⟩
      simp only [List.length_map] at hj
      simpa using hus j hj
    have hp24 : H2 <+: H4 := hp3'.trans (hpc3.trans hp4)
    have hpC4 : C.H <+: H4 := hpC1.trans (hp2'.trans hp24)
    -- the domains defeq
    refine specR_okMonoA (fun a s' h => am_bind_okMono (cbd_of_csd mode C.fe 0 fvs us p.nP) _ a s' h) ?_
    refine specR_callNIH (C := ctxH C H4) cagX fSdoms sdParams [vv cagFa, vv cagDm, .const 0, vv cagNP] sdBody
      [cellA C oa, cellA C H3.length, BitVec.ofNat 64 0, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hc.sd
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H4)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sdParams _ rfl hlk)
        (sd_spec mode ra C hok hs hk hac hc.sd hc.fvt fvs us oa H3.length 0 p.nP H4 s4 (by omega) hpC4
          (blkAt_mono hfb hp24) hdoms))
      (fun _ w s5 H5 hp5 _ => ?_)
    have hp5' : H4 <+: H5 := hp5
    have hpH5 : H <+: H5 := hp1'.trans (hp2'.trans (hp24.trans hp5'))
    -- the sorts
    refine UD.specR_heapLoadI' (C := ctxH C H5) cagSv (vv cagLst) o1 _ (get_prefix ho1 hpH5) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv]; rfl) ?_
    refine specR_atEntry fun t5 ht5 => ?_
    obtain ⟨lv, hlv⟩ := hD (p.members[i].cvT, sv) (by simp)
    refine specR_callNIH (C := ctxH C H5) cagO LLeq.fEqv [LEq.pLa, LEq.pLb] [vv cagSv, vv cagS0] LLeq.eqvBody
      [Enc.idxW sv, Enc.idxW s0] (by decide) rfl (by decide) hc.eqv
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv], trivial⟩
      (LLeq.PostOB (ctxH C H5)) (fun o w s' H' => H' = H5 ∧ w = LLeq.obW o)
      (fun o w s' st ⟨hw, hsr⟩ => ⟨H5, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
        (heqS H5 sv s0 s5 lv l0 (denoteL_ext hlv ht5.sr.floor) (denoteL_ext hs0 ht5.sr.floor) ht5.sr.cok))
      (fun o w s6 H6 hp6 ⟨eH6, hw⟩ => ?_)
    subst hw; subst H6
    rcases o with _ | ⟨_ | _⟩
    · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [liftFueled, pure_bind, ↓reduceIte]
    refine UD.specR_heapLoadI' (C := ctxH C H5) cagNx _ (o1 + 1) _ (get_prefix ho1n hpH5) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv]; exact cellA_add8 C o1) ?_
    refine specR_congr (m' := checkBlockAgree mode C.fe p.nP cv0 s0 rest >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H5) cagX fCag cagParams
      [vv cagOm, .op .add [vv cagI, .const 1], vv cagN, vv cagNP, vv cagTy0, vv cagS0, vv cagNx] (cagBody C)
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP,
        Enc.idxW cv0.type, Enc.idxW s0, w1] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cagParams, ctxEnv],
        by simp +decide [sev, Env.get_cons], trivial⟩
      (Decl.PostU (ctxH C H5)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cagParams _ rfl hlk)
        (ih (i + 1) H5 s6 w1 hmap' (by omega) (hp.trans hpH5) (sLink_mono hpH5 _ _ hL')
          (fun x hx => hD x (List.mem_cons_of_mem _ hx))))
      (fun _ w s7 H7 hp7 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H7, hpH5.trans hp7, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
