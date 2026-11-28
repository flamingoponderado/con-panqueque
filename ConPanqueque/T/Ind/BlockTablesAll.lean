import ConPanqueque.T.Ind.BlockTables
import ConPanqueque.T.Ind.IndParams

/-!
# `blockTables` at any number of members

`btaBody(om, i, n, nP)`: member `i`'s tables (`bt` on the member record at the pointer-block cell
`om + 8 (i + 1)`: an empty or one-entry block), then itself at `i + 1`; the two blocks are joined when one of
them is empty (two members with a table each hang: the install still takes at most one table). At `i = n` an
empty block. `bta_spec` refines `blockTables p (p.members.drop i)`; `blockTables_cons` splits the twin's walk
into the head member's tables and the rest's, `blockTables_len` bounds the answer by the member count.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- The twin's walk, split at the head member. -/
theorem blockTables_cons (p : BlockShape) (ms : MemberShape) (rest : List MemberShape) :
    blockTables p (ms :: rest) = (blockTables p [ms] >>= fun o => match o with
      | none => pure none
      | some Q1 => blockTables p rest >>= fun o2 => pure (o2.map (Q1 ++ ·))) := by
  simp only [blockTables]
  cases ms.structCtor? with
  | none =>
    simp only [pure_bind, List.nil_append]
    have : (fun o2 : Option (List IProjTable) => (pure (Option.map (fun x => x) o2) : AM _)) = pure := by
      funext o2; cases o2 <;> rfl
    rw [this, bind_pure]
  | some c =>
    simp only [bind_assoc]
    congr 1; funext b
    cases b with
    | none => rfl
    | some bodies =>
      simp only [pure_bind, Option.map_some, List.singleton_append]

/-- At most one table per member. -/
theorem blockTables_len (p : BlockShape) : ∀ (ms : List MemberShape) {s s' : AState} {Q : List IProjTable},
    blockTables p ms s = .ok (some Q, s') → Q.length ≤ ms.length
  | [], s, s', Q, h => by
    simp only [blockTables] at h
    obtain ⟨e, -⟩ := AM.pure_ok h
    cases e; simp
  | m :: rest, s, s', Q, h => by
    revert h
    simp only [blockTables]
    cases m.structCtor? with
    | none =>
      intro h
      have := blockTables_len p rest h
      simp only [List.length_cons]; omega
    | some c =>
      intro h
      obtain ⟨b, s1, -, h⟩ := AM.bind_ok h
      cases b with
      | none =>
        obtain ⟨e, -⟩ := AM.pure_ok h
        cases e
      | some bodies =>
        obtain ⟨o2, s2, h2, h⟩ := AM.bind_ok h
        obtain ⟨e, -⟩ := AM.pure_ok h
        cases o2 with
        | none => cases e
        | some Q2 =>
          simp only [Option.map_some, Option.some.injEq] at e
          subst e
          have := blockTables_len p rest h2
          simp only [List.length_cons]; omega

def btaO := ofString "bta_o"
def btaI := ofString "bta_i"
def btaN := ofString "bta_n"
def btaNp := ofString "bta_np"
def btaMr := ofString "bta_mr"
def btaB := ofString "bta_b"
def btaR := ofString "bta_r"
def btaNb := ofString "bta_nb"
def btaNr := ofString "bta_nr"
def fBta := ofString "blockTablesAll"

def btaParams : List MlS := [btaO, btaI, btaN, btaNp]
def btaLocals : List MlS := [btaMr, btaB, btaR, btaNb, btaNr, lW]

def btaBody (C : Ctx) : ProgHOL 64 := prologue btaLocals
  (.ite (.cmp .lower (vv btaI) (vv btaN))
    (.seq (.assign .local btaMr (.load .one (.op .add [vv btaO, .op .add [.panop .mul [vv btaI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, btaB), none)) fBt [vv btaMr, vv btaNp])
    (.seq (.call (some (some (.local, btaR), none)) fBta [vv btaO, .op .add [vv btaI, .const 1], vv btaN, vv btaNp])
    (.seq (.assign .local btaNb (.load .one (vv btaB)))
    (.ite (.cmp .equal (vv btaNb) (.const 0)) (.return (vv btaR))
      (.seq (.assign .local btaNr (.load .one (vv btaR)))
      (.ite (.cmp .equal (vv btaNr) (.const 0)) (.return (vv btaB)) hang)))))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure BTACodes (C : Ctx) : Prop where
  bt : BTCodes C
  self : C.code.lookup fBta = some (btaParams.map (fun p => (p, ShapeHOL.one)), btaBody C, .one)

section
variable {σ : Type}

theorem bta_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ btaLocals → (ctxEnv C ++ btaParams.zip vals).get x = none :=
  Knot.params_none C btaLocals btaParams vals (by decide) (by decide)

theorem bta_empty_spec (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} :
    SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ btaLocals)) (alloc1 C lW (.const 0) (.return (vv lW))) s
      (pure (some [])) (PostBTb C) := by
  refine specR_alloc1I hok lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
  have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
  have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
  exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]) (fun t ht => ⟨[], _, H2.length, rfl,
    (hp2 : C.H <+: H2).trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem pRep_len {α : Type} {C : Ctx} {H : List (BitVec 64)} {o : Nat} {Rep : List (BitVec 64) → Nat → α → Prop}
    {xs : List α} (h : PRep C H o Rep xs) : H[o]? = some (BitVec.ofNat 64 xs.length) := by
  obtain ⟨os, hl, hb, -⟩ := h
  rw [hb.1, List.length_map, hl]

theorem ofNat_ne_zero_of_ne_nil {α : Type} {xs : List α} (h : xs ≠ []) (hl : xs.length < 2 ^ 64) :
    BitVec.ofNat 64 xs.length ≠ 0#64 := fun e => h (by
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at this
  exact List.eq_nil_of_length_eq_zero (by omega))

set_option maxHeartbeats 32000000 in
/-- **`blockTables`** over the members from `i` on (at most one table in all, else a hang). -/
theorem bta_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BTACodes C)
    (p : BlockShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (hml : p.members.length < 2 ^ 58) (hnP : p.nP < 2 ^ 57)
    (hlps : ∀ ms ∈ p.members, p.lps = ms.cvT.levelParams) (hni : ∀ ms ∈ p.members, ms.nIdx < 2 ^ 64)
    (hnf : ∀ ms ∈ p.members, ∀ c ∈ ms.ctors, c.2 < 2 ^ 57) (hcl : ∀ ms ∈ p.members, ms.ctors.length < 2 ^ 63) :
    ∀ f i (H : List (BitVec 64)) (s : AState), p.members.length - i = f → i ≤ p.members.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (btaParams.zip [cellA C om, BitVec.ofNat 64 i,
        BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP])) (btaBody C) s
        (blockTables p (p.members.drop i)) (PostBTb (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = p.members.length := by omega
    subst hin
    refine specR_prologue (postBTb_locals _) (bta_none _ _) ?_
    have hlw := nd_lt_iff p.members.length p.members.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, btaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact bta_empty_spec (ctxH C H) (ctxOK_H hok H)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < p.members.length := by omega
    refine specR_prologue (postBTb_locals _) (bta_none _ _) ?_
    have hlw := nd_lt_iff i p.members.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, btaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oi, hoi, hrep⟩ := hM.2 i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) btaMr _ (om + 1 + i) _ (get_prefix hoi hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, btaParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin, blockTables_cons]
    have hmem : p.members[i] ∈ p.members := List.getElem_mem _
    have hok1 := ctxOK_H hok H
    refine specR_callNIH (C := ctxH C H) btaB fBt btParams [vv btaMr, vv btaNp] (btBody C)
      [cellA C oi, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) (by ctx_tr hc.bt.self)
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, btaParams, ctxEnv], trivial⟩
      (fun a w s' st => blockTables p [p.members[i]] s = .ok (a, s') ∧ PostBTb (ctxH C H) a w s' st)
      (fun o w s' H' => blockTables p [p.members[i]] s = .ok (o, s') ∧ ∃ Q ob, o = some Q ∧ w = cellA C ob ∧
        PRep C H' ob (fun H o t => TblVRep C H o t) Q)
      (fun a w s' st ⟨hr, Q, H', ob, h1, h2, h3, h4, h5⟩ => ⟨H', h2, ⟨hr, Q, ob, h1, h3, h4⟩, h5⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu btParams _ rfl hlk)
        (bt_spec ra (ctxH C H) hok1 (by ctx_tr hc.bt) p p.members[i] (hlps _ hmem) oi (memberRep_mono hp hrep)
          hnP (hni _ hmem) (hnf _ hmem) (hcl _ hmem) s)))
      (fun o w s1 H1 hp1 ⟨hbrun, Q1, ob, eo, ew, hq1⟩ => ?_)
    subst eo ew
    have hQ1 : Q1.length ≤ 1 := blockTables_len p [p.members[i]] hbrun
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) btaR fBta btaParams
      [vv btaO, .op .add [vv btaI, .const 1], vv btaN, vv btaNp] (btaBody C)
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP]
      (by decide) rfl (by decide) (by ctx_tr hc.self)
      ⟨by simp +decide [sev, Env.get_cons, Env.get, btaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, btaParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, btaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, btaParams, ctxEnv], trivial⟩
      (fun a w s' st => blockTables p (p.members.drop (i + 1)) s1 = .ok (a, s') ∧ PostBTb (ctxH C H1) a w s' st)
      (fun o w s' H' => blockTables p (p.members.drop (i + 1)) s1 = .ok (o, s') ∧ ∃ Q ob, o = some Q ∧
        w = cellA C ob ∧ PRep C H' ob (fun H o t => TblVRep C H o t) Q)
      (fun a w s' st ⟨hr, Q, H', ob, h1, h2, h3, h4, h5⟩ => ⟨H', h2, ⟨hr, Q, ob, h1, h3, h4⟩, h5⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu btaParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1'))))
      (fun o2 w s2 H2 hp2 ⟨hrrun, Q2, ob2, eo2, ew2, hq2⟩ => ?_)
    subst eo2 ew2
    have hQ2 : Q2.length ≤ (p.members.drop (i + 1)).length := blockTables_len p _ hrrun
    simp only [List.length_drop] at hQ2
    have hp2' : H1 <+: H2 := hp2
    simp only [Option.map_some]
    have hq1' := pRep_mono hp2' (fun _ _ h => tblVRep_mono hp2' h) hq1
    refine UD.specR_heapLoadI' (C := ctxH C H2) btaNb (vv btaB) ob _ (pRep_len hq1') (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    by_cases h1 : Q1 = []
    · subst h1
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (cellA C ob2) (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨Q2, H2, ob2, by simp,
        hp1'.trans hp2', rfl, hq2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hw1 : BitVec.ofNat 64 Q1.length ≠ 0#64 := ofNat_ne_zero_of_ne_nil h1 (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw1])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H2) btaNr (vv btaR) ob2 _ (pRep_len hq2) (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    by_cases h2 : Q2 = []
    · subst h2
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (cellA C ob) (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨Q1, H2, ob, by simp,
        hp1'.trans hp2', rfl, hq1', sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hw2 : BitVec.ofNat 64 Q2.length ≠ 0#64 := ofNat_ne_zero_of_ne_nil h2 (by omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw2])
      (fun h => absurd rfl h) (fun _ => specR_hangI)

end

end ConPanqueque.T.Ind
