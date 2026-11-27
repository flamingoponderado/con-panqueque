import ConPanqueque.T.Ind.CtorsFresh

/-!
# The members' names: none at a `Bool` constructor's name, each declared name fresh (else hang)

`mokBody(om, i, n, bt, bf)`: member `i`'s former name against the two words `bt`, `bf` (equal hangs), its
declared name looked up in the constant table (a hit hangs), then itself at `i + 1`, until `i` reaches `n`.
Pure: the state is kept.  This is `checkBlock`'s `memberNames.contains bt || memberNames.contains bf` test at any
number of members, with the freshness `consBlockInds`' inserts need.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def mokOm := ofString "mok_om"
def mokI := ofString "mok_i"
def mokN := ofString "mok_n"
def mokBt := ofString "mok_bt"
def mokBf := ofString "mok_bf"
def mokMi := ofString "mok_mi"
def mokOc := ofString "mok_oc"
def mokNm := ofString "mok_nm"
def mokOd := ofString "mok_od"
def mokDn := ofString "mok_dn"
def mokY := ofString "mok_y"
def mokR := ofString "mok_r"
def fMok := ofString "membersOk"

def mokParams : List MlS := [mokOm, mokI, mokN, mokBt, mokBf]
def mokLocals : List MlS := [mokMi, mokOc, mokNm, mokOd, mokDn, mokY, mokR]

def mokBody (C : Ctx) : ProgHOL 64 := prologue mokLocals
  (.ite (.cmp .lower (vv mokI) (vv mokN))
    (.seq (.assign .local mokMi (.load .one (.op .add [vv mokOm, .op .add [.panop .mul [vv mokI, .const 8], .const 8]])))
    (.seq (.assign .local mokOc (.load .one (vv mokMi)))
    (.seq (.assign .local mokNm (.load .one (vv mokOc)))
    (.ite (.cmp .equal (vv mokNm) (vv mokBt)) hang
    (.ite (.cmp .equal (vv mokNm) (vv mokBf)) hang
    (.seq (.assign .local mokOd (.load .one (.op .add [vv mokMi, .const 8])))
    (.seq (.assign .local mokDn (.load .one (vv mokOd)))
    (envFindP C mokY (vv mokDn)
    (.ite (.cmp .notEqual (vv mokY) (.const 0)) hang
    (.seq (.call (some (some (.local, mokR), none)) fMok [vv mokOm, .op .add [vv mokI, .const 1], vv mokN, vv mokBt, vv mokBf])
      (.return (.const 0))))))))))))
    (.return (.const 0)))

structure MOKCodes (C : Ctx) : Prop where
  g : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  p : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  self : C.code.lookup fMok = some (mokParams.map (fun p => (p, ShapeHOL.one)), mokBody C, .one)

section
variable {σ : Type}

theorem mok_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mokLocals → (ctxEnv C ++ mokParams.zip vals).get x = none :=
  Knot.params_none C mokLocals mokParams vals (by decide) (by decide)

/-- What the members from `i` on satisfy once the loop returns. -/
def MembersOk (fe : IFEnv) (bt bf : NIdx) (ms : List MemberShape) : Prop :=
  ∀ m ∈ ms, m.cvT.name ≠ bt ∧ m.cvT.name ≠ bf ∧ fe.find? m.declared.name = none

set_option maxHeartbeats 8000000 in
/-- **The members from `i` on**: no former at `bt` or `bf`, every declared name fresh (else hang). -/
theorem mok_spec (C : Ctx) (hok : CtxOK C) (hc : MOKCodes C) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 58) (bt bf : NIdx) :
    ∀ f i (s : AState), ms.length - i = f → i ≤ ms.length →
      SpecR (σ := σ) (Pre C s (mokParams.zip [cellA C om, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length, Enc.idxW bt,
        Enc.idxW bf])) (mokBody C) s (pure ()) (PostKF C s (MembersOk C.fe bt bf (ms.drop i))) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hil : i = ms.length := by omega
    subst hil
    refine specR_prologue (postKF_locals _ _ _) (mok_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, mokParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp [MembersOk], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hil : i < ms.length := by omega
    refine specR_prologue (postKF_locals _ _ _) (mok_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, mokParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨mi, hmi, hrep⟩ := hM.2 i hil
    obtain ⟨⟨oc, hoc, hcv⟩, ⟨od, hod, hdv⟩, -, -⟩ := hrep
    refine UD.specR_heapLoadI' (C := C) mokMi _ (om + 1 + i) _ hmi (by decide)
      (by simp +decide [sev, Env.get, mokParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := C) mokOc (vv mokMi) mi _ hoc (by decide) (by simp [sev, Env.get_cons]) ?_
    refine UD.specR_heapLoadI' (C := C) mokNm (vv mokOc) oc _ hcv.1 (by decide) (by simp [sev, Env.get_cons]) ?_
    by_cases e1 : ms[i].cvT.name = bt
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e1]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact fun h => e1 (Enc.idxW_inj h)) (fun h => absurd rfl h) (fun _ => ?_)
    by_cases e2 : ms[i].cvT.name = bf
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e2]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact fun h => e2 (Enc.idxW_inj h)) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := C) mokOd _ (mi + 1) _ hod (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C mi) ?_
    refine UD.specR_heapLoadI' (C := C) mokDn (vv mokOd) od _ hdv.1 (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_envFindI hok hc.g hc.p mokY (vv mokDn) ms[i].declared.name (by decide)
      (by simp +decide [sev, Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, mokParams, ctxEnv]) ?_
    have hrel := find_rel hok ms[i].declared.name
    revert hrel
    rcases hfn : C.fe.find? ms[i].declared.name with _ | ci0
    swap
    · intro ⟨o', hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    intro hrel
    simp only at hrel
    rw [hrel]
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM mokR fMok mokParams [vv mokOm, .op .add [vv mokI, .const 1], vv mokN, vv mokBt, vv mokBf]
      (mokBody C) [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length, Enc.idxW bt, Enc.idxW bf]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mokParams, ctxEnv], trivial⟩
      (PostKF C s (MembersOk C.fe bt bf (ms.drop (i + 1)))) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mokParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s1 st ⟨hs1, hall, _⟩ => ?_)
    subst s1
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by
      rw [List.drop_eq_getElem_cons hil]
      intro m hm
      rcases List.mem_cons.mp hm with e | e
      · subst e; exact ⟨e1, e2, hfn⟩
      · exact hall m e, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- The twin's `Bool`-name test at the members, from `MembersOk`. -/
theorem membersOk_contains {fe : IFEnv} {bt bf : NIdx} {p : BlockShape} (h : MembersOk fe bt bf p.members) :
    (p.memberNames.contains bt || p.memberNames.contains bf) = false := by
  simp only [BlockShape.memberNames, Bool.or_eq_false_iff, List.contains_eq_any_beq, List.any_eq_false,
    List.mem_map, beq_iff_eq]
  refine ⟨?_, ?_⟩ <;> rintro x ⟨m, hm, rfl⟩ e
  · exact (h m hm).1 e.symm
  · exact (h m hm).2.1 e.symm

end

end ConPanqueque.T.Ind
