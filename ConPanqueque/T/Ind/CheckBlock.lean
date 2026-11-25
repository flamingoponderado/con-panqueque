import ConPanqueque.T.Ind.BlockReadsSpec
import ConPanqueque.T.Decl.StepDefn

/-!
# `checkBlock`

`rmFill`: `reduceMembers` on the blocks the port supports: every member's former already at its telescope (its
type ends in a sort, `formerDefHeaded` false). A member stored at a definition hangs (the twin reduces it).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl ConPanqueque.T.WC

def rmMs := ofString "rm_ms"
def rmI := ofString "rm_i"
def rmK := ofString "rm_k"
def rmO := ofString "rm_o"
def rmCv := ofString "rm_cv"
def rmT := ofString "rm_t"
def rmS := ofString "rm_s"
def rmX := ofString "rm_x"
def fRmFill := ofString "reduceMembers"

def rmParams : List MlS := [rmMs, rmI, rmK]
def rmLocals : List MlS := [rmO, rmCv, rmT, rmS, rmX, lJ0]

def rmBody (C : Ctx) : ProgHOL 64 := prologue rmLocals
  (.ite (.cmp .lower (vv rmI) (vv rmK))
    (flushCode C (flushRegions false)
    (.seq (.assign .local rmO (.load .one (.op .add [vv rmMs, .op .add [.panop .mul [vv rmI, .const 8], .const 8]])))
    (.seq (.assign .local rmCv (.load .one (vv rmO)))
    (.seq (.assign .local rmT (.load .one (.op .add [vv rmCv, .const 16])))
    (.seq (.call (some (some (.local, rmS), none)) fFs [vv rmT])
    (.ite (.cmp .equal (vv rmS) (.const 0)) hang
    (.seq (.call (some (some (.local, rmX), none)) fRmFill [vv rmMs, .op .add [vv rmI, .const 1], vv rmK])
      (.return (.const 0)))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem rm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rmLocals → (ctxEnv C ++ rmParams.zip vals).get x = none :=
  Knot.params_none C rmLocals rmParams vals (by decide) (by decide)

/-- **`reduceMembers`** from member `i`: on every path the port takes, the members as they are. -/
theorem rm_spec (mode : ConLeche.CheckMode) (fe : IFEnv) (nP : Nat) (C : Ctx) (hok : CtxOK C)
    (hpl : C.saved = none)
    (hcs : C.code.lookup fFs = some ([(fsT, ShapeHOL.one)], fsBody, .one))
    (hcp : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one))
    (hcode : C.code.lookup fRmFill = some (rmParams.map (fun p => (p, ShapeHOL.one)), rmBody C, .one))
    (ms : List MemberShape) (om : Nat) (hms : PtrsRep C C.H om (MemberRep C C.H) ms) :
    ∀ k i (H : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length → C.H <+: H →
      SpecR (Pre (σ := σ) (ctxH C H) s (rmParams.zip [cellA C om, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length]))
        (rmBody C) s (reduceMembers mode fe nP (ms.drop i))
        (fun r _ s' st => r = ms.drop i ∧ ∃ H', H <+: H' ∧ SR (ctxH C H') s' st) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk hi hp
    refine specR_prologue (fun _ _ _ _ _ ⟨h1, H', hp', hs⟩ => ⟨h1, H', hp', sr_of_eq hs rfl rfl rfl rfl⟩)
      (rm_none _ _) ?_
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
        simp +decide [sev, Env.get, rmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨by simp [reduceMembers], H, List.prefix_refl _,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i H s hk hi hp
    have hil : i < ms.length := by omega
    refine specR_prologue (fun _ _ _ _ _ ⟨h1, H', hp', hs⟩ => ⟨h1, H', hp', sr_of_eq hs rfl rfl rfl rfl⟩)
      (rm_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hml : ms.length < 2 ^ 61 := by
      obtain ⟨oc, h1, -⟩ := hms.2 (ms.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp (get_prefix h1 hp)).1; omega
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hil]
    simp only [reduceMembers]
    refine specR_flushTopI (ctxOK_H hok H) hpl false flushCaches rfl (by decide) ?_
    obtain ⟨oi, h1, hmr⟩ := hms.2 i hil
    obtain ⟨⟨oc, hoc, hcv⟩, -⟩ := hmr
    refine UD.specR_heapLoadI' (C := ctxH C H) rmO _ (om + 1 + i) _ (get_prefix h1 hp) (by decide)
      (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, rmParams, ctxEnv]
          exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rmCv _ oi _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rmT _ (oc + 2) _ (get_prefix hcv.2.2 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
    simp only [reduceMember, formerDefHeaded, bind_assoc]
    refine specR_callNIH (C := ctxH C H) rmS fFs [fsT] [vv rmT] fsBody [Enc.idxW ms[i].cvT.type] (by decide) rfl
      (by decide) hcs ⟨by simp +decide [sev, Env.get], trivial⟩
      (fun a w s' st => formerResSort ms[i].cvT.type (flushedS false s) = .ok (a, s') ∧
        PostOL (ctxH C H) (flushedS false s) a w s' st)
      (fun a w s' _ => s' = flushedS false s ∧ w = optWG Enc.idxW a)
      (fun a w s' st ⟨hrun, h1, h2, H', hp', h3⟩ => ⟨H', hp', ⟨h1, h2⟩, by subst h1; exact h3⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [fsT] _ rfl hlk)
        (fs_spec (ctxH C H) hcp (flushedS false s) ms[i].cvT.type)))
      (fun r w s1 H1 hp1 ⟨hs1, hw⟩ => ?_)
    subst hw; subst s1
    have hp1' : H <+: H1 := hp1
    rcases r with _ | u
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    have hne : ¬ Enc.idxW u + 1 = 0 := lidxW_add_one_ne u
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_false, Bool.false_eq_true, pure_bind]
    refine specR_congr (m' := reduceMembers mode fe nP (ms.drop (i + 1)) >>= fun rest => pure (ms[i] :: rest))
      (by rfl) ?_
    refine specR_callNIH (C := ctxH C H1) rmX fRmFill rmParams [vv rmMs, .op .add [vv rmI, .const 1], vv rmK]
      (rmBody C) [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, rmParams, ctxEnv],
        by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, rmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, rmParams, ctxEnv], trivial⟩
      (fun r _ s' st => r = ms.drop (i + 1) ∧ ∃ H', H1 <+: H' ∧ SR (ctxH C H') s' st)
      (fun r _ s' _ => r = ms.drop (i + 1))
      (fun r w s' st ⟨h1, H', hp', hs⟩ => ⟨H', hp', h1, hs⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk)
        (ih (i + 1) H1 (flushedS false s) (by omega) (by omega) (hp.trans hp1')))
      (fun r w s2 H2 hp2 hr => ?_)
    subst hr
    have hp2' : H1 <+: H2 := hp2
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, H2, hp1'.trans hp2', sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
