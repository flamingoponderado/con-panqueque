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

end ConPanqueque.T.Ind
