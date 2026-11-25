import ConPanqueque.T.Ind.RecsRead

/-!
# How a recursor's rules fire (`recFire`), and the pieces it needs

`vlFill us o i`: the level list `us` copied into the value-heap block at `o` from position `i`. A heap store drops
the memory facts a view leaves, so the list is viewed again at each position.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP

def vlU := ofString "vl_u"
def vlD := ofString "vl_d"
def vlI := ofString "vl_i"
def vlX := ofString "vl_x"
def vlR := ofString "vl_r"
def fVlFill := ofString "vlFill"

def vlParams : List MlS := [vlU, vlD, vlI]
def vlLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, vlX, vlR]

def vlBody : ProgHOL 64 := prologue vlLocals
  (.seq (.assign .local lDh (vv vlU)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.ite (.cmp .lower (vv vlI) (vv lRn))
    (.seq (.assign .local vlX (.load .one (.op .add [vv lRp, .shift .lsl (vv vlI) (.const 3)])))
    (.seq (.store (.op .add [vv vlD, .shift .lsl (.op .add [vv vlI, .const 1]) (.const 3)]) (vv vlX))
    (.seq (.call (some (some (.local, vlR), none)) fVlFill [vv vlU, vv vlD, .op .add [vv vlI, .const 1]])
      (.return (.const 0)))))
    (.return (.const 0))))))

section
variable {σ : Type}

/-- The level list's words from position `i` on, past the frozen prefix `Hc`. -/
def PostVL (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (vl : List LIdx) (i : Nat) (_ : Unit) (_ : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ ∀ j (hj : j < vl.length), i ≤ j → H'[o + 1 + j]? = some (Enc.idxW vl[j])

theorem postVL_locals (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (vl : List LIdx) (i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostVL C Hc o vl i a w s' st → PostVL C Hc o vl i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem vl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ vlLocals → (ctxEnv C ++ vlParams.zip vals).get x = none :=
  Knot.params_none C vlLocals vlParams vals (by decide) (by decide)

/-- **`vlFill`** from position `i`. -/
theorem vl_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fVlFill = some (vlParams.map (fun p => (p, ShapeHOL.one)), vlBody, .one))
    (us : LsIdx) (vl : List LIdx) (o : Nat) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), vl.length - i = k → i ≤ vl.length →
      s.store.lss.view us = some vl → Hc.length ≤ o + 1 + i → Hc <+: H → o + 1 + vl.length ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (vlParams.zip [Enc.idxW us, cellA C o, BitVec.ofNat 64 i])) vlBody s
        (pure ()) (PostVL C Hc o vl i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi hv hHc hp hl
    refine specR_prologue (postVL_locals _ _ _ _ _) (vl_none _ _) ?_
    refine specR_assignI lDh (vv vlU) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get, vlParams, ctxEnv]) ?_
    refine specR_assignI lFl (vv lFls) (ctxH C H).FLs (by decide)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) (by decide) (fun vl' P hv' htl hlenl => ?_)
    rw [hv] at hv'; cases hv'
    simp only [List.length_map] at hlenl
    refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 vl.length)
          (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]) (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc s hk hi hv hHc hp hl
    refine specR_prologue (postVL_locals _ _ _ _ _) (vl_none _ _) ?_
    refine specR_assignI lDh (vv vlU) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get, vlParams, ctxEnv]) ?_
    refine specR_assignI lFl (vv lFls) (ctxH C H).FLs (by decide)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) (by decide) (fun vl' P hv' htl hlenl => ?_)
    rw [hv] at hv'; cases hv'
    simp only [List.length_map] at hlenl
    have hil : i < vl.length := by omega
    refine specR_ifI _ 1 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 vl.length)
          (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]) (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp; omega) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' vlX _ (P + BitVec.ofNat 64 i <<< 3) (P + BitVec.ofNat 64 (8 * i)) (Enc.idxW vl[i]) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv])
      (by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega)
      (by have := wordsAt_get P (vl.map Enc.idxW) i (by simp; omega) []; simpa using this) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hj : o + 1 + i < (ctxH C H).H.length := by show o + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_H hok H) _ (vv vlX) (o + 1 + i) hj (Enc.idxW vl[i])
      (by
        simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]
        show _ = cellA C (o + 1 + i)
        apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega)
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H.set (o + 1 + i) (Enc.idxW vl[i]))) _ _ _ _) _ _ _ _
    generalize hB : H.set (o + 1 + i) (Enc.idxW vl[i]) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[o + 1 + i]? = some (Enc.idxW vl[i]) := by rw [← hB, List.getElem?_set_self (by omega)]
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
    refine specR_callNIG (C := ctxH C B) vlR fVlFill vlParams [vv vlU, vv vlD, .op .add [vv vlI, .const 1]] vlBody
      [Enc.idxW us, cellA C o, BitVec.ofNat 64 (i + 1)] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv],
        by
          show sev _ _ = _
          rw [sev_add2 _ _ _ (BitVec.ofNat 64 i) _ (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]) rfl]
          exact congrArg some (word_add1_eq i), trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostVL C Hc' o vl (i + 1) a w s' st)
      (fun a w s' H' => s' = s ∧ Hc' <+: H' ∧ ∀ j (hj : j < vl.length), i + 1 ≤ j → H'[o + 1 + j]? = some (Enc.idxW vl[j]))
      (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) B Hc' s (by omega) (by omega) hv (by simp [Hc']; omega) hpc' (by omega) _
          (pre_of_lookups hu vlParams _ rfl hlk)))
      (fun a w s' H' ⟨hs', hp', hc'⟩ => ?_)
    subst hs'
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
      rcases Nat.lt_or_ge i j with h | h
      · exact hc' j hj (by omega)
      · have e : j = i := by omega
        subst e
        have := ConPanqueque.T.Decl.get_prefix (show Hc'[o + 1 + j]? = some (Enc.idxW vl[j]) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'
        exact this⟩)

end

end ConPanqueque.T.Ind
