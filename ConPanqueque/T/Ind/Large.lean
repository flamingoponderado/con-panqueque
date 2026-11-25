import ConPanqueque.T.Ind.LpsEq

/-!
# The large eliminator

`readBlock`: the first recursor's universe parameters are `elim :: lps` with `elim` fresh (not among the
block's `lps`) exactly when the block eliminates into any sort.  `lpsHas(b, x, i, n)`: `x` among handles
`i … n - 1` of the list at `b`; `largeChk(r, l)`: the recursor's list `r` is `elim :: (list l)`, `elim` fresh.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- `readBlock`'s `large?`. -/
def largeT (lps rl : List NIdx) : Option NIdx :=
  match rl with
  | [] => none
  | elim :: relps => if relps == lps && !lps.contains elim then some elim else none

def lhB := ofString "lh_b"
def lhX := ofString "lh_x"
def lhI := ofString "lh_i"
def lhN := ofString "lh_n"
def lhY := ofString "lh_y"
def lhR := ofString "lh_r"
def fLpsHas := ofString "lpsHas"

def lhParams : List MlS := [lhB, lhX, lhI, lhN]
def lhLocals : List MlS := [lhY, lhR]

def lhBody : ProgHOL 64 := prologue lhLocals
  (.ite (.cmp .lower (vv lhI) (vv lhN))
    (.seq (.assign .local lhY (.load .one (.op .add [vv lhB, .op .add [.panop .mul [vv lhI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv lhY) (vv lhX)) (.return (.const 1))
      (.seq (.call (some (some (.local, lhR), none)) fLpsHas [vv lhB, vv lhX, .op .add [vv lhI, .const 1], vv lhN])
        (.return (vv lhR)))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem lh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lhLocals → (ctxEnv C ++ lhParams.zip vals).get x = none :=
  Knot.params_none C lhLocals lhParams vals (by decide) (by decide)

/-- **`lpsHas`** from index `i`. -/
theorem lh_spec (C : Ctx) (hc : C.code.lookup fLpsHas = some (lhParams.map (fun p => (p, ShapeHOL.one)), lhBody, .one))
    (xs : List NIdx) (ob : Nat) (x : NIdx) (hl : xs.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → Elems H ob xs → xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (lhParams.zip [cellA C ob, Enc.idxW x, BitVec.ofNat 64 i,
        BitVec.ofNat 64 xs.length])) lhBody s (pure ((xs.drop i).contains x)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hp hb hf hi
    have hil : i = xs.length := by omega
    subst hil
    refine specR_prologue (postB_locals _) (lh_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hp hb hf hi
    have hix : i < xs.length := by omega
    refine specR_prologue (postB_locals _) (lh_none _ _) ?_
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, lhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hix])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[ob + 1 + i]? = some (Enc.idxW xs[i]) := by show H[ob + 1 + i]? = _; exact hb i hix
    refine UD.specR_heapLoadI' (C := ctxH C H) lhY _ (ob + 1 + i) _ hw (by decide)
      (by simp +decide [sev, Env.get, lhParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hix, List.contains_cons]
    by_cases he : xs[i] = x
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, he, Env.get, lhParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      have : (x == xs[i]) = true := by simp [he]
      rw [this, Bool.true_or]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : Enc.idxW xs[i] ≠ Enc.idxW x := fun h => he (ConPanqueque.V.Enc.idxW_inj h)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, lhParams, ctxEnv, hne,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      have : (x == xs[i]) = false := by simp; exact fun e => he e.symm
      rw [this, Bool.false_or]
      refine specR_congr (m' := (pure ((xs.drop (i + 1)).contains x) : AM Bool) >>= fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) lhR fLpsHas lhParams [vv lhB, vv lhX, .op .add [vv lhI, .const 1], vv lhN]
        lhBody [cellA C ob, Enc.idxW x, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl
        (by simp +decide [ctxLocals, lhLocals]) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, lhParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, lhParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, lhParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, lhParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lhParams _ rfl hlk)
          (ih (i + 1) H s hp hb (by omega) (by omega)))
        (fun b w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW b) (by simp +decide [Env.get])
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def lgR := ofString "lg_r"
def lgL := ofString "lg_l"
def lgA := ofString "lg_a"
def lgB := ofString "lg_b"
def lgQ := ofString "lg_q"
def fLargeChk := ofString "largeChk"

def lgParams : List MlS := [lgR, lgL]
def lgLocals : List MlS := [lgA, lgB, lgQ]

def lgBody : ProgHOL 64 := prologue lgLocals
  (.seq (.assign .local lgA (.load .one (vv lgR)))
  (.seq (.assign .local lgB (.load .one (vv lgL)))
  (.ite (.cmp .equal (vv lgA) (.op .add [vv lgB, .const 1]))
    (.seq (.call (some (some (.local, lgQ), none)) fLpsEqGo [.op .add [vv lgR, .const 8], vv lgL, .const 0, vv lgB])
    (.ite (.cmp .equal (vv lgQ) (.const 0)) (.return (.const 0))
      (.seq (.assign .local lgA (.load .one (.op .add [vv lgR, .const 8])))
      (.seq (.call (some (some (.local, lgQ), none)) fLpsHas [vv lgL, vv lgA, .const 0, vv lgB])
        (.return (.cmp .equal (vv lgQ) (.const 0)))))))
    (.return (.const 0)))))

section
variable {σ : Type}

theorem lg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lgLocals → (ctxEnv C ++ lgParams.zip vals).get x = none :=
  Knot.params_none C lgLocals lgParams vals (by decide) (by decide)

/-- **`largeChk`**: `large?` is `some`. -/
theorem lg_spec (C : Ctx)
    (hc : C.code.lookup fLargeChk = some (lgParams.map (fun p => (p, ShapeHOL.one)), lgBody, .one))
    (hcg : C.code.lookup fLpsEqGo = some (legParams.map (fun p => (p, ShapeHOL.one)), legBody, .one))
    (hch : C.code.lookup fLpsHas = some (lhParams.map (fun p => (p, ShapeHOL.one)), lhBody, .one))
    (rl lps : List NIdx) (orl ol : Nat) (hr : rl.length < 2 ^ 59) (hl : lps.length < 2 ^ 59)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hbr : EBlk H orl (rl.map Enc.idxW))
    (hbl : EBlk H ol (lps.map Enc.idxW)) :
    SpecR (σ := σ) (Pre (ctxH C H) s (lgParams.zip [cellA C orl, cellA C ol])) lgBody s
      (pure (largeT lps rl).isSome) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (lg_none _ _) ?_
  have hla : (ctxH C H).H[orl]? = some (BitVec.ofNat 64 rl.length) := by show H[orl]? = _; rw [hbr.1]; simp
  have hlb : (ctxH C H).H[ol]? = some (BitVec.ofNat 64 lps.length) := by show H[ol]? = _; rw [hbl.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) lgA (vv lgR) orl _ hla (by decide)
    (by simp +decide [sev, Env.get, lgParams, ctxEnv]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) lgB (vv lgL) ol _ hlb (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, lgParams, ctxEnv]; rfl) ?_
  have hadd : sev ((lgB, BitVec.ofNat 64 lps.length) :: (lgA, BitVec.ofNat 64 rl.length) ::
      (ctxEnv (ctxH C H) ++ lgParams.zip [cellA C orl, cellA C ol])) (.op .add [vv lgB, .const 1]) =
      some (BitVec.ofNat 64 (lps.length + 1)) := by
    simp [sev, Env.get_cons]; exact word_add1_eq _
  refine specR_ifI _ _ (ConPanqueque.T.WC.sev_eqNatB (x := rl.length) (y := lps.length + 1) (by omega) (by omega)
    (by simp +decide [sev, Env.get_cons]) hadd) (fun h => ?_) (fun h => ?_)
  · have hlen : rl.length = lps.length + 1 := by
      by_cases c : rl.length = lps.length + 1; exact c; simp [boolW, c] at h
    obtain ⟨elim, relps, rfl⟩ : ∃ e r, rl = e :: r := by
      cases rl with
      | nil => simp at hlen
      | cons e r => exact ⟨e, r, rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [largeT]
    have hel : Elems H (orl + 1) relps := fun j hj => by
      have := hbr.2 (j + 1) (by simp; omega)
      simp only [List.map_cons, List.getElem_cons_succ, List.getElem_map] at this
      rw [show orl + 1 + 1 + j = orl + 1 + (j + 1) by omega]; exact this
    have hd : (relps == lps) = (relps.drop 0 == lps.drop 0) := by simp
    -- the tail
    refine specR_congr (m' := (pure (relps.drop 0 == lps.drop 0) : AM Bool) >>= fun q =>
        pure (if q && !lps.contains elim then some elim else none).isSome) (by simp [hd]) ?_
    refine specR_callNIH (C := ctxH C H) lgQ fLpsEqGo legParams [.op .add [vv lgR, .const 8], vv lgL, .const 0, vv lgB]
      legBody [cellA C (orl + 1), cellA C ol, BitVec.ofNat 64 0, BitVec.ofNat 64 relps.length] (by decide) rfl
      (by simp +decide [ctxLocals, lgLocals]) hcg
      ⟨by simp +decide [sev, Env.get_cons, Env.get, lgParams, ctxEnv]; exact cellA_add8 C orl,
        by simp +decide [sev, Env.get_cons, Env.get, lgParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, hlen], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu legParams _ rfl hlk)
        (leg_spec C hcg relps lps (orl + 1) ol hlen (by simp at hr; omega) relps.length 0 H s hp hel
          (elems_of_eblk hbl) (by omega) (by omega)))
      (fun q w s1 H1 hp1 hw => ?_)
    subst hw
    have hpH : H <+: H1 := hp1
    cases q
    · refine specR_ifI _ 1 (by simp [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hpH, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by simp [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      have he : (ctxH C H1).H[orl + 1]? = some (Enc.idxW elim) := by
        show H1[orl + 1]? = _
        have := hbr.2 0 (by simp); simp at this; exact get_prefix this hpH
      refine UD.specR_heapLoadI' (C := ctxH C H1) lgA _ (orl + 1) _ he (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, lgParams, ctxEnv]; exact cellA_add8 C orl) ?_
      simp only [Bool.true_and]
      refine specR_congr (m' := (pure ((lps.drop 0).contains elim) : AM Bool) >>= fun c =>
          pure (if !c then some elim else none).isSome) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) lgQ fLpsHas lhParams [vv lgL, vv lgA, .const 0, vv lgB]
        lhBody [cellA C ol, Enc.idxW elim, BitVec.ofNat 64 0, BitVec.ofNat 64 lps.length] (by decide) rfl
        (by simp +decide [ctxLocals, lgLocals]) hch
        ⟨by simp +decide [sev, Env.get_cons, Env.get, lgParams, ctxEnv],
          by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
        (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lhParams _ rfl hlk)
          (lh_spec C hch lps ol elim hl lps.length 0 H1 s1 (hp.trans hpH) (fun j hj => get_prefix (elems_of_eblk hbl j hj) hpH)
            (by omega) (by omega)))
        (fun c w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW (!c)) (by cases c <;> simp [sev, Env.get_cons, boolW,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun t ht => ⟨H2, hpH.trans hp2, by cases c <;> simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hlen : rl.length ≠ lps.length + 1 := by intro c; simp [boolW, c] at h
    have hnone : (largeT lps rl).isSome = false := by
      cases rl with
      | nil => rfl
      | cons e r =>
        simp only [largeT]
        have : (r == lps) = false := beq_of_length_ne (by simp at hlen; omega)
        simp [this]
    rw [hnone]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
