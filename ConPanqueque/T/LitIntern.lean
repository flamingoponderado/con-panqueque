import ConPanqueque.T.LInternLv
import ConPanqueque.Start.PinName
import ConPanqueque.T.PinRead

/-!
# Interning a literal, node by node

A literal level (or expression) known when the program is built is interned by straight-line code: each
node's children into the next depth's locals, then the node (`genL d u rest`: `u`'s handle in `gl d`,
then `rest`). It refines the twin's plain interning (`internLevel`, `PlainIntern.plainE`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Lit

open ConPanqueque.T ConPanqueque.Start

/-- The level result local at depth `d`. -/
def gl (d : Nat) : MlS := ofString ("gl" ++ String.ofList (List.replicate d 'x'))

theorem gl_explode (d : Nat) : (gl d).explode =
    [BitVec.ofNat 8 'g'.toNat, BitVec.ofNat 8 'l'.toNat] ++ List.replicate d (BitVec.ofNat 8 'x'.toNat) := by
  simp [gl, ofString, List.map_replicate]

theorem gl_ne {i j : Nat} (h : i ≠ j) : gl i ≠ gl j := fun e => by
  have := congrArg (fun m => m.explode.length) e
  simp only [gl_explode, List.length_append, List.length_cons, List.length_nil, List.length_replicate] at this
  omega

theorem gl_ne_of {d : Nat} {m : MlS} (h : m.explode.head? ≠ some (BitVec.ofNat 8 'g'.toNat)) : gl d ≠ m :=
  fun e => h (by rw [← e, gl_explode]; rfl)

theorem gl_ne_vPn (d : Nat) : gl d ≠ vPn := gl_ne_of (by simp [vPn, ofString])
theorem gl_ne_vKa (d : Nat) : gl d ≠ vKa := gl_ne_of (by simp [vKa, ofString])

/-- A literal level's names are string names the name interner takes. -/
def LvlOK : ConLeche.Level → Prop
  | .zero => True
  | .succ u => LvlOK u
  | .max u v => LvlOK u ∧ LvlOK v
  | .imax u v => LvlOK u ∧ LvlOK v
  | .param n => ∃ cs, strComps n = some cs ∧ compsOK cs

/-- Intern literal level `u` into `gl d`, then `rest`. -/
def genL (C : Ctx) : Nat → ConLeche.Level → ProgHOL 64 → ProgHOL 64
  | d, .zero, rest => .seq (.call (some (some (.local, gl d), none)) fInternLZero []) rest
  | d, .succ u, rest => genL C d u (.seq (.call (some (some (.local, gl d), none)) fInternLSucc [vv (gl d)]) rest)
  | d, .max u v, rest => genL C d u (genL C (d + 1) v
      (.seq (.call (some (some (.local, gl d), none)) fInternLMax [vv (gl d), vv (gl (d + 1))]) rest))
  | d, .imax u v, rest => genL C d u (genL C (d + 1) v
      (.seq (.call (some (some (.local, gl d), none)) fInternLImax [vv (gl d), vv (gl (d + 1))]) rest))
  | d, .param n, rest => nameP C ((strComps n).getD [])
      (.seq (.call (some (some (.local, gl d), none)) fInternLParam [vv vPn]) rest)

/-- `Γ'` agrees with `Γ` off the level locals from depth `d` and the name interner's two locals. -/
def AgreeL (Γ Γ' : Env) (d : Nat) : Prop :=
  ∀ y, (∀ j, d ≤ j → y ≠ gl j) → y ≠ vPn → y ≠ vKa → Γ'.get y = Γ.get y

theorem agreeL_refl (Γ : Env) (d : Nat) : AgreeL Γ Γ d := fun _ _ _ _ => rfl

theorem agreeL_trans {Γ1 Γ2 Γ3 : Env} {d : Nat} (h1 : AgreeL Γ1 Γ2 d) (h2 : AgreeL Γ2 Γ3 d) : AgreeL Γ1 Γ3 d :=
  fun y hy h3 h4 => (h2 y hy h3 h4).trans (h1 y hy h3 h4)

theorem agreeL_succ {Γ1 Γ2 : Env} {d : Nat} (h : AgreeL Γ1 Γ2 (d + 1)) : AgreeL Γ1 Γ2 d :=
  fun y hy h3 h4 => h y (fun j hj => hy j (by omega)) h3 h4


theorem agreeL_cons {Γ : Env} {d j : Nat} (hj : d ≤ j) (w : BitVec 64) : AgreeL Γ ((gl j, w) :: Γ) d :=
  fun y hy _ _ => by rw [Env.get_cons, ite_eq_right (fun e => hy j hj e)]

/-- The level local at depth `d` survives what depth `d + 1` on writes. -/
theorem agreeL_keep {Γ Γ' : Env} {d : Nat} (h : AgreeL Γ Γ' (d + 1)) : Γ'.get (gl d) = Γ.get (gl d) :=
  h (gl d) (fun j hj e => gl_ne (by omega) e) (gl_ne_vPn d) (gl_ne_vKa d)

/-- How deep a literal level's locals go. -/
def ldepth : ConLeche.Level → Nat
  | .zero => 1
  | .succ u => ldepth u
  | .max u v => max (ldepth u) (ldepth v + 1)
  | .imax u v => max (ldepth u) (ldepth v + 1)
  | .param _ => 1

theorem ldepth_pos : ∀ u : ConLeche.Level, 1 ≤ ldepth u
  | .zero => Nat.le_refl _
  | .succ u => ldepth_pos u
  | .max u _ => Nat.le_trans (ldepth_pos u) (Nat.le_max_left _ _)
  | .imax u _ => Nat.le_trans (ldepth_pos u) (Nat.le_max_left _ _)
  | .param _ => Nat.le_refl _

/-- The level node functions and the name interner. -/
structure LCodes (C : Ctx) : Prop where
  z : C.code.lookup fInternLZero = some ([], internLZeroBody, .one)
  s : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  m : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one)
  i : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one)
  p : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  n : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one)

section
variable {σ : Type}

theorem genL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : ConPanqueque.Front.FrontOK C)
    (hA : denoteN C.St.ns default = some .anonymous) (hc : LCodes C) (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D) :
    ∀ (u : ConLeche.Level) (d : Nat) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState) {β : Type}
      {k : LIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}, LvlOK u →
      (∀ j, d ≤ j → j < d + ldepth u → gl j ∈ D) →
      (∀ h s' Γ', AgreeL Γ Γ' d → Γ'.get (gl d) = some (Enc.idxW h) →
        SpecR (Inv C s' Γ' [] D) rest s' (k h) R) →
      SpecR (Inv C s Γ M D) (genL C d u rest) s (internLevel u >>= k) R := by
  intro u
  induction u with
  | zero =>
    intro d rest Γ M s β k R _ hD hk
    unfold genL
    refine specR_congr (m' := internLNode .zero >>= k) (by simp [internLevel]) ?_
    exact callLN (gl d) fInternLZero [] [] internLZeroBody [] (by decide) rfl (hD d (Nat.le_refl _) (by simp [ldepth]))
      hc.z trivial .zero (internLZero_body_spec ra C hok s)
      (fun h s' _ => hk h s' _ (agreeL_cons (Nat.le_refl _) _) (by simp [Env.get_cons]))
  | succ u ih =>
    intro d rest Γ M s β k R hu hD hk
    unfold genL
    refine specR_congr (m' := internLevel u >>= fun hu => internLNode (.succ hu) >>= k)
      (by simp [internLevel, bind_assoc]) ?_
    refine ih d _ Γ M s hu (fun j h1 h2 => hD j h1 (by simpa [ldepth] using h2)) (fun h1 s1 Γ1 ag1 hg1 => ?_)
    exact callLN (gl d) fInternLSucc [lEu] [vv (gl d)] internLSuccBody [Enc.idxW h1] (by decide) rfl
      (hD d (Nat.le_refl _) (by have := ldepth_pos u; simp [ldepth]; omega)) hc.s ⟨by simp [sev, vv, hg1], trivial⟩ (.succ h1)
      (internLSucc_body_spec ra C hok s1 h1)
      (fun h s' _ => hk h s' _ (agreeL_trans ag1 (agreeL_cons (Nat.le_refl _) _)) (by simp [Env.get_cons]))
  | max u v ihu ihv =>
    intro d rest Γ M s β k R huv hD hk
    unfold genL
    refine specR_congr (m' := internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.max hu hv) >>= k)
      (by simp [internLevel, bind_assoc]) ?_
    refine ihu d _ Γ M s huv.1 (fun j h1 h2 => hD j h1 (by simp [ldepth]; omega)) (fun h1 s1 Γ1 ag1 hg1 => ?_)
    refine ihv (d + 1) _ Γ1 [] s1 huv.2 (fun j h1 h2 => hD j (by omega) (by simp [ldepth]; omega))
      (fun h2 s2 Γ2 ag2 hg2 => ?_)
    have hg1' : Γ2.get (gl d) = some (Enc.idxW h1) := by rw [agreeL_keep ag2]; exact hg1
    exact callLN (gl d) fInternLMax [lEu, lEv] [vv (gl d), vv (gl (d + 1))] internLMaxBody [Enc.idxW h1, Enc.idxW h2]
      (by decide) rfl (hD d (Nat.le_refl _) (by have := ldepth_pos u; simp [ldepth]; omega)) hc.m
      ⟨by simp [sev, vv, hg1'], by simp [sev, vv, hg2], trivial⟩ (.max h1 h2) (internLMax_body_spec ra C hok s2 h1 h2)
      (fun h s' _ => hk h s' _ (agreeL_trans ag1 (agreeL_trans (agreeL_succ ag2) (agreeL_cons (Nat.le_refl _) _)))
        (by simp [Env.get_cons]))
  | imax u v ihu ihv =>
    intro d rest Γ M s β k R huv hD hk
    unfold genL
    refine specR_congr (m' := internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.imax hu hv) >>= k)
      (by simp [internLevel, bind_assoc]) ?_
    refine ihu d _ Γ M s huv.1 (fun j h1 h2 => hD j h1 (by simp [ldepth]; omega)) (fun h1 s1 Γ1 ag1 hg1 => ?_)
    refine ihv (d + 1) _ Γ1 [] s1 huv.2 (fun j h1 h2 => hD j (by omega) (by simp [ldepth]; omega))
      (fun h2 s2 Γ2 ag2 hg2 => ?_)
    have hg1' : Γ2.get (gl d) = some (Enc.idxW h1) := by rw [agreeL_keep ag2]; exact hg1
    exact callLN (gl d) fInternLImax [lEu, lEv] [vv (gl d), vv (gl (d + 1))] internLImaxBody [Enc.idxW h1, Enc.idxW h2]
      (by decide) rfl (hD d (Nat.le_refl _) (by have := ldepth_pos u; simp [ldepth]; omega)) hc.i
      ⟨by simp [sev, vv, hg1'], by simp [sev, vv, hg2], trivial⟩ (.imax h1 h2) (internLImax_body_spec ra C hok s2 h1 h2)
      (fun h s' _ => hk h s' _ (agreeL_trans ag1 (agreeL_trans (agreeL_succ ag2) (agreeL_cons (Nat.le_refl _) _)))
        (by simp [Env.get_cons]))
  | param n =>
    intro d rest Γ M s β k R hn hD hk
    obtain ⟨cs, hcs, hcok⟩ := hn
    unfold genL
    rw [hcs, Option.getD_some]
    refine specR_congr (m' := internName n >>= fun hn => internLNode (.param hn) >>= k)
      (by simp [internLevel, bind_assoc]) ?_
    refine specR_atEntry fun t0 ht0 => ?_
    refine name_spec ra C hok hf hc.n D hPn hKa n cs hcs hcok s ⟨ht0.sr.twf⟩ (denoteN_ext hA ht0.sr.floor) Γ M _
      (fun h1 s1 Γ1 ag1 hg1 _ => ?_)
    exact callLN (gl d) fInternLParam [lEn] [vv vPn] internLParamBody [Enc.idxW h1] (by decide) rfl
      (hD d (Nat.le_refl _) (by simp [ldepth])) hc.p ⟨by simp [sev, vv, hg1], trivial⟩ (.param h1)
      (internLParam_body_spec ra C hok s1 h1)
      (fun h s' _ => hk h s' _ (fun y hy h3 h4 => by
          rw [Env.get_cons, ite_eq_right (fun e => hy d (Nat.le_refl _) e)]; exact ag1 y h3 h4)
        (by simp [Env.get_cons]))

end

end ConPanqueque.T.Lit
