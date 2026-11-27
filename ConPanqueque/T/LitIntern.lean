import ConPanqueque.T.LInternLv
import ConPanqueque.Start.PinName
import ConPanqueque.T.PinRead
import ConPanqueque.T.LvlMk
import ConPanqueque.T.SubstLsTop
import ConPanqueque.T.CtxTr
import ConPanqueque.T.EIntern2
import ConPanqueque.Logic.PlainIntern

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

/-- A generated local: family `c` at depth `d`. -/
def gv (c : Char) (d : Nat) : MlS := ofString (String.ofList ('g' :: c :: List.replicate d 'x'))

/-- The level result local at depth `d`. -/
abbrev gl (d : Nat) : MlS := gv 'l' d

theorem gv_explode (c : Char) (d : Nat) : (gv c d).explode =
    BitVec.ofNat 8 'g'.toNat :: BitVec.ofNat 8 c.toNat :: List.replicate d (BitVec.ofNat 8 'x'.toNat) := by
  simp [gv, ofString, List.map_replicate]

theorem gv_ne {c c' : Char} {i j : Nat} (h : i ≠ j) : gv c i ≠ gv c' j := fun e => by
  have := congrArg (fun m => m.explode.length) e
  simp only [gv_explode, List.length_cons, List.length_replicate] at this
  omega

theorem gv_ne_c {c c' : Char} {i j : Nat} (h : BitVec.ofNat 8 c.toNat ≠ BitVec.ofNat 8 c'.toNat) : gv c i ≠ gv c' j :=
  fun e => by
  have := congrArg (fun m => m.explode.tail.head?) e
  simp only [gv_explode, List.tail_cons, List.head?_cons, Option.some.injEq] at this
  exact h this

theorem gl_ne {i j : Nat} (h : i ≠ j) : gl i ≠ gl j := gv_ne h

theorem gv_ne_of {c : Char} {d : Nat} {m : MlS} (h : m.explode.head? ≠ some (BitVec.ofNat 8 'g'.toNat)) : gv c d ≠ m :=
  fun e => h (by rw [← e, gv_explode]; rfl)

theorem gv_ne_vPn (c : Char) (d : Nat) : gv c d ≠ vPn := gv_ne_of (by simp [vPn, ofString])
theorem gv_ne_vKa (c : Char) (d : Nat) : gv c d ≠ vKa := gv_ne_of (by simp [vKa, ofString])

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

theorem allocP_ctxH (C : Ctx) (H : List (BitVec 64)) (x : MlS) (e : ExpHOL 64) (r : ProgHOL 64) :
    allocP (ctxH C H) x e r = allocP C x e r := rfl

theorem stepsP_ctxH (C : Ctx) (H : List (BitVec 64)) : ∀ (cs : List String) (r : ProgHOL 64),
    stepsP (ctxH C H) cs r = stepsP C cs r
  | [], _ => rfl
  | c :: cs, r => by simp only [stepsP, strStepP, allocP_ctxH, stepsP_ctxH C H cs r]

theorem genL_ctxH (C : Ctx) (H : List (BitVec 64)) : ∀ (d : Nat) (u : ConLeche.Level) (r : ProgHOL 64),
    genL (ctxH C H) d u r = genL C d u r
  | d, .zero, r => rfl
  | d, .succ u, r => by simp only [genL, genL_ctxH C H d u]
  | d, .max u v, r => by simp only [genL, genL_ctxH C H d u, genL_ctxH C H (d + 1) v]
  | d, .imax u v, r => by simp only [genL, genL_ctxH C H d u, genL_ctxH C H (d + 1) v]
  | d, .param n, r => by simp only [genL, nameP, stepsP_ctxH]

/-- `Γ'` agrees with `Γ` off the level locals from depth `d` and the name interner's two locals. -/
def AgreeL (Γ Γ' : Env) (d : Nat) : Prop :=
  ∀ y, (∀ c j, d ≤ j → y ≠ gv c j) → y ≠ vPn → y ≠ vKa → Γ'.get y = Γ.get y

theorem agreeL_refl (Γ : Env) (d : Nat) : AgreeL Γ Γ d := fun _ _ _ _ => rfl

theorem agreeL_trans {Γ1 Γ2 Γ3 : Env} {d : Nat} (h1 : AgreeL Γ1 Γ2 d) (h2 : AgreeL Γ2 Γ3 d) : AgreeL Γ1 Γ3 d :=
  fun y hy h3 h4 => (h2 y hy h3 h4).trans (h1 y hy h3 h4)

theorem agreeL_succ {Γ1 Γ2 : Env} {d : Nat} (h : AgreeL Γ1 Γ2 (d + 1)) : AgreeL Γ1 Γ2 d :=
  fun y hy h3 h4 => h y (fun c j hj => hy c j (by omega)) h3 h4


theorem agreeL_cons {Γ : Env} {d j : Nat} {c : Char} (hj : d ≤ j) (w : BitVec 64) : AgreeL Γ ((gv c j, w) :: Γ) d :=
  fun y hy _ _ => by rw [Env.get_cons, ite_eq_right (fun e => hy c j hj e)]

/-- The level local at depth `d` survives what depth `d + 1` on writes. -/
theorem agreeL_keep {Γ Γ' : Env} {d : Nat} {c : Char} (h : AgreeL Γ Γ' (d + 1)) : Γ'.get (gv c d) = Γ.get (gv c d) :=
  h (gv c d) (fun _ j hj e => gv_ne (by omega) e) (gv_ne_vPn c d) (gv_ne_vKa c d)

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
          rw [Env.get_cons, ite_eq_right (fun e => hy 'l' d (Nat.le_refl _) e)]; exact ag1 y h3 h4)
        (by simp [Env.get_cons]))

end

/-! ## Level lists -/

/-- Levels `us` into the key block at `gv 'k' d` from slot `i` (each through `gl (d + 1)`), then `rest`. -/
def fillLs (C : Ctx) (d : Nat) : List ConLeche.Level → Nat → ProgHOL 64 → ProgHOL 64
  | [], _, rest => rest
  | u :: us, i, rest => genL C (d + 1) u
      (.seq (.store (.op .add [vv (gv 'k' d), .const (BitVec.ofNat 64 (8 * i))]) (vv (gl (d + 1))))
        (fillLs C d us (i + 1) rest))

/-- Intern literal level list `us` into `gv 's' d`, then `rest`. -/
def genLs (C : Ctx) (d : Nat) (us : List ConLeche.Level) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C (gv 'k' d) (.const (BitVec.ofNat 64 (8 * us.length)))
    (fillLs C d us 0 (.seq (.call (some (some (.local, gv 's' d), none)) fInternLs
      [vv (gv 'k' d), .const (BitVec.ofNat 64 us.length)]) rest))

def lsdepth (us : List ConLeche.Level) : Nat := (us.map ldepth).foldl max 0 + 1

section
variable {σ : Type}

theorem lit_dropMem {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ}
    (h : Inv C s Γ M D t) : Inv C s Γ [] D t :=
  ⟨h.sr, h.env, fun _ _ h' => absurd h' (by simp), h.decl⟩

theorem fillLs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous) (hc : LCodes C)
    (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D) (d o n : Nat) (H1 : List (BitVec 64)) (ho : H1.length = o) :
    ∀ (us : List ConLeche.Level) (i : Nat) (hs : List LIdx) (H : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env)
      (M : Mem) (s : AState) {β : Type} {k : List LIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
      (_ : ∀ u ∈ us, LvlOK u) (_ : ∀ u ∈ us, ∀ j, d + 1 ≤ j → j < d + 1 + ldepth u → gl j ∈ D)
      (hl : hs.length = i) (_ : i + us.length = n) (_ : H1 <+: H) (_ : H.length = o + n)
      (_ : ∀ j (hj : j < i), H[o + j]? = some (Enc.idxW (hs[j]'(by omega))))
      (_ : Γ.get (gv 'k' d) = some (cellA C o))
      (_ : ∀ hs' s' Γ' H' (e1 : (hs ++ hs').length = n),
        (∀ j (hj : j < n), H'[o + j]? = some (Enc.idxW ((hs ++ hs')[j]'(by omega)))) →
        H1 <+: H' → H'.length = o + n → AgreeL Γ Γ' (d + 1) →
        SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k (hs ++ hs')) R),
      SpecR (Inv (ctxH C H) s Γ M D) (fillLs C d us i rest) s (internLevelList us >>= fun hs' => k (hs ++ hs')) R := by
  intro us
  induction us with
  | nil =>
    intro i hs H rest Γ M s β k R _ _ hl hn hp hH hcell hk0 hk
    unfold fillLs
    simp only [internLevelList, pure_bind, List.append_nil]
    intro t ht
    simp only [List.length_nil, Nat.add_zero] at hn
    have := hk [] s Γ H (by simp; omega) (fun j hj => by simpa using hcell j (by omega)) hp hH (agreeL_refl _ _)
    rw [List.append_nil] at this
    exact this t (lit_dropMem ht)
  | cons u us ih =>
    intro i hs H rest Γ M s β k R hok' hD hl hn hp hH hcell hk0 hk
    unfold fillLs
    refine specR_congr (m' := internLevel u >>= fun hu => internLevelList us >>= fun hs' => k (hs ++ hu :: hs'))
      (by simp [internLevelList, bind_assoc]) ?_
    rw [← genL_ctxH C H]
    refine genL_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hf) hA (by ctx_tr hc) D hPn hKa u (d + 1) _ Γ M s
      (hok' u (List.mem_cons_self ..)) (hD u (List.mem_cons_self ..)) (fun hu s1 Γ1 ag1 hg1 => ?_)
    have hk1 : Γ1.get (gv 'k' d) = some (cellA C o) := by rw [agreeL_keep ag1]; exact hk0
    simp only [List.length_cons] at hn
    have hlt : o + i < H.length := by omega
    refine specR_heapStoreI (ctxOK_H hok H) _ _ (o + i) hlt (Enc.idxW hu)
      (by simp only [sev, vv, hk1]; simp; exact cellA_add_ofNat C o i) (by simp [sev, vv, hg1]) ?_
    have := ih (i + 1) (hs ++ [hu]) (H.set (o + i) (Enc.idxW hu)) rest Γ1 [] s1
      (fun v hv => hok' v (List.mem_cons_of_mem _ hv)) (fun v hv => hD v (List.mem_cons_of_mem _ hv))
      (by simp [hl]) (by omega) (by
        obtain ⟨t, ht⟩ := hp
        refine ⟨t.set i (Enc.idxW hu), ?_⟩
        rw [← ht, ← ho]; simp [List.set_append_right])
      (by simp [hH])
      (fun j hj => by
        rw [List.getElem?_set]
        by_cases hji : j = i
        · subst hji
          rw [if_pos rfl]
          simp only [List.getElem_append_right (show hs.length ≤ j by omega)]
          simp [hl, hlt]
        · rw [if_neg (by omega)]
          have := hcell j (by omega)
          rw [this]; simp [List.getElem_append_left (show j < hs.length by omega)])
      hk1 (fun hs' s' Γ' H' e1 e2 e3 e4 e5 => by
        have := hk (hu :: hs') s' Γ' H' (by simpa using e1) (fun j hj => by simpa using e2 j hj) e3 e4
          (agreeL_trans ag1 e5)
        simpa using this)
    simp only [List.append_assoc, List.singleton_append] at this
    exact this


theorem genLs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous) (hc : LCodes C)
    (hcIs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D) (d : Nat) (us : List ConLeche.Level) (rest : ProgHOL 64)
    (Γ : Env) (M : Mem) (s : AState) {β : Type} {k : LsIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hus : ∀ u ∈ us, LvlOK u) (hD : ∀ u ∈ us, ∀ j, d + 1 ≤ j → j < d + 1 + ldepth u → gl j ∈ D)
    (hgk : gv 'k' d ∈ D) (hgs : gv 's' d ∈ D) (hlen : us.length < 2 ^ 59)
    (hk : ∀ h s' Γ' H', C.H <+: H' → AgreeL Γ Γ' d → Γ'.get (gv 's' d) = some (Enc.idxW h) →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (genLs C d us rest) s (internLevels us >>= k) R := by
  unfold genLs
  refine specR_congr (m' := internLevelList us >>= fun hs' => (fun hs => internLsNode hs >>= k) ([] ++ hs'))
    (by simp [internLevels, bind_assoc]) ?_
  refine specR_allocI (gv 'k' d) _ us.length (by omega) hgk (fun v => rfl) (fun H1 ws hp1 hws hroom => ?_)
  refine fillLs_spec ra C hok hf hA hc D hPn hKa d H1.length us.length H1 rfl us 0 [] (H1 ++ ws) _ ((gv 'k' d, cellA C H1.length) :: Γ) M s (k := fun hs => internLsNode hs >>= k) (R := R) hus hD rfl
    (by simp) (List.prefix_append _ _) (by simp [hws]) (fun j hj => absurd hj (by omega)) (by rw [Env.get_cons, if_pos rfl])
    (fun hs' s1 Γ1 H2 e1 e2 e3 e4 e5 => ?_)
  simp only [List.nil_append] at e1 e2 ⊢
  have gk : Γ1.get (gv 'k' d) = some (cellA C H1.length) := by
    rw [agreeL_keep e5, Env.get_cons, if_pos rfl]
  refine specR_callNIA (C := ctxH C H2) (gv 's' d) fInternLs [pKey, lEc] [vv (gv 'k' d), .const (BitVec.ofNat 64 us.length)]
    internLsBody [cellA C H1.length, BitVec.ofNat 64 hs'.length] (by decide) rfl hgs hcIs
    ⟨by simp [sev, vv, gk], by rw [e1]; rfl, trivial⟩
    (fun a w s' st => internLsNode hs' s1 = .ok (a, s') ∧ PostLs (ctxH (ctxH C H2) H1) a w s' st)
    (fun a w s' H' => H' = H1 ∧ w = Enc.idxW a)
    (fun a w s' st ⟨_, hw, hsr⟩ => ⟨H1, ⟨rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact internLs_body_spec ra (ctxH C H2) (ctxOK_H hok H2) s1 hs' H1.length H1 e3 (Nat.le_refl _)
        (by show H1.length + hs'.length ≤ H2.length; omega) (by omega)
        (fun j hj => e2 j (by omega)) _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
    (fun h w2 s2 H' ⟨e, hw⟩ => ?_)
  subst hw
  exact hk h s2 _ H' (e ▸ hp1) (fun y hy h3 h4 => by
      rw [Env.get_cons, ite_eq_right (fun e => hy 's' d (Nat.le_refl _) e)]
      rw [e5 y (fun c j hj => hy c j (by omega)) h3 h4, Env.get_cons, ite_eq_right (fun e => hy 'k' d (Nat.le_refl _) e)])
    (by simp [Env.get_cons])

end

/-! ## Expressions -/

/-- The expression result local at depth `d`. -/
abbrev ge (d : Nat) : MlS := gv 'e' d

/-- A literal expression the generator takes: the basis literals' six node kinds, string names. -/
def ExprOK : ConLeche.Expr → Prop
  | .bvar i => i < 2 ^ 63
  | .sort u => LvlOK u
  | .const n us => (∃ cs, strComps n = some cs ∧ compsOK cs) ∧ (∀ u ∈ us, LvlOK u) ∧ us.length < 2 ^ 59
  | .app f a => ExprOK f ∧ ExprOK a
  | .lam t b => ExprOK t ∧ ExprOK b
  | .forallE t b => ExprOK t ∧ ExprOK b
  | _ => False

/-- How deep a literal expression's locals go. -/
def edepth : ConLeche.Expr → Nat
  | .sort u => ldepth u
  | .const _ us => (us.map ldepth).foldl max 0 + 3
  | .app f a => max (edepth f) (edepth a + 1)
  | .lam t b => max (edepth t) (edepth b + 1)
  | .forallE t b => max (edepth t) (edepth b + 1)
  | _ => 1

theorem edepth_pos : ∀ e : ConLeche.Expr, 1 ≤ edepth e
  | .sort u => ldepth_pos u
  | .const _ _ => by simp [edepth]
  | .app f _ => Nat.le_trans (edepth_pos f) (Nat.le_max_left _ _)
  | .lam t _ => Nat.le_trans (edepth_pos t) (Nat.le_max_left _ _)
  | .forallE t _ => Nat.le_trans (edepth_pos t) (Nat.le_max_left _ _)
  | .bvar _ => Nat.le_refl _
  | .lit _ => Nat.le_refl _
  | .fvar _ _ => Nat.le_refl _
  | .letE _ _ _ => Nat.le_refl _
  | .proj _ _ _ => Nat.le_refl _

theorem ldepth_le_fold (us : List ConLeche.Level) (m : Nat) : ∀ u ∈ us, ldepth u ≤ (us.map ldepth).foldl max m := by
  induction us generalizing m with
  | nil => intro u hu; cases hu
  | cons v vs ih =>
    intro u hu
    simp only [List.map_cons, List.foldl_cons]
    rcases List.mem_cons.mp hu with rfl | hu
    · have : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a := by
        intro l; induction l with
        | nil => intro a; exact Nat.le_refl _
        | cons x xs ihx => intro a; exact Nat.le_trans (Nat.le_max_left _ _) (ihx _)
      exact Nat.le_trans (Nat.le_max_right _ _) (this _ _)
    · exact ih _ u hu

/-- Intern literal expression `e` into `ge d`, then `rest`. -/
def genE (C : Ctx) : Nat → ConLeche.Expr → ProgHOL 64 → ProgHOL 64
  | d, .bvar i, rest => .seq (.call (some (some (.local, ge d), none)) fInternBVar [.const (BitVec.ofNat 64 i)]) rest
  | d, .sort u, rest => genL C d u (.seq (.call (some (some (.local, ge d), none)) fInternSort [vv (gl d)]) rest)
  | d, .const n us, rest => nameP C ((strComps n).getD [])
      (.seq (.assign .local (gv 'n' d) (vv vPn))
      (genLs C (d + 1) us (.seq (.call (some (some (.local, ge d), none)) fInternConst
        [vv (gv 'n' d), vv (gv 's' (d + 1))]) rest)))
  | d, .app f a, rest => genE C d f (genE C (d + 1) a
      (.seq (.call (some (some (.local, ge d), none)) fInternApp [vv (ge d), vv (ge (d + 1))]) rest))
  | d, .lam t b, rest => genE C d t (genE C (d + 1) b
      (.seq (.call (some (some (.local, ge d), none)) fInternLam [vv (ge d), vv (ge (d + 1))]) rest))
  | d, .forallE t b, rest => genE C d t (genE C (d + 1) b
      (.seq (.call (some (some (.local, ge d), none)) fInternForallE [vv (ge d), vv (ge (d + 1))]) rest))
  | _, _, _ => hang

theorem genLs_ctxH (C : Ctx) (H : List (BitVec 64)) (d : Nat) (us : List ConLeche.Level) (r : ProgHOL 64) :
    genLs (ctxH C H) d us r = genLs C d us r := by
  unfold genLs
  have : ∀ (us : List ConLeche.Level) (i : Nat) (r : ProgHOL 64), fillLs (ctxH C H) d us i r = fillLs C d us i r := by
    intro us; induction us with
    | nil => intro i r; rfl
    | cons u us ih => intro i r; simp only [fillLs, genL_ctxH, ih]
  rw [allocP_ctxH, this]

theorem genE_ctxH (C : Ctx) (H : List (BitVec 64)) : ∀ (d : Nat) (e : ConLeche.Expr) (r : ProgHOL 64),
    genE (ctxH C H) d e r = genE C d e r
  | d, .bvar _, r => rfl
  | d, .sort u, r => by simp only [genE, genL_ctxH]
  | d, .const n us, r => by simp only [genE, nameP, stepsP_ctxH, genLs_ctxH]
  | d, .app f a, r => by simp only [genE, genE_ctxH C H d f, genE_ctxH C H (d + 1) a]
  | d, .lam t b, r => by simp only [genE, genE_ctxH C H d t, genE_ctxH C H (d + 1) b]
  | d, .forallE t b, r => by simp only [genE, genE_ctxH C H d t, genE_ctxH C H (d + 1) b]
  | d, .lit _, r => rfl
  | d, .fvar _ _, r => rfl
  | d, .letE _ _ _, r => rfl
  | d, .proj _ _ _, r => rfl

/-- The expression node functions, with the levels'. -/
structure ECodes (C : Ctx) : Prop where
  l : LCodes C
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  bvar : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  sort : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  const : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  lam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  all : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)

section
variable {σ : Type}

theorem callEN {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs) (m : AM EIdx)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s m (PostE C))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIM x f ps es B vs hnd hl hx hC hes (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hlk => fun t ht => by subst ht; exact hspec _ (pre_of_lookups hu ps vs hl hlk))
    (fun h w s' st ⟨hw, _⟩ => by subst hw; exact hk h s')

end

section
variable {σ : Type}

theorem agreeL_mono {Γ Γ' : Env} {d e : Nat} (h : AgreeL Γ Γ' e) (hde : d ≤ e) : AgreeL Γ Γ' d :=
  fun y hy h3 h4 => h y (fun c j hj => hy c j (by omega)) h3 h4

open ConPanqueque.Logic.PlainIntern in
theorem genE_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous) (hc : ECodes C)
    (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D) (N : Nat) (hD : ∀ c j, j < N → gv c j ∈ D) :
    ∀ (e : ConLeche.Expr) (d : Nat) (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
      {β : Type} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}, ExprOK e → d + edepth e ≤ N →
      (∀ h s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → Γ'.get (ge d) = some (Enc.idxW h) →
        SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k h) R) →
      SpecR (Inv (ctxH C H0) s Γ M D) (genE C d e rest) s (plainE e >>= k) R := by
  intro e
  induction e with
  | bvar i =>
    intro d H0 rest Γ M s β k R he hdN hk
    unfold genE plainE
    exact specR_internBVarI ra (ctxOK_H hok H0) hc.bvar (ge d) _ i he (hD _ _ (by simp [edepth] at hdN; omega)) rfl
      (fun h s' => hk h s' _ H0 (List.prefix_refl _) (agreeL_cons (Nat.le_refl _) _) (by simp [Env.get_cons]))
  | sort u =>
    intro d H0 rest Γ M s β k R he hdN hk
    unfold genE plainE
    rw [← genL_ctxH C H0]
    refine specR_congr (m' := internLevel u >>= fun hu => internE (.sort hu) >>= k) (by simp [bind_assoc]) ?_
    refine genL_spec ra (ctxH C H0) (ctxOK_H hok H0) (by ctx_tr hf) hA (by ctx_tr hc.l) D hPn hKa u d _ Γ M s he
      (fun j h1 h2 => hD _ _ (by simp [edepth] at hdN; omega)) (fun hu s1 Γ1 ag1 hg1 => ?_)
    exact callEN (C := ctxH C H0) (ge d) fInternSort [lEu] [vv (gl d)] sortBody [Enc.idxW hu] (by decide) rfl
      (hD _ _ (by have := ldepth_pos u; simp [edepth] at hdN; omega)) hc.sort ⟨by simp [sev, vv, hg1], trivial⟩ _
      (sort_body_spec ra (ctxH C H0) (ctxOK_H hok H0) s1 hu)
      (fun h s' => hk h s' _ H0 (List.prefix_refl _) (agreeL_trans ag1 (agreeL_cons (Nat.le_refl _) _))
        (by simp [Env.get_cons]))
  | const n us =>
    intro d H0 rest Γ M s β k R he hdN hk
    obtain ⟨⟨cs, hcs, hcok⟩, hus, hlen⟩ := he
    unfold genE plainE
    rw [hcs, Option.getD_some]
    refine specR_congr (m' := internName n >>= fun hn => internLevels us >>= fun hus => internE (.const hn hus) >>= k)
      (by simp [bind_assoc]) ?_
    have hd3 : d + 3 ≤ N := by simp [edepth] at hdN; omega
    refine specR_atEntry fun t0 ht0 => ?_
    rw [show nameP C cs = nameP (ctxH C H0) cs from by funext r; simp only [nameP, stepsP_ctxH]]
    refine name_spec ra (ctxH C H0) (ctxOK_H hok H0) (by ctx_tr hf) hc.l.n D hPn hKa n cs hcs hcok s ⟨ht0.sr.twf⟩
      (denoteN_ext hA ht0.sr.floor) Γ M _ (fun hn s1 Γ1 ag1 hg1 _ => ?_)
    refine specR_assignI (gv 'n' d) (vv vPn) (Enc.idxW hn) (hD _ _ (by omega)) (by simp [sev, vv, hg1]) ?_
    rw [← genLs_ctxH C H0]
    refine genLs_spec ra (ctxH C H0) (ctxOK_H hok H0) (by ctx_tr hf) hA (by ctx_tr hc.l) hc.ls D hPn hKa (d + 1) us _
      _ [] s1 hus (fun u hu j h1 h2 => hD _ _ (by
        have := ldepth_le_fold us 0 u hu; simp [edepth] at hdN; omega))
      (hD _ _ (by omega)) (hD _ _ (by omega)) hlen (fun hus' s2 Γ2 H2 hp2 ag2 hg2 => ?_)
    have gn : Γ2.get (gv 'n' d) = some (Enc.idxW hn) := by
      rw [agreeL_keep ag2]; simp [Env.get_cons]
    exact callEN (C := ctxH C H2) (ge d) fInternConst [lEn, lEus] [vv (gv 'n' d), vv (gv 's' (d + 1))] constBody
      [Enc.idxW hn, Enc.idxW hus'] (by decide) rfl (hD _ _ (by omega)) hc.const
      ⟨by simp [sev, vv, gn], by simp [sev, vv, hg2], trivial⟩ _
      (const_body_spec ra (ctxH C H2) (ctxOK_H hok H2) s2 hn hus')
      (fun h s' => hk h s' _ H2 hp2 (fun y hy h3 h4 => by
          rw [Env.get_cons, ite_eq_right (fun e => hy 'e' d (Nat.le_refl _) e)]
          rw [ag2 y (fun c j hj => hy c j (by omega)) h3 h4, Env.get_cons,
            ite_eq_right (fun e => hy 'n' d (Nat.le_refl _) e)]
          exact ag1 y h3 h4)
        (by simp [Env.get_cons]))
  | app f a ihf iha =>
    intro d H0 rest Γ M s β k R he hdN hk
    unfold genE plainE
    refine specR_congr (m' := plainE f >>= fun hf => plainE a >>= fun ha => internAppE hf ha >>= k)
      (by simp [bind_assoc]; rfl) ?_
    refine ihf d H0 _ Γ M s he.1 (by simp [edepth] at hdN; omega) (fun h1 s1 Γ1 H1 hp1 ag1 hg1 => ?_)
    refine iha (d + 1) H1 _ Γ1 [] s1 he.2 (by simp [edepth] at hdN; omega) (fun h2 s2 Γ2 H2 hp2 ag2 hg2 => ?_)
    have g1 : Γ2.get (ge d) = some (Enc.idxW h1) := by rw [agreeL_keep ag2]; exact hg1
    exact specR_internAppI ra (ctxOK_H hok H2) hc.app (ge d) _ _ h1 h2
      (hD _ _ (by have := edepth_pos f; simp [edepth] at hdN; omega)) (by simp [sev, vv, g1]) (by simp [sev, vv, hg2])
      (fun h s' => hk h s' _ H2 (hp1.trans hp2)
        (agreeL_trans ag1 (agreeL_trans (agreeL_mono ag2 (Nat.le_succ _)) (agreeL_cons (Nat.le_refl _) _)))
        (by simp [Env.get_cons]))
  | lam t b iht ihb =>
    intro d H0 rest Γ M s β k R he hdN hk
    unfold genE plainE
    refine specR_congr (m' := plainE t >>= fun ht => plainE b >>= fun hb => internLamE ht hb >>= k)
      (by simp [bind_assoc]; rfl) ?_
    refine iht d H0 _ Γ M s he.1 (by simp [edepth] at hdN; omega) (fun h1 s1 Γ1 H1 hp1 ag1 hg1 => ?_)
    refine ihb (d + 1) H1 _ Γ1 [] s1 he.2 (by simp [edepth] at hdN; omega) (fun h2 s2 Γ2 H2 hp2 ag2 hg2 => ?_)
    have g1 : Γ2.get (ge d) = some (Enc.idxW h1) := by rw [agreeL_keep ag2]; exact hg1
    exact specR_internLamI ra (ctxOK_H hok H2) hc.lam (ge d) _ _ h1 h2
      (hD _ _ (by have := edepth_pos t; simp [edepth] at hdN; omega)) (by simp [sev, vv, g1]) (by simp [sev, vv, hg2])
      (fun h s' => hk h s' _ H2 (hp1.trans hp2)
        (agreeL_trans ag1 (agreeL_trans (agreeL_mono ag2 (Nat.le_succ _)) (agreeL_cons (Nat.le_refl _) _)))
        (by simp [Env.get_cons]))
  | forallE t b iht ihb =>
    intro d H0 rest Γ M s β k R he hdN hk
    unfold genE plainE
    refine specR_congr (m' := plainE t >>= fun ht => plainE b >>= fun hb => internForallEE ht hb >>= k)
      (by simp [bind_assoc]; rfl) ?_
    refine iht d H0 _ Γ M s he.1 (by simp [edepth] at hdN; omega) (fun h1 s1 Γ1 H1 hp1 ag1 hg1 => ?_)
    refine ihb (d + 1) H1 _ Γ1 [] s1 he.2 (by simp [edepth] at hdN; omega) (fun h2 s2 Γ2 H2 hp2 ag2 hg2 => ?_)
    have g1 : Γ2.get (ge d) = some (Enc.idxW h1) := by rw [agreeL_keep ag2]; exact hg1
    exact specR_internForallEI ra (ctxOK_H hok H2) hc.all (ge d) _ _ h1 h2
      (hD _ _ (by have := edepth_pos t; simp [edepth] at hdN; omega)) (by simp [sev, vv, g1]) (by simp [sev, vv, hg2])
      (fun h s' => hk h s' _ H2 (hp1.trans hp2)
        (agreeL_trans ag1 (agreeL_trans (agreeL_mono ag2 (Nat.le_succ _)) (agreeL_cons (Nat.le_refl _) _)))
        (by simp [Env.get_cons]))
  | lit _ => intro _ _ _ _ _ _ _ _ _ he; exact he.elim
  | fvar _ _ _ => intro _ _ _ _ _ _ _ _ _ he; exact he.elim
  | letE _ _ _ _ _ _ => intro _ _ _ _ _ _ _ _ _ he; exact he.elim
  | proj _ _ _ _ => intro _ _ _ _ _ _ _ _ _ he; exact he.elim

end

/-! ## Constants -/

def NameLit (n : ConLeche.Name) : Prop := ∃ cs, strComps n = some cs ∧ compsOK cs

def genNames (C : Ctx) : List ConLeche.Name → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | n :: ns, rest => nameP C ((strComps n).getD []) (genNames C ns rest)

def genLvls (C : Ctx) (d : Nat) : List ConLeche.Level → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | u :: us, rest => genL C d u (genLvls C d us rest)

def genCV (C : Ctx) (d : Nat) (cv : ConLeche.ConstantVal) (rest : ProgHOL 64) : ProgHOL 64 :=
  nameP C ((strComps cv.name).getD []) (genNames C cv.levelParams (genE C d cv.type rest))

def genFire (C : Ctx) (d : Nat) : ConLeche.RecRuleFire → ProgHOL 64 → ProgHOL 64
  | .plain, rest => rest
  | .levels us, rest => genLvls C d us rest
  | .nested _ _, _ => hang

def genRule (C : Ctx) (d : Nat) (rl : ConLeche.RecRule) (rest : ProgHOL 64) : ProgHOL 64 :=
  nameP C ((strComps rl.ctor).getD []) (genFire C d rl.fire (genE C d rl.rhs rest))

def genRules (C : Ctx) (d : Nat) : List ConLeche.RecRule → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | r :: rs, rest => genRule C d r (genRules C d rs rest)

def genCI (C : Ctx) (d : Nat) : ConLeche.ConstantInfo → ProgHOL 64 → ProgHOL 64
  | .axiomInfo v, rest => genCV C d v rest
  | .thmInfo v, rest => genCV C d v rest
  | .defnInfo v e _, rest => genCV C d v (genE C d e rest)
  | .indInfo v c, rest => genCV C d v (genNames C c.all (genNames C c.ctors rest))
  | .ctorInfo v _ _ T, rest => genCV C d v (nameP C ((strComps T).getD []) rest)
  | .recInfo v _ _ _ rs, rest => genCV C d v (genRules C d rs rest)

def genCIList (C : Ctx) (d : Nat) : List ConLeche.ConstantInfo → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | c :: cs, rest => genCI C d c (genCIList C d cs rest)

def CVLit (d N : Nat) (cv : ConLeche.ConstantVal) : Prop :=
  NameLit cv.name ∧ (∀ n ∈ cv.levelParams, NameLit n) ∧ ExprOK cv.type ∧ d + edepth cv.type ≤ N

def FireLit (d N : Nat) : ConLeche.RecRuleFire → Prop
  | .plain => True
  | .levels us => ∀ u ∈ us, LvlOK u ∧ d + ldepth u ≤ N
  | .nested _ _ => False

def RuleLit (d N : Nat) (rl : ConLeche.RecRule) : Prop :=
  NameLit rl.ctor ∧ FireLit d N rl.fire ∧ ExprOK rl.rhs ∧ d + edepth rl.rhs ≤ N

def CILit (d N : Nat) : ConLeche.ConstantInfo → Prop
  | .axiomInfo v => CVLit d N v
  | .thmInfo v => CVLit d N v
  | .defnInfo v e _ => CVLit d N v ∧ ExprOK e ∧ d + edepth e ≤ N
  | .indInfo v c => CVLit d N v ∧ (∀ n ∈ c.all, NameLit n) ∧ ∀ n ∈ c.ctors, NameLit n
  | .ctorInfo v _ _ T => CVLit d N v ∧ NameLit T
  | .recInfo v _ _ _ rs => CVLit d N v ∧ ∀ r ∈ rs, RuleLit d N r

theorem genNames_ctxH (C : Ctx) (H : List (BitVec 64)) : ∀ (ns : List ConLeche.Name) (r : ProgHOL 64),
    genNames (ctxH C H) ns r = genNames C ns r
  | [], _ => rfl
  | n :: ns, r => by simp only [genNames, nameP, stepsP_ctxH, genNames_ctxH C H ns r]

section
variable {σ : Type}

open ConPanqueque.Logic.PlainIntern

/-- The shared hypotheses of the constant-level specs. -/
structure GenEnv (C : Ctx) (D : List MlS) (N : Nat) : Prop where
  hok : CtxOK C
  hf : ConPanqueque.Front.FrontOK C
  hA : denoteN C.St.ns default = some .anonymous
  hc : ECodes C
  hPn : vPn ∈ D
  hKa : vKa ∈ D
  hD : ∀ c j, j < N → gv c j ∈ D

theorem name_step (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (n : ConLeche.Name) (hn : NameLit n) (d : Nat) (H0 : List (BitVec 64)) (rest : ProgHOL 64)
    (Γ : Env) (M : Mem) (s : AState) {β : Type} {k : NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ h s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k h) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (nameP C ((strComps n).getD []) rest) s (internName n >>= k) R := by
  obtain ⟨cs, hcs, hcok⟩ := hn
  rw [hcs, Option.getD_some]
  refine specR_atEntry fun t0 ht0 => ?_
  rw [show nameP C cs = nameP (ctxH C H0) cs from by funext r; simp only [nameP, stepsP_ctxH]]
  exact name_spec ra (ctxH C H0) (ctxOK_H G.hok H0) (by ctx_tr G.hf) G.hc.l.n D G.hPn G.hKa n cs hcs hcok s
    ⟨ht0.sr.twf⟩ (denoteN_ext G.hA ht0.sr.floor) Γ M _
    (fun h s1 Γ1 ag1 _ _ => hk h s1 Γ1 H0 (List.prefix_refl _) (fun y _ h3 h4 => ag1 y h3 h4))

theorem genNames_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) :
    ∀ (ns : List ConLeche.Name) (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
      {β : Type} {k : List NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}, (∀ n ∈ ns, NameLit n) →
      (∀ hs s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k hs) R) →
      SpecR (Inv (ctxH C H0) s Γ M D) (genNames C ns rest) s (ConRon.Arena.Frontend.internNameList ns >>= k) R := by
  intro ns
  induction ns with
  | nil =>
    intro H0 rest Γ M s β k R _ hk
    simp only [genNames, ConRon.Arena.Frontend.internNameList, pure_bind]
    intro t ht; exact hk [] s Γ H0 (List.prefix_refl _) (agreeL_refl _ _) t (lit_dropMem ht)
  | cons n ns ih =>
    intro H0 rest Γ M s β k R hns hk
    simp only [genNames, ConRon.Arena.Frontend.internNameList, bind_assoc]
    refine name_step ra G n (hns n (List.mem_cons_self ..)) d H0 _ Γ M s (fun h s1 Γ1 H1 hp1 ag1 => ?_)
    refine ih H1 rest Γ1 [] s1 (fun m hm => hns m (List.mem_cons_of_mem _ hm)) (fun hs s2 Γ2 H2 hp2 ag2 => ?_)
    simp only [pure_bind]
    exact hk _ s2 Γ2 H2 (hp1.trans hp2) (agreeL_trans ag1 ag2)

end

section
variable {σ : Type}

open ConPanqueque.Logic.PlainIntern

theorem genLvls_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) :
    ∀ (us : List ConLeche.Level) (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
      {β : Type} {k : List LIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop},
      (∀ u ∈ us, LvlOK u ∧ d + ldepth u ≤ N) →
      (∀ hs s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k hs) R) →
      SpecR (Inv (ctxH C H0) s Γ M D) (genLvls C d us rest) s (internLevelList us >>= k) R := by
  intro us
  induction us with
  | nil =>
    intro H0 rest Γ M s β k R _ hk
    simp only [genLvls, internLevelList, pure_bind]
    intro t ht; exact hk [] s Γ H0 (List.prefix_refl _) (agreeL_refl _ _) t (lit_dropMem ht)
  | cons u us ih =>
    intro H0 rest Γ M s β k R hus hk
    simp only [genLvls, internLevelList, bind_assoc]
    obtain ⟨hu, hdu⟩ := hus u (List.mem_cons_self ..)
    rw [← genL_ctxH C H0]
    refine genL_spec ra (ctxH C H0) (ctxOK_H G.hok H0) (by ctx_tr G.hf) G.hA (by ctx_tr G.hc.l) D G.hPn G.hKa u d _ Γ M s hu
      (fun j h1 h2 => G.hD _ _ (by omega)) (fun h1 s1 Γ1 ag1 _ => ?_)
    refine ih H0 rest Γ1 [] s1 (fun v hv => hus v (List.mem_cons_of_mem _ hv)) (fun hs s2 Γ2 H2 hp2 ag2 => ?_)
    simp only [pure_bind]
    exact hk _ s2 Γ2 H2 hp2 (agreeL_trans ag1 ag2)

theorem genCV_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) (cv : ConLeche.ConstantVal) (H0 : List (BitVec 64)) (rest : ProgHOL 64)
    (Γ : Env) (M : Mem) (s : AState) {β : Type} {k : IConstantVal → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hcv : CVLit d N cv)
    (hk : ∀ r s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genCV C d cv rest) s (plainCV cv >>= k) R := by
  obtain ⟨hn, hl, he, hde⟩ := hcv
  unfold genCV plainCV
  simp only [bind_assoc]
  refine name_step ra G _ hn d H0 _ Γ M s (fun h1 s1 Γ1 H1 hp1 ag1 => ?_)
  refine genNames_spec ra G d _ H1 _ Γ1 [] s1 hl (fun hs s2 Γ2 H2 hp2 ag2 => ?_)
  refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa N G.hD _ d H2 rest Γ2 [] s2 he hde
    (fun h s3 Γ3 H3 hp3 ag3 _ => ?_)
  simp only [pure_bind]
  exact hk _ s3 Γ3 H3 (hp1.trans (hp2.trans hp3)) (agreeL_trans ag1 (agreeL_trans ag2 ag3))

theorem genFire_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) (f : ConLeche.RecRuleFire) (H0 : List (BitVec 64)) (rest : ProgHOL 64)
    (Γ : Env) (M : Mem) (s : AState) {β : Type} {k : IRecRuleFire → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hf : FireLit d N f)
    (hk : ∀ r s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genFire C d f rest) s (plainFire f >>= k) R := by
  cases f with
  | plain =>
    simp only [genFire, plainFire, pure_bind]
    intro t ht; exact hk _ s Γ H0 (List.prefix_refl _) (agreeL_refl _ _) t (lit_dropMem ht)
  | levels us =>
    simp only [genFire, plainFire, bind_assoc]
    exact genLvls_spec ra G d us H0 rest Γ M s hf (fun hs s' Γ' H' hp ag => by
      simp only [pure_bind]; exact hk _ s' Γ' H' hp ag)
  | nested _ _ => exact hf.elim

theorem genRule_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) (rl : ConLeche.RecRule) (H0 : List (BitVec 64)) (rest : ProgHOL 64)
    (Γ : Env) (M : Mem) (s : AState) {β : Type} {k : IRecRule → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hr : RuleLit d N rl)
    (hk : ∀ r s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genRule C d rl rest) s (plainRule rl >>= k) R := by
  obtain ⟨hn, hf, he, hde⟩ := hr
  unfold genRule plainRule
  simp only [bind_assoc]
  refine name_step ra G _ hn d H0 _ Γ M s (fun h1 s1 Γ1 H1 hp1 ag1 => ?_)
  refine genFire_spec ra G d _ H1 _ Γ1 [] s1 hf (fun f s2 Γ2 H2 hp2 ag2 => ?_)
  refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa N G.hD _ d H2 rest Γ2 [] s2 he hde
    (fun h s3 Γ3 H3 hp3 ag3 _ => ?_)
  simp only [pure_bind]
  exact hk _ s3 Γ3 H3 (hp1.trans (hp2.trans hp3)) (agreeL_trans ag1 (agreeL_trans ag2 ag3))

theorem genRules_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) :
    ∀ (rs : List ConLeche.RecRule) (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
      {β : Type} {k : List IRecRule → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}, (∀ r ∈ rs, RuleLit d N r) →
      (∀ hs s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k hs) R) →
      SpecR (Inv (ctxH C H0) s Γ M D) (genRules C d rs rest) s (plainRules rs >>= k) R := by
  intro rs
  induction rs with
  | nil =>
    intro H0 rest Γ M s β k R _ hk
    simp only [genRules, plainRules, pure_bind]
    intro t ht; exact hk [] s Γ H0 (List.prefix_refl _) (agreeL_refl _ _) t (lit_dropMem ht)
  | cons r rs ih =>
    intro H0 rest Γ M s β k R hrs hk
    simp only [genRules, plainRules, bind_assoc]
    refine genRule_spec ra G d r H0 _ Γ M s (hrs r (List.mem_cons_self ..)) (fun h1 s1 Γ1 H1 hp1 ag1 => ?_)
    refine ih H1 rest Γ1 [] s1 (fun m hm => hrs m (List.mem_cons_of_mem _ hm)) (fun hs s2 Γ2 H2 hp2 ag2 => ?_)
    simp only [pure_bind]
    exact hk _ s2 Γ2 H2 (hp1.trans hp2) (agreeL_trans ag1 ag2)

theorem genCI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) (c : ConLeche.ConstantInfo) (H0 : List (BitVec 64)) (rest : ProgHOL 64)
    (Γ : Env) (M : Mem) (s : AState) {β : Type} {k : IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hc : CILit d N c)
    (hk : ∀ r s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genCI C d c rest) s (plainCI c >>= k) R := by
  cases c with
  | axiomInfo v =>
    simp only [genCI, plainCI, bind_assoc]
    exact genCV_spec ra G d v H0 rest Γ M s hc (fun r s' Γ' H' hp ag => by simp only [pure_bind]; exact hk _ s' Γ' H' hp ag)
  | thmInfo v =>
    simp only [genCI, plainCI, bind_assoc]
    exact genCV_spec ra G d v H0 rest Γ M s hc (fun r s' Γ' H' hp ag => by simp only [pure_bind]; exact hk _ s' Γ' H' hp ag)
  | defnInfo v e hint =>
    simp only [genCI, plainCI, bind_assoc]
    refine genCV_spec ra G d v H0 _ Γ M s hc.1 (fun r1 s1 Γ1 H1 hp1 ag1 => ?_)
    refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa N G.hD _ d H1 rest Γ1 [] s1 hc.2.1 hc.2.2
      (fun h s2 Γ2 H2 hp2 ag2 _ => ?_)
    simp only [pure_bind]
    exact hk _ s2 Γ2 H2 (hp1.trans hp2) (agreeL_trans ag1 ag2)
  | indInfo v caps =>
    simp only [genCI, plainCI, bind_assoc]
    refine genCV_spec ra G d v H0 _ Γ M s hc.1 (fun r1 s1 Γ1 H1 hp1 ag1 => ?_)
    unfold ConRon.Arena.Frontend.internCaps
    simp only [bind_assoc]
    refine genNames_spec ra G d _ H1 _ Γ1 [] s1 hc.2.1 (fun hs s2 Γ2 H2 hp2 ag2 => ?_)
    refine genNames_spec ra G d _ H2 rest Γ2 [] s2 hc.2.2 (fun hs' s3 Γ3 H3 hp3 ag3 => ?_)
    simp only [pure_bind]
    exact hk _ s3 Γ3 H3 (hp1.trans (hp2.trans hp3)) (agreeL_trans ag1 (agreeL_trans ag2 ag3))
  | ctorInfo v nP nF T =>
    simp only [genCI, plainCI, bind_assoc]
    refine genCV_spec ra G d v H0 _ Γ M s hc.1 (fun r1 s1 Γ1 H1 hp1 ag1 => ?_)
    refine name_step ra G T hc.2 d H1 rest Γ1 [] s1 (fun h s2 Γ2 H2 hp2 ag2 => ?_)
    simp only [pure_bind]
    exact hk _ s2 Γ2 H2 (hp1.trans hp2) (agreeL_trans ag1 ag2)
  | recInfo v mI rP isK rs =>
    simp only [genCI, plainCI, bind_assoc]
    refine genCV_spec ra G d v H0 _ Γ M s hc.1 (fun r1 s1 Γ1 H1 hp1 ag1 => ?_)
    refine genRules_spec ra G d rs H1 rest Γ1 [] s1 hc.2 (fun hs s2 Γ2 H2 hp2 ag2 => ?_)
    simp only [pure_bind]
    exact hk _ s2 Γ2 H2 (hp1.trans hp2) (agreeL_trans ag1 ag2)

theorem genCIList_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (d : Nat) :
    ∀ (cs : List ConLeche.ConstantInfo) (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
      {β : Type} {k : List IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop},
      (∀ c ∈ cs, CILit d N c) →
      (∀ hs s' Γ' H', H0 <+: H' → AgreeL Γ Γ' d → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k hs) R) →
      SpecR (Inv (ctxH C H0) s Γ M D) (genCIList C d cs rest) s (plainCIList cs >>= k) R := by
  intro cs
  induction cs with
  | nil =>
    intro H0 rest Γ M s β k R _ hk
    simp only [genCIList, plainCIList, pure_bind]
    intro t ht; exact hk [] s Γ H0 (List.prefix_refl _) (agreeL_refl _ _) t (lit_dropMem ht)
  | cons c cs ih =>
    intro H0 rest Γ M s β k R hcs hk
    simp only [genCIList, plainCIList, bind_assoc]
    refine genCI_spec ra G d c H0 _ Γ M s (hcs c (List.mem_cons_self ..)) (fun h1 s1 Γ1 H1 hp1 ag1 => ?_)
    refine ih H1 rest Γ1 [] s1 (fun m hm => hcs m (List.mem_cons_of_mem _ hm)) (fun hs s2 Γ2 H2 hp2 ag2 => ?_)
    simp only [pure_bind]
    exact hk _ s2 Γ2 H2 (hp1.trans hp2) (agreeL_trans ag1 ag2)

end

/-! ## Checking a literal's conditions by evaluation -/

def nameLitB (n : ConLeche.Name) : Bool :=
  match strComps n with
  | some cs => cs.all fun c => decide ((strBytes c).length < 2 ^ 50)
  | none => false

theorem nameLit_of {n : ConLeche.Name} (h : nameLitB n = true) : NameLit n := by
  unfold nameLitB at h
  split at h
  · rename_i cs hcs
    exact ⟨cs, hcs, fun c hc => by simpa using List.all_eq_true.mp h c hc⟩
  · cases h

def lvlB (N : Nat) : Nat → ConLeche.Level → Bool
  | d, u => decide (d + ldepth u ≤ N) && lvlOKB u
where lvlOKB : ConLeche.Level → Bool
  | .zero => true
  | .succ u => lvlOKB u
  | .max u v => lvlOKB u && lvlOKB v
  | .imax u v => lvlOKB u && lvlOKB v
  | .param n => nameLitB n

theorem lvlOK_of : ∀ {u : ConLeche.Level}, lvlB.lvlOKB u = true → LvlOK u
  | .zero, _ => trivial
  | .succ u, h => lvlOK_of (u := u) h
  | .max u v, h => by simp only [lvlB.lvlOKB, Bool.and_eq_true] at h; exact ⟨lvlOK_of h.1, lvlOK_of h.2⟩
  | .imax u v, h => by simp only [lvlB.lvlOKB, Bool.and_eq_true] at h; exact ⟨lvlOK_of h.1, lvlOK_of h.2⟩
  | .param n, h => nameLit_of h

def exprOKB : ConLeche.Expr → Bool
  | .bvar i => decide (i < 2 ^ 63)
  | .sort u => lvlB.lvlOKB u
  | .const n us => nameLitB n && us.all lvlB.lvlOKB && decide (us.length < 2 ^ 59)
  | .app f a => exprOKB f && exprOKB a
  | .lam t b => exprOKB t && exprOKB b
  | .forallE t b => exprOKB t && exprOKB b
  | _ => false

theorem exprOK_of : ∀ {e : ConLeche.Expr}, exprOKB e = true → ExprOK e
  | .bvar i, h => by simp only [exprOKB, decide_eq_true_eq] at h; exact h
  | .sort u, h => lvlOK_of h
  | .const n us, h => by
    simp only [exprOKB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact ⟨nameLit_of h.1.1, fun u hu => lvlOK_of (h.1.2 u hu), h.2⟩
  | .app f a, h => by simp only [exprOKB, Bool.and_eq_true] at h; exact ⟨exprOK_of h.1, exprOK_of h.2⟩
  | .lam t b, h => by simp only [exprOKB, Bool.and_eq_true] at h; exact ⟨exprOK_of h.1, exprOK_of h.2⟩
  | .forallE t b, h => by simp only [exprOKB, Bool.and_eq_true] at h; exact ⟨exprOK_of h.1, exprOK_of h.2⟩
  | .lit _, h => by simp [exprOKB] at h
  | .fvar _ _, h => by simp [exprOKB] at h
  | .letE _ _ _, h => by simp [exprOKB] at h
  | .proj _ _ _, h => by simp [exprOKB] at h

def eB (d N : Nat) (e : ConLeche.Expr) : Bool := exprOKB e && decide (d + edepth e ≤ N)

theorem eB_of {d N : Nat} {e : ConLeche.Expr} (h : eB d N e = true) : ExprOK e ∧ d + edepth e ≤ N := by
  simp only [eB, Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨exprOK_of h.1, h.2⟩

def cvB (d N : Nat) (cv : ConLeche.ConstantVal) : Bool :=
  nameLitB cv.name && cv.levelParams.all nameLitB && eB d N cv.type

theorem cvLit_of {d N : Nat} {cv : ConLeche.ConstantVal} (h : cvB d N cv = true) : CVLit d N cv := by
  simp only [cvB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨nameLit_of h.1.1, fun n hn => nameLit_of (h.1.2 n hn), (eB_of h.2).1, (eB_of h.2).2⟩

def fireB (d N : Nat) : ConLeche.RecRuleFire → Bool
  | .plain => true
  | .levels us => us.all (lvlB N d)
  | .nested _ _ => false

theorem fireLit_of {d N : Nat} : ∀ {f : ConLeche.RecRuleFire}, fireB d N f = true → FireLit d N f
  | .plain, _ => trivial
  | .levels us, h => fun u hu => by
    have := List.all_eq_true.mp h u hu
    simp only [lvlB, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨lvlOK_of this.2, this.1⟩
  | .nested _ _, h => by simp [fireB] at h

def ruleB (d N : Nat) (rl : ConLeche.RecRule) : Bool :=
  nameLitB rl.ctor && fireB d N rl.fire && eB d N rl.rhs

theorem ruleLit_of {d N : Nat} {rl : ConLeche.RecRule} (h : ruleB d N rl = true) : RuleLit d N rl := by
  simp only [ruleB, Bool.and_eq_true] at h
  exact ⟨nameLit_of h.1.1, fireLit_of h.1.2, (eB_of h.2).1, (eB_of h.2).2⟩

def ciB (d N : Nat) : ConLeche.ConstantInfo → Bool
  | .axiomInfo v => cvB d N v
  | .thmInfo v => cvB d N v
  | .defnInfo v e _ => cvB d N v && eB d N e
  | .indInfo v c => cvB d N v && c.all.all nameLitB && c.ctors.all nameLitB
  | .ctorInfo v _ _ T => cvB d N v && nameLitB T
  | .recInfo v _ _ _ rs => cvB d N v && rs.all (ruleB d N)

theorem ciLit_of {d N : Nat} : ∀ {c : ConLeche.ConstantInfo}, ciB d N c = true → CILit d N c
  | .axiomInfo v, h => cvLit_of h
  | .thmInfo v, h => cvLit_of h
  | .defnInfo v e _, h => by
    simp only [ciB, Bool.and_eq_true] at h; exact ⟨cvLit_of h.1, (eB_of h.2).1, (eB_of h.2).2⟩
  | .indInfo v c, h => by
    simp only [ciB, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨cvLit_of h.1.1, fun n hn => nameLit_of (h.1.2 n hn), fun n hn => nameLit_of (h.2 n hn)⟩
  | .ctorInfo v _ _ T, h => by simp only [ciB, Bool.and_eq_true] at h; exact ⟨cvLit_of h.1, nameLit_of h.2⟩
  | .recInfo v _ _ _ rs, h => by
    simp only [ciB, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨cvLit_of h.1, fun r hr => ruleLit_of (h.2 r hr)⟩

/-! ## The basis phase -/

set_option maxRecDepth 100000 in
theorem basis_lits : ∀ k : ConLeche.BasisKind, ∀ c ∈ ConLeche.BasisKind.decls k, CILit 0 12 c := by
  intro k c hc
  have : ∀ k ∈ [ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK, .quotK],
      ∀ c ∈ ConLeche.BasisKind.decls k, ciB 0 12 c = true := by decide
  exact ciLit_of (this k (by cases k <;> simp) c hc)

/-- The pinned blocks, in the order the phase interns them. -/
def basisKinds : List ConLeche.BasisKind := [.eqK, .natK, .emptyK, .falseK, .quotK]

/-- Intern every pinned block's literals, then `rest`. -/
def basisP (C : Ctx) : List ConLeche.BasisKind → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | k :: ks, rest => genCIList C 0 (ConLeche.BasisKind.decls k) (basisP C ks rest)

/-- The phase's twin: each pinned block's plain interning. -/
def basisTwin : List ConLeche.BasisKind → AM Unit
  | [] => pure ()
  | k :: ks => do
    let _ ← ConPanqueque.Logic.PlainIntern.plainCIList (ConLeche.BasisKind.decls k)
    basisTwin ks

section
variable {σ : Type}

theorem basisP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) :
    ∀ (ks : List ConLeche.BasisKind) (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
      {β : Type} {k : Unit → AM β} {R : β → BitVec 64 → AState → PState σ → Prop},
      (∀ s' Γ' H', H0 <+: H' → AgreeL Γ Γ' 0 → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k ()) R) →
      SpecR (Inv (ctxH C H0) s Γ M D) (basisP C ks rest) s (basisTwin ks >>= k) R := by
  intro ks
  induction ks with
  | nil =>
    intro H0 rest Γ M s β k R hk
    simp only [basisP, basisTwin, pure_bind]
    intro t ht; exact hk s Γ H0 (List.prefix_refl _) (agreeL_refl _ _) t (lit_dropMem ht)
  | cons b bs ih =>
    intro H0 rest Γ M s β k R hk
    simp only [basisP, basisTwin, bind_assoc]
    refine genCIList_spec ra G 0 _ H0 _ Γ M s (basis_lits b) (fun hs s1 Γ1 H1 hp1 ag1 => ?_)
    exact ih H1 rest Γ1 [] s1 (fun s2 Γ2 H2 hp2 ag2 => hk s2 Γ2 H2 (hp1.trans hp2) (agreeL_trans ag1 ag2))

end

end ConPanqueque.T.Lit
