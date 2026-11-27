import ConPanqueque.T.LInternLv
import ConPanqueque.Start.PinName
import ConPanqueque.T.PinRead
import ConPanqueque.T.LvlMk
import ConPanqueque.T.SubstLsTop
import ConPanqueque.T.CtxTr

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

end ConPanqueque.T.Lit
