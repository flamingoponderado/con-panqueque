import ConPanqueque.Prelude.OverStep
import ConPanqueque.Prelude.HoistDen

/-! # The hoist check

`hoistP` walks the registry at `kRB`: at a definition record whose name word is a pinned operation's
pin word (environment cell `64 + o`), every ground slot `g ≠ o` of `opTable` must be the name word of
an earlier value record (`seenP`), else hang.  `hoistP_spec`: the continuation runs knowing
`HoistW` of the registry's records. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConPanqueque.V

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

def hsN := ofString "hs_n"
def hsI := ofString "hs_i"
def hsD := ofString "hs_d"
def hsT := ofString "hs_t"
def hsNm := ofString "hs_nm"
def hsX := ofString "hs_x"
def hsG := ofString "hs_g"
def hsK := ofString "hs_k"
def hsE := ofString "hs_e"
def hsF := ofString "hs_f"

def hsVars : List MlS := [hsN, hsI, hsD, hsT, hsNm, hsX, hsG, hsK, hsE, hsF]

/-- `hsF := 1` iff a value record before index `hsI` is named by the word in `hsG`; hang otherwise. -/
def seenP : ProgHOL 64 :=
  .seq (.assign .local hsF (.const 0))
  (.seq (.assign .local hsK (.const 0))
  (.seq (.while (.cmp .lower (vv hsK) (vv hsI))
     (.seq (.assign .local hsE (.load .one (slotE kRB hsK 1)))
     (.seq (.assign .local hsT (.load .one (vv hsE)))
     (.seq (.ite (.cmp .equal (vv hsT) (.const 4)) .skip
             (.seq (.assign .local hsX (.load .one (offE hsE 1)))
                (.ite (.cmp .equal (vv hsX) (vv hsG)) (.assign .local hsF (.const 1)) .skip)))
       (.assign .local hsK (.op .add [vv hsK, .const 1]))))))
    (.ite (.cmp .equal (vv hsF) (.const 0)) hang .skip)))

/-- One ground slot's check. -/
def depP (g : Nat) : ProgHOL 64 :=
  .seq (.assign .local hsG (.load .one (.const (ConPanqueque.Start.ecb (64 + g))))) seenP

/-- An operation's ground slots, itself skipped. -/
def depsP (o : Nat) : List Nat → ProgHOL 64
  | [] => .skip
  | g :: gs => .seq (if g = o then .skip else depP g) (depsP o gs)

/-- The operations, against the name word in `hsNm`. -/
def opP : List (Nat × List Nat) → ProgHOL 64
  | [] => .skip
  | (o, gs) :: t => .seq (.assign .local hsX (.load .one (.const (ConPanqueque.Start.ecb (64 + o)))))
      (.seq (.ite (.cmp .equal (vv hsNm) (vv hsX)) (depsP o gs) .skip) (opP t))

def hoistBody : ProgHOL 64 :=
  .seq (.assign .local hsD (.load .one (slotE kRB hsI 1)))
  (.seq (.assign .local hsT (.load .one (vv hsD)))
  (.seq (.ite (.cmp .equal (vv hsT) (.const 1))
          (.seq (.assign .local hsNm (.load .one (offE hsD 1))) (opP opTable)) .skip)
    (.assign .local hsI (.op .add [vv hsI, .const 1]))))

/-- **The hoist check.** -/
def hoistP (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local hsN (.load .one (vv kRB)))
  (.seq (.assign .local hsI (.const 0))
  (.seq (.while (.cmp .lower (vv hsI) (vv hsN)) hoistBody) rest))

/-! ## Its specification -/

/-- `seenP`: it returns only if a value record before `i` is named `g`. -/
theorem seenP_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ hsVars, x ∈ D)
    {F rb capD : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hcap : 8 * (rb + 1 + capD) < 2 ^ 64)
    (hRB : Γ.get kRB = some (cellA C rb)) (i : Nat) (hi : i ≤ decls.size)
    (hI : Γ.get hsI = some (BitVec.ofNat 64 i)) (g : NIdx) (hG : Γ.get hsG = some (Enc.idxW g)) :
    Step (Inv (σ := σ) C s Γ [] D) seenP (fun t => (∃ k, ∃ hk : k < i, isVal (decls[k]'(by omega)) = true ∧
      valName (decls[k]'(by omega)) = g) ∧ ∃ Γ', (∀ y, y ∉ [hsF, hsK, hsE, hsT, hsX] → Γ'.get y = Γ.get y) ∧
      Inv C s Γ' [] D t) := by
  have hle : decls.size ≤ capD := hdr.2.1
  let W : Nat → Prop := fun k => ∃ k', ∃ hk : k' < i, k' < k ∧ isVal (decls[k']'(by omega)) = true ∧
    valName (decls[k']'(by omega)) = g
  refine step_seq (step_assignI hsF (.const 0) 0 (hD _ (by simp [hsVars])) rfl) ?_
  refine step_seq (step_assignI hsK (.const 0) 0 (hD _ (by simp [hsVars])) rfl) ?_
  have g0 : ∀ y, y ∉ [hsF, hsK, hsE, hsT, hsX] →
      T.Env.get ((hsK, 0) :: (hsF, 0) :: Γ) y = Γ.get y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp (config := {decide := true}) [T.Env.get_cons, hy.1, hy.2.1]
  refine step_cont (step_whileCE _ _
    (fun C' Γ' => C' = C ∧ ∃ k f, k ≤ i ∧ Γ'.get hsK = some (BitVec.ofNat 64 k) ∧ Γ'.get hsF = some f ∧
      (f ≠ 0 → W k) ∧ (∀ y, y ∉ [hsF, hsK, hsE, hsT, hsX] → Γ'.get y = Γ.get y))
    (fun C' Γ' => C' = C ∧ ∃ f, Γ'.get hsF = some f ∧ (f ≠ 0 → W i) ∧
      (∀ y, y ∉ [hsF, hsK, hsE, hsT, hsX] → Γ'.get y = Γ.get y))
    C _ ⟨rfl, 0, 0, Nat.zero_le _, (by simp (config := {decide := true}) [T.Env.get_cons]),
      (by simp (config := {decide := true}) [T.Env.get_cons]), fun h => absurd rfl h, g0⟩
    ?_) (fun t ⟨C', Γ', ⟨hC, f, gF, hW, hag⟩, ht⟩ => ?_)
  · intro C' Γ' ⟨hC, k, f, hk, gK, gF, hW, hag⟩
    subst C'
    have gI : Γ'.get hsI = some (BitVec.ofNat 64 i) := by rw [hag _ (by decide)]; exact hI
    refine ⟨bw (k < i), sev_lowerV _ _ _ _ _ gK gI (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
    · have : k = i := by have := bw_eq0' h0; omega
      subst this; exact ⟨rfl, f, gF, hW, hag⟩
    · have hlt := bw_ne0' h1
      obtain ⟨o, ho, hro⟩ := regAt hdr k (by omega)
      have gR : Γ'.get kRB = some (cellA C rb) := by rw [hag _ (by decide)]; exact hRB
      refine step_seq (step_loadW hsE (slotE kRB hsK 1) _ _ ho (hD _ (by simp [hsVars]))
        (by rw [sev_slot _ C kRB hsK rb k 1 gR gK (by omega)])) ?_
      refine step_seq (step_loadW hsT (vv hsE) o _ (recEnc_tag hro) (hD _ (by simp [hsVars]))
        (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
      let Γ2 : Env := (hsT, BitVec.ofNat 64 (tagOf decls[k])) :: (hsE, cellA C o) :: Γ'
      have g2 : ∀ y, y ∉ [hsF, hsK, hsE, hsT, hsX] → Γ2.get y = Γ.get y := by
        intro y hy
        have h1 : y ≠ hsT := fun e => hy (by simp [e])
        have h2 : y ≠ hsE := fun e => hy (by simp [e])
        simp only [Γ2, T.Env.get_cons, h1, h2, ite_false]; exact hag y hy
      refine step_seq (Q := fun t => ∃ Γ3 f', Γ3.get hsK = some (BitVec.ofNat 64 k) ∧ Γ3.get hsF = some f' ∧
          (f' ≠ 0 → W (k + 1)) ∧ (∀ y, y ∉ [hsF, hsK, hsE, hsT, hsX] → Γ3.get y = Γ.get y) ∧ Inv C s Γ3 [] D t)
        (step_ifI _ _ (sev_eqC _ hsT 4 (BitVec.ofNat 64 (tagOf decls[k])) (by simp (config := {decide := true}) [Γ2, T.Env.get_cons]))
          (fun _ => fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, Γ2, f,
            (by simp (config := {decide := true}) [Γ2, T.Env.get_cons, gK]), (by simp (config := {decide := true}) [Γ2, T.Env.get_cons, gF]),
            fun hf => let ⟨k', hk', a, b, c⟩ := hW hf; ⟨k', hk', by omega, b, c⟩, g2, hq⟩))
          (fun h4 => ?_)) ?_
      · have hv : isVal decls[k] = true := isVal_of_tag (fun e => ite10_eq h4 (by rw [e]))
        refine step_seq (step_loadW hsX (offE hsE 1) (o + 1) _ (name_of_val hro hv) (hD _ (by simp [hsVars]))
          (sev_off _ C hsE o 1 (by simp (config := {decide := true}) [Γ2, T.Env.get_cons]))) ?_
        have gG : T.Env.get ((hsX, Enc.idxW (valName decls[k])) :: Γ2) hsG = some (Enc.idxW g) := by
          rw [get_cons_ne _ _ _ _ (by decide), g2 _ (by decide)]; exact hG
        refine step_ifI _ _ (sev_eqv _ hsX hsG (Enc.idxW (valName decls[k])) (Enc.idxW g) (by simp (config := {decide := true}) [T.Env.get_cons]) gG) (fun he => ?_) (fun he => ?_)
        · have en : valName decls[k] = g := Enc.idxW_inj (ite10_ne he)
          refine fun t ht => (step_assignI hsF (.const 1) 1 (hD _ (by simp [hsVars])) rfl t ht).imp id
            (fun ⟨hn, hq⟩ => ⟨hn, _, 1, (by simp (config := {decide := true}) [Γ2, T.Env.get_cons, gK]), by simp (config := {decide := true}) [T.Env.get_cons],
              fun _ => ⟨k, hlt, by omega, hv, en⟩, fun y hy => ?_, hq⟩)
          have h1 : y ≠ hsF := fun e => hy (by simp [e])
          have h2 : y ≠ hsX := fun e => hy (by simp [e])
          simp only [T.Env.get_cons, h1, h2, ite_false]; exact g2 y hy
        · refine fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, _, f,
            (by simp (config := {decide := true}) [Γ2, T.Env.get_cons, gK]), (by simp (config := {decide := true}) [Γ2, T.Env.get_cons, gF]),
            fun hf => let ⟨k', hk', a, b, c⟩ := hW hf; ⟨k', hk', by omega, b, c⟩, fun y hy => ?_, hq⟩)
          have h2 : y ≠ hsX := fun e => hy (by simp [e])
          simp only [T.Env.get_cons, h2, ite_false]; exact g2 y hy
      · intro t ⟨Γ3, f', gK3, gF3, hW3, hag3, ht3⟩
        refine (step_assignI hsK (.op .add [vv hsK, .const 1]) _ (hD _ (by simp [hsVars]))
          (sev_succV _ hsK k gK3) t ht3).imp id (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, k + 1, f', by omega,
            by simp (config := {decide := true}) [T.Env.get_cons], (by simp (config := {decide := true}) [T.Env.get_cons, gF3]), hW3, fun y hy => ?_⟩, hq⟩)
        have h1 : y ≠ hsK := fun e => hy (by simp [e])
        simp only [T.Env.get_cons, h1, ite_false]; exact hag3 y hy
  · subst C'
    refine step_here ?_ ht
    refine step_ifI _ _ (sev_eqC _ hsF 0 _ gF)
      (fun _ => step_hangI) (fun hf => ?_)
    have hf0 : f ≠ 0 := fun e => ite10_eq hf e
    obtain ⟨k', hk', -, hv, hn⟩ := hW hf0
    exact fun t ht => (step_skipI t ht).imp id (fun ⟨hn', hq⟩ => ⟨hn', ⟨k', hk', hv, hn⟩, Γ', hag, hq⟩)

/-- The ground condition at index `i` (the hoist check's per-record verdict). -/
def HoistAt (pinH : Array NIdx) (decls : Array IDeclaration) (i : Nat) (hi : i < decls.size) : Prop :=
  ∀ o gs, (o, gs) ∈ opTable → (∃ cv v h, decls[i] = .defnDecl cv v h ∧ cv.name = pinH[o]!) →
    ∀ g ∈ gs, g = o ∨ ∃ k, ∃ hk : k < i, isVal (decls[k]'(by omega)) = true ∧ valName (decls[k]'(by omega)) = pinH[g]!

/-- The locals the per-record checks write. -/
def hsInner : List MlS := [hsF, hsK, hsE, hsT, hsX, hsG]

theorem pin_word {C : Ctx} {P : ConRon.Arena.Pins} (hb : ConPanqueque.Start.PinBlock C.EH P)
    (h52 : P.names.size = 52) (g : Nat) (hg : g < 52) : C.EH[64 + g]? = some (Enc.idxW P.names[g]!) := by
  rw [getElem!_pos P.names g (by omega)]; exact hb.names g (by omega)

theorem depsP_step {C : Ctx} {s : AState} {D : List MlS} (hD : ∀ x ∈ hsVars, x ∈ D)
    {F rb capD : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hcap : 8 * (rb + 1 + capD) < 2 ^ 64) (hEB : ∀ j, ecell C j = ConPanqueque.Start.ecb j)
    {P : ConRon.Arena.Pins} (hb : ConPanqueque.Start.PinBlock C.EH P) (h52 : P.names.size = 52)
    (i : Nat) (hi : i ≤ decls.size) (o : Nat) :
    ∀ (gs : List Nat) (Γ : Env), (∀ g ∈ gs, g < 52) → Γ.get kRB = some (cellA C rb) →
      Γ.get hsI = some (BitVec.ofNat 64 i) →
      Step (Inv (σ := σ) C s Γ [] D) (depsP o gs) (fun t => (∀ g ∈ gs, g ≠ o → ∃ k, ∃ hk : k < i,
        isVal (decls[k]'(by omega)) = true ∧ valName (decls[k]'(by omega)) = P.names[g]!) ∧
        ∃ Γ', (∀ y, y ∉ hsInner → Γ'.get y = Γ.get y) ∧ Inv C s Γ' [] D t)
  | [], Γ, _, _, _ => fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, fun g hg => absurd hg (by simp),
      Γ, fun _ _ => rfl, hq⟩)
  | g :: gs, Γ, hlt, hRB, hI => by
    refine step_seq (Q := fun t => (g ≠ o → ∃ k, ∃ hk : k < i, isVal (decls[k]'(by omega)) = true ∧
        valName (decls[k]'(by omega)) = P.names[g]!) ∧
        ∃ Γ', (∀ y, y ∉ hsInner → Γ'.get y = Γ.get y) ∧ Inv C s Γ' [] D t) ?_ ?_
    · by_cases hgo : g = o
      · simp only [hgo, ite_true]
        exact fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, fun h => absurd rfl h, Γ, fun _ _ => rfl, hq⟩)
      · simp only [hgo, ite_false, depP]
        have hg52 := hlt g (List.mem_cons_self ..)
        refine step_seq (ConPanqueque.Start.step_envLoadI hsG _ (64 + g) _ (hD _ (by simp [hsVars]))
          (by simp [sev, hEB]) (pin_word hb h52 g hg52)) ?_
        refine fun t ht => (seenP_step hD hdr hcap (by rw [get_cons_ne _ _ _ _ (by decide)]; exact hRB) i hi
          (by rw [get_cons_ne _ _ _ _ (by decide)]; exact hI) _ (by simp (config := {decide := true}) [T.Env.get_cons]) t ht).imp id
          (fun ⟨hn, hw, Γ', hag, hq⟩ => ⟨hn, fun _ => hw, Γ', fun y hy => ?_, hq⟩)
        have hy' : y ∉ [hsF, hsK, hsE, hsT, hsX] := fun h => hy (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl | rfl <;> decide)
        rw [hag y hy']
        have : y ≠ hsG := fun e => hy (by simp [e, hsInner])
        simp (config := {decide := true}) [T.Env.get_cons, this]
    · intro t ⟨h1, Γ', hag, ht⟩
      refine (depsP_step hD hdr hcap hEB hb h52 i hi o gs Γ' (fun g hg => hlt g (List.mem_cons_of_mem _ hg))
        (by rw [hag _ (by decide)]; exact hRB) (by rw [hag _ (by decide)]; exact hI) t ht).imp id
        (fun ⟨hn, h2, Γ'', hag', hq⟩ => ⟨hn, fun g' hg' hne => ?_, Γ'', fun y hy => (hag' y hy).trans (hag y hy), hq⟩)
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact h1 hne
      · exact h2 g' hg' hne

theorem opP_step {C : Ctx} {s : AState} {D : List MlS} (hD : ∀ x ∈ hsVars, x ∈ D)
    {F rb capD : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hcap : 8 * (rb + 1 + capD) < 2 ^ 64) (hEB : ∀ j, ecell C j = ConPanqueque.Start.ecb j)
    {P : ConRon.Arena.Pins} (hb : ConPanqueque.Start.PinBlock C.EH P) (h52 : P.names.size = 52)
    (i : Nat) (hi : i ≤ decls.size) (nm : BitVec 64) :
    ∀ (tbl : List (Nat × List Nat)) (Γ : Env), (∀ og ∈ tbl, og ∈ opTable) → Γ.get kRB = some (cellA C rb) →
      Γ.get hsI = some (BitVec.ofNat 64 i) → Γ.get hsNm = some nm →
      Step (Inv (σ := σ) C s Γ [] D) (opP tbl) (fun t => (∀ og ∈ tbl, nm = Enc.idxW P.names[og.1]! →
        ∀ g ∈ og.2, g ≠ og.1 → ∃ k, ∃ hk : k < i, isVal (decls[k]'(by omega)) = true ∧
          valName (decls[k]'(by omega)) = P.names[g]!) ∧
        ∃ Γ', (∀ y, y ∉ hsInner → Γ'.get y = Γ.get y) ∧ Inv C s Γ' [] D t)
  | [], Γ, _, _, _, _ => fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, fun og hog => absurd hog (by simp),
      Γ, fun _ _ => rfl, hq⟩)
  | (o, gs) :: tbl, Γ, hsub, hRB, hI, hNm => by
    have hog := hsub _ (List.mem_cons_self ..)
    have ho52 := (opTable_lt _ hog).1
    refine step_seq (ConPanqueque.Start.step_envLoadI hsX _ (64 + o) _ (hD _ (by simp [hsVars]))
      (by simp [sev, hEB]) (pin_word hb h52 o ho52)) ?_
    let Γ1 : Env := (hsX, Enc.idxW P.names[o]!) :: Γ
    have hag1 : ∀ y, y ∉ hsInner → Γ1.get y = Γ.get y := by
      intro y hy; have : y ≠ hsX := fun e => hy (by simp [e, hsInner]); simp (config := {decide := true}) [Γ1, T.Env.get_cons, this]
    refine step_seq (Q := fun t => (nm = Enc.idxW P.names[o]! → ∀ g ∈ gs, g ≠ o → ∃ k, ∃ hk : k < i,
        isVal (decls[k]'(by omega)) = true ∧ valName (decls[k]'(by omega)) = P.names[g]!) ∧
        ∃ Γ', (∀ y, y ∉ hsInner → Γ'.get y = Γ.get y) ∧ Inv C s Γ' [] D t)
      (step_ifI _ _ (sev_eqv _ hsNm hsX nm (Enc.idxW P.names[o]!) (by rw [get_cons_ne _ _ _ _ (by decide)]; exact hNm)
        (by simp (config := {decide := true}) [T.Env.get_cons])) (fun he => ?_) (fun he => ?_)) ?_
    · refine fun t ht => (depsP_step hD hdr hcap hEB hb h52 i hi o gs Γ1 (opTable_lt _ hog).2
        (by rw [hag1 _ (by decide)]; exact hRB) (by rw [hag1 _ (by decide)]; exact hI) t ht).imp id
        (fun ⟨hn, hw, Γ', hag, hq⟩ => ⟨hn, fun _ => hw, Γ', fun y hy => (hag y hy).trans (hag1 y hy), hq⟩)
    · exact fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, fun h => absurd h (ite10_eq he), Γ1, hag1, hq⟩)
    · intro t ⟨h1, Γ', hag, ht⟩
      refine (opP_step hD hdr hcap hEB hb h52 i hi nm tbl Γ' (fun og h => hsub og (List.mem_cons_of_mem _ h))
        (by rw [hag _ (by decide)]; exact hRB) (by rw [hag _ (by decide)]; exact hI)
        (by rw [hag _ (by decide)]; exact hNm) t ht).imp id
        (fun ⟨hn, h2, Γ'', hag', hq⟩ => ⟨hn, fun og hog' => ?_, Γ'', fun y hy => (hag' y hy).trans (hag y hy), hq⟩)
      rcases List.mem_cons.mp hog' with rfl | hog'
      · exact h1
      · exact h2 og hog'

/-- **The hoist check**: the continuation knows `HoistW` of the registry's records. -/
theorem hoistP_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (hD : ∀ x ∈ hsVars, x ∈ D)
    {F rb capD : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hcap : 8 * (rb + 1 + capD) < 2 ^ 64) (hRB : Γ.get kRB = some (cellA C rb))
    (hEB : ∀ j, ecell C j = ConPanqueque.Start.ecb j)
    {P : ConRon.Arena.Pins} (hb : ConPanqueque.Start.PinBlock C.EH P) (h52 : P.names.size = 52)
    {rest : ProgHOL 64} {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ Γ', (∀ y, y ∉ hsVars → Γ'.get y = Γ.get y) → HoistW P.names decls.toList →
      SpecR (Inv C s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (hoistP rest) s m R := by
  suffices hM : SpecR (Inv C s Γ [] D) (hoistP rest) s m R from
    fun t ht => hM t ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  have hle : decls.size ≤ capD := hdr.2.1
  have hcnt := hdr.1
  unfold hoistP
  refine specR_heapLoadI hsN (vv kRB) rb (lt_of_get hcnt) (hD _ (by simp [hsVars])) (by simpa [sev, vv] using hRB) ?_
  rw [getElem_of_get hcnt]
  refine specR_assignI hsI (.const 0) 0 (hD _ (by simp [hsVars])) rfl ?_
  let n := decls.size
  refine specR_step (step_whileCE _ _
    (fun C' Γ' => C' = C ∧ ∃ i, ∃ hi : i ≤ n, Γ'.get hsI = some (BitVec.ofNat 64 i) ∧
      Γ'.get hsN = some (BitVec.ofNat 64 n) ∧ (∀ i' (hi' : i' < i), HoistAt P.names decls i' (Nat.lt_of_lt_of_le hi' hi)) ∧
      (∀ y, y ∉ hsVars → Γ'.get y = Γ.get y))
    (fun C' Γ' => C' = C ∧ (∀ i' (hi' : i' < n), HoistAt P.names decls i' hi') ∧
      (∀ y, y ∉ hsVars → Γ'.get y = Γ.get y))
    C _ ⟨rfl, 0, Nat.zero_le _, (by simp (config := {decide := true}) [T.Env.get_cons]),
      (by simp (config := {decide := true}) [T.Env.get_cons]; rfl),
      fun i' h => absurd h (by omega), fun y hy => by
        have h1 : y ≠ hsI := fun e => hy (by simp [e, hsVars])
        have h2 : y ≠ hsN := fun e => hy (by simp [e, hsVars])
        simp (config := {decide := true}) [T.Env.get_cons, h1, h2]⟩ ?_) ?_
  · intro C' Γ' ⟨hC, i, hi, gI, gN, hdone, hag⟩
    subst C'
    have gR : Γ'.get kRB = some (cellA C rb) := by rw [hag _ (by decide)]; exact hRB
    refine ⟨bw (i < n), sev_lowerV _ _ _ _ _ gI gN (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
    · have : i = n := by have := bw_eq0' h0; omega
      subst this; exact ⟨rfl, hdone, hag⟩
    · have hlt := bw_ne0' h1
      obtain ⟨o, ho, hro⟩ := regAt hdr i hlt
      refine step_seq (step_loadW hsD (slotE kRB hsI 1) _ _ ho (hD _ (by simp [hsVars]))
        (by rw [sev_slot _ C kRB hsI rb i 1 gR gI (by omega)])) ?_
      refine step_seq (step_loadW hsT (vv hsD) o _ (recEnc_tag hro) (hD _ (by simp [hsVars]))
        (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
      let Γ2 : Env := (hsT, BitVec.ofNat 64 (tagOf decls[i])) :: (hsD, cellA C o) :: Γ'
      have g2 : ∀ y, y ∉ hsVars → Γ2.get y = Γ.get y := by
        intro y hy
        have h1 : y ≠ hsT := fun e => hy (by simp [e, hsVars])
        have h2 : y ≠ hsD := fun e => hy (by simp [e, hsVars])
        simp only [Γ2, T.Env.get_cons, h1, h2, ite_false]; exact hag y hy
      have gI2 : Γ2.get hsI = some (BitVec.ofNat 64 i) := (by simp (config := {decide := true}) [Γ2, T.Env.get_cons, gI])
      have gN2 : Γ2.get hsN = some (BitVec.ofNat 64 n) := (by simp (config := {decide := true}) [Γ2, T.Env.get_cons, gN])
      refine step_seq (Q := fun t => HoistAt P.names decls i hlt ∧ ∃ Γ3, Γ3.get hsI = some (BitVec.ofNat 64 i) ∧
          Γ3.get hsN = some (BitVec.ofNat 64 n) ∧ (∀ y, y ∉ hsVars → Γ3.get y = Γ.get y) ∧ Inv C s Γ3 [] D t)
        (step_ifI _ _ (sev_eqC _ hsT 1 (BitVec.ofNat 64 (tagOf decls[i])) (by simp (config := {decide := true}) [Γ2, T.Env.get_cons]))
          (fun h1 => ?_) (fun h1 => ?_)) ?_
      · have e1 : tagOf decls[i] = 1 := tagOf_inj (tagOf_lt _) (by omega) (ite10_ne h1)
        have hv : isVal decls[i] = true := isVal_of_tag (by rw [e1]; decide)
        refine step_seq (step_loadW hsNm (offE hsD 1) (o + 1) _ (name_of_val hro hv) (hD _ (by simp [hsVars]))
          (sev_off _ C hsD o 1 (by simp (config := {decide := true}) [Γ2, T.Env.get_cons]))) ?_
        refine fun t ht => (opP_step hD hdr hcap hEB hb h52 i (by omega) (Enc.idxW (valName decls[i])) opTable _ (fun og h => h)
          (by rw [get_cons_ne _ _ _ _ (by decide), g2 _ (by decide)]; exact hRB)
          (by rw [get_cons_ne _ _ _ _ (by decide)]; exact gI2) (by simp (config := {decide := true}) [T.Env.get_cons]) t ht).imp id
          (fun ⟨hn, hw, Γ3, hag3, hq⟩ => ⟨hn, ?_, Γ3, (by rw [hag3 _ (by decide), get_cons_ne _ _ _ _ (by decide)]; exact gI2),
            (by rw [hag3 _ (by decide), get_cons_ne _ _ _ _ (by decide)]; exact gN2), fun y hy => ?_, hq⟩)
        · intro o' gs hog ⟨cv, v, h, hd, hcv⟩ g hg
          by_cases hgo : g = o'
          · exact Or.inl hgo
          · refine Or.inr (hw (o', gs) hog ?_ g hg hgo)
            rw [hd] at hv ⊢
            simp only [valName] at ⊢
            rw [hcv]
        · have hy' : y ∉ hsInner := fun h => hy (by
            simp only [hsInner, List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          rw [hag3 y hy']
          have : y ≠ hsNm := fun e => hy (by simp [e, hsVars])
          simp only [T.Env.get_cons, this, ite_false]; exact g2 y hy
      · refine fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, ?_, Γ2, gI2, gN2, g2, hq⟩)
        intro o' gs hog ⟨cv, v, h, hd, hcv⟩
        exfalso; apply ite10_eq h1; rw [hd]; rfl
      · intro t ⟨hat, Γ3, gI3, gN3, hag3, ht3⟩
        refine (step_assignI hsI (.op .add [vv hsI, .const 1]) _ (hD _ (by simp [hsVars]))
          (sev_succV _ hsI i gI3) t ht3).imp id (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, i + 1, by omega,
            by simp (config := {decide := true}) [T.Env.get_cons], (by simp (config := {decide := true}) [T.Env.get_cons, gN3]), fun i' hi' => ?_, fun y hy => ?_⟩, hq⟩)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
          · exact hdone i' h
          · exact hat
        · have : y ≠ hsI := fun e => hy (by simp [e, hsVars])
          simp only [T.Env.get_cons, this, ite_false]; exact hag3 y hy
  · intro t ⟨C', Γ', ⟨hC, hall, hag⟩, ht⟩
    subst C'
    exact hk Γ' hag (fun i hi => hall i (by simpa using hi)) t ht

end ConPanqueque.Prelude
