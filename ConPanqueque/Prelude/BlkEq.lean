import ConPanqueque.Prelude.OverStep

/-! # The override pass's block pieces

* `declP`: does the record at `ovX` declare the handle in `ovKey` (con-ron's `IDeclaration.names`: a value
  record's name, every member's name of a block)?  The answer is the flag `ovFL` (`declP_step`).
* `cieEqP`: hang unless the stored constants at `ovCX` and `ovCY` hold the same words (kinds 3–5: inductive,
  constructor, recursor; a recursor's rules all plain); then they are the same `IConstantInfo` (`cieEq_step`).
* `blkEqP`: hang unless the block record at `ovD` has the record at `ovP`'s words, member by member; then they
  are the same `IDeclaration` (`blkEqP_step`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConPanqueque.V

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

theorem frame_cons {Γ Γ0 : Env} {mods : List MlS} (h : ∀ z, z ∉ mods → Γ.get z = Γ0.get z) (x : MlS)
    (hx : x ∈ mods) (v : BitVec 64) : ∀ z, z ∉ mods → T.Env.get ((x, v) :: Γ) z = Γ0.get z := by
  intro z hz
  have : z ≠ x := fun e => hz (e ▸ hx)
  rw [get_cons_ne _ _ _ _ this]; exact h z hz

theorem frame_trans {Γ1 Γ2 Γ0 : Env} {mods : List MlS} (h2 : ∀ z, z ∉ mods → Γ2.get z = Γ1.get z)
    (h1 : ∀ z, z ∉ mods → Γ1.get z = Γ0.get z) : ∀ z, z ∉ mods → Γ2.get z = Γ0.get z :=
  fun z hz => (h2 z hz).trans (h1 z hz)

theorem frame_get {Γ Γ0 : Env} {mods : List MlS} (h : ∀ z, z ∉ mods → Γ.get z = Γ0.get z) {x : MlS}
    (hx : x ∉ mods) {v : BitVec 64} (h0 : Γ0.get x = some v) : Γ.get x = some v := by rw [h x hx]; exact h0

theorem blkAt_len {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) :
    xs.length ≤ H.length := by
  cases e : xs.length with
  | zero => exact Nat.zero_le _
  | succ n =>
    have := lt_of_get (h.2 n (by omega))
    omega

theorem blkAt_eq63 {H : List (BitVec 64)} {ol ol' : Nat} {xs ys : List (BitVec 64)} (hx : BlkAt H ol xs)
    (hy : BlkAt H ol' ys) (hn : H[ol]? = H[ol']?)
    (he : ∀ i, i < xs.length → H[ol + 1 + i]? = H[ol' + 1 + i]?) (h1 : xs.length < 2 ^ 63) (h2 : ys.length < 2 ^ 63) :
    xs = ys := by
  have hl : xs.length = ys.length := ofNat_inj63 h1 h2 (some_inj' hx.1 (hn.trans hy.1))
  apply List.ext_getElem hl
  intro i i1 i2
  exact some_inj' (hx.2 i i1) ((he i i1).trans (hy.2 i i2))

theorem boolW_inj {a b : Bool} (h : boolW a = boolW b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

theorem natE_inj {H : List (BitVec 64)} {i j a b : Nat} (ha : NatE H i a) (hb : NatE H j b) (h : H[i]? = H[j]?) :
    a = b := ofNat_inj63 ha.2 hb.2 (some_inj' ha.1 (h.trans hb.1))

/-! ## `declP` -/

def declBodyP : ProgHOL 64 :=
  .seq (.assign .local ovQX (.load .one (slotE ovQB ovQ 1)))
  (.seq (.assign .local ovQX (.load .one (offE ovQX 1)))
  (.seq (.ite (.cmp .equal (vv ovQX) (vv ovKey)) (.assign .local ovFL (.const 1)) .skip)
    (.assign .local ovQ (.op .add [vv ovQ, .const 1]))))

/-- `ovFL := 1` if the record at `ovX` declares `ovKey`, else `0`. -/
def declP : ProgHOL 64 :=
  .seq (.assign .local ovQX (.load .one (vv ovX)))
  (.ite (.cmp .equal (vv ovQX) (.const 4))
    (.seq (.assign .local ovQB (.load .one (offE ovX 2)))
    (.seq (.assign .local ovQN (.load .one (vv ovQB)))
    (.seq (.assign .local ovFL (.const 0))
    (.seq (.assign .local ovQ (.const 0))
      (.while (.cmp .lower (vv ovQ) (vv ovQN)) declBodyP)))))
    (.seq (.assign .local ovQX (.load .one (offE ovX 1)))
      (.assign .local ovFL (.cmp .equal (vv ovQX) (vv ovKey)))))

def declMods : List MlS := [ovQX, ovQB, ovQN, ovQ, ovFL]

theorem names_ind_contains (block : List IConstantInfo) (nP : Nat) (key : NIdx) :
    (IDeclaration.indDecl block nP).names.contains key = true ↔ ∃ i, ∃ hi : i < block.length, block[i].name = key := by
  simp only [IDeclaration.names, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨ci, hci, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hci
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, List.getElem_mem hi, rfl⟩

/-- **`declP`**: the flag says whether the record declares the key. -/
theorem declP_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F o : Nat} {d : IDeclaration} (hr : RecEnc C F C.H o d) (hX : Γ.get ovX = some (cellA C o))
    (key : NIdx) (hK : Γ.get ovKey = some (Enc.idxW key)) :
    Step (Inv (σ := σ) C s Γ [] D) declP (fun t => ∃ Γ', Γ'.get ovFL = some (if d.names.contains key then 1 else 0) ∧
      (∀ z, z ∉ declMods → Γ'.get z = Γ.get z) ∧ Inv C s Γ' [] D t) := by
  have hT := recEnc_tag hr
  refine step_seq (step_loadW ovQX (vv ovX) o _ hT (hD _ (by simp [ovVars])) (by simpa [sev, vv] using hX)) ?_
  have f0 : ∀ z, z ∉ declMods → T.Env.get ((ovQX, BitVec.ofNat 64 (tagOf d)) :: Γ) z = Γ.get z :=
    frame_cons (fun _ _ => rfl) ovQX (by simp [declMods]) _
  refine step_ifI _ _ (sev_eqC _ ovQX 4 (BitVec.ofNat 64 (tagOf d)) (by simp (config := {decide := true}) [T.Env.get_cons]))
    (fun h4 => ?_) (fun h4 => ?_)
  · have ht4 : tagOf d = 4 := tagOf_inj (tagOf_lt d) (by omega) (ite10_ne h4)
    cases d with
    | indDecl block nP =>
      obtain ⟨-, -, -, -, ob, hob, h3, h4', h59, -⟩ := hr
      obtain ⟨os, hlen, hblk, hcie⟩ := h4' C.H (fun _ _ _ h => h)
      refine step_seq (step_loadW ovQB (offE ovX 2) (o + 2) _ h3 (hD _ (by simp [ovVars]))
        (sev_off _ C ovX o 2 (frame_get f0 (by decide) hX))) ?_
      have f1 := frame_cons f0 ovQB (by simp [declMods]) (cellA C ob)
      refine step_seq (step_loadW ovQN (vv ovQB) ob _ hblk.1 (hD _ (by simp [ovVars]))
        (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
      have f2 := frame_cons f1 ovQN (by simp [declMods]) (BitVec.ofNat 64 (os.map (cellA C)).length)
      refine step_seq (step_assignI ovFL (.const 0) 0 (hD _ (by simp [ovVars])) rfl) ?_
      have f3 := frame_cons f2 ovFL (by simp [declMods]) 0
      refine step_seq (step_assignI ovQ (.const 0) 0 (hD _ (by simp [ovVars])) rfl) ?_
      have f4 := frame_cons f3 ovQ (by simp [declMods]) 0
      have hnl : os.length < 2 ^ 59 := by omega
      let P : Nat → Prop := fun i => ∃ i', ∃ hi' : i' < block.length, i' < i ∧ block[i'].name = key
      refine fun t ht => (step_whileCE (s := s) (D := D) _ _
        (fun C' Γ' => C' = C ∧ ∃ i, i ≤ os.length ∧ Γ'.get ovQ = some (BitVec.ofNat 64 i) ∧
          Γ'.get ovFL = some (if P i then 1 else 0) ∧ Γ'.get ovQN = some (BitVec.ofNat 64 os.length) ∧
          Γ'.get ovQB = some (cellA C ob) ∧ (∀ z, z ∉ declMods → Γ'.get z = Γ.get z))
        (fun C' Γ' => C' = C ∧ Γ'.get ovFL = some (if P os.length then 1 else 0) ∧
          (∀ z, z ∉ declMods → Γ'.get z = Γ.get z))
        C _ ⟨rfl, 0, Nat.zero_le _, by simp (config := {decide := true}) [T.Env.get_cons],
          by simp (config := {decide := true}) [T.Env.get_cons, P],
          by simp (config := {decide := true}) [T.Env.get_cons],
          by simp (config := {decide := true}) [T.Env.get_cons], f4⟩ ?_ t ht).imp id
        (fun ⟨hn, C', Γ', ⟨hC, gF, hag⟩, hq⟩ => by
          subst C'
          refine ⟨hn, Γ', ?_, hag, hq⟩
          rw [gF]
          have e : P os.length ↔ (IDeclaration.indDecl block nP).names.contains key = true := by
            rw [names_ind_contains]
            constructor
            · rintro ⟨i, hi, -, h⟩; exact ⟨i, hi, h⟩
            · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by omega, h⟩
          by_cases hp : P os.length
          · rw [if_pos hp, if_pos (e.mp hp)]
          · rw [if_neg hp, if_neg (fun h => hp (e.mpr h))])
      intro C' Γ' ⟨hC, i, hi, gQ, gF, gN, gB, hag⟩
      subst C'
      refine ⟨bw (i < os.length), sev_lowerV _ _ _ _ _ gQ gN (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
      · have : i = os.length := by have := bw_eq0' h0; omega
        subst this; exact ⟨rfl, gF, hag⟩
      · have hlt := bw_ne0' h1
        have hbi := hblk.2 i (by simpa using hlt)
        simp only [List.getElem_map] at hbi
        have hc := hcie i (by omega) hlt
        refine step_seq (step_loadW ovQX (slotE ovQB ovQ 1) _ _ hbi (hD _ (by simp [ovVars]))
          (by rw [sev_slot _ C ovQB ovQ ob i 1 gB gQ (by omega)])) ?_
        refine step_seq (step_loadW ovQX (offE ovQX 1) (os[i] + 1) _ hc.1.1 (hD _ (by simp [ovVars]))
          (sev_off _ C ovQX _ 1 (by simp (config := {decide := true}) [T.Env.get_cons]))) ?_
        let Γ2 : Env := (ovQX, Enc.idxW block[i].toConstantVal.name) :: (ovQX, cellA C os[i]) :: Γ'
        have gK2 : Γ2.get ovKey = some (Enc.idxW key) := by
          simp (config := {decide := true}) only [Γ2, T.Env.get_cons, ite_false]; rw [hag _ (by decide)]; exact hK
        have gF2 : Γ2.get ovFL = some (if P i then 1 else 0) := by
          simp (config := {decide := true}) only [Γ2, T.Env.get_cons, ite_false]; exact gF
        have branchT : block[i].name = key → (if P (i + 1) then (1 : BitVec 64) else 0) = 1 := fun en =>
          if_pos ⟨i, by omega, by omega, en⟩
        have branchF : block[i].name ≠ key → (if P (i + 1) then (1 : BitVec 64) else 0) = (if P i then 1 else 0) := by
          intro ne
          have e : P (i + 1) ↔ P i := by
            constructor
            · rintro ⟨i', hi', h1, h2⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | rfl
              · exact ⟨i', hi', h, h2⟩
              · exact absurd h2 ne
            · rintro ⟨i', hi', h1, h2⟩; exact ⟨i', hi', by omega, h2⟩
          by_cases hp : P i
          · rw [if_pos (e.mpr hp), if_pos hp]
          · rw [if_neg (fun h => hp (e.mp h)), if_neg hp]
        refine step_seq (Q := fun t => ∃ Γ3, Γ3.get ovFL = some (if P (i + 1) then 1 else 0) ∧
            (∀ z, z ≠ ovFL → Γ3.get z = Γ2.get z) ∧ Inv C s Γ3 [] D t)
          (step_ifI _ _ (sev_eqv _ ovQX ovKey (Enc.idxW block[i].toConstantVal.name) (Enc.idxW key)
            (by simp (config := {decide := true}) [Γ2, T.Env.get_cons]) gK2)
            (fun he => fun t ht => (step_assignI ovFL (.const 1) 1 (hD _ (by simp [ovVars])) rfl t ht).imp id
              (fun ⟨hn, hq⟩ => ⟨hn, _, by
                rw [branchT (by rw [name_cons_val]; exact Enc.idxW_inj (ite10_ne he))]
                simp (config := {decide := true}) [T.Env.get_cons], fun z hz => get_cons_ne _ _ _ _ hz, hq⟩))
            (fun he => fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, Γ2, by
                rw [branchF (fun e => ite10_eq he (by rw [← name_cons_val, e]))]; exact gF2,
                fun _ _ => rfl, hq⟩))) ?_
        · intro t ⟨Γ3, gF3, hag3, ht3⟩
          have gQ3 : Γ3.get ovQ = some (BitVec.ofNat 64 i) := by
            rw [hag3 _ (by decide)]; simp (config := {decide := true}) only [Γ2, T.Env.get_cons, ite_false]; exact gQ
          refine (step_assignI ovQ (.op .add [vv ovQ, .const 1]) _ (hD _ (by simp [ovVars])) (sev_succV _ ovQ i gQ3)
            t ht3).imp id (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, i + 1, by omega, by simp (config := {decide := true}) [T.Env.get_cons],
              by rw [get_cons_ne _ _ _ _ (by decide)]; exact gF3, ?_, ?_, ?_⟩, hq⟩)
          · rw [get_cons_ne _ _ _ _ (by decide), hag3 _ (by decide)]
            simp (config := {decide := true}) only [Γ2, T.Env.get_cons, ite_false]; exact gN
          · rw [get_cons_ne _ _ _ _ (by decide), hag3 _ (by decide)]
            simp (config := {decide := true}) only [Γ2, T.Env.get_cons, ite_false]; exact gB
          · refine frame_cons (fun z hz => ?_) ovQ (by simp [declMods]) _
            rw [hag3 z (fun e => hz (by simp [e, declMods]))]
            have : z ≠ ovQX := fun e => hz (by simp [e, declMods])
            simp only [Γ2, get_cons_ne _ _ _ _ this]; exact hag z hz
    | _ => simp [tagOf] at ht4
  · have hv : isVal d = true := isVal_of_tag (fun e => ite10_eq h4 (by rw [e]))
    refine step_seq (step_loadW ovQX (offE ovX 1) (o + 1) _ (name_of_val hr hv) (hD _ (by simp [ovVars]))
      (sev_off _ C ovX o 1 (frame_get f0 (by decide) hX))) ?_
    refine fun t ht => (step_assignI ovFL (.cmp .equal (vv ovQX) (vv ovKey)) _ (hD _ (by simp [ovVars]))
      (sev_eqv _ ovQX ovKey (Enc.idxW (valName d)) (Enc.idxW key) (by simp (config := {decide := true}) [T.Env.get_cons])
        (by simp (config := {decide := true}) only [T.Env.get_cons, ite_false]; exact hK)) t ht).imp id
      (fun ⟨hn, hq⟩ => ⟨hn, _, ?_, frame_cons (frame_cons f0 ovQX (by simp [declMods]) _) ovFL (by simp [declMods]) _, hq⟩)
    rw [names_val hv]
    simp only [T.Env.get_cons, ite_true, List.contains_cons, List.contains_nil, Bool.or_false]
    by_cases e : valName d = key
    · subst e; simp
    · have : (key == valName d) = false := beq_eq_false_iff_ne.mpr (fun h => e h.symm)
      rw [this]; simp only [Bool.false_eq_true, ite_false]
      rw [if_neg (fun h => e (Enc.idxW_inj h))]

/-! ## Word and list comparisons in frame form -/

/-- Hang unless the words at `x + 8k` and `y + 8k` agree. -/
def cmpXY (x y : MlS) (k : Nat) : ProgHOL 64 :=
  .seq (.assign .local ovX (.load .one (offE x k)))
  (.seq (.assign .local ovY (.load .one (offE y k)))
    (.ite (.cmp .equal (vv ovX) (vv ovY)) .skip hang))

theorem cmpXY_step {C : Ctx} {s : AState} {Γ Γ0 : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {mods : List MlS} (hag : ∀ z, z ∉ mods → Γ.get z = Γ0.get z) (hXm : ovX ∈ mods) (hYm : ovY ∈ mods)
    {x y : MlS} (hx0 : x ∉ mods) (hy0 : y ∉ mods) {ox oy : Nat} (hx : Γ0.get x = some (cellA C ox))
    (hy : Γ0.get y = some (cellA C oy)) (k : Nat) {a b : BitVec 64} (ha : C.H[ox + k]? = some a)
    (hb : C.H[oy + k]? = some b) :
    Step (Inv (σ := σ) C s Γ [] D) (cmpXY x y k)
      (fun t => a = b ∧ ∃ Γ', (∀ z, z ∉ mods → Γ'.get z = Γ0.get z) ∧ Inv C s Γ' [] D t) := by
  have hyX : y ≠ ovX := fun e => hy0 (e ▸ hXm)
  refine step_seq (step_loadW ovX (offE x k) (ox + k) a ha (hD _ (by simp [ovVars]))
    (sev_off _ C x ox k (frame_get hag hx0 hx))) ?_
  refine step_seq (step_loadW ovY (offE y k) (oy + k) b hb (hD _ (by simp [ovVars]))
    (sev_off _ C y oy k (by rw [get_cons_ne _ _ _ _ hyX]; exact frame_get hag hy0 hy))) ?_
  refine step_ifI _ _ (sev_eqv _ ovX ovY a b (by simp (config := {decide := true}) [T.Env.get_cons])
    (by simp (config := {decide := true}) [T.Env.get_cons])) (fun h => ?_) (fun _ => step_hangI)
  exact fun t ht => (step_skipI t ht).imp id (fun ⟨h1, h2⟩ => ⟨h1, ite10_ne h, _,
    frame_cons (frame_cons hag ovX hXm a) ovY hYm b, h2⟩)

/-- The handle lists named by the words at `x + 8k` and `y + 8k` (into `ovA`, `ovB2`). -/
def lstXY (x y : MlS) (k : Nat) : ProgHOL 64 :=
  .seq (.assign .local ovA (.load .one (offE x k))) (.seq (.assign .local ovB2 (.load .one (offE y k))) lpEqP)

theorem lstXY_step {C : Ctx} {s : AState} {Γ Γ0 : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    (hHL : C.H.length < 2 ^ 61)
    {mods : List MlS} (hag : ∀ z, z ∉ mods → Γ.get z = Γ0.get z) (hlp : ∀ z ∈ lpMods, z ∈ mods)
    {x y : MlS} (hx0 : x ∉ mods) (hy0 : y ∉ mods) {ox oy : Nat} (hx : Γ0.get x = some (cellA C ox))
    (hy : Γ0.get y = some (cellA C oy)) (k : Nat) {kd : IdxKind} {w w' : BitVec 64} {xs ys : List (Idx kd)}
    (ha : C.H[ox + k]? = some w) (hb : C.H[oy + k]? = some w') (hw : ENList C.HB C.H w xs)
    (hw' : ENList C.HB C.H w' ys) :
    Step (Inv (σ := σ) C s Γ [] D) (lstXY x y k)
      (fun t => xs = ys ∧ ∃ Γ', (∀ z, z ∉ mods → Γ'.get z = Γ0.get z) ∧ Inv C s Γ' [] D t) := by
  obtain ⟨o1, rfl, hb1⟩ := hw
  obtain ⟨o2, rfl, hb2⟩ := hw'
  have hb1' : BlkAt C.H o1 (xs.map Enc.idxW) := hb1
  have hb2' : BlkAt C.H o2 (ys.map Enc.idxW) := hb2
  have l1 := blkAt_len hb1'
  have l2 := blkAt_len hb2'
  have hAm : ovA ∈ mods := hlp _ (by simp [lpMods])
  have hyA : y ≠ ovA := fun e => hy0 (e ▸ hAm)
  refine step_seq (step_loadW ovA (offE x k) (ox + k) _ ha (hD _ (by simp [ovVars]))
    (sev_off _ C x ox k (frame_get hag hx0 hx))) ?_
  refine step_seq (step_loadW ovB2 (offE y k) (oy + k) _ hb (hD _ (by simp [ovVars]))
    (sev_off _ C y oy k (by rw [get_cons_ne _ _ _ _ hyA]; exact frame_get hag hy0 hy))) ?_
  refine fun t ht => (lpEq_step hD hb1' hb2' (by omega) (by omega)
    (by simp (config := {decide := true}) [T.Env.get_cons]; rfl)
    (by simp (config := {decide := true}) [T.Env.get_cons]; rfl) t ht).imp id (fun ⟨hn, h0, he, Γ', hag', hq⟩ =>
      ⟨hn, map_idxW_inj (blkAt_eq63 hb1' hb2' h0 he (by omega) (by omega)), Γ', fun z hz => ?_, hq⟩)
  rw [hag' z (fun h => hz (hlp _ h))]
  exact frame_cons (frame_cons hag ovA hAm _) ovB2 (hlp _ (by simp [lpMods])) _ z hz

/-! ## Stored constants -/

def tagCI : IConstantInfo → Nat
  | .axiomInfo .. => 0 | .defnInfo .. => 1 | .thmInfo .. => 2 | .indInfo .. => 3 | .ctorInfo .. => 4
  | .recInfo .. => 5

theorem tagCI_lt (ci : IConstantInfo) : tagCI ci < 6 := by cases ci <;> simp [tagCI]

theorem cie_tag {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) :
    H[o]? = some (BitVec.ofNat 64 (tagCI ci)) := by
  cases ci <;> simp only [CIE] at h <;> simp only [tagCI] <;> first | exact h.2 | exact h.2.1

def fireTag : IRecRuleFire → Nat
  | .plain => 0 | .nested .. => 1 | .levels .. => 2

theorem fireE_tag {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {f : IRecRuleFire} (h : FireE EB H o f) :
    H[o]? = some (BitVec.ofNat 64 (fireTag f)) := by
  cases f <;> simp only [FireE] at h <;> simp only [fireTag]
  · exact h
  all_goals exact h.1

def cmpC (k : Nat) : ProgHOL 64 := cmpXY ovCX ovCY k
def lstC (k : Nat) : ProgHOL 64 := lstXY ovCX ovCY k

def indTailP : ProgHOL 64 := .seq (cmpC 4) (.seq (cmpC 6) (.seq (cmpC 7) (.seq (cmpC 9) (.seq (lstC 5) (lstC 8)))))
def ctorTailP : ProgHOL 64 := .seq (cmpC 4) (.seq (cmpC 5) (cmpC 6))

def ruleBodyP : ProgHOL 64 :=
  .seq (.assign .local ovRX (.load .one (slotE ovRA ovRI 1)))
  (.seq (.assign .local ovRY (.load .one (slotE ovRB ovRI 1)))
  (.seq (cmpXY ovRX ovRY 0) (.seq (cmpXY ovRX ovRY 1) (.seq (cmpXY ovRX ovRY 5) (.seq (cmpXY ovRX ovRY 2)
  (.seq (.assign .local ovX (.load .one (offE ovRX 2)))
  (.seq (.ite (.cmp .equal (vv ovX) (.const 0)) .skip hang)
    (.assign .local ovRI (.op .add [vv ovRI, .const 1])))))))))

def rulesEqP : ProgHOL 64 :=
  .seq (.assign .local ovRA (.load .one (offE ovCX 7)))
  (.seq (.assign .local ovRB (.load .one (offE ovCY 7)))
  (.seq (.assign .local ovRN (.load .one (vv ovRA)))
  (.seq (.assign .local ovX (.load .one (vv ovRB)))
  (.seq (.ite (.cmp .equal (vv ovRN) (vv ovX)) .skip hang)
  (.seq (.assign .local ovRI (.const 0))
    (.while (.cmp .lower (vv ovRI) (vv ovRN)) ruleBodyP))))))

def recTailP : ProgHOL 64 := .seq (cmpC 4) (.seq (cmpC 5) (.seq (cmpC 6) rulesEqP))

/-- Hang unless the stored constants at `ovCX` and `ovCY` hold the same words. -/
def cieEqP : ProgHOL 64 :=
  .seq (cmpC 0) (.seq (cmpC 1) (.seq (cmpC 3) (.seq (lstC 2)
  (.seq (.assign .local ovCT (.load .one (vv ovCX)))
  (.ite (.cmp .equal (vv ovCT) (.const 3)) indTailP
  (.ite (.cmp .equal (vv ovCT) (.const 4)) ctorTailP
  (.ite (.cmp .equal (vv ovCT) (.const 5)) recTailP hang)))))))

def cieMods : List MlS := [ovX, ovY, ovI, ovA, ovB2, ovT, ovCT, ovRA, ovRB, ovRN, ovRI, ovRX, ovRY]

theorem lp_cie : ∀ z ∈ lpMods, z ∈ cieMods := by decide

theorem indTail_step {C : Ctx} {s : AState} {Γ Γ0 : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    (hHL : C.H.length < 2 ^ 61) (hag : ∀ z, z ∉ cieMods → Γ.get z = Γ0.get z) {ox oy : Nat}
    (hX : Γ0.get ovCX = some (cellA C ox)) (hY : Γ0.get ovCY = some (cellA C oy)) {v v' : IConstantVal}
    {caps caps' : IIndCaps} (hc : CIE C.HB C.H ox (.indInfo v caps)) (hc' : CIE C.HB C.H oy (.indInfo v' caps')) :
    Step (Inv (σ := σ) C s Γ [] D) indTailP
      (fun t => caps = caps' ∧ ∃ Γ', (∀ z, z ∉ cieMods → Γ'.get z = Γ0.get z) ∧ Inv C s Γ' [] D t) := by
  obtain ⟨-, -, h4, ⟨wa, h5, hla⟩, h6, h7, ⟨wc, h8, hlc⟩, h9⟩ := hc
  obtain ⟨-, -, h4', ⟨wa', h5', hla'⟩, h6', h7', ⟨wc', h8', hlc'⟩, h9'⟩ := hc'
  have mX : ovX ∈ cieMods := by decide
  have mY : ovY ∈ cieMods := by decide
  have nX : ovCX ∉ cieMods := by decide
  have nY : ovCY ∉ cieMods := by decide
  refine step_cont (cmpXY_step hD hag mX mY nX nY hX hY 4 h4 h4') (fun t ⟨e4, Γ1, hag1, ht1⟩ => step_here ?_ ht1)
  refine step_cont (cmpXY_step hD hag1 mX mY nX nY hX hY 6 h6.1 h6'.1) (fun t ⟨e6, Γ2, hag2, ht2⟩ => step_here ?_ ht2)
  refine step_cont (cmpXY_step hD hag2 mX mY nX nY hX hY 7 h7.1 h7'.1) (fun t ⟨e7, Γ3, hag3, ht3⟩ => step_here ?_ ht3)
  refine step_cont (cmpXY_step hD hag3 mX mY nX nY hX hY 9 h9 h9') (fun t ⟨e9, Γ4, hag4, ht4⟩ => step_here ?_ ht4)
  refine step_cont (lstXY_step hD hHL hag4 lp_cie nX nY hX hY 5 h5 h5' hla hla') (fun t ⟨ea, Γ5, hag5, ht5⟩ => step_here ?_ ht5)
  refine fun t ht => (lstXY_step hD hHL hag5 lp_cie nX nY hX hY 8 h8 h8' hlc hlc' t ht).imp id
    (fun ⟨hn, ec, hq⟩ => ⟨hn, ?_, hq⟩)
  cases caps; cases caps'
  simp only [IIndCaps.mk.injEq]
  exact ⟨boolW_inj e4, ea, ofNat_inj63 h6.2 h6'.2 e6, ofNat_inj63 h7.2 h7'.2 e7, ec, boolW_inj e9⟩

theorem ctorTail_step {C : Ctx} {s : AState} {Γ Γ0 : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    (hag : ∀ z, z ∉ cieMods → Γ.get z = Γ0.get z) {ox oy : Nat}
    (hX : Γ0.get ovCX = some (cellA C ox)) (hY : Γ0.get ovCY = some (cellA C oy)) {v v' : IConstantVal}
    {np nf np' nf' : Nat} {T T' : NIdx} (hc : CIE C.HB C.H ox (.ctorInfo v np nf T))
    (hc' : CIE C.HB C.H oy (.ctorInfo v' np' nf' T')) :
    Step (Inv (σ := σ) C s Γ [] D) ctorTailP
      (fun t => (np = np' ∧ nf = nf' ∧ T = T') ∧ ∃ Γ', (∀ z, z ∉ cieMods → Γ'.get z = Γ0.get z) ∧ Inv C s Γ' [] D t) := by
  obtain ⟨-, -, h4, h5, h6⟩ := hc
  obtain ⟨-, -, h4', h5', h6'⟩ := hc'
  have mX : ovX ∈ cieMods := by decide
  have mY : ovY ∈ cieMods := by decide
  have nX : ovCX ∉ cieMods := by decide
  have nY : ovCY ∉ cieMods := by decide
  refine step_cont (cmpXY_step hD hag mX mY nX nY hX hY 4 h4.1 h4'.1) (fun t ⟨e4, Γ1, hag1, ht1⟩ => step_here ?_ ht1)
  refine step_cont (cmpXY_step hD hag1 mX mY nX nY hX hY 5 h5.1 h5'.1) (fun t ⟨e5, Γ2, hag2, ht2⟩ => step_here ?_ ht2)
  refine fun t ht => (cmpXY_step hD hag2 mX mY nX nY hX hY 6 h6 h6' t ht).imp id
    (fun ⟨hn, e6, hq⟩ => ⟨hn, ⟨ofNat_inj63 h4.2 h4'.2 e4, ofNat_inj63 h5.2 h5'.2 e5, Enc.idxW_inj e6⟩, hq⟩)

theorem rulesE_len {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {rs : List IRecRule}
    (hp : ∀ i (hi : i < rs.length), ∃ q, H[o + 1 + i]? = some (EB + BitVec.ofNat 64 (8 * q)) ∧ RuleE EB H q rs[i]) :
    rs.length ≤ H.length := by
  cases e : rs.length with
  | zero => exact Nat.zero_le _
  | succ n =>
    obtain ⟨q, hq, -⟩ := hp n (by omega)
    have := lt_of_get hq; omega

theorem rule_eq {EB : BitVec 64} {H : List (BitVec 64)} {q q' : Nat} {r r' : IRecRule} (h : RuleE EB H q r)
    (h' : RuleE EB H q' r') (e0 : H[q]? = H[q']?) (e1 : H[q + 1]? = H[q' + 1]?) (e5 : H[q + 5]? = H[q' + 5]?)
    (hf : fireTag r.fire = 0) (hf' : fireTag r'.fire = 0) : r = r' := by
  obtain ⟨c, n, f, x⟩ := r
  obtain ⟨c', n', f', x'⟩ := r'
  obtain ⟨h0, h1, -, h5⟩ := h
  obtain ⟨h0', h1', -, h5'⟩ := h'
  simp only at hf hf' h0 h1 h5 h0' h1' h5'
  have ef : f = f' := by
    cases f <;> cases f' <;> simp_all [fireTag]
  simp only [IRecRule.mk.injEq]
  exact ⟨Enc.idxW_inj (some_inj' h0 (e0.trans h0')), natE_inj h1 h1' e1, ef, Enc.idxW_inj (some_inj' h5 (e5.trans h5'))⟩

theorem rulesEq_step {C : Ctx} {s : AState} {Γ Γ0 : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    (hHL : C.H.length < 2 ^ 61) (hag : ∀ z, z ∉ cieMods → Γ.get z = Γ0.get z) {ox oy : Nat}
    (hX : Γ0.get ovCX = some (cellA C ox)) (hY : Γ0.get ovCY = some (cellA C oy)) {w w' : BitVec 64}
    {rs rs' : List IRecRule} (h7 : C.H[ox + 7]? = some w) (h7' : C.H[oy + 7]? = some w')
    (hr : RulesE C.HB C.H w rs) (hr' : RulesE C.HB C.H w' rs') :
    Step (Inv (σ := σ) C s Γ [] D) rulesEqP
      (fun t => rs = rs' ∧ ∃ Γ', (∀ z, z ∉ cieMods → Γ'.get z = Γ0.get z) ∧ Inv C s Γ' [] D t) := by
  obtain ⟨o1, rfl, hn1, hp1⟩ := hr
  obtain ⟨o2, rfl, hn2, hp2⟩ := hr'
  have l1 := rulesE_len hp1
  have l2 := rulesE_len hp2
  have nX : ovCX ∉ cieMods := by decide
  have nY : ovCY ∉ cieMods := by decide
  refine step_seq (step_loadW ovRA (offE ovCX 7) (ox + 7) _ h7 (hD _ (by simp [ovVars]))
    (sev_off _ C ovCX ox 7 (frame_get hag nX hX))) ?_
  have f1 := frame_cons hag ovRA (by decide) (C.HB + BitVec.ofNat 64 (8 * o1))
  refine step_seq (step_loadW ovRB (offE ovCY 7) (oy + 7) _ h7' (hD _ (by simp [ovVars]))
    (sev_off _ C ovCY oy 7 (frame_get f1 nY hY))) ?_
  have f2 := frame_cons f1 ovRB (by decide) (C.HB + BitVec.ofNat 64 (8 * o2))
  refine step_seq (step_loadW ovRN (vv ovRA) o1 _ hn1 (hD _ (by simp [ovVars]))
    (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons]; rfl)) ?_
  have f3 := frame_cons f2 ovRN (by decide) (BitVec.ofNat 64 rs.length)
  refine step_seq (step_loadW ovX (vv ovRB) o2 _ hn2 (hD _ (by simp [ovVars]))
    (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons]; rfl)) ?_
  have f4 := frame_cons f3 ovX (by decide) (BitVec.ofNat 64 rs'.length)
  let Γ4 : Env := (ovX, BitVec.ofNat 64 rs'.length) :: (ovRN, BitVec.ofNat 64 rs.length) ::
    (ovRB, C.HB + BitVec.ofNat 64 (8 * o2)) :: (ovRA, C.HB + BitVec.ofNat 64 (8 * o1)) :: Γ
  refine step_cont (Q := fun t => rs.length = rs'.length ∧ Inv C s Γ4 [] D t)
    (step_ifI _ _ (sev_eqv _ ovRN ovX (BitVec.ofNat 64 rs.length) (BitVec.ofNat 64 rs'.length)
      (by simp (config := {decide := true}) [Γ4, T.Env.get_cons]) (by simp (config := {decide := true}) [Γ4, T.Env.get_cons]))
      (fun h => fun t ht => (step_skipI t ht).imp id (fun ⟨h1, h2⟩ => ⟨h1, ofNat_inj63 (by omega) (by omega) (ite10_ne h), h2⟩))
      (fun _ => step_hangI)) (fun t ⟨hl, ht⟩ => step_here ?_ ht)
  refine step_seq (step_assignI ovRI (.const 0) 0 (hD _ (by simp [ovVars])) rfl) ?_
  have f5 := frame_cons f4 ovRI (by decide) 0
  refine fun t ht => (step_whileCE (s := s) (D := D) _ _
    (fun C' Γ' => C' = C ∧ ∃ i, i ≤ rs.length ∧ Γ'.get ovRI = some (BitVec.ofNat 64 i) ∧
      Γ'.get ovRN = some (BitVec.ofNat 64 rs.length) ∧ Γ'.get ovRA = some (cellA C o1) ∧
      Γ'.get ovRB = some (cellA C o2) ∧ (∀ i' (h1 : i' < i) (h2 : i' < rs.length) (h3 : i' < rs'.length), rs[i'] = rs'[i']) ∧
      (∀ z, z ∉ cieMods → Γ'.get z = Γ0.get z))
    (fun C' Γ' => C' = C ∧ (∀ i' (h2 : i' < rs.length) (h3 : i' < rs'.length), rs[i'] = rs'[i']) ∧
      (∀ z, z ∉ cieMods → Γ'.get z = Γ0.get z))
    C _ ⟨rfl, 0, Nat.zero_le _, by simp (config := {decide := true}) [T.Env.get_cons],
      by simp (config := {decide := true}) [Γ4, T.Env.get_cons],
      by simp (config := {decide := true}) [Γ4, T.Env.get_cons]; rfl,
      by simp (config := {decide := true}) [Γ4, T.Env.get_cons]; rfl,
      fun i' h => absurd h (by omega), f5⟩ ?_ t ht).imp id
    (fun ⟨hn, C', Γ', ⟨hC, hall, hag'⟩, hq⟩ => by
      subst C'
      exact ⟨hn, List.ext_getElem hl (fun i h1 h2 => hall i h1 h2), Γ', hag', hq⟩)
  intro C' Γ' ⟨hC, i, hi, gI, gN, gA, gB, hdone, hag'⟩
  subst C'
  refine ⟨bw (i < rs.length), sev_lowerV _ _ _ _ _ gI gN (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
  · have : i = rs.length := by have := bw_eq0' h0; omega
    subst this; exact ⟨rfl, fun i' h2 h3 => hdone i' h2 h2 h3, hag'⟩
  · have hlt := bw_ne0' h1
    obtain ⟨q, hq, hrq⟩ := hp1 i hlt
    have hi62 : 8 * i < 2 ^ 64 := by
      have h1 : i < 2 ^ 61 := Nat.lt_of_lt_of_le hlt (Nat.le_trans l1 (Nat.le_of_lt hHL))
      omega
    obtain ⟨q', hq', hrq'⟩ := hp2 i (by omega)
    refine step_seq (step_loadW ovRX (slotE ovRA ovRI 1) _ _ hq (hD _ (by simp [ovVars]))
      (by rw [sev_slot _ C ovRA ovRI o1 i 1 gA gI hi62])) ?_
    refine step_seq (step_loadW ovRY (slotE ovRB ovRI 1) _ _ hq' (hD _ (by simp [ovVars]))
      (by rw [sev_slot _ C ovRB ovRI o2 i 1 (by simp (config := {decide := true}) [T.Env.get_cons, gB])
        (by simp (config := {decide := true}) [T.Env.get_cons, gI]) hi62])) ?_
    let Γb : Env := (ovRY, C.HB + BitVec.ofNat 64 (8 * q')) :: (ovRX, C.HB + BitVec.ofNat 64 (8 * q)) :: Γ'
    have bX : Γb.get ovRX = some (cellA C q) := by simp (config := {decide := true}) [Γb, T.Env.get_cons]; rfl
    have bY : Γb.get ovRY = some (cellA C q') := by simp (config := {decide := true}) [Γb, T.Env.get_cons]; rfl
    have m0 : ∀ z, z ∉ [ovX, ovY] → Γb.get z = Γb.get z := fun _ _ => rfl
    have mX : ovX ∈ [ovX, ovY] := by decide
    have mY : ovY ∈ [ovX, ovY] := by decide
    have nRX : ovRX ∉ [ovX, ovY] := by decide
    have nRY : ovRY ∉ [ovX, ovY] := by decide
    refine step_cont (cmpXY_step hD m0 mX mY nRX nRY bX bY 0 (a := Enc.idxW rs[i].ctor) (b := Enc.idxW rs'[i].ctor)
      (by simpa using hrq.1) (by simpa using hrq'.1))
      (fun t ⟨e0, Γ1, hag1, ht1⟩ => step_here ?_ ht1)
    refine step_cont (cmpXY_step hD hag1 mX mY nRX nRY bX bY 1 hrq.2.1.1 hrq'.2.1.1)
      (fun t ⟨e1, Γ2, hag2, ht2⟩ => step_here ?_ ht2)
    refine step_cont (cmpXY_step hD hag2 mX mY nRX nRY bX bY 5 hrq.2.2.2 hrq'.2.2.2)
      (fun t ⟨e5, Γ3, hag3, ht3⟩ => step_here ?_ ht3)
    refine step_cont (cmpXY_step hD hag3 mX mY nRX nRY bX bY 2 (fireE_tag hrq.2.2.1) (fireE_tag hrq'.2.2.1))
      (fun t ⟨e2, Γ5, hag5, ht5⟩ => step_here ?_ ht5)
    refine step_seq (step_loadW ovX (offE ovRX 2) (q + 2) _ (fireE_tag hrq.2.2.1) (hD _ (by simp [ovVars]))
      (sev_off _ C ovRX q 2 (frame_get hag5 nRX bX))) ?_
    refine step_cont (Q := fun t => fireTag rs[i].fire = 0 ∧ Inv C s ((ovX, BitVec.ofNat 64 (fireTag rs[i].fire)) :: Γ5) [] D t)
      (step_ifI _ _ (sev_eqC _ ovX 0 _ (by simp (config := {decide := true}) [T.Env.get_cons]))
        (fun h => fun t ht => (step_skipI t ht).imp id (fun ⟨h1, h2⟩ => ⟨h1, ofNat_inj63 (by
          have := rs[i].fire; cases rs[i].fire <;> simp [fireTag]) (by decide) (ite10_ne h), h2⟩))
        (fun _ => step_hangI)) (fun t ⟨hf, ht6⟩ => step_here ?_ ht6)
    have hf' : fireTag rs'[i].fire = 0 := by
      have := ofNat_inj63 (by cases rs[i].fire <;> simp [fireTag]) (by cases rs'[i].fire <;> simp [fireTag]) e2
      omega
    have hre : rs[i] = rs'[i] := rule_eq hrq hrq' (by rw [hrq.1, hrq'.1, e0]) (by rw [hrq.2.1.1, hrq'.2.1.1, e1])
      (by rw [hrq.2.2.2, hrq'.2.2.2, e5]) hf hf'
    have g6 : ∀ z, z ∉ [ovX, ovY] → z ≠ ovRX → z ≠ ovRY →
        T.Env.get ((ovX, BitVec.ofNat 64 (fireTag rs[i].fire)) :: Γ5) z = Γ'.get z := by
      intro z hz h1 h2
      have : z ≠ ovX := fun e => hz (by simp [e])
      rw [get_cons_ne _ _ _ _ this, hag5 z hz]; simp only [Γb, get_cons_ne _ _ _ _ h1, get_cons_ne _ _ _ _ h2]
    refine fun t ht => (step_assignI ovRI (.op .add [vv ovRI, .const 1]) _ (hD _ (by simp [ovVars]))
      (sev_succV _ ovRI i (by rw [g6 _ (by decide) (by decide) (by decide)]; exact gI)) t ht).imp id
      (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, i + 1, by omega, by simp (config := {decide := true}) [T.Env.get_cons],
        by rw [get_cons_ne _ _ _ _ (by decide), g6 _ (by decide) (by decide) (by decide)]; exact gN,
        by rw [get_cons_ne _ _ _ _ (by decide), g6 _ (by decide) (by decide) (by decide)]; exact gA,
        by rw [get_cons_ne _ _ _ _ (by decide), g6 _ (by decide) (by decide) (by decide)]; exact gB,
        fun i' h1 h2 h3 => ?_, fun z hz => ?_⟩, hq⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | rfl
      · exact hdone i' h h2 h3
      · exact hre
    · have h1 : z ≠ ovRI := fun e => hz (by simp [e, cieMods])
      have h2 : z ∉ [ovX, ovY] := fun h => hz (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> decide)
      rw [get_cons_ne _ _ _ _ h1, g6 z h2 (fun e => hz (by simp [e, cieMods])) (fun e => hz (by simp [e, cieMods]))]
      exact hag' z hz

theorem recTail_step {C : Ctx} {s : AState} {Γ Γ0 : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    (hHL : C.H.length < 2 ^ 61) (hag : ∀ z, z ∉ cieMods → Γ.get z = Γ0.get z) {ox oy : Nat}
    (hX : Γ0.get ovCX = some (cellA C ox)) (hY : Γ0.get ovCY = some (cellA C oy)) {v v' : IConstantVal}
    {mi rp mi' rp' : Nat} {k k' : Bool} {rs rs' : List IRecRule} (hc : CIE C.HB C.H ox (.recInfo v mi rp k rs))
    (hc' : CIE C.HB C.H oy (.recInfo v' mi' rp' k' rs')) :
    Step (Inv (σ := σ) C s Γ [] D) recTailP
      (fun t => (mi = mi' ∧ rp = rp' ∧ k = k' ∧ rs = rs') ∧
        ∃ Γ', (∀ z, z ∉ cieMods → Γ'.get z = Γ0.get z) ∧ Inv C s Γ' [] D t) := by
  obtain ⟨-, -, h4, h5, h6, w, h7, hR⟩ := hc
  obtain ⟨-, -, h4', h5', h6', w', h7', hR'⟩ := hc'
  have mX : ovX ∈ cieMods := by decide
  have mY : ovY ∈ cieMods := by decide
  have nX : ovCX ∉ cieMods := by decide
  have nY : ovCY ∉ cieMods := by decide
  refine step_cont (cmpXY_step hD hag mX mY nX nY hX hY 4 h4.1 h4'.1) (fun t ⟨e4, Γ1, hag1, ht1⟩ => step_here ?_ ht1)
  refine step_cont (cmpXY_step hD hag1 mX mY nX nY hX hY 5 h5.1 h5'.1) (fun t ⟨e5, Γ2, hag2, ht2⟩ => step_here ?_ ht2)
  refine step_cont (cmpXY_step hD hag2 mX mY nX nY hX hY 6 h6 h6') (fun t ⟨e6, Γ3, hag3, ht3⟩ => step_here ?_ ht3)
  refine fun t ht => (rulesEq_step hD hHL hag3 hX hY h7 h7' hR hR' t ht).imp id
    (fun ⟨hn, er, hq⟩ => ⟨hn, ⟨ofNat_inj63 h4.2 h4'.2 e4, ofNat_inj63 h5.2 h5'.2 e5, boolW_inj e6, er⟩, hq⟩)

theorem cv_ext {a b : IConstantVal} (h1 : a.name = b.name) (h2 : a.levelParams = b.levelParams)
    (h3 : a.type = b.type) : a = b := by
  cases a; cases b; simp_all

theorem tag3 {ci : IConstantInfo} (h : tagCI ci = 3) : ∃ v caps, ci = .indInfo v caps := by
  cases ci <;> simp_all [tagCI]
theorem tag4 {ci : IConstantInfo} (h : tagCI ci = 4) : ∃ v np nf T, ci = .ctorInfo v np nf T := by
  cases ci <;> simp_all [tagCI]
theorem tag5 {ci : IConstantInfo} (h : tagCI ci = 5) : ∃ v mi rp k rs, ci = .recInfo v mi rp k rs := by
  cases ci <;> simp_all [tagCI]

/-- **`cieEqP`**: it returns only if the two stored constants are equal. -/
theorem cieEq_step {C : Ctx} {s : AState} {Γ Γ0 : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    (hHL : C.H.length < 2 ^ 61) (hag : ∀ z, z ∉ cieMods → Γ.get z = Γ0.get z) {ox oy : Nat}
    (hX : Γ0.get ovCX = some (cellA C ox)) (hY : Γ0.get ovCY = some (cellA C oy)) {ci ci' : IConstantInfo}
    (hc : CIE C.HB C.H ox ci) (hc' : CIE C.HB C.H oy ci') :
    Step (Inv (σ := σ) C s Γ [] D) cieEqP
      (fun t => ci = ci' ∧ ∃ Γ', (∀ z, z ∉ cieMods → Γ'.get z = Γ0.get z) ∧ Inv C s Γ' [] D t) := by
  have ht := cie_tag hc
  have ht' := cie_tag hc'
  obtain ⟨hn, ⟨wl, hl, hll⟩, hty⟩ := hc.1
  obtain ⟨hn', ⟨wl', hl', hll'⟩, hty'⟩ := hc'.1
  have mX : ovX ∈ cieMods := by decide
  have mY : ovY ∈ cieMods := by decide
  have nX : ovCX ∉ cieMods := by decide
  have nY : ovCY ∉ cieMods := by decide
  refine step_cont (cmpXY_step hD hag mX mY nX nY hX hY 0 (a := BitVec.ofNat 64 (tagCI ci))
    (b := BitVec.ofNat 64 (tagCI ci')) (by simpa using ht) (by simpa using ht'))
    (fun t ⟨e0, Γ1, hag1, ht1⟩ => step_here ?_ ht1)
  have et : tagCI ci = tagCI ci' := ofNat_inj63 (by have := tagCI_lt ci; omega) (by have := tagCI_lt ci'; omega) e0
  refine step_cont (cmpXY_step hD hag1 mX mY nX nY hX hY 1 hn hn') (fun t ⟨e1, Γ2, hag2, ht2⟩ => step_here ?_ ht2)
  refine step_cont (cmpXY_step hD hag2 mX mY nX nY hX hY 3 hty hty') (fun t ⟨e3, Γ3, hag3, ht3⟩ => step_here ?_ ht3)
  refine step_cont (lstXY_step hD hHL hag3 lp_cie nX nY hX hY 2 hl hl' hll hll') (fun t ⟨e2, Γ4, hag4, ht4⟩ => step_here ?_ ht4)
  have hv : ci.toConstantVal = ci'.toConstantVal := cv_ext (Enc.idxW_inj e1) e2 (Enc.idxW_inj e3)
  refine step_seq (step_loadW ovCT (vv ovCX) ox _ ht (hD _ (by simp [ovVars]))
    (by simp only [sev, vv]; exact frame_get hag4 nX hX)) ?_
  have hag5 := frame_cons hag4 ovCT (by decide) (BitVec.ofNat 64 (tagCI ci))
  have gT : T.Env.get ((ovCT, BitVec.ofNat 64 (tagCI ci)) :: Γ4) ovCT = some (BitVec.ofNat 64 (tagCI ci)) := by
    simp (config := {decide := true}) [T.Env.get_cons]
  refine step_ifI _ _ (sev_eqC _ ovCT 3 _ gT) (fun h3 => ?_) (fun h3 => ?_)
  · have e : tagCI ci = 3 := ofNat_inj63 (by have := tagCI_lt ci; omega) (by decide) (ite10_ne h3)
    obtain ⟨v, caps, rfl⟩ := tag3 e
    obtain ⟨v', caps', rfl⟩ := tag3 (et ▸ e)
    refine fun t ht => (indTail_step hD hHL hag5 hX hY hc hc' t ht).imp id (fun ⟨hn, ec, hq⟩ => ⟨hn, ?_, hq⟩)
    simp only [IConstantInfo.toConstantVal] at hv; rw [hv, ec]
  refine step_ifI _ _ (sev_eqC _ ovCT 4 _ gT) (fun h4 => ?_) (fun h4 => ?_)
  · have e : tagCI ci = 4 := ofNat_inj63 (by have := tagCI_lt ci; omega) (by decide) (ite10_ne h4)
    obtain ⟨v, np, nf, T, rfl⟩ := tag4 e
    obtain ⟨v', np', nf', T', rfl⟩ := tag4 (et ▸ e)
    refine fun t ht => (ctorTail_step hD hag5 hX hY hc hc' t ht).imp id (fun ⟨hn, ⟨a, b, c⟩, hq⟩ => ⟨hn, ?_, hq⟩)
    simp only [IConstantInfo.toConstantVal] at hv; rw [hv, a, b, c]
  refine step_ifI _ _ (sev_eqC _ ovCT 5 _ gT) (fun h5 => ?_) (fun _ => step_hangI)
  have e : tagCI ci = 5 := ofNat_inj63 (by have := tagCI_lt ci; omega) (by decide) (ite10_ne h5)
  obtain ⟨v, mi, rp, k, rs, rfl⟩ := tag5 e
  obtain ⟨v', mi', rp', k', rs', rfl⟩ := tag5 (et ▸ e)
  refine fun t ht => (recTail_step hD hHL hag5 hX hY hc hc' t ht).imp id (fun ⟨hn, ⟨a, b, c, d⟩, hq⟩ => ⟨hn, ?_, hq⟩)
  simp only [IConstantInfo.toConstantVal] at hv; rw [hv, a, b, c, d]

/-! ## Blocks -/

def memBodyP : ProgHOL 64 :=
  .seq (.assign .local ovCX (.load .one (slotE ovMA ovM 1)))
  (.seq (.assign .local ovCY (.load .one (slotE ovMB ovM 1)))
  (.seq cieEqP (.assign .local ovM (.op .add [vv ovM, .const 1]))))

/-- Hang unless the block record at `ovD` has the record at `ovP`'s words, member by member. -/
def blkEqP : ProgHOL 64 :=
  .seq (cmpXY ovD ovP 0) (.seq (cmpXY ovD ovP 1)
  (.seq (.assign .local ovMA (.load .one (offE ovD 2)))
  (.seq (.assign .local ovMB (.load .one (offE ovP 2)))
  (.seq (.assign .local ovMN (.load .one (vv ovMA)))
  (.seq (.assign .local ovX (.load .one (vv ovMB)))
  (.seq (.ite (.cmp .equal (vv ovMN) (vv ovX)) .skip hang)
  (.seq (.assign .local ovM (.const 0))
    (.while (.cmp .lower (vv ovM) (vv ovMN)) memBodyP))))))))

def blkMods : List MlS := cieMods ++ [ovM, ovMN, ovMA, ovMB, ovCX, ovCY]

theorem cie_blk : ∀ z, z ∉ blkMods → z ∉ cieMods := fun z hz h => hz (List.mem_append_left _ h)

/-- **`blkEqP`**: it returns only if the block record at `ovD` is the record at `ovP`. -/
theorem blkEqP_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    (hHL : C.H.length < 2 ^ 61) {F od op : Nat} {block : List IConstantInfo} {nP : Nat} {p : IDeclaration}
    (hrd : RecEnc C F C.H od (.indDecl block nP)) (hrp : RecEnc C F C.H op p)
    (hd : Γ.get ovD = some (cellA C od)) (hp : Γ.get ovP = some (cellA C op)) :
    Step (Inv (σ := σ) C s Γ [] D) blkEqP (fun t => IDeclaration.indDecl block nP = p ∧
      ∃ Γ', (∀ z, z ∉ blkMods → Γ'.get z = Γ.get z) ∧ Inv C s Γ' [] D t) := by
  have mX : ovX ∈ blkMods := by decide
  have mY : ovY ∈ blkMods := by decide
  have nD : ovD ∉ blkMods := by decide
  have nP0 : ovP ∉ blkMods := by decide
  have m0 : ∀ z, z ∉ blkMods → Γ.get z = Γ.get z := fun _ _ => rfl
  refine step_cont (cmpXY_step hD m0 mX mY nD nP0 hd hp 0 (a := BitVec.ofNat 64 (tagOf (.indDecl block nP)))
    (b := BitVec.ofNat 64 (tagOf p)) (by simpa using recEnc_tag hrd) (by simpa using recEnc_tag hrp))
    (fun t ⟨e0, Γ1, hag1, ht1⟩ => step_here ?_ ht1)
  have et : tagOf p = 4 := (tagOf_inj (tagOf_lt _) (tagOf_lt p) e0).symm
  cases p with
  | indDecl block' nP' =>
    obtain ⟨-, -, -, h1, ob, -, h2, hIB, hl59, hn59, -⟩ := hrd
    obtain ⟨-, -, -, h1', ob', -, h2', hIB', hl59', hn59', -⟩ := hrp
    obtain ⟨os, hlen, hblk, hcie⟩ := hIB C.H (fun _ _ _ h => h)
    obtain ⟨os', hlen', hblk', hcie'⟩ := hIB' C.H (fun _ _ _ h => h)
    refine step_cont (cmpXY_step hD hag1 mX mY nD nP0 hd hp 1 h1 h1') (fun t ⟨e1, Γ2, hag2, ht2⟩ => step_here ?_ ht2)
    have enP : nP = nP' := ofNat_inj63 (by omega) (by omega) e1
    refine step_seq (step_loadW ovMA (offE ovD 2) (od + 2) _ h2 (hD _ (by simp [ovVars]))
      (sev_off _ C ovD od 2 (frame_get hag2 nD hd))) ?_
    have f3 := frame_cons hag2 ovMA (by decide) (cellA C ob)
    refine step_seq (step_loadW ovMB (offE ovP 2) (op + 2) _ h2' (hD _ (by simp [ovVars]))
      (sev_off _ C ovP op 2 (frame_get f3 nP0 hp))) ?_
    have f4 := frame_cons f3 ovMB (by decide) (cellA C ob')
    refine step_seq (step_loadW ovMN (vv ovMA) ob _ hblk.1 (hD _ (by simp [ovVars]))
      (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
    have f5 := frame_cons f4 ovMN (by decide) (BitVec.ofNat 64 (os.map (cellA C)).length)
    refine step_seq (step_loadW ovX (vv ovMB) ob' _ hblk'.1 (hD _ (by simp [ovVars]))
      (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
    have f6 := frame_cons f5 ovX mX (BitVec.ofNat 64 (os'.map (cellA C)).length)
    let Γ6 : Env := (ovX, BitVec.ofNat 64 (os'.map (cellA C)).length) ::
      (ovMN, BitVec.ofNat 64 (os.map (cellA C)).length) :: (ovMB, cellA C ob') :: (ovMA, cellA C ob) :: Γ2
    refine step_cont (Q := fun t => os.length = os'.length ∧ Inv C s Γ6 [] D t)
      (step_ifI _ _ (sev_eqv _ ovMN ovX (BitVec.ofNat 64 (os.map (cellA C)).length)
        (BitVec.ofNat 64 (os'.map (cellA C)).length) (by simp (config := {decide := true}) [Γ6, T.Env.get_cons])
        (by simp (config := {decide := true}) [Γ6, T.Env.get_cons]))
        (fun h => fun t ht => (step_skipI t ht).imp id (fun ⟨a, b⟩ => ⟨a, by
          have := ofNat_inj63 (by simp; omega) (by simp; omega) (ite10_ne h); simpa using this, b⟩))
        (fun _ => step_hangI)) (fun t ⟨hl, ht⟩ => step_here ?_ ht)
    refine step_seq (step_assignI ovM (.const 0) 0 (hD _ (by simp [ovVars])) rfl) ?_
    have f7 := frame_cons f6 ovM (by decide) 0
    refine fun t ht => (step_whileCE (s := s) (D := D) _ _
      (fun C' Γ' => C' = C ∧ ∃ i, i ≤ os.length ∧ Γ'.get ovM = some (BitVec.ofNat 64 i) ∧
        Γ'.get ovMN = some (BitVec.ofNat 64 os.length) ∧ Γ'.get ovMA = some (cellA C ob) ∧
        Γ'.get ovMB = some (cellA C ob') ∧
        (∀ i' (h1 : i' < i) (h2 : i' < block.length) (h3 : i' < block'.length), block[i'] = block'[i']) ∧
        (∀ z, z ∉ blkMods → Γ'.get z = Γ.get z))
      (fun C' Γ' => C' = C ∧ (∀ i' (h2 : i' < block.length) (h3 : i' < block'.length), block[i'] = block'[i']) ∧
        (∀ z, z ∉ blkMods → Γ'.get z = Γ.get z))
      C _ ⟨rfl, 0, Nat.zero_le _, by simp (config := {decide := true}) [T.Env.get_cons],
        by simp (config := {decide := true}) [Γ6, T.Env.get_cons],
        by simp (config := {decide := true}) [Γ6, T.Env.get_cons],
        by simp (config := {decide := true}) [Γ6, T.Env.get_cons],
        fun i' h => absurd h (by omega), f7⟩ ?_ t ht).imp id
      (fun ⟨hn, C', Γ', ⟨hC, hall, hag'⟩, hq⟩ => by
        subst C'
        refine ⟨hn, ?_, Γ', hag', hq⟩
        rw [enP, List.ext_getElem (by omega) (fun i h1 h2 => hall i h1 h2)])
    intro C' Γ' ⟨hC, i, hi, gM, gN, gA, gB, hdone, hag'⟩
    subst C'
    refine ⟨bw (i < os.length), sev_lowerV _ _ _ _ _ gM gN (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
    · have : i = os.length := by have := bw_eq0' h0; omega
      subst this; exact ⟨rfl, fun i' h2 h3 => hdone i' (by omega) h2 h3, hag'⟩
    · have hlt := bw_ne0' h1
      have hx1 := hblk.2 i (by simpa using hlt)
      have hy1 := hblk'.2 i (by simp; omega)
      simp only [List.getElem_map] at hx1 hy1
      refine step_seq (step_loadW ovCX (slotE ovMA ovM 1) _ _ hx1 (hD _ (by simp [ovVars]))
        (by rw [sev_slot _ C ovMA ovM ob i 1 gA gM (by omega)])) ?_
      refine step_seq (step_loadW ovCY (slotE ovMB ovM 1) _ _ hy1 (hD _ (by simp [ovVars]))
        (by rw [sev_slot _ C ovMB ovM ob' i 1 (by simp (config := {decide := true}) [T.Env.get_cons, gB])
          (by simp (config := {decide := true}) [T.Env.get_cons, gM]) (by omega)])) ?_
      let Γb : Env := (ovCY, cellA C os'[i]) :: (ovCX, cellA C os[i]) :: Γ'
      refine step_cont (cieEq_step hD hHL (Γ0 := Γb) (fun _ _ => rfl)
        (by simp (config := {decide := true}) [Γb, T.Env.get_cons]) (by simp (config := {decide := true}) [Γb, T.Env.get_cons])
        (hcie i (by omega) hlt) (hcie' i (by omega) (by omega))) (fun t ⟨ec, Γ5, hag5, ht5⟩ => step_here ?_ ht5)
      have gM5 : Γ5.get ovM = some (BitVec.ofNat 64 i) := by
        rw [hag5 _ (by decide)]; simp (config := {decide := true}) only [Γb, T.Env.get_cons, ite_false]; exact gM
      refine fun t ht => (step_assignI ovM (.op .add [vv ovM, .const 1]) _ (hD _ (by simp [ovVars]))
        (sev_succV _ ovM i gM5) t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, i + 1, by omega,
          by simp (config := {decide := true}) [T.Env.get_cons],
          by rw [get_cons_ne _ _ _ _ (by decide), hag5 _ (by decide)]
             simp (config := {decide := true}) only [Γb, T.Env.get_cons, ite_false]; exact gN,
          by rw [get_cons_ne _ _ _ _ (by decide), hag5 _ (by decide)]
             simp (config := {decide := true}) only [Γb, T.Env.get_cons, ite_false]; exact gA,
          by rw [get_cons_ne _ _ _ _ (by decide), hag5 _ (by decide)]
             simp (config := {decide := true}) only [Γb, T.Env.get_cons, ite_false]; exact gB,
          fun i' h1 h2 h3 => ?_, fun z hz => ?_⟩, hq⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | rfl
        · exact hdone i' h h2 h3
        · exact ec
      · have h1 : z ≠ ovM := fun e => hz (by simp [e, blkMods])
        have h2 : z ≠ ovCX := fun e => hz (by simp [e, blkMods])
        have h3 : z ≠ ovCY := fun e => hz (by simp [e, blkMods])
        rw [get_cons_ne _ _ _ _ h1, hag5 z (cie_blk z hz)]
        simp only [Γb, get_cons_ne _ _ _ _ h2, get_cons_ne _ _ _ _ h3]; exact hag' z hz
  | _ => simp [tagOf] at et

end ConPanqueque.Prelude
