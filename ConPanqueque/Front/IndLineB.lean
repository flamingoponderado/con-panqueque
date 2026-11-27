import ConPanqueque.Front.IndLineA

/-! # The inductive line: loops over environments, and the distinct-names check

* `step_whileE`: a loop as a `Step`, with an invariant over the environment;
* `distP`: the constructor names of the block are pairwise distinct handles (else hang). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

set_option autoImplicit false

variable {σ : Type}

theorem inv_env_mono {C : Ctx} {s : AState} {Γ Γ' : Env} {M : Mem} {D : List MlS} {t : PState σ}
    (h : Inv C s Γ M D t) (hg : ∀ x v, Γ'.get x = some v → Γ.get x = some v) : Inv C s Γ' M D t :=
  ⟨h.sr, fun x v hx => h.env x v (hg x v hx), h.mem, h.decl⟩

/-- A loop as a step: an invariant over the environment, the test, and the body's step. -/
theorem step_whileE {C : Ctx} {s : AState} {D : List MlS} (c : ExpHOL 64) (body : ProgHOL 64)
    (I Q : Env → Prop) (Γ0 : Env) (h0 : I Γ0)
    (hc : ∀ Γ, I Γ → ∃ w, sev Γ c = some w ∧ (w = 0 → Q Γ) ∧
      (w ≠ 0 → Step (σ := σ) (Inv C s Γ [] D) body (fun t => ∃ Γ', I Γ' ∧ Inv C s Γ' [] D t))) :
    Step (σ := σ) (Inv C s Γ0 [] D) (.while c body) (fun t => ∃ Γ, Q Γ ∧ Inv C s Γ [] D t) := by
  intro t ht
  exact while_stop (σ := σ) c body (fun u => ∃ Γ, I Γ ∧ Inv C s Γ [] D u) (fun u => ∃ Γ, Q Γ ∧ Inv C s Γ [] D u)
    (by
      intro u ⟨Γ, hI, hu⟩
      obtain ⟨w, hw, h0', h1⟩ := hc Γ hI
      refine ⟨w, ?_, fun e => ⟨Γ, h0' e, hu⟩, fun hn _ => ?_⟩
      · simp only [evalHOLFinite]; exact inv_ev hu hw
      · exact h1 hn _ (inv_decClock hu)) t ⟨Γ0, h0, ht⟩

theorem step_skipI {P : PState σ → Prop} : Step P .skip P := by
  intro t ht
  refine Or.inr ⟨?_, ?_⟩ <;> simp [evaluateHOLFiniteState_eq_evaluate_def] <;> first | rfl | exact ht

/-- The address of slot `k + i` of a block at cell `o` whose address is in `x`, `i` in `y`. -/
theorem sev_slot (Γ : Env) (C : Ctx) (x y : MlS) (o i k : Nat) (hx : Γ.get x = some (cellA C o))
    (hy : Γ.get y = some (BitVec.ofNat 64 i)) (hi : 8 * i < 2 ^ 64) :
    sev Γ (.op .add [vv x, .op .add [.shift .lsl (vv y) (.const 3), .const (BitVec.ofNat 64 (8 * k))]]) =
      some (cellA C (o + k + i)) := by
  simp only [sev, vv, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
    show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, ite_true]
  rw [shl3 i hi, show o + k + i = o + (i + k) by omega, cellA_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.mul_add, Nat.add_mod]

def ilA := ofString "il_a"
def ilB := ofString "il_b"
def ilX := ofString "il_x"
def ilY := ofString "il_y"
def ilCB := ofString "il_cb"
def ilNc := ofString "il_nc"

def slotE (x y : MlS) (k : Nat) : ExpHOL 64 :=
  .op .add [vv x, .op .add [.shift .lsl (vv y) (.const 3), .const (BitVec.ofNat 64 (8 * k))]]

def distInner : ProgHOL 64 :=
  .while (.cmp .lower (vv ilB) (vv ilA))
    (.seq (.assign .local ilY (.load .one (slotE ilCB ilB 1)))
    (.seq (.ite (.cmp .equal (vv ilX) (vv ilY)) hang .skip)
      (.assign .local ilB (.op .add [vv ilB, .const 1]))))

/-- The words of the block at `ilCB` (`ilNc` of them) are pairwise distinct, else hang. -/
def distP (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local ilA (.const 0))
   (.seq (.while (.cmp .lower (vv ilA) (vv ilNc))
      (.seq (.assign .local ilB (.const 0))
      (.seq (.assign .local ilX (.load .one (slotE ilCB ilA 1)))
      (.seq distInner
        (.assign .local ilA (.op .add [vv ilA, .const 1]))))))
    rest)

def distMods : List MlS := [ilA, ilB, ilX, ilY]

theorem sev_lower_nat (Γ : Env) (x y : MlS) (a b : Nat) (hx : Γ.get x = some (BitVec.ofNat 64 a))
    (hy : Γ.get y = some (BitVec.ofNat 64 b)) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    sev Γ (.cmp .lower (vv x) (vv y)) = some (bw (a < b)) :=
  sev_lower Γ (vv x) (vv y) a b (by simpa [sev, vv] using hx) (by simpa [sev, vv] using hy) ha hb

theorem bw_ne0 {p : Prop} [Decidable p] (h : bw p ≠ 0) : p := by
  by_cases e : p
  · exact e
  · simp [bw, e] at h

theorem bw_eq0 {p : Prop} [Decidable p] (h : bw p = 0) : ¬ p := by
  intro e; simp [bw, e] at h

theorem sev_succ (Γ : Env) (x : MlS) (i : Nat) (hx : Γ.get x = some (BitVec.ofNat 64 i)) :
    sev Γ (.op .add [vv x, .const 1]) = some (BitVec.ofNat 64 (i + 1)) := by
  simp only [sev, vv, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem distP_spec {α : Type} (C : Ctx) (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ distMods, x ∈ D) (cb : Nat) (ws : List (BitVec 64)) (hb : BlkAt C.H cb ws) (hn : ws.length < B55)
    (hCB : Γ.get ilCB = some (cellA C cb)) (hNc : Γ.get ilNc = some (BitVec.ofNat 64 ws.length))
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64)
    (hk : ∀ Γ' : Env, ws.Nodup → (∀ y, y ∉ distMods → Γ'.get y = Γ.get y) → SpecR (Inv C s Γ' [] D) rest s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (distP rest) s m R := by
  unfold B55 at hn
  have hcell : ∀ i (hi : i < ws.length), C.H[cb + 1 + i]? = some ws[i] := hb.2
  have hlenH : ∀ i (hi : i < ws.length), cb + 1 + i < C.H.length := fun i hi => by
    have := hcell i hi
    by_cases hl : cb + 1 + i < C.H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at this; cases this
  unfold distP
  refine specR_assignI ilA (.const 0) 0 (hD ilA (by simp [distMods])) rfl ?_
  refine specR_dropMem ?_
  -- outer invariant
  let Kp : Env → Nat → Prop := fun G i => i ≤ ws.length ∧ G.get ilA = some (BitVec.ofNat 64 i) ∧
    (∀ y, y ∉ distMods → G.get y = Γ.get y) ∧ (∀ a b (ha : a < i) (hb : b < a) (hal : a < ws.length), ws[a] ≠ ws[b]'(by omega))
  let P : LoopPt α → Prop := fun p => p.C = C ∧ p.s = s ∧ p.m = m ∧ ∃ i, Kp p.Γ i
  have hp0 : P ⟨C, s, (ilA, 0) :: Γ, m⟩ := ⟨rfl, rfl, rfl, 0, Nat.zero_le _, by simp [Env.get_cons],
    fun y hy => by
      rw [Env.get_cons, ite_eq_right (fun e => hy (by rw [e]; simp [distMods]))],
    fun a b ha => absurd ha (by omega)⟩
  refine (specR_whileT (σ := σ) (D := D) P ⟨C, s, (ilA, 0) :: Γ, m⟩ hp0 ?_ : _)
  intro p ⟨hpC, hps, hpm, i, hiL, hpA, hpk, hpd⟩ _
  have gCB : p.Γ.get ilCB = some (cellA C cb) := by rw [hpk ilCB (by decide)]; exact hCB
  have gNc : p.Γ.get ilNc = some (BitVec.ofNat 64 ws.length) := by rw [hpk ilNc (by decide)]; exact hNc
  refine ⟨_, sev_lower_nat _ ilA ilNc i ws.length hpA gNc (by omega) (by omega), fun hw => ?_, fun hw => ?_⟩
  · have hi : i = ws.length := by have := bw_eq0 hw; omega
    subst hi
    rw [hpC, hps, hpm]
    refine hk p.Γ ?_ hpk
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro a b ha hb hab e
    exact hpd b a hb hab hb e.symm
  · have hi : i < ws.length := bw_ne0 hw
    rw [hpC, hps]
    refine step_seq (step_assignI ilB (.const 0) 0 (hD ilB (by simp [distMods])) rfl) ?_
    let G1 : Env := (ilB, 0) :: p.Γ
    have g1CB : G1.get ilCB = some (cellA C cb) := by rw [Env.get_cons, ite_eq_right (by decide)]; exact gCB
    have g1A : G1.get ilA = some (BitVec.ofNat 64 i) := by rw [Env.get_cons, ite_eq_right (by decide)]; exact hpA
    refine step_seq (step_heapLoadI ilX (slotE ilCB ilA 1) (cb + 1 + i) (hlenH i hi) (hD ilX (by simp [distMods]))
      (sev_slot G1 C ilCB ilA cb i 1 g1CB g1A (by omega))) ?_
    rw [show C.H[cb + 1 + i]'(hlenH i hi) = ws[i] by
      have := hcell i hi; rw [List.getElem?_eq_getElem (hlenH i hi)] at this; exact Option.some.inj this]
    let G2 : Env := (ilX, ws[i]) :: G1
    -- inner loop
    let I : Env → Prop := fun G => ∃ j, j ≤ i ∧ G.get ilB = some (BitVec.ofNat 64 j) ∧
      G.get ilX = some ws[i] ∧ G.get ilA = some (BitVec.ofNat 64 i) ∧
      (∀ y, y ∉ distMods → G.get y = Γ.get y) ∧ (∀ b (hb : b < j) (hbl : b < ws.length), ws[i] ≠ ws[b])
    have hI0 : I G2 := ⟨0, Nat.zero_le _, by simp [G2, G1, Env.get_cons, show ilB ≠ ilX by decide], by simp [G2, Env.get_cons],
      by rw [Env.get_cons, ite_eq_right (by decide)]; exact g1A,
      fun y hy => by
        simp only [distMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        rw [Env.get_cons, ite_eq_right hy.2.2.1, Env.get_cons, ite_eq_right hy.2.1]
        exact hpk y (by simp [distMods]; exact hy),
      fun b hb => absurd hb (by omega)⟩
    refine step_seq (step_whileE (C := C) (s := s) (D := D) _ _ I
      (fun G => I G ∧ G.get ilB = some (BitVec.ofNat 64 i)) G2 hI0 ?_) ?_
    · intro G ⟨j, hj, hgB, hgX, hgA, hgk, hgd⟩
      have gCB' : G.get ilCB = some (cellA C cb) := by rw [hgk ilCB (by decide)]; exact hCB
      refine ⟨_, sev_lower_nat _ ilB ilA j i hgB hgA (by omega) (by omega), fun hw0 => ?_, fun hw1 => ?_⟩
      · have : j = i := by have := bw_eq0 hw0; omega
        subst this; exact ⟨⟨j, hj, hgB, hgX, hgA, hgk, hgd⟩, hgB⟩
      · have hji : j < i := bw_ne0 hw1
        refine step_seq (step_heapLoadI ilY (slotE ilCB ilB 1) (cb + 1 + j) (hlenH j (by omega))
          (hD ilY (by simp [distMods])) (sev_slot G C ilCB ilB cb j 1 gCB' hgB (by omega))) ?_
        rw [show C.H[cb + 1 + j]'(hlenH j (by omega)) = ws[j]'(by omega) by
          have := hcell j (by omega); rw [List.getElem?_eq_getElem (hlenH j (by omega))] at this
          exact Option.some.inj this]
        have hjl : j < ws.length := by omega
        let G3 : Env := (ilY, ws[j]) :: G
        have h3X : G3.get ilX = some ws[i] := by rw [Env.get_cons, ite_eq_right (by decide)]; exact hgX
        have h3B : G3.get ilB = some (BitVec.ofNat 64 j) := by rw [Env.get_cons, ite_eq_right (by decide)]; exact hgB
        refine step_seq (step_ifI (.cmp .equal (vv ilX) (vv ilY)) (bw (ws[i] = ws[j])) (by
            have h3Y : G3.get ilY = some ws[j] := by simp [G3, Env.get_cons]
            simp only [sev, vv]; rw [h3X, h3Y]
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
            congr 1; simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw]
            by_cases h : ws[i] = ws[j] <;> simp [h]) (fun _ => step_hangI)
          (fun hne => step_mono (Q' := fun t => ¬ (ws[i] = ws[j]) ∧ Inv C s G3 [] D t) step_skipI (fun t ht => ht)
            (fun t ht => ⟨bw_eq0 hne, ht⟩))) ?_
        intro t ⟨hne, ht⟩
        rcases step_assignI (C := C) (Γ := G3) ilB (.op .add [vv ilB, .const 1]) (BitVec.ofNat 64 (j + 1))
          (hD ilB (by simp [distMods])) (sev_succ G3 ilB j h3B) t ht with hs | ⟨hn', hq⟩
        · exact Or.inl hs
        · refine Or.inr ⟨hn', _, ⟨j + 1, by omega, by simp [Env.get_cons],
            by rw [Env.get_cons, ite_eq_right (by decide)]; exact h3X,
            by rw [Env.get_cons, ite_eq_right (by decide), Env.get_cons, ite_eq_right (by decide)]; exact hgA,
            fun y hy => ?_, fun b hb => ?_⟩, hq⟩
          · simp only [distMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
            rw [Env.get_cons, ite_eq_right hy.2.1, Env.get_cons, ite_eq_right hy.2.2.2]; exact hgk y (by
              simp [distMods]; exact hy)
          · intro hbl
            by_cases e : b = j
            · subst e; exact hne
            · exact hgd b (by omega) _
    · intro t ⟨G, ⟨⟨j, hj, hgB, hgX, hgA, hgk, hgd⟩, hgB'⟩, ht⟩
      have hji : j = i := by
        rw [hgB] at hgB'; have := congrArg BitVec.toNat (Option.some.inj hgB'); simp at this; omega
      subst hji
      rcases step_assignI (C := C) (Γ := G) ilA (.op .add [vv ilA, .const 1]) (BitVec.ofNat 64 (j + 1))
        (hD ilA (by simp [distMods])) (sev_succ G ilA j hgA) t ht with hs | ⟨hn', hq⟩
      · exact Or.inl hs
      · refine Or.inr ⟨hn', ⟨C, s, _, m⟩, ⟨rfl, rfl, rfl, j + 1, by omega, by simp [Env.get_cons],
          fun y hy => ?_, fun a b ha hb hal => ?_⟩, by show m s = p.m s; rw [hpm], hq⟩
        · rw [Env.get_cons, ite_eq_right (fun e => hy (by rw [e]; simp [distMods]))]; exact hgk y hy
        · by_cases e : a = j
          · subst e; exact hgd b hb _
          · exact hpd a b (by omega) hb _

end ConPanqueque.Front
