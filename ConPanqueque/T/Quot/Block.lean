import ConPanqueque.T.Quot.PinGen

/-!
# The pinned quotient block, interned with one slot's handles kept

`quotSlotP C k`: the block's literals before slot `k`, the slot by `genPinCI` (its handles kept), the rest.
It refines the block's plain interning (`plainCIList`), the slot's handles those of the answer's slot `k`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.Start ConPanqueque.T.Lit ConPanqueque.Logic.PlainIntern

/-- A pin's constant (not a recursor), its handles kept; a constructor's former in `qX`. -/
def genPinCI (C : Ctx) : ConLeche.ConstantInfo → ProgHOL 64 → ProgHOL 64
  | .indInfo v c, rest => genPinCV C v (genNames C c.all (genNames C c.ctors rest))
  | .ctorInfo v _ _ T, rest => genPinCV C v (nameP C ((strComps T).getD []) (.seq (.assign .local qX (vv vPn)) rest))
  | .axiomInfo v, rest => genPinCV C v rest
  | _, _ => hang

/-- The pinned quotient block. -/
abbrev quotBasis : List ConLeche.ConstantInfo := ConLeche.BasisKind.decls .quotK

/-- The block, slot `k`'s handles kept. -/
def quotSlotP (C : Ctx) (k : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  genCIList C 0 (quotBasis.take k) (genPinCI C (quotBasis.getD k default)
    (genCIList C 0 (quotBasis.drop (k + 1)) rest))

/-- A pin constant value's handles: name in `qN`, level parameters a block at `qL`, type in `qT`. -/
def PinH (C : Ctx) (Γ : Env) (H : List (BitVec 64)) (v : IConstantVal) : Prop :=
  Γ.get qN = some (Enc.idxW v.name) ∧ (∃ o, Γ.get qL = some (cellA C o) ∧ BlkAt H o (v.levelParams.map Enc.idxW)) ∧
    Γ.get qT = some (Enc.idxW v.type)

/-- A constructor pin's former in `qX`. -/
def PinX (Γ : Env) (r : IConstantInfo) : Prop :=
  ∀ v nP nF T, r = .ctorInfo v nP nF T → Γ.get qX = some (Enc.idxW T)

theorem q_not_gen {x : MlS} (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX) :
    (∀ c j, x ≠ gv c j) ∧ x ≠ vPn ∧ x ≠ vKa := by
  refine ⟨fun c j e => ?_, ?_, ?_⟩
  · have := gv_ne_q c j
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp_all
  · rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide

theorem agreeL_q {Γ Γ' : Env} {d : Nat} (h : AgreeL Γ Γ' d) {x : MlS}
    (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX) : Γ'.get x = Γ.get x :=
  have hq := q_not_gen hx
  h x (fun c j _ => hq.1 c j) hq.2.1 hq.2.2

theorem pinH_mono {C : Ctx} {Γ Γ' : Env} {H H' : List (BitVec 64)} {v : IConstantVal} (h : PinH C Γ H v)
    (hq : ∀ x, (x = qN ∨ x = qL ∨ x = qT) → Γ'.get x = Γ.get x) (hp : H <+: H') : PinH C Γ' H' v := by
  obtain ⟨h1, ⟨o, h2, h3⟩, h4⟩ := h
  exact ⟨by rw [hq qN (Or.inl rfl)]; exact h1, ⟨o, by rw [hq qL (Or.inr (Or.inl rfl))]; exact h2, blkAt_mono h3 hp⟩,
    by rw [hq qT (Or.inr (Or.inr rfl))]; exact h4⟩

theorem pinX_mono {Γ Γ' : Env} {r : IConstantInfo} (h : PinX Γ r) (hq : Γ'.get qX = Γ.get qX) : PinX Γ' r :=
  fun v nP nF T e => by rw [hq]; exact h v nP nF T e

theorem pinH_L {C : Ctx} {Γ Γ' : Env} {H H' : List (BitVec 64)} {v : IConstantVal} {r : IConstantInfo} {d : Nat}
    (h : PinH C Γ H v ∧ PinX Γ r) (ha : AgreeL Γ Γ' d) (hp : H <+: H') : PinH C Γ' H' v ∧ PinX Γ' r :=
  ⟨pinH_mono h.1 (fun x hx => agreeL_q ha (by rcases hx with h | h | h <;> simp [h])) hp,
    pinX_mono h.2 (agreeL_q ha (by simp))⟩

theorem plainCIList_append : ∀ (a b : List ConLeche.ConstantInfo),
    plainCIList (a ++ b) = (do let x ← plainCIList a; let y ← plainCIList b; pure (x ++ y))
  | [], b => by simp [plainCIList]
  | c :: a, b => by
    simp only [List.cons_append, plainCIList, bind_assoc, plainCIList_append a b, pure_bind, List.cons_append]

theorem plainCIList_len : ∀ (a : List ConLeche.ConstantInfo) (s s' : AState) (x : List IConstantInfo),
    plainCIList a s = .ok (x, s') → x.length = a.length
  | [], s, s', x, h => by simp only [plainCIList] at h; obtain ⟨rfl, -⟩ := AM.pure_ok h; rfl
  | c :: a, s, s', x, h => by
    simp only [plainCIList] at h
    obtain ⟨y, s1, -, h2⟩ := AM.bind_ok h
    obtain ⟨ys, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, -⟩ := AM.pure_ok h4
    simp [plainCIList_len a s1 s2 ys h3]

section
variable {σ : Type}

/-- **`genPinCI`**: a pin constant (not a recursor) interned (`plainCI`), its handles kept. -/
theorem genPinCI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX], x ∈ D)
    (c : ConLeche.ConstantInfo) (hc : CILit 0 12 c)
    (hl : c.toConstantVal.levelParams.length = 1 ∨ c.toConstantVal.levelParams.length = 2)
    (hnr : ∀ v mI rP isK rs, c ≠ .recInfo v mI rP isK rs) (hnd : ∀ v e h, c ≠ .defnInfo v e h)
    (hnt : ∀ v, c ≠ .thmInfo v)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H', H0 <+: H' → AgreeQ Γ Γ' → plainCI c s = .ok (r, s') →
      PinH C Γ' H' r.toConstantVal → PinX Γ' r → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genPinCI C c rest) s (plainCI c >>= k) R := by
  cases c with
  | axiomInfo v =>
    simp only [genPinCI, plainCI, bind_assoc]
    refine genPinCV_spec ra G hq v hc hl H0 rest Γ M s (fun r s' Γ' H' o hp ag hr h1 h2 h3 h4 => ?_)
    simp only [pure_bind]
    exact hk _ s' Γ' H' hp ag (bind_ok_of hr rfl) ⟨h1, ⟨o, h2, h3⟩, h4⟩ (fun _ _ _ _ e => by cases e)
  | indInfo v caps =>
    simp only [genPinCI, plainCI, bind_assoc]
    refine genPinCV_spec ra G hq v hc.1 hl H0 _ Γ M s (fun r1 s1 Γ1 H1 o hp1 ag1 hr1 h1 h2 h3 h4 => ?_)
    unfold ConRon.Arena.Frontend.internCaps
    simp only [bind_assoc]
    refine genNames_spec ra G 0 _ H1 _ Γ1 [] s1 hc.2.1 (fun hs s2 Γ2 H2 hp2 ag2 hr2 => ?_)
    refine genNames_spec ra G 0 _ H2 rest Γ2 [] s2 hc.2.2 (fun hs' s3 Γ3 H3 hp3 ag3 hr3 => ?_)
    simp only [pure_bind]
    have hP := pinH_L (pinH_L (r := .axiomInfo r1) ⟨⟨h1, ⟨o, h2, h3⟩, h4⟩, fun _ _ _ _ e => by cases e⟩ ag2 hp2) ag3 hp3
    exact hk _ s3 Γ3 H3 (hp1.trans (hp2.trans hp3))
      (agreeQ_trans ag1 (agreeQ_trans (agreeQ_of_L (agreeL_mono ag2 (Nat.zero_le _)))
        (agreeQ_of_L (agreeL_mono ag3 (Nat.zero_le _)))))
      (bind_ok_of hr1 (bind_ok_of (A := ConRon.Arena.Frontend.internCaps caps)
        (by unfold ConRon.Arena.Frontend.internCaps; exact bind_ok_of hr2 (bind_ok_of hr3 rfl)) rfl))
      hP.1 (fun _ _ _ _ e => by cases e)
  | ctorInfo v nP nF T =>
    simp only [genPinCI, plainCI, bind_assoc]
    refine genPinCV_spec ra G hq v hc.1 hl H0 _ Γ M s (fun r1 s1 Γ1 H1 o hp1 ag1 hr1 h1 h2 h3 h4 => ?_)
    refine name_stepP ra G T hc.2 H1 _ Γ1 [] s1 (fun h s2 Γ2 hf2 hv2 hr2 => ?_)
    refine specR_assignI qX (vv vPn) (Enc.idxW h) (hq qX (by simp)) (by simp only [sev_vv, hv2]) ?_
    simp only [pure_bind]
    have g : ∀ x, (x = qN ∨ x = qL ∨ x = qT) → Env.get ((qX, Enc.idxW h) :: Γ2) x = Γ1.get x := fun x hx => by
      have hq' := q_not_gen (x := x) (by rcases hx with h | h | h <;> simp [h])
      rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by rcases hx with rfl | rfl | rfl <;> decide)),
        hf2 x hq'.2.1 hq'.2.2]
    refine hk _ s2 _ H1 hp1 (agreeQ_trans ag1 (agreeQ_trans (fun y _ h1 h2 _ _ _ _ _ => hf2 y h1 h2)
      (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _))) (bind_ok_of hr1 (bind_ok_of hr2 rfl))
      (pinH_mono ⟨h1, ⟨o, h2, h3⟩, h4⟩ g (List.prefix_refl _)) (fun _ _ _ T' e => ?_)
    cases e; simp [Env.get_cons]
  | recInfo v mI rP isK rs => exact absurd rfl (hnr v mI rP isK rs)
  | defnInfo v e h => exact absurd rfl (hnd v e h)
  | thmInfo v => exact absurd rfl (hnt v)

/-- **The pinned block, slot `k`'s handles kept** (slot `k` not a recursor). -/
theorem quotSlot_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX], x ∈ D) (k : Nat) (hk5 : k < 5)
    (hnr : ∀ v mI rP isK rs, quotBasis.getD k default ≠ .recInfo v mI rP isK rs)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {kk : List IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ blk s' Γ' H', H0 <+: H' → AgreeQ Γ Γ' → plainCIList quotBasis s = .ok (blk, s') →
      PinH C Γ' H' (blk.getD k default).toConstantVal → PinX Γ' (blk.getD k default) →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (kk blk) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (quotSlotP C k rest) s (plainCIList quotBasis >>= kk) R := by
  have hsplit : quotBasis = quotBasis.take k ++ quotBasis.getD k default :: quotBasis.drop (k + 1) := by
    have hlt : k < quotBasis.length := by simp [quotBasis, ConLeche.BasisKind.decls, ConLeche.quotBasis]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [← List.drop_eq_getElem_cons hlt]; exact (List.take_append_drop k _).symm
  have hlit : ∀ c ∈ quotBasis, CILit 0 12 c := basis_lits .quotK
  have hmem : ∀ c ∈ quotBasis.take k, c ∈ quotBasis := fun c h => List.mem_of_mem_take h
  have hmem2 : ∀ c ∈ quotBasis.drop (k + 1), c ∈ quotBasis := fun c h => List.mem_of_mem_drop h
  have hck : quotBasis.getD k default ∈ quotBasis := by
    have hlt : k < quotBasis.length := by simp [quotBasis, ConLeche.BasisKind.decls, ConLeche.quotBasis]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem _
  have e : (plainCIList quotBasis >>= kk) = (plainCIList (quotBasis.take k) >>= fun a =>
      plainCI (quotBasis.getD k default) >>= fun x => plainCIList (quotBasis.drop (k + 1)) >>= fun b =>
        kk (a ++ x :: b)) := by
    conv => lhs; rw [hsplit]
    rw [plainCIList_append]
    simp only [plainCIList, bind_assoc, pure_bind]
  rw [e]
  unfold quotSlotP
  refine genCIList_spec ra G 0 _ H0 _ Γ M s (fun c h => hlit c (hmem c h)) (fun a s1 Γ1 H1 hp1 ag1 hr1 => ?_)
  refine genPinCI_spec ra G hq _ (hlit _ hck) ?_ hnr ?_ ?_ H1 _ Γ1 [] s1 (fun x s2 Γ2 H2 hp2 ag2 hr2 hP2 hX2 => ?_)
  · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v e h he
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> cases he
  · intro v he
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> cases he
  refine genCIList_spec ra G 0 _ H2 rest Γ2 [] s2 (fun c h => hlit c (hmem2 c h))
    (fun b s3 Γ3 H3 hp3 ag3 hr3 => ?_)
  have hla := plainCIList_len _ _ _ _ hr1
  have hget : (a ++ x :: b).getD k default = x := by
    have hk' : k = a.length := by
      rw [hla, List.length_take]; simp [quotBasis, ConLeche.BasisKind.decls, ConLeche.quotBasis]; omega
    subst hk'
    simp
  have hP3 := pinH_L ⟨hP2, hX2⟩ ag3 hp3
  refine hk _ s3 Γ3 H3 (hp1.trans (hp2.trans hp3)) (agreeQ_trans (agreeQ_of_L ag1) (agreeQ_trans ag2 (agreeQ_of_L ag3)))
    ?_ (by rw [hget]; exact hP3.1) (by rw [hget]; exact hP3.2)
  conv => lhs; rw [hsplit]
  rw [plainCIList_append]
  simp only [plainCIList, bind_assoc, pure_bind]
  exact bind_ok_of hr1 (bind_ok_of hr2 (bind_ok_of hr3 rfl))

end

end ConPanqueque.T.Quot
