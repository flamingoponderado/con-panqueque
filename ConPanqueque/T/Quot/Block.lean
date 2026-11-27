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

/-- A recursor pin's one rule (firing at one level), its handles kept: constructor in `qX`, level in `qU`,
right-hand side in `qW`. -/
def genPinRule (C : Ctx) : ConLeche.RecRule → ProgHOL 64 → ProgHOL 64
  | ⟨c, _, .levels [u], rhs⟩, rest => nameP C ((strComps c).getD []) (.seq (.assign .local qX (vv vPn))
      (genL C 0 u (.seq (.assign .local qU (vv (gl 0))) (genE C 0 rhs (.seq (.assign .local qW (vv (ge 0))) rest)))))
  | _, _ => hang

/-- A pin's constant, its handles kept; a constructor's former in `qX`; a recursor's one rule's handles. -/
def genPinCI (C : Ctx) : ConLeche.ConstantInfo → ProgHOL 64 → ProgHOL 64
  | .indInfo v c, rest => genPinCV C v (genNames C c.all (genNames C c.ctors rest))
  | .ctorInfo v _ _ T, rest => genPinCV C v (nameP C ((strComps T).getD []) (.seq (.assign .local qX (vv vPn)) rest))
  | .axiomInfo v, rest => genPinCV C v rest
  | .recInfo v _ _ _ [rl], rest => genPinCV C v (genPinRule C rl rest)
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

/-- A constructor pin's former in `qX`; a recursor pin's one rule's handles in `qX`, `qU`, `qW`. -/
def PinX (Γ : Env) (r : IConstantInfo) : Prop :=
  (∀ v nP nF T, r = .ctorInfo v nP nF T → Γ.get qX = some (Enc.idxW T)) ∧
  (∀ v mI rP isK rs, r = .recInfo v mI rP isK rs → ∃ rl u, rs = [rl] ∧ rl.fire = .levels [u] ∧
    Γ.get qX = some (Enc.idxW rl.ctor) ∧ Γ.get qU = some (Enc.idxW u) ∧ Γ.get qW = some (Enc.idxW rl.rhs))

theorem q_not_gen {x : MlS} (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) :
    (∀ c j, x ≠ gv c j) ∧ x ≠ vPn ∧ x ≠ vKa := by
  refine ⟨fun c j e => ?_, ?_, ?_⟩
  · have := gv_ne_q c j
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem agreeL_q {Γ Γ' : Env} {d : Nat} (h : AgreeL Γ Γ' d) {x : MlS}
    (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) : Γ'.get x = Γ.get x :=
  have hq := q_not_gen hx
  h x (fun c j _ => hq.1 c j) hq.2.1 hq.2.2

theorem pinH_mono {C : Ctx} {Γ Γ' : Env} {H H' : List (BitVec 64)} {v : IConstantVal} (h : PinH C Γ H v)
    (hq : ∀ x, (x = qN ∨ x = qL ∨ x = qT) → Γ'.get x = Γ.get x) (hp : H <+: H') : PinH C Γ' H' v := by
  obtain ⟨h1, ⟨o, h2, h3⟩, h4⟩ := h
  exact ⟨by rw [hq qN (Or.inl rfl)]; exact h1, ⟨o, by rw [hq qL (Or.inr (Or.inl rfl))]; exact h2, blkAt_mono h3 hp⟩,
    by rw [hq qT (Or.inr (Or.inr rfl))]; exact h4⟩

theorem pinX_mono {Γ Γ' : Env} {r : IConstantInfo} (h : PinX Γ r)
    (hq : ∀ x, (x = qX ∨ x = qU ∨ x = qW) → Γ'.get x = Γ.get x) : PinX Γ' r :=
  ⟨fun v nP nF T e => by rw [hq qX (Or.inl rfl)]; exact h.1 v nP nF T e,
   fun v mI rP isK rs e => by
    obtain ⟨rl, u, h1, h2, h3, h4, h5⟩ := h.2 v mI rP isK rs e
    exact ⟨rl, u, h1, h2, by rw [hq qX (Or.inl rfl)]; exact h3, by rw [hq qU (Or.inr (Or.inl rfl))]; exact h4,
      by rw [hq qW (Or.inr (Or.inr rfl))]; exact h5⟩⟩

theorem pinH_L {C : Ctx} {Γ Γ' : Env} {H H' : List (BitVec 64)} {v : IConstantVal} {r : IConstantInfo} {d : Nat}
    (h : PinH C Γ H v ∧ PinX Γ r) (ha : AgreeL Γ Γ' d) (hp : H <+: H') : PinH C Γ' H' v ∧ PinX Γ' r :=
  ⟨pinH_mono h.1 (fun x hx => agreeL_q ha (by rcases hx with h | h | h <;> simp [h])) hp,
    pinX_mono h.2 (fun x hx => agreeL_q ha (by rcases hx with h | h | h <;> simp [h]))⟩

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

/-- **`genPinCI`**: a pin constant interned (`plainCI`), its handles kept. -/
theorem genPinCI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D)
    (c : ConLeche.ConstantInfo) (hc : CILit 0 12 c)
    (hl : c.toConstantVal.levelParams.length = 1 ∨ c.toConstantVal.levelParams.length = 2)
    (hrs : ∀ v mI rP isK rs, c = .recInfo v mI rP isK rs → ∃ rl u, rs = [rl] ∧ rl.fire = .levels [u])
    (hnd : ∀ v e h, c ≠ .defnInfo v e h) (hnt : ∀ v, c ≠ .thmInfo v)
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
    exact hk _ s' Γ' H' hp ag (bind_ok_of hr rfl) ⟨h1, ⟨o, h2, h3⟩, h4⟩
      ⟨fun _ _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e)⟩
  | indInfo v caps =>
    simp only [genPinCI, plainCI, bind_assoc]
    refine genPinCV_spec ra G hq v hc.1 hl H0 _ Γ M s (fun r1 s1 Γ1 H1 o hp1 ag1 hr1 h1 h2 h3 h4 => ?_)
    unfold ConRon.Arena.Frontend.internCaps
    simp only [bind_assoc]
    refine genNames_spec ra G 0 _ H1 _ Γ1 [] s1 hc.2.1 (fun hs s2 Γ2 H2 hp2 ag2 hr2 => ?_)
    refine genNames_spec ra G 0 _ H2 rest Γ2 [] s2 hc.2.2 (fun hs' s3 Γ3 H3 hp3 ag3 hr3 => ?_)
    simp only [pure_bind]
    have hP := pinH_L (pinH_L (r := .axiomInfo r1) ⟨⟨h1, ⟨o, h2, h3⟩, h4⟩,
      ⟨fun _ _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e)⟩⟩ ag2 hp2) ag3 hp3
    exact hk _ s3 Γ3 H3 (hp1.trans (hp2.trans hp3))
      (agreeQ_trans ag1 (agreeQ_trans (agreeQ_of_L (agreeL_mono ag2 (Nat.zero_le _)))
        (agreeQ_of_L (agreeL_mono ag3 (Nat.zero_le _)))))
      (bind_ok_of hr1 (bind_ok_of (A := ConRon.Arena.Frontend.internCaps caps)
        (by unfold ConRon.Arena.Frontend.internCaps; exact bind_ok_of hr2 (bind_ok_of hr3 rfl)) rfl))
      hP.1 ⟨fun _ _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e)⟩
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
    refine hk _ s2 _ H1 hp1 (agreeQ_trans ag1 (agreeQ_trans (fun y _ h1 h2 _ _ _ _ _ _ => hf2 y h1 h2)
      (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _))) (bind_ok_of hr1 (bind_ok_of hr2 rfl))
      (pinH_mono ⟨h1, ⟨o, h2, h3⟩, h4⟩ g (List.prefix_refl _)) ⟨fun _ _ _ T' e => ?_, fun _ _ _ _ _ e => by cases e⟩
    cases e; simp [Env.get_cons]
  | recInfo v mI rP isK rs =>
    obtain ⟨rl, u, rfl, hfire⟩ := hrs v mI rP isK rs rfl
    obtain ⟨hcv, hrl⟩ := hc
    obtain ⟨hcn, hfl, hre, hrd⟩ := hrl rl (by simp)
    obtain ⟨cn, nf, fire, rhs⟩ := rl
    simp only at hfire; subst hfire
    simp only [FireLit, List.mem_singleton, forall_eq] at hfl
    obtain ⟨hu, hud⟩ := hfl
    simp only [genPinCI, genPinRule, plainCI, plainRules, plainRule, plainFire, internLevelList, bind_assoc]
    refine genPinCV_spec ra G hq v hcv hl H0 _ Γ M s (fun r1 s1 Γ1 H1 o hp1 ag1 hr1 h1 h2 h3 h4 => ?_)
    refine name_stepP ra G cn hcn H1 _ Γ1 [] s1 (fun hc s2 Γ2 hf2 hv2 hr2 => ?_)
    refine specR_assignI qX (vv vPn) (Enc.idxW hc) (hq qX (by simp)) (by simp only [sev_vv, hv2]) ?_
    rw [← genL_ctxH C H1]
    refine genL_spec ra (ctxH C H1) (ctxOK_H G.hok H1) (by ctx_tr G.hf) G.hA (by ctx_tr G.hc.l) D G.hPn G.hKa u 0 _ _
      [] s2 hu (fun j h1 h2 => G.hD _ (by decide) _ (by omega)) (fun hu' s3 Γ3 ag3 hv3 hr3 => ?_)
    refine specR_assignI qU (vv (gl 0)) (Enc.idxW hu') (hq qU (by simp)) (by simp only [sev_vv, hv3]) ?_
    simp only [pure_bind]
    refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa 12 G.hD _ 0 H1 _ _ [] s3 hre (by omega)
      (fun hr s4 Γ4 H4 hp4 ag4 hv4 hr4 => ?_)
    refine specR_assignI qW (vv (ge 0)) (Enc.idxW hr) (hq qW (by simp)) (by simp only [sev_vv, hv4]) ?_
    try simp only [pure_bind]
    -- the frame
    have fq : ∀ x, (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) →
        ∀ (Γa Γb : Env) (d : Nat), AgreeL Γa Γb d → Γb.get x = Γa.get x := fun x hx Γa Γb d h => agreeL_q h hx
    have gx : ∀ x, (x = qN ∨ x = qL ∨ x = qT) →
        Env.get ((qW, Enc.idxW hr) :: Γ4) x = Γ1.get x := fun x hx => by
      have hq' := q_not_gen (x := x) (by rcases hx with h | h | h <;> simp [h])
      rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by rcases hx with rfl | rfl | rfl <;> decide)),
        fq x (by rcases hx with h | h | h <;> simp [h]) _ _ 0 ag4, Env.get_cons,
        ite_eq_right_iff.mpr (fun e => absurd e (by rcases hx with rfl | rfl | rfl <;> decide)),
        fq x (by rcases hx with h | h | h <;> simp [h]) _ _ 0 ag3, Env.get_cons,
        ite_eq_right_iff.mpr (fun e => absurd e (by rcases hx with rfl | rfl | rfl <;> decide)),
        hf2 x hq'.2.1 hq'.2.2]
    refine hk _ s4 _ H4 (hp1.trans hp4) ?_ ?_ (pinH_mono ⟨h1, ⟨o, h2, h3⟩, h4⟩ gx hp4)
      ⟨fun _ _ _ _ e => (by cases e), fun v' mI' rP' isK' rs' e => ?_⟩
    · refine agreeQ_trans ag1 (agreeQ_trans (fun y _ h1 h2 _ _ _ _ _ _ => hf2 y h1 h2)
        (agreeQ_trans (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _)
        (agreeQ_trans (agreeQ_of_L ag3) (agreeQ_trans (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _)
        (agreeQ_trans (agreeQ_of_L ag4) (agreeQ_cons (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _))))))
    · simp only [plainCI, plainRules, plainRule, plainFire, internLevelList, bind_assoc, pure_bind]
      exact bind_ok_of hr1 (bind_ok_of hr2 (bind_ok_of hr3 (bind_ok_of hr4 rfl)))
    · cases e
      refine ⟨_, hu', rfl, rfl, ?_, ?_, by simp [Env.get_cons]⟩
      · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)),
          fq qX (by simp) _ _ 0 ag4, Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)),
          fq qX (by simp) _ _ 0 ag3]
        simp [Env.get_cons]
      · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)), fq qU (by simp) _ _ 0 ag4]
        simp [Env.get_cons]
  | defnInfo v e h => exact absurd rfl (hnd v e h)
  | thmInfo v => exact absurd rfl (hnt v)

/-- **The pinned block, slot `k`'s handles kept** (slot `k` not a recursor). -/
theorem quotSlot_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) (k : Nat) (hk5 : k < 5)
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
  refine genPinCI_spec ra G hq _ (hlit _ hck) ?_ ?_ ?_ ?_ H1 _ Γ1 [] s1 (fun x s2 Γ2 H2 hp2 ag2 hr2 hP2 hX2 => ?_)
  · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v mI rP isK rs he
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> cases he <;> exact ⟨_, _, rfl, rfl⟩
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
