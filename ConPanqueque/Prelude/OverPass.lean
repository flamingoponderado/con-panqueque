import ConPanqueque.Prelude.OverStep

/-! # The override pass

The registry at `kRB` holds the stream's records `Q` (the first `nq = kNQ`) and then the prelude's
`P`.  `overP`:

1. copies `P`'s record pointers into a second registry at `kRA + 8·4096` (checking every prelude
   record has a key);
2. walks `Q`: a block hangs; a value record whose name is some prelude record's key must be that
   record (`recEqP`) and the only stream record of that name (`scanP`), and is dropped; any other
   record is appended to the second registry;
3. points `kRB` at the second registry: `P` followed by the kept stream records.

`overP_spec`: the continuation runs with the second registry (`DeclsRel`) and the facts the bridge
needs (`OverW`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConPanqueque.V

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

/-- The stream's record count, saved before the prelude's parse. -/
def kNQ := ofString "knq"

/-- Hang if a stream record before index `ovK` has the name `ovNm`. -/
def scanP : ProgHOL 64 :=
  .seq (.assign .local ovI (.const 0))
  (.while (.cmp .lower (vv ovI) (vv ovK))
    (.seq (.assign .local ovX (.load .one (slotE kRB ovI 1)))
    (.seq (.assign .local ovY (.load .one (offE ovX 1)))
    (.seq (.ite (.cmp .equal (vv ovY) (vv ovNm)) hang .skip)
      (.assign .local ovI (.op .add [vv ovI, .const 1]))))))

/-- One prelude record against the stream record at `ovD`. -/
def innerBody : ProgHOL 64 :=
  .seq (.assign .local ovT (.op .add [vv kNQ, vv ovJ]))
  (.seq (.assign .local ovP (.load .one (slotE kRB ovT 1)))
  (.seq keyP
  (.seq (.ite (.cmp .equal (vv ovKey) (vv ovNm))
           (.seq scanP (.seq recEqP (.assign .local ovDrop (.const 1))))
           .skip)
    (.assign .local ovJ (.op .add [vv ovJ, .const 1])))))

/-- One stream record. -/
def streamBody : ProgHOL 64 :=
  .seq (.assign .local ovD (.load .one (slotE kRB ovK 1)))
  (.seq (.assign .local ovT (.load .one (vv ovD)))
  (.seq (.ite (.cmp .equal (vv ovT) (.const 4)) hang .skip)
  (.seq (.assign .local ovNm (.load .one (offE ovD 1)))
  (.seq (.assign .local ovDrop (.const 0))
  (.seq (.assign .local ovJ (.const 0))
  (.seq (.while (.cmp .lower (vv ovJ) (vv ovNP)) innerBody)
  (.seq (.ite (.cmp .equal (vv ovDrop) (.const 0))
           (.seq (.assign .local ovT (.op .add [vv ovNP, vv ovW]))
           (.seq (.store (slotE ovR2 ovT 1) (vv ovD))
             (.assign .local ovW (.op .add [vv ovW, .const 1]))))
           .skip)
    (.assign .local ovK (.op .add [vv ovK, .const 1])))))))))

/-- One prelude record copied (its key checked). -/
def copyBody : ProgHOL 64 :=
  .seq (.assign .local ovT (.op .add [vv kNQ, vv ovJ]))
  (.seq (.assign .local ovP (.load .one (slotE kRB ovT 1)))
  (.seq keyP
  (.seq (.store (slotE ovR2 ovJ 1) (vv ovP))
    (.assign .local ovJ (.op .add [vv ovJ, .const 1])))))

/-- **The override pass.** -/
def overP (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local ovN (.load .one (vv kRB)))
  (.seq (.assign .local ovNP (.op .sub [vv ovN, vv kNQ]))
  (.seq (.assign .local ovR2 (offE kRA 4096))
  (.seq (.assign .local ovJ (.const 0))
  (.seq (.while (.cmp .lower (vv ovJ) (vv ovNP)) copyBody)
  (.seq (.assign .local ovK (.const 0))
  (.seq (.assign .local ovW (.const 0))
  (.seq (.while (.cmp .lower (vv ovK) (vv kNQ)) streamBody)
  (.seq (.assign .local ovT (.op .add [vv ovNP, vv ovW]))
  (.seq (.store (vv ovR2) (vv ovT))
  (.seq (.assign .local kRB (vv ovR2)) rest))))))))))

/-! ## What the pass establishes -/

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

theorem take_filter_eq {α : Type} [Inhabited α] (a : Array α) (p : α → Bool) : ∀ n, n ≤ a.size →
    (a.toList.take n).filter p = ((List.range n).filter (fun k => p a[k]!)).map (fun k => a[k]!)
  | 0, _ => by simp
  | n + 1, hn => by
    rw [List.take_succ, List.range_succ, List.filter_append, List.filter_append, List.map_append,
      take_filter_eq a p n (by omega)]
    congr 1
    rw [List.getElem?_eq_getElem (by simp; omega), Option.toList_some]
    have e : a[n]! = a[n] := getElem!_pos a n (by omega)
    simp only [List.filter_cons, List.filter_nil, e, Array.getElem_toList]
    split <;> simp [e]

theorem recEnc_ctxH {C : Ctx} {F : Nat} {H H' : List (BitVec 64)} {o : Nat} {d : IDeclaration}
    (h : RecEnc C F H o d) : RecEnc (ctxH C H') F H o d := h

@[simp] theorem cellA_ctxH (C : Ctx) (H : List (BitVec 64)) (j : Nat) : cellA (ctxH C H) j = cellA C j := rfl

/-- `scanP`: it returns only if no stream record before `k` has the name word `nm`. -/
theorem scanP_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F rb capD : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hcap : 8 * (rb + 1 + capD) < 2 ^ 64) (hRB : Γ.get kRB = some (cellA C rb)) (k : Nat) (hk : k ≤ decls.size)
    (hval : ∀ k' (hk' : k' < k), isVal (decls[k']'(by omega)) = true)
    (hK : Γ.get ovK = some (BitVec.ofNat 64 k)) (nm : NIdx) (hN : Γ.get ovNm = some (Enc.idxW nm)) :
    Step (Inv (σ := σ) C s Γ [] D) scanP (fun t => (∀ k' (hk' : k' < k), valName (decls[k']'(by omega)) ≠ nm) ∧
      ∃ Γ', (∀ y, y ∉ [ovI, ovX, ovY] → Γ'.get y = Γ.get y) ∧ Inv C s Γ' [] D t) := by
  have hle : decls.size ≤ capD := hdr.2.1
  refine step_seq (step_assignI ovI (.const 0) 0 (hD _ (by simp [ovVars])) rfl) ?_
  refine fun t ht => (step_whileCE (s := s) (D := D) _ _
    (fun C' Γ' => C' = C ∧ ∃ i, ∃ hik : i ≤ k, Γ'.get ovI = some (BitVec.ofNat 64 i) ∧
      (∀ k' (hk' : k' < i), valName (decls[k']'(by omega)) ≠ nm) ∧ (∀ y, y ∉ [ovI, ovX, ovY] → Γ'.get y = Γ.get y))
    (fun C' Γ' => C' = C ∧ (∀ k' (hk' : k' < k), valName (decls[k']'(by omega)) ≠ nm) ∧
      (∀ y, y ∉ [ovI, ovX, ovY] → Γ'.get y = Γ.get y))
    C _ ⟨rfl, 0, Nat.zero_le _, by simp (config := {decide := true}) [T.Env.get_cons], fun k' h => absurd h (by omega), fun y hy => by
      have : y ≠ ovI := fun e => hy (by simp [e])
      simp (config := {decide := true}) [T.Env.get_cons, this]⟩ ?_ t ht).imp id (fun ⟨hn, C', Γ', ⟨hC, hall, hag⟩, hq⟩ => by
        subst C'; exact ⟨hn, hall, Γ', hag, hq⟩)
  intro C' Γ' ⟨hC, i, hi, gI, hdone, hag⟩
  subst C'
  have gK : Γ'.get ovK = some (BitVec.ofNat 64 k) := by rw [hag _ (by decide)]; exact hK
  refine ⟨bw (i < k), sev_lowerV _ _ _ _ _ gI gK (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
  · have : i = k := by have := bw_eq0' h0; omega
    subst this; exact ⟨rfl, hdone, hag⟩
  · have hlt := bw_ne0' h1
    obtain ⟨o, ho, hro⟩ := regAt hdr i (by omega)
    refine step_seq (step_loadW ovX (slotE kRB ovI 1) _ _ ho (hD _ (by simp [ovVars]))
      (by rw [sev_slot _ C kRB ovI rb i 1 (by rw [hag _ (by decide)]; exact hRB) gI (by omega)])) ?_
    refine step_seq (step_loadW ovY (offE ovX 1) (o + 1) _ (name_of_val hro (hval i hlt)) (hD _ (by simp [ovVars]))
      (sev_off _ C ovX o 1 (by simp (config := {decide := true}) [T.Env.get_cons]))) ?_
    have gN : Γ'.get ovNm = some (Enc.idxW nm) := by rw [hag _ (by decide)]; exact hN
    refine step_seq (Q := fun t => valName decls[i] ≠ nm ∧ _) (step_ifI _ _ (sev_eqv _ ovY ovNm (Enc.idxW (valName decls[i])) (Enc.idxW nm)
      (by simp (config := {decide := true}) [T.Env.get_cons]) (by simp (config := {decide := true}) [T.Env.get_cons, gN])) (fun _ => step_hangI)
      (fun he => fun t ht => (step_skipI t ht).imp id (fun ⟨h1, h2⟩ => ⟨h1, fun e => ite10_eq he (by rw [e]), h2⟩))) ?_
    intro t ⟨hne, ht⟩
    refine (step_assignI ovI (.op .add [vv ovI, .const 1]) _ (hD _ (by simp [ovVars])) (sev_succV _ ovI i
      ((by simp (config := {decide := true}) [T.Env.get_cons, gI]))) t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, i + 1, by omega,
        by simp (config := {decide := true}) [T.Env.get_cons], fun k' hk' => ?_, fun y hy => ?_⟩, hq⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h | rfl
      · exact hdone k' h
      · exact hne
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp (config := {decide := true}) [T.Env.get_cons, hy.1, hy.2.1, hy.2.2]; exact hag y (by simp [hy.1, hy.2.1, hy.2.2])

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

/-- The values the pass keeps fixed. -/
structure OvFix (C : Ctx) (rb nq np r2 : Nat) (Γ : Env) : Prop where
  rb : Γ.get kRB = some (cellA C rb)
  nq : Γ.get kNQ = some (BitVec.ofNat 64 nq)
  np : Γ.get ovNP = some (BitVec.ofNat 64 np)
  r2 : Γ.get ovR2 = some (cellA C r2)

theorem ovFix_agree {C : Ctx} {rb nq np r2 : Nat} {Γ Γ' : Env} (h : OvFix C rb nq np r2 Γ)
    (hag : ∀ y, y = kRB ∨ y = kNQ ∨ y = ovNP ∨ y = ovR2 → Γ'.get y = Γ.get y) : OvFix C rb nq np r2 Γ' :=
  ⟨by rw [hag _ (Or.inl rfl)]; exact h.rb, by rw [hag _ (Or.inr (Or.inl rfl))]; exact h.nq,
    by rw [hag _ (Or.inr (Or.inr (Or.inl rfl)))]; exact h.np, by rw [hag _ (Or.inr (Or.inr (Or.inr rfl)))]; exact h.r2⟩

theorem ovFix_cons {C : Ctx} {rb nq np r2 : Nat} {Γ : Env} (h : OvFix C rb nq np r2 Γ) (x : MlS)
    (hx : x ≠ kRB ∧ x ≠ kNQ ∧ x ≠ ovNP ∧ x ≠ ovR2) (v : BitVec 64) : OvFix C rb nq np r2 ((x, v) :: Γ) :=
  ovFix_agree h (fun y hy => by
    rcases hy with rfl | rfl | rfl | rfl
    · exact get_cons_ne _ _ _ _ (Ne.symm hx.1)
    · exact get_cons_ne _ _ _ _ (Ne.symm hx.2.1)
    · exact get_cons_ne _ _ _ _ (Ne.symm hx.2.2.1)
    · exact get_cons_ne _ _ _ _ (Ne.symm hx.2.2.2))

theorem ovFix_ctxH {C : Ctx} {rb nq np r2 : Nat} {Γ : Env} (h : OvFix C rb nq np r2 Γ) (H : List (BitVec 64)) :
    OvFix (ctxH C H) rb nq np r2 Γ := ⟨h.rb, h.nq, h.np, h.r2⟩

theorem ovFix_of_ctxH {C : Ctx} {H : List (BitVec 64)} {rb nq np r2 : Nat} {Γ : Env}
    (h : OvFix (ctxH C H) rb nq np r2 Γ) : OvFix C rb nq np r2 Γ := ⟨h.rb, h.nq, h.np, h.r2⟩

theorem sev_addV (Γ : Env) (x y : MlS) (a b : Nat) (hx : Γ.get x = some (BitVec.ofNat 64 a))
    (hy : Γ.get y = some (BitVec.ofNat 64 b)) : sev Γ (.op .add [vv x, vv y]) = some (BitVec.ofNat 64 (a + b)) := by
  simp only [sev, vv, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [ConPanqueque.Code.addr_add]

/-- The keys of the first `j` prelude records (the prelude starts at index `nq`). -/
def keysUpTo (decls : Array IDeclaration) (nq j : Nat) : List NIdx :=
  (List.range j).map (fun j' => keyOf decls[nq + j']!)

theorem keysUpTo_succ (decls : Array IDeclaration) (nq j : Nat) :
    keysUpTo decls nq (j + 1) = keysUpTo decls nq j ++ [keyOf decls[nq + j]!] := by
  simp [keysUpTo, List.range_succ]

/-- The registry is unchanged where the pass does not write. -/
theorem declsRel_agree {C : Ctx} {F rb capD a b : Nat} {H H' : List (BitVec 64)} {decls : Array IDeclaration}
    (h : DeclsRel C F rb capD H decls) (ha : Agree a b H H') (hrb : rb + 1 + capD ≤ a) (hbF : b ≤ F) :
    DeclsRel C F rb capD H' decls := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [ha.2 _ (Or.inl (by omega))]; exact h1, h2, h3, by rw [ha.1]; exact h4, fun k hk => ?_⟩
  obtain ⟨o, ho, hr⟩ := h5 k hk
  exact ⟨o, by rw [ha.2 _ (Or.inl (by omega))]; exact ho, recEnc_keeps hr (agree_keeps ha hbF)⟩

/-- The locals the inner loop writes. -/
def innerMods : List MlS := [ovJ, ovT, ovP, ovB, ovO, ovKey, ovDrop, ovX, ovY, ovI, ovA, ovB2]

/-- The inner loop: the stream record `d` at `od` (index `k`) against the prelude's records. -/
theorem inner_step {C : Ctx} {s : AState} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F rb capD nq np r2 : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hsz : decls.size = nq + np) (hcap : 8 * (rb + 1 + capD) < 2 ^ 64)
    (k : Nat) (hk : k < nq) (hval : ∀ k' (hk' : k' ≤ k), isVal (decls[k']'(by omega)) = true)
    (od : Nat) (hrd : RecEnc C F C.H od decls[k]) (Γ0 : Env) (hfix : OvFix C rb nq np r2 Γ0)
    (hK : Γ0.get ovK = some (BitVec.ofNat 64 k)) (hDd : Γ0.get ovD = some (cellA C od))
    (hNm : Γ0.get ovNm = some (Enc.idxW (valName decls[k]))) :
    Step (Inv (σ := σ) C s ((ovJ, 0) :: (ovDrop, 0) :: Γ0) [] D) (.while (.cmp .lower (vv ovJ) (vv ovNP)) innerBody)
      (fun t => ∃ Γ', Γ'.get ovDrop = some (if (keysUpTo decls nq np).contains (valName decls[k]) then 1 else 0) ∧
        (∀ j (hj : j < np), valName decls[k] = keyOf (decls[nq + j]'(by omega)) → decls[k] = decls[nq + j]'(by omega)) ∧
        ((keysUpTo decls nq np).contains (valName decls[k]) = true →
          ∀ k' (hk' : k' < k), valName (decls[k']'(by omega)) ≠ valName decls[k]) ∧
        (∀ y, y ∉ innerMods → Γ'.get y = Γ0.get y) ∧ OvFix C rb nq np r2 Γ' ∧
        Γ'.get ovK = some (BitVec.ofNat 64 k) ∧ Γ'.get ovD = some (cellA C od) ∧ Inv C s Γ' [] D t) := by
  have hle : decls.size ≤ capD := hdr.2.1
  let d := decls[k]
  let I : Ctx → Env → Prop := fun C' Γ' => C' = C ∧ ∃ j, ∃ hjn : j ≤ np, Γ'.get ovJ = some (BitVec.ofNat 64 j) ∧
    Γ'.get ovDrop = some (if (keysUpTo decls nq j).contains (valName d) then 1 else 0) ∧
    (∀ j' (hj' : j' < j), valName d = keyOf (decls[nq + j']'(by omega)) → d = decls[nq + j']'(by omega)) ∧
    ((keysUpTo decls nq j).contains (valName d) = true → ∀ k' (hk' : k' < k), valName (decls[k']'(by omega)) ≠ valName d) ∧
    (∀ y, y ∉ innerMods → Γ'.get y = Γ0.get y) ∧ OvFix C rb nq np r2 Γ' ∧
    Γ'.get ovK = some (BitVec.ofNat 64 k) ∧ Γ'.get ovD = some (cellA C od) ∧ Γ'.get ovNm = some (Enc.idxW (valName d))
  have hne : ∀ y ∈ [ovJ, ovDrop], y ≠ kRB ∧ y ≠ kNQ ∧ y ≠ ovNP ∧ y ≠ ovR2 := by decide
  refine fun t ht => (step_whileCE (s := s) (D := D) _ _ I
    (fun C' Γ' => C' = C ∧ ∃ j, j = np ∧ I C' Γ' ∧ Γ'.get ovJ = some (BitVec.ofNat 64 j)) C _ ⟨rfl, 0, Nat.zero_le _,
      by simp (config := {decide := true}) [T.Env.get_cons], by simp (config := {decide := true}) [T.Env.get_cons, keysUpTo], fun j' h => absurd h (by omega),
      fun h => by simp [keysUpTo] at h,
      fun y hy => by
        have h1 : y ≠ ovJ := fun e => hy (by simp [e, innerMods])
        have h2 : y ≠ ovDrop := fun e => hy (by simp [e, innerMods])
        simp (config := {decide := true}) [T.Env.get_cons, h1, h2],
      ovFix_cons (ovFix_cons hfix _ (hne _ (by simp)) _) _ (hne _ (by simp)) _,
      (by simp (config := {decide := true}) [T.Env.get_cons, hK]), (by simp (config := {decide := true}) [T.Env.get_cons, hDd]),
      (by simp (config := {decide := true}) [T.Env.get_cons, hNm, d])⟩ ?_ t ht).imp id (fun ⟨hn, C', Γ', ⟨hC, j, hj, ⟨_, j2, hj2, gJ, gDrop, heq,
        hscan, hag, hfx, gK, gD, _⟩, gJ'⟩, hq⟩ => by
      subst C'
      have : j2 = j := by
        rw [gJ] at gJ'; exact ofNat_inj63 (by omega) (by omega) (Option.some.inj gJ')
      subst this; subst hj
      exact ⟨hn, Γ', gDrop, heq, hscan, hag, hfx, gK, gD, hq⟩)
  intro C' Γ' hI
  obtain ⟨hC, j, hj, gJ, gDrop, heq, hscan, hag, hfx, gK, gD, gNm⟩ := hI
  subst C'
  refine ⟨bw (j < np), sev_lowerV _ _ _ _ _ gJ hfx.np (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
  · have : j = np := by have := bw_eq0' h0; omega
    exact ⟨rfl, j, this, ⟨rfl, j, hj, gJ, gDrop, heq, hscan, hag, hfx, gK, gD, gNm⟩, gJ⟩
  · have hlt := bw_ne0' h1
    obtain ⟨op, hop, hrp⟩ := regAt hdr (nq + j) (by omega)
    refine step_seq (step_assignI ovT (.op .add [vv kNQ, vv ovJ]) _ (hD _ (by simp [ovVars]))
      (sev_addV _ _ _ nq j hfx.nq gJ)) ?_
    have hfx1 := ovFix_cons hfx ovT (by decide) (BitVec.ofNat 64 (nq + j))
    refine step_seq (step_loadW ovP (slotE kRB ovT 1) _ _ hop (hD _ (by simp [ovVars]))
      (by rw [sev_slot _ C kRB ovT rb (nq + j) 1 hfx1.rb (by simp (config := {decide := true}) [T.Env.get_cons]) (by omega)])) ?_
    let Γ2 : Env := (ovP, cellA C op) :: (ovT, BitVec.ofNat 64 (nq + j)) :: Γ'
    refine step_cont (keyP_step hD hrp (by simp (config := {decide := true}) [Γ2, T.Env.get_cons])) (fun t ⟨key, Γ3, hkey, hag3, gKey, ht3⟩ => ?_)
    have hkeyOf : keyOf decls[nq + j] = key := by simp [keyOf, hkey]
    have g3 : ∀ y, y ≠ ovT → y ≠ ovB → y ≠ ovO → y ≠ ovKey → y ≠ ovP → Γ3.get y = Γ'.get y := by
      intro y h1 h2 h3 h4 h5
      rw [hag3 y h1 h2 h3 h4]; simp (config := {decide := true}) [Γ2, T.Env.get_cons, h1, h5]
    have gNm3 : Γ3.get ovNm = some (Enc.idxW (valName d)) := by
      rw [g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact gNm
    refine step_here ?_ ht3
    -- the comparison
    refine step_seq (Q := fun t => ∃ Γ4, Γ4.get ovDrop = some (if (keysUpTo decls nq (j + 1)).contains (valName d)
        then 1 else 0) ∧
        (valName d = keyOf decls[nq + j] → d = decls[nq + j]) ∧
        (valName d = keyOf decls[nq + j] → ∀ k' (hk' : k' < k), valName (decls[k']'(by omega)) ≠ valName d) ∧
        (∀ y, y ≠ ovT → y ≠ ovB → y ≠ ovO → y ≠ ovKey → y ≠ ovP → y ∉ recMods → y ≠ ovDrop →
          Γ4.get y = Γ'.get y) ∧ Inv C s Γ4 [] D t)
      (step_ifI _ _ (sev_eqv _ ovKey ovNm _ _ gKey gNm3) (fun he => ?_) (fun he => ?_)) ?_
    · have ek : key = valName d := Enc.idxW_inj (ite10_ne he)
      have gK3 : Γ3.get ovK = some (BitVec.ofNat 64 k) := by
        rw [g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact gK
      have gR3 : Γ3.get kRB = some (cellA C rb) := by
        rw [g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hfx.rb
      refine step_cont (scanP_step hD hdr hcap gR3 k (by omega) (fun k' hk' => hval k' (by omega)) gK3 _ gNm3) (fun t ⟨hsc, Γ5, hag5, ht5⟩ => ?_)
      have gD5 : Γ5.get ovD = some (cellA C od) := by
        rw [hag5 _ (by decide), g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact gD
      have gP5 : Γ5.get ovP = some (cellA C op) := by
        rw [hag5 _ (by decide), hag3 _ (by decide) (by decide) (by decide) (by decide)]; simp (config := {decide := true}) [Γ2, T.Env.get_cons]
      refine step_here ?_ ht5
      refine step_seq (recEqP_step hD hrd hrp (hval k (Nat.le_refl _)) gD5 gP5) ?_
      intro t ⟨hdp, Γ6, hag6, ht6⟩
      refine (step_assignI ovDrop (.const 1) 1 (hD _ (by simp [ovVars])) rfl t ht6).imp id (fun ⟨hn, hq⟩ =>
        ⟨hn, _, ?_, fun _ => hdp, fun _ => hsc, fun y h1 h2 h3 h4 h5 h6 h7 => ?_, hq⟩)
      · have : valName d ∈ keysUpTo decls nq (j + 1) := by
          rw [keysUpTo_succ, List.mem_append]; right
          rw [getElem!_pos decls (nq + j) (by omega), hkeyOf, ek]; simp
        simp (config := {decide := true}) [T.Env.get_cons, this]
      · have hy1 : y ∉ [ovI, ovX, ovY] := by
          simp only [recMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at h6
          simp [h6.1, h6.2.1, h6.2.2.1]
        simp only [T.Env.get_cons, h7, ite_false]
        rw [hag6 y h6, hag5 y hy1]; exact g3 y h1 h2 h3 h4 h5
    · have nk : key ≠ valName d := fun e => ite10_eq he (by rw [e])
      refine fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, Γ3, ?_, fun e => absurd (hkeyOf ▸ e.symm) nk,
        fun e => absurd (hkeyOf ▸ e.symm) nk, fun y h1 h2 h3 h4 h5 _ _ => g3 y h1 h2 h3 h4 h5, hq⟩)
      have : (keysUpTo decls nq (j + 1)).contains (valName d) = (keysUpTo decls nq j).contains (valName d) := by
        rw [keysUpTo_succ, getElem!_pos decls (nq + j) (by omega), hkeyOf]
        simp only [List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false]
        have : (valName d == key) = false := beq_eq_false_iff_ne.mpr (fun e => nk e.symm)
        rw [this, Bool.or_false]
      rw [this, g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact gDrop
    · intro t ⟨Γ4, gDrop4, heq4, hsc4, hag4, ht4⟩
      have gJ4 : Γ4.get ovJ = some (BitVec.ofNat 64 j) := by
        rw [hag4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact gJ
      refine (step_assignI ovJ (.op .add [vv ovJ, .const 1]) _ (hD _ (by simp [ovVars])) (sev_succV _ ovJ j gJ4)
        t ht4).imp id (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, j + 1, by omega, by simp (config := {decide := true}) [T.Env.get_cons],
          by rw [get_cons_ne _ _ _ _ (by decide)]; exact gDrop4, fun j' hj' => ?_, fun hc => ?_, fun y hy => ?_,
          ?_, ?_, ?_, ?_⟩, hq⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | rfl
        · exact heq j' h
        · exact heq4
      · rw [keysUpTo_succ, List.contains_append] at hc
        rcases Bool.or_eq_true_iff.mp hc with hc | hc
        · exact hscan hc
        · rw [getElem!_pos decls (nq + j) (by omega)] at hc
          exact hsc4 (by simpa using hc)
      · have hm : ∀ z ∈ [ovJ, ovT, ovB, ovO, ovKey, ovP, ovDrop, ovX, ovY, ovI, ovA, ovB2], z ∈ innerMods := by decide
        have h0 : y ≠ ovJ := fun e => hy (hm _ (by simp [e]))
        simp only [T.Env.get_cons, h0, ite_false]
        rw [hag4 y (fun e => hy (hm _ (by simp [e]))) (fun e => hy (hm _ (by simp [e]))) (fun e => hy (hm _ (by simp [e])))
          (fun e => hy (hm _ (by simp [e]))) (fun e => hy (hm _ (by simp [e]))) (fun h => hy (by
            simp only [recMods, List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (fun e => hy (hm _ (by simp [e])))]
        exact hag y hy
      · refine ovFix_cons (ovFix_agree hfx (fun y hy => ?_)) ovJ (by decide) _
        rcases hy with rfl | rfl | rfl | rfl <;>
          exact hag4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · rw [get_cons_ne _ _ _ _ (by decide), hag4 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact gK
      · rw [get_cons_ne _ _ _ _ (by decide), hag4 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact gD
      · rw [get_cons_ne _ _ _ _ (by decide), hag4 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact gNm

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

/-- The kept stream indices below `k`. -/
def keptIdx (decls : Array IDeclaration) (keys : List NIdx) (k : Nat) : List Nat :=
  (List.range k).filter (fun k' => keepW keys decls[k']!)

theorem keptIdx_succ (decls : Array IDeclaration) (keys : List NIdx) (k : Nat) :
    keptIdx decls keys (k + 1) = keptIdx decls keys k ++ (if keepW keys decls[k]! then [k] else []) := by
  simp only [keptIdx, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  try (split <;> simp_all)

theorem keptIdx_lt (decls : Array IDeclaration) (keys : List NIdx) (k : Nat) :
    ∀ x ∈ keptIdx decls keys k, x < k := by
  intro x hx; simp only [keptIdx, List.mem_filter, List.mem_range] at hx; exact hx.1

/-- The stream loop's invariant at record `k`, image `H'`. -/
structure StreamInv (C : Ctx) (F rb capD nq np r2 : Nat) (decls : Array IDeclaration) (H' : List (BitVec 64))
    (k : Nat) : Prop where
  agree : Agree r2 (r2 + 1 + capD) C.H H'
  pre : ∀ j, j < np → H'[r2 + 1 + j]? = C.H[rb + 1 + nq + j]?
  kept : ∀ i, i < (keptIdx decls (keysUpTo decls nq np) k).length →
    ∃ x, (keptIdx decls (keysUpTo decls nq np) k)[i]? = some x ∧ H'[r2 + 1 + np + i]? = C.H[rb + 1 + x]?
  val : ∀ k' (hk' : k' < k) (hs : k' < decls.size), isVal decls[k'] = true
  eq : ∀ k' (hk' : k' < k) (hs : k' < decls.size) j (hj : nq + j < decls.size), j < np →
    valName decls[k'] = keyOf decls[nq + j] → decls[k'] = decls[nq + j]
  uniq : ∀ k1 k2 (h1 : k1 < decls.size) (h2 : k2 < decls.size), k1 < k2 → k2 < k →
    (keysUpTo decls nq np).contains (valName decls[k2]) = true → valName decls[k1] ≠ valName decls[k2]

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

theorem streamInv_step {C : Ctx} {F rb capD nq np r2 : Nat} {decls : Array IDeclaration} {H' H'' : List (BitVec 64)}
    {k : Nat} (hk : k < decls.size) (hI : StreamInv C F rb capD nq np r2 decls H' k) (hv : isVal decls[k] = true)
    (heq : ∀ j (hj : j < np) (hj' : nq + j < decls.size), valName decls[k] = keyOf decls[nq + j] → decls[k] = decls[nq + j])
    (hscan : (keysUpTo decls nq np).contains (valName decls[k]) = true →
      ∀ k' (hk' : k' < k), valName (decls[k']'(by omega)) ≠ valName decls[k])
    (hagree : Agree r2 (r2 + 1 + capD) C.H H'') (hpre : ∀ j, j < np → H''[r2 + 1 + j]? = H'[r2 + 1 + j]?)
    (hkept : ∀ i, i < (keptIdx decls (keysUpTo decls nq np) (k + 1)).length →
      ∃ x, (keptIdx decls (keysUpTo decls nq np) (k + 1))[i]? = some x ∧ H''[r2 + 1 + np + i]? = C.H[rb + 1 + x]?) :
    StreamInv C F rb capD nq np r2 decls H'' (k + 1) where
  agree := hagree
  pre j hj := (hpre j hj).trans (hI.pre j hj)
  kept := hkept
  val k' hk' hs := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h | rfl
    · exact hI.val k' h hs
    · exact hv
  eq k' hk' hs j hj h := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
    · exact hI.eq k' h' hs j hj h
    · exact heq j h hj
  uniq k1 k2 h1 h2 h12 hk2 hc := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk2 with h | rfl
    · exact hI.uniq k1 k2 h1 h2 h12 h hc
    · exact hscan hc k1 h12

theorem streamBody_step {C : Ctx} (hok : CtxOK C) {s : AState} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F rb capD nq np r2 : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hsz : decls.size = nq + np) (hcap : 8 * (r2 + 1 + capD) < 2 ^ 64) (hrb : rb + 1 + capD ≤ r2)
    (hF : r2 + 1 + capD ≤ F)
    (k : Nat) (hk : k < nq) (H' : List (BitVec 64)) (hI : StreamInv C F rb capD nq np r2 decls H' k)
    (Γ0 Γ : Env) (hfix : OvFix C rb nq np r2 Γ) (hK : Γ.get ovK = some (BitVec.ofNat 64 k))
    (hW : Γ.get ovW = some (BitVec.ofNat 64 (keptIdx decls (keysUpTo decls nq np) k).length))
    (hag : ∀ y, y ∉ ovVars → Γ.get y = Γ0.get y) :
    Step (Inv (σ := σ) (ctxH C H') s Γ [] D) streamBody (fun t => ∃ H'' Γ', StreamInv C F rb capD nq np r2 decls H'' (k + 1) ∧
      OvFix C rb nq np r2 Γ' ∧ Γ'.get ovK = some (BitVec.ofNat 64 (k + 1)) ∧
      Γ'.get ovW = some (BitVec.ofNat 64 (keptIdx decls (keysUpTo decls nq np) (k + 1)).length) ∧
      (∀ y, y ∉ ovVars → Γ'.get y = Γ0.get y) ∧ Inv (ctxH C H'') s Γ' [] D t) := by
  have hle : decls.size ≤ capD := hdr.2.1
  have hdr' : DeclsRel (ctxH C H') F rb capD (ctxH C H').H decls := declsRel_agree hdr hI.agree (by omega) hF
  obtain ⟨od, hod, hrd⟩ := regAt hdr' k (by omega)
  have hfix' := ovFix_ctxH hfix H'
  refine step_seq (step_loadW ovD (slotE kRB ovK 1) _ _ hod (hD _ (by simp [ovVars]))
    (by rw [sev_slot _ _ kRB ovK rb k 1 hfix'.rb hK (by omega)])) ?_
  refine step_seq (step_loadW ovT (vv ovD) od _ (recEnc_tag hrd) (hD _ (by simp [ovVars]))
    (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
  refine step_cont (Q := fun t => isVal decls[k] = true ∧ _) (step_ifI _ _ (sev_eqC _ ovT 4 (BitVec.ofNat 64 (tagOf decls[k]))
    (by simp (config := {decide := true}) [T.Env.get_cons])) (fun _ => step_hangI) (fun h4 => fun t ht => (step_skipI t ht).imp id
      (fun ⟨h1, h2⟩ => ⟨h1, isVal_of_tag (fun e => ite10_eq h4 (by rw [e])), h2⟩))) (fun t ⟨hv, ht⟩ => ?_)
  refine step_here ?_ ht
  refine step_seq (step_loadW ovNm (offE ovD 1) (od + 1) _ (name_of_val hrd hv) (hD _ (by simp [ovVars]))
    (sev_off _ _ ovD od 1 (by simp (config := {decide := true}) [T.Env.get_cons]))) ?_
  refine step_seq (step_assignI ovDrop (.const 0) 0 (hD _ (by simp [ovVars])) rfl) ?_
  refine step_seq (step_assignI ovJ (.const 0) 0 (hD _ (by simp [ovVars])) rfl) ?_
  let Γ1 : Env := (ovNm, Enc.idxW (valName decls[k])) :: (ovT, BitVec.ofNat 64 (tagOf decls[k])) ::
    (ovD, cellA C od) :: Γ
  have hfix1 : OvFix (ctxH C H') rb nq np r2 Γ1 :=
    ovFix_cons (ovFix_cons (ovFix_cons hfix' _ (by decide) _) _ (by decide) _) _ (by decide) _
  refine step_cont (inner_step hD hdr' hsz (by omega) k hk (fun k' hk' => by
      rcases Nat.lt_or_eq_of_le hk' with h | rfl
      · exact hI.val k' h (by omega)
      · exact hv) od hrd Γ1 hfix1 ((by simp (config := {decide := true}) [Γ1, T.Env.get_cons, hK])) (by simp (config := {decide := true}) [Γ1, T.Env.get_cons])
    (by simp (config := {decide := true}) [Γ1, T.Env.get_cons])) (fun t ⟨Γ2, gDrop, heq, hscan, hag2, hfix2, gK2, gD2, ht2⟩ => ?_)
  have g2 : ∀ y, y ∉ ovVars → Γ2.get y = Γ0.get y := by
    intro y hy; rw [hag2 y (fun h => hy (by
      simp only [innerMods, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))]
    have h1 : y ≠ ovNm := fun e => hy (by simp [e, ovVars])
    have h2 : y ≠ ovT := fun e => hy (by simp [e, ovVars])
    have h3 : y ≠ ovD := fun e => hy (by simp [e, ovVars])
    simp only [Γ1, T.Env.get_cons, h1, h2, h3, ite_false]; exact hag y hy
  have gW2 : Γ2.get ovW = some (BitVec.ofNat 64 (keptIdx decls (keysUpTo decls nq np) k).length) := by
    rw [hag2 _ (by decide)]; simp only [Γ1, get_cons_ne _ _ _ _ (show ovW ≠ ovNm by decide),
      get_cons_ne _ _ _ _ (show ovW ≠ ovT by decide), get_cons_ne _ _ _ _ (show ovW ≠ ovD by decide)]; exact hW
  let keys := keysUpTo decls nq np
  let w := (keptIdx decls keys k).length
  have hwk : w ≤ k := by
    have := List.Sublist.length_le (List.filter_sublist (p := fun k' => keepW keys decls[k']!) (l := List.range k))
    simpa [keptIdx, w] using this
  refine step_here ?_ ht2
  refine step_seq (Q := fun t => ∃ H'' Γ3, StreamInv C F rb capD nq np r2 decls H'' (k + 1) ∧
      OvFix C rb nq np r2 Γ3 ∧ Γ3.get ovK = some (BitVec.ofNat 64 k) ∧
      Γ3.get ovW = some (BitVec.ofNat 64 (keptIdx decls keys (k + 1)).length) ∧
      (∀ y, y ∉ ovVars → Γ3.get y = Γ0.get y) ∧ Inv (ctxH C H'') s Γ3 [] D t)
    (step_ifI _ _ (sev_eqC _ ovDrop 0 _ gDrop) (fun h0 => ?_) (fun h0 => ?_)) ?_
  · -- kept
    have h' := ite10_ne h0
    have hkeep : keepW keys decls[k] = true := by
      have : keys.contains (valName decls[k]) = false := by
        cases e : keys.contains (valName decls[k])
        · rfl
        · exfalso; simp only [keys] at e; rw [e] at h'; exact absurd h' (by decide)
      simp only [keepW, this, Bool.not_false, Bool.not_true]
    have hkk : keptIdx decls keys (k + 1) = keptIdx decls keys k ++ [k] := by
      rw [keptIdx_succ, getElem!_pos decls k (by omega), if_pos hkeep]
    refine step_seq (step_assignI ovT (.op .add [vv ovNP, vv ovW]) _ (hD _ (by simp [ovVars]))
      (sev_addV _ _ _ np w hfix2.np gW2)) ?_
    have hj : r2 + 1 + (np + w) < (ctxH C H').H.length := by
      show _ < H'.length; rw [hI.agree.1]; have := hdr.2.2.2.1; omega
    refine step_seq (T.step_heapStoreI (ctxOK_ctxH hok) (slotE ovR2 ovT 1) (vv ovD) (r2 + 1 + (np + w)) hj (cellA C od)
      (by rw [sev_slot _ _ ovR2 ovT r2 (np + w) 1 (ovFix_cons (ovFix_ctxH hfix2 H') ovT (by decide) _).r2
        (by simp (config := {decide := true}) [T.Env.get_cons]) (by omega)]; try rfl)
      ((by simp (config := {decide := true}) [sev, vv, T.Env.get_cons, gD2]))) ?_
    refine fun t ht => (step_assignI ovW (.op .add [vv ovW, .const 1]) _ (hD _ (by simp [ovVars]))
      (sev_succV _ ovW w (by rw [get_cons_ne _ _ _ _ (by decide)]; exact gW2)) t ht).imp id (fun ⟨hn, hq⟩ =>
        ⟨hn, H'.set (r2 + 1 + (np + w)) (cellA C od), _, ?_, ovFix_cons (ovFix_cons (ovFix_of_ctxH hfix2) _ (by decide) _) _ (by decide) _,
          (by simp (config := {decide := true}) [T.Env.get_cons, gK2]),
          (by simp (config := {decide := true}) [T.Env.get_cons, hkk, w]), fun y hy => ?_, hq⟩)
    · have hrbk : H'[rb + 1 + k]? = C.H[rb + 1 + k]? := hI.agree.2 _ (Or.inl (by omega))
      refine streamInv_step (by omega) hI hv (fun j hj hj' => heq j hj) hscan
        (agree_set hI.agree _ (by omega) (by omega) _) (fun j hj => by
          rw [List.getElem?_set, ite_eq_right (by omega)]) (fun i hi => ?_)
      rw [hkk, List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · obtain ⟨x, hx, he⟩ := hI.kept i h
        exact ⟨x, by rw [hkk, List.getElem?_append_left h]; exact hx,
          by rw [List.getElem?_set, ite_eq_right (by omega)]; exact he⟩
      · refine ⟨k, by rw [hkk, List.getElem?_concat_length], ?_⟩
        rw [show r2 + 1 + np + (keptIdx decls keys k).length = r2 + 1 + (np + w) by simp [w]; omega,
          List.getElem?_set_self (by have := hdr.2.2.2.1; rw [hI.agree.1]; omega), ← hrbk]
        exact hod.symm
    · have h1 : y ≠ ovW := fun e => hy (by simp [e, ovVars])
      have h2 : y ≠ ovT := fun e => hy (by simp [e, ovVars])
      simp only [T.Env.get_cons, h1, h2, ite_false]; exact g2 y hy
  · -- dropped
    have h' := ite10_eq h0
    have hdrop : keepW keys decls[k] = false := by
      have : keys.contains (valName decls[k]) = true := by
        cases e : keys.contains (valName decls[k])
        · exfalso; simp only [keys] at e; rw [e] at h'; exact h' (by decide)
        · rfl
      simp only [keepW, this, Bool.not_false, Bool.not_true]
    have hkk : keptIdx decls keys (k + 1) = keptIdx decls keys k := by
      rw [keptIdx_succ, getElem!_pos decls k (by omega), if_neg (by simp [hdrop])]; simp
    refine fun t ht => (step_skipI t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, H', Γ2, ?_, ovFix_of_ctxH hfix2, gK2,
      by rw [hkk]; exact gW2, g2, hq⟩)
    exact streamInv_step (by omega) hI hv (fun j hj hj' => heq j hj) hscan hI.agree (fun _ _ => rfl)
      (fun i hi => by
        rw [hkk] at hi
        obtain ⟨x, hx, he⟩ := hI.kept i hi
        exact ⟨x, by rw [hkk]; exact hx, he⟩)
  · intro t ⟨H'', Γ3, hI3, hfix3, gK3, gW3, hag3, ht3⟩
    refine (step_assignI ovK (.op .add [vv ovK, .const 1]) _ (hD _ (by simp [ovVars])) (sev_succV _ ovK k gK3)
      t ht3).imp id (fun ⟨hn, hq⟩ => ⟨hn, H'', _, hI3, ovFix_cons hfix3 _ (by decide) _, by simp (config := {decide := true}) [T.Env.get_cons],
        by rw [get_cons_ne _ _ _ _ (by decide)]; exact gW3, fun y hy => ?_, hq⟩)
    have : y ≠ ovK := fun e => hy (by simp [e, ovVars])
    simp only [T.Env.get_cons, this, ite_false]; exact hag3 y hy

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

theorem keysUpTo_eq (decls : Array IDeclaration) (nq np : Nat) (hsz : decls.size = nq + np) :
    (decls.toList.drop nq).map keyOf = keysUpTo decls nq np := by
  apply List.ext_getElem
  · simp [keysUpTo, hsz]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_drop, Array.getElem_toList, keysUpTo, List.getElem_range]
    rw [getElem!_pos decls (nq + i) (by simp [hsz] at h1; omega)]

/-- The copy loop: the prelude's record pointers into the second registry, each key checked. -/
theorem copy_step {C : Ctx} (hok : CtxOK C) {s : AState} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F rb capD nq np r2 : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hsz : decls.size = nq + np) (hcap : 8 * (r2 + 1 + capD) < 2 ^ 64) (hrb : rb + 1 + capD ≤ r2)
    (hF : r2 + 1 + capD ≤ F) (Γ0 Γ : Env) (hfix : OvFix C rb nq np r2 Γ)
    (hJ : Γ.get ovJ = some 0) (hag : ∀ y, y ∉ ovVars → Γ.get y = Γ0.get y) :
    Step (Inv (σ := σ) C s Γ [] D) (.while (.cmp .lower (vv ovJ) (vv ovNP)) copyBody)
      (fun t => ∃ H' Γ', Agree r2 (r2 + 1 + capD) C.H H' ∧
        (∀ j, j < np → H'[r2 + 1 + j]? = C.H[rb + 1 + nq + j]?) ∧
        (∀ j (hj : nq + j < decls.size), j < np → decls[nq + j].names.head? = some (keyOf decls[nq + j])) ∧
        OvFix C rb nq np r2 Γ' ∧ (∀ y, y ∉ ovVars → Γ'.get y = Γ0.get y) ∧ Inv (ctxH C H') s Γ' [] D t) := by
  have hle : decls.size ≤ capD := hdr.2.1
  let I : Ctx → Env → Prop := fun C' Γ' => ∃ H' j, C' = ctxH C H' ∧ j ≤ np ∧ Agree r2 (r2 + 1 + capD) C.H H' ∧
    (∀ j', j' < j → H'[r2 + 1 + j']? = C.H[rb + 1 + nq + j']?) ∧
    (∀ j' (hj : nq + j' < decls.size), j' < j → decls[nq + j'].names.head? = some (keyOf decls[nq + j'])) ∧
    OvFix C rb nq np r2 Γ' ∧ Γ'.get ovJ = some (BitVec.ofNat 64 j) ∧ (∀ y, y ∉ ovVars → Γ'.get y = Γ0.get y)
  have := step_whileCE (σ := σ) (s := s) (D := D) (.cmp .lower (vv ovJ) (vv ovNP)) copyBody I
    (fun C' Γ' => ∃ H', C' = ctxH C H' ∧ Agree r2 (r2 + 1 + capD) C.H H' ∧
      (∀ j, j < np → H'[r2 + 1 + j]? = C.H[rb + 1 + nq + j]?) ∧
      (∀ j (hj : nq + j < decls.size), j < np → decls[nq + j].names.head? = some (keyOf decls[nq + j])) ∧
      OvFix C rb nq np r2 Γ' ∧ (∀ y, y ∉ ovVars → Γ'.get y = Γ0.get y))
    C Γ ⟨C.H, 0, (ctxH_self C).symm, Nat.zero_le _, agree_refl _ _ _, fun _ h => absurd h (by omega),
      fun _ _ h => absurd h (by omega), hfix, hJ, hag⟩ ?_
  · intro t ht
    rcases this t ht with hs | ⟨hn, C', Γ', ⟨H', rfl, a, b, c, d, e⟩, hq⟩
    · exact Or.inl hs
    · exact Or.inr ⟨hn, H', Γ', a, b, c, d, e, hq⟩
  intro C' Γ' ⟨H', j, hC, hj, hA, hpre, hkey, hfx, gJ, hag'⟩
  subst C'
  refine ⟨bw (j < np), sev_lowerV _ _ _ _ _ gJ hfx.np (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
  · have : j = np := by have := bw_eq0' h0; omega
    subst this; exact ⟨H', rfl, hA, hpre, hkey, hfx, hag'⟩
  · have hlt := bw_ne0' h1
    have hdr' : DeclsRel (ctxH C H') F rb capD (ctxH C H').H decls := declsRel_agree hdr hA (by omega) hF
    obtain ⟨op, hop, hrp⟩ := regAt hdr' (nq + j) (by omega)
    have hfx' := ovFix_ctxH hfx H'
    refine step_seq (step_assignI ovT (.op .add [vv kNQ, vv ovJ]) _ (hD _ (by simp [ovVars]))
      (sev_addV _ _ _ nq j hfx'.nq gJ)) ?_
    have hfx1 := ovFix_cons hfx' ovT (by decide) (BitVec.ofNat 64 (nq + j))
    refine step_seq (step_loadW ovP (slotE kRB ovT 1) _ _ hop (hD _ (by simp [ovVars]))
      (by rw [sev_slot _ _ kRB ovT rb (nq + j) 1 hfx1.rb (by simp (config := {decide := true}) [T.Env.get_cons]) (by omega)])) ?_
    refine step_cont (keyP_step hD hrp (by simp (config := {decide := true}) [T.Env.get_cons])) (fun t ⟨key, Γ3, hkey3, hag3, gKey, ht3⟩ => ?_)
    have g3 : ∀ y, y ≠ ovT → y ≠ ovB → y ≠ ovO → y ≠ ovKey → y ≠ ovP → Γ3.get y = Γ'.get y := by
      intro y h1 h2 h3 h4 h5
      rw [hag3 y h1 h2 h3 h4]; simp (config := {decide := true}) [T.Env.get_cons, h1, h5]
    have hfx3 : OvFix (ctxH C H') rb nq np r2 Γ3 := ovFix_agree hfx' (fun y hy => by
      rcases hy with rfl | rfl | rfl | rfl <;> exact g3 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    have gJ3 : Γ3.get ovJ = some (BitVec.ofNat 64 j) := by
      rw [g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact gJ
    have gP3 : Γ3.get ovP = some (cellA C op) := by
      rw [hag3 _ (by decide) (by decide) (by decide) (by decide)]; simp (config := {decide := true}) [T.Env.get_cons]
    have hj2 : r2 + 1 + j < (ctxH C H').H.length := by
      show _ < H'.length; rw [hA.1]; have := hdr.2.2.2.1; omega
    refine step_here ?_ ht3
    refine step_seq (T.step_heapStoreI (ctxOK_ctxH hok) (slotE ovR2 ovJ 1) (vv ovP) (r2 + 1 + j) hj2 (cellA C op)
      (by rw [sev_slot _ _ ovR2 ovJ r2 j 1 hfx3.r2 gJ3 (by omega)]; try rfl) (by simp [sev, vv, gP3])) ?_
    refine fun t ht => (step_assignI ovJ (.op .add [vv ovJ, .const 1]) _ (hD _ (by simp [ovVars]))
      (sev_succV _ ovJ j gJ3) t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, _, _, ⟨H'.set (r2 + 1 + j) (cellA C op), j + 1, rfl,
        by omega, agree_set hA _ (by omega) (by omega) _, fun j' hj' => ?_, fun j' hj'' hj' => ?_,
        ovFix_cons (ovFix_of_ctxH hfx3) _ (by decide) _, (by simp (config := {decide := true}) [T.Env.get_cons]), fun y hy => ?_⟩, hq⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
      · rw [List.getElem?_set, ite_eq_right (by omega)]; exact hpre j' h
      · rw [h, List.getElem?_set_self (by rw [hA.1]; have := hdr.2.2.2.1; omega),
          show rb + 1 + nq + j = rb + 1 + (nq + j) by omega, ← hA.2 _ (Or.inl (by omega))]; exact hop.symm
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
      · exact hkey j' hj'' h
      · subst h; simp [keyOf, hkey3]
    · have h0 : y ≠ ovJ := fun e => hy (by simp [e, ovVars])
      simp only [T.Env.get_cons, h0, ite_false]
      rw [g3 y (fun e => hy (by simp [e, ovVars])) (fun e => hy (by simp [e, ovVars])) (fun e => hy (by simp [e, ovVars]))
        (fun e => hy (by simp [e, ovVars])) (fun e => hy (by simp [e, ovVars]))]
      exact hag' y hy

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

theorem stream_step {C : Ctx} (hok : CtxOK C) {s : AState} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F rb capD nq np r2 : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hsz : decls.size = nq + np) (hcap : 8 * (r2 + 1 + capD) < 2 ^ 64) (hrb : rb + 1 + capD ≤ r2)
    (hF : r2 + 1 + capD ≤ F) (H0 : List (BitVec 64)) (hI0 : StreamInv C F rb capD nq np r2 decls H0 0)
    (Γ0 Γ : Env) (hfix : OvFix C rb nq np r2 Γ) (hK : Γ.get ovK = some 0) (hW : Γ.get ovW = some 0)
    (hag : ∀ y, y ∉ ovVars → Γ.get y = Γ0.get y) :
    Step (Inv (σ := σ) (ctxH C H0) s Γ [] D) (.while (.cmp .lower (vv ovK) (vv kNQ)) streamBody)
      (fun t => ∃ H' Γ', StreamInv C F rb capD nq np r2 decls H' nq ∧ OvFix C rb nq np r2 Γ' ∧
        Γ'.get ovW = some (BitVec.ofNat 64 (keptIdx decls (keysUpTo decls nq np) nq).length) ∧
        (∀ y, y ∉ ovVars → Γ'.get y = Γ0.get y) ∧ Inv (ctxH C H') s Γ' [] D t) := by
  let I : Ctx → Env → Prop := fun C' Γ' => ∃ H' k, C' = ctxH C H' ∧ k ≤ nq ∧
    StreamInv C F rb capD nq np r2 decls H' k ∧ OvFix C rb nq np r2 Γ' ∧ Γ'.get ovK = some (BitVec.ofNat 64 k) ∧
    Γ'.get ovW = some (BitVec.ofNat 64 (keptIdx decls (keysUpTo decls nq np) k).length) ∧
    (∀ y, y ∉ ovVars → Γ'.get y = Γ0.get y)
  have := step_whileCE (σ := σ) (s := s) (D := D) (.cmp .lower (vv ovK) (vv kNQ)) streamBody I
    (fun C' Γ' => ∃ H', C' = ctxH C H' ∧ StreamInv C F rb capD nq np r2 decls H' nq ∧ OvFix C rb nq np r2 Γ' ∧
      Γ'.get ovW = some (BitVec.ofNat 64 (keptIdx decls (keysUpTo decls nq np) nq).length) ∧
      (∀ y, y ∉ ovVars → Γ'.get y = Γ0.get y))
    (ctxH C H0) Γ ⟨H0, 0, rfl, Nat.zero_le _, hI0, hfix, hK, by simp [keptIdx]; exact hW, hag⟩ ?_
  · intro t ht
    rcases this t ht with hs | ⟨hn, C', Γ', ⟨H', rfl, a, b, c, d⟩, hq⟩
    · exact Or.inl hs
    · exact Or.inr ⟨hn, H', Γ', a, b, c, d, hq⟩
  intro C' Γ' ⟨H', k, hC, hk, hI, hfx, gK, gW, hag'⟩
  subst C'
  have hle : decls.size ≤ capD := hdr.2.1
  refine ⟨bw (k < nq), sev_lowerV _ _ _ _ _ gK hfx.nq (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
  · have : k = nq := by have := bw_eq0' h0; omega
    subst this; exact ⟨H', rfl, hI, hfx, gW, hag'⟩
  · have hlt := bw_ne0' h1
    exact fun t ht => (streamBody_step hok hD hdr hsz hcap hrb hF k hlt H' hI Γ0 Γ' hfx gK gW hag' t ht).imp id
      (fun ⟨hn, H'', Γ'', a, b, c, d, e, hq⟩ => ⟨hn, _, Γ'', ⟨H'', k + 1, rfl, by omega, a, b, c, d, e⟩, hq⟩)

/-- **The override pass**: the continuation runs at the second registry, `P` then the kept stream
records, with `OverW` of the stream and the prelude. -/
theorem overP_spec {β : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (hD : ∀ x ∈ ovVars, x ∈ D) (hDk : kRB ∈ D)
    {F rb capD j0 nq : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls) (hnq : nq ≤ decls.size)
    (hrb : rb + 1 + capD ≤ j0 + 4096) (hF : j0 + 4096 + 1 + capD ≤ F) (hcap : 8 * (j0 + 4096 + 1 + capD) < 2 ^ 64)
    (hRB : Γ.get kRB = some (cellA C rb)) (hNQ : Γ.get kNQ = some (BitVec.ofNat 64 nq))
    (hRA : Γ.get kRA = some (cellA C j0))
    {rest : ProgHOL 64} {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ H' Γ', Agree (j0 + 4096) (j0 + 4096 + 1 + capD) C.H H' →
      (∀ y, y ∉ kRB :: ovVars → Γ'.get y = Γ.get y) → Γ'.get kRB = some (cellA C (j0 + 4096)) →
      OverW (decls.toList.take nq) (decls.toList.drop nq) →
      DeclsRel C F (j0 + 4096) capD H' (decls.toList.drop nq ++ (decls.toList.take nq).filter
        (keepW ((decls.toList.drop nq).map keyOf))).toArray →
      SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (overP rest) s m R := by
  suffices hM : SpecR (Inv C s Γ [] D) (overP rest) s m R from
    fun t ht => hM t ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  have hle : decls.size ≤ capD := hdr.2.1
  let np := decls.size - nq
  let r2 := j0 + 4096
  have hsz : decls.size = nq + np := by omega
  unfold overP
  refine specR_heapLoadI ovN (vv kRB) rb (lt_of_get hdr.1) (hD _ (by simp [ovVars])) (by simpa [sev, vv] using hRB) ?_
  rw [getElem_of_get hdr.1]
  refine specR_assignI ovNP _ (BitVec.ofNat 64 np) (hD _ (by simp [ovVars])) (by
    simp only [sev, vv, T.Env.get_cons, show ovN = ovN from rfl, ite_true, show kNQ ≠ ovN by decide, ite_false, hNQ,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]) ?_
  refine specR_assignI ovR2 (offE kRA 4096) (cellA C r2) (hD _ (by simp [ovVars]))
    (sev_off _ C kRA j0 4096 ((by simp (config := {decide := true}) [T.Env.get_cons, hRA]))) ?_
  refine specR_assignI ovJ (.const 0) 0 (hD _ (by simp [ovVars])) rfl ?_
  let Γ1 : Env := (ovJ, 0) :: (ovR2, cellA C r2) :: (ovNP, BitVec.ofNat 64 np) ::
    (ovN, BitVec.ofNat 64 decls.size) :: Γ
  have hag1 : ∀ y, y ∉ ovVars → Γ1.get y = Γ.get y := by
    intro y hy
    have h1 : y ≠ ovJ := fun e => hy (by simp [e, ovVars])
    have h2 : y ≠ ovR2 := fun e => hy (by simp [e, ovVars])
    have h3 : y ≠ ovNP := fun e => hy (by simp [e, ovVars])
    have h4 : y ≠ ovN := fun e => hy (by simp [e, ovVars])
    simp (config := {decide := true}) [Γ1, T.Env.get_cons, h1, h2, h3, h4]
  have hfix1 : OvFix C rb nq np r2 Γ1 :=
    ⟨by rw [hag1 _ (by decide)]; exact hRB, by rw [hag1 _ (by decide)]; exact hNQ, by simp (config := {decide := true}) [Γ1, T.Env.get_cons],
      by simp (config := {decide := true}) [Γ1, T.Env.get_cons]⟩
  refine specR_cont (copy_step hok hD hdr hsz (by omega) hrb hF Γ Γ1 hfix1 (by simp (config := {decide := true}) [Γ1, T.Env.get_cons]) hag1) (fun t ⟨H1, Γ2, hA1, hpre1, hkey1, hfix2, hag2, ht2⟩ => ?_)
  refine specR_here ?_ ht2
  refine specR_assignI ovK (.const 0) 0 (hD _ (by simp [ovVars])) rfl ?_
  refine specR_assignI ovW (.const 0) 0 (hD _ (by simp [ovVars])) rfl ?_
  have hI0 : StreamInv C F rb capD nq np r2 decls H1 0 :=
    ⟨hA1, hpre1, fun i hi => absurd hi (by simp [keptIdx]), fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ _ _ _ _ h => absurd h (by omega)⟩
  refine specR_cont (stream_step hok hD hdr hsz (by omega) hrb hF H1 hI0 Γ _
    (ovFix_cons (ovFix_cons hfix2 _ (by decide) _) _ (by decide) _) (by simp (config := {decide := true}) [T.Env.get_cons])
    (by simp (config := {decide := true}) [T.Env.get_cons]) (fun y hy => by
      have h1 : y ≠ ovW := fun e => hy (by simp [e, ovVars])
      have h2 : y ≠ ovK := fun e => hy (by simp [e, ovVars])
      simp (config := {decide := true}) [T.Env.get_cons, h1, h2]; exact hag2 y hy)) (fun t ⟨H2, Γ3, hI, hfix3, gW3, hag3, ht3⟩ => ?_)
  refine specR_here ?_ ht3
  let keys := keysUpTo decls nq np
  let w := (keptIdx decls keys nq).length
  have hwq : w ≤ nq := by
    have := List.Sublist.length_le (List.filter_sublist (p := fun k' => keepW keys decls[k']!) (l := List.range nq))
    simpa [keptIdx, w] using this
  refine specR_assignI ovT (.op .add [vv ovNP, vv ovW]) _ (hD _ (by simp [ovVars]))
    (sev_addV _ _ _ np w (ovFix_ctxH hfix3 H2).np gW3) ?_
  have hr2 : r2 < (ctxH C H2).H.length := by show _ < H2.length; rw [hI.agree.1]; have := hdr.2.2.2.1; omega
  refine specR_heapStoreI (ctxOK_ctxH hok) (vv ovR2) (vv ovT) r2 hr2 (BitVec.ofNat 64 (np + w))
    (by simp only [sev, vv]; rw [get_cons_ne _ _ _ _ (by decide)]; exact (ovFix_ctxH hfix3 H2).r2)
    (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons]) ?_
  refine specR_assignI kRB (vv ovR2) (cellA C r2) hDk
    (by simp only [sev, vv]; rw [get_cons_ne _ _ _ _ (by decide)]; exact hfix3.r2) ?_
  let H3 := H2.set r2 (BitVec.ofNat 64 (np + w))
  have hA3 : Agree r2 (r2 + 1 + capD) C.H H3 := agree_set hI.agree r2 (Nat.le_refl _) (by omega) _
  refine hk H3 _ hA3 (fun y hy => ?_) (by simp (config := {decide := true}) [T.Env.get_cons, r2]) ?_ ?_
  · simp only [List.mem_cons, not_or] at hy
    have h1 : y ≠ ovT := fun e => hy.2 (by simp [e, ovVars])
    simp only [T.Env.get_cons, hy.1, h1, ite_false]
    exact hag3 y hy.2
  · -- the facts
    have hkeys := keysUpTo_eq decls nq np hsz
    refine ⟨fun p hp => ?_, fun d hd => ?_, fun d hd p hp he => ?_, fun i j hi hj hij hc => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
      simp only [List.getElem_drop, Array.getElem_toList]
      exact hkey1 j (by simp at hj; omega) (by simp at hj; omega)
    · obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hd
      simp only [List.getElem_take, Array.getElem_toList]
      exact hI.val k (by simp at hk'; omega) (by simp at hk'; omega)
    · obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hd
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
      simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList] at he ⊢
      exact hI.eq k (by simp at hk'; omega) _ j _ (by simp at hj; omega) he
    · simp only [List.getElem_take, Array.getElem_toList] at hc ⊢
      rw [hkeys] at hc
      exact hI.uniq i j _ _ hij (by simp at hj; omega) hc
  · -- the second registry
    have hkeys := keysUpTo_eq decls nq np hsz
    have hfil : (decls.toList.take nq).filter (keepW ((decls.toList.drop nq).map keyOf)) =
        (keptIdx decls keys nq).map (fun k => decls[k]!) := by
      rw [hkeys]; exact take_filter_eq decls _ nq hnq
    have hdl : (decls.toList.drop nq).length = np := by simp; omega
    have hlenL : (decls.toList.drop nq ++ (decls.toList.take nq).filter
        (keepW ((decls.toList.drop nq).map keyOf))).length = np + w := by
      rw [List.length_append, hdl, hfil, List.length_map]
    have hlen3 : H3.length = C.H.length := hA3.1
    refine ⟨?_, ?_, hF, ?_, fun i hi => ?_⟩
    · simp only [List.size_toArray, hlenL, H3]
      exact List.getElem?_set_self (by rw [hI.agree.1]; have := hdr.2.2.2.1; omega)
    · simp only [List.size_toArray, hlenL]; omega
    · rw [hlen3]; exact hdr.2.2.2.1
    · simp only [List.size_toArray, hlenL] at hi
      simp only [List.getElem_toArray]
      by_cases hip : i < np
      · obtain ⟨o, ho, hro⟩ := regAt hdr (nq + i) (by omega)
        refine ⟨o, ?_, ?_⟩
        · simp only [H3]; rw [List.getElem?_set, ite_eq_right (by omega), hI.pre i hip,
            show rb + 1 + nq + i = rb + 1 + (nq + i) by omega]; exact ho
        · rw [List.getElem_append_left (by rw [hdl]; exact hip)]
          simp only [List.getElem_drop, Array.getElem_toList]
          exact recEnc_keeps hro (agree_keeps hA3 hF)
      · have hiw : i - np < w := by omega
        obtain ⟨x, hx, hk⟩ := hI.kept (i - np) hiw
        have hxe : (keptIdx decls keys nq)[i - np] = x := by
          rw [List.getElem?_eq_getElem hiw] at hx; exact Option.some.inj hx
        have hkx := keptIdx_lt decls keys nq _ (List.getElem_mem hiw)
        rw [hxe] at hkx
        obtain ⟨o, ho, hro⟩ := regAt hdr x (by omega)
        refine ⟨o, ?_, ?_⟩
        · simp only [H3]; rw [List.getElem?_set, ite_eq_right (by omega),
            show r2 + 1 + i = r2 + 1 + np + (i - np) by omega, hk]; exact ho
        · rw [List.getElem_append_right (by rw [hdl]; omega)]
          simp only [hfil, List.getElem_map, hdl, hxe]
          rw [getElem!_pos decls _ (by omega)]
          exact recEnc_keeps hro (agree_keeps hA3 hF)

end ConPanqueque.Prelude
