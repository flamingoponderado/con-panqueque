import ConPanqueque.T.Quot.ArmSpec

/-!
# The standard and compiler-trust axioms: the proof

`stdP C k` against the twin's `stdAxiomOk` (`propext`, `Classical.choice`), `trustCompilerOk` and
`ofReduceAxOk`, then the install. The steps: `findTagP` (a stored constant at a pinned name, of a tag),
`fieldP` (a count), `pinP`/`pinCtorP` (a pin interned, its plain interning the twin's `internCV`/`internCI`
with the scratch tier off), `cmpEP`/`cmpRP` (`matchesPin`, by handle equality), `stdInstP` (the install).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Decl
open ConPanqueque.T.Lit ConPanqueque.Logic.PlainIntern

section
variable {σ : Type}

/-! ## Small steps -/

theorem get_head (Γ : Env) (x : MlS) (w : BitVec 64) : Env.get ((x, w) :: Γ) x = some w := by simp

theorem sev_ecell {Γ : Env} {e : ExpHOL 64} {C : Ctx} {o : Nat} (h : sev Γ e = some (ecell C o)) (c : BitVec 64)
    (k : Nat) (hc : c = BitVec.ofNat 64 (8 * k)) : sev Γ (.op .add [e, .const c]) = some (ecell C (o + k)) := by
  simp [sev, h, hc, ecell_addk]

theorem sev_cellA {Γ : Env} {e : ExpHOL 64} {C : Ctx} {o : Nat} (h : sev Γ e = some (cellA C o)) (c : BitVec 64)
    (k : Nat) (hc : c = BitVec.ofNat 64 (8 * k)) : sev Γ (.op .add [e, .const c]) = some (cellA C (o + k)) := by
  have : cellA C o + BitVec.ofNat 64 (8 * k) = cellA C (o + k) := by
    unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega
  simp [sev, h, hc, this]

theorem sev_vvG {Γ : Env} {x : MlS} {w : BitVec 64} (h : Γ.get x = some w) : sev Γ (vv x) = some w := by
  simp [sev_vv, h]

/-- `if x ≠ n then hang` (a constant): past it the word is `n`. -/
theorem specR_guardNeC {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (a : BitVec 64) (n : Nat)
    (ha : Γ.get x = some a) (hk : a = BitVec.ofNat 64 n → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .notEqual (vv x) (.const (BitVec.ofNat 64 n))) hang rest) s m R := by
  by_cases e : a = BitVec.ofNat 64 n
  · subst e
    exact specR_ifI _ 0 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => hk rfl)
  · exact specR_ifI _ 1 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))

theorem cie_tag0 {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci)
    (ht : H[o]? = some (BitVec.ofNat 64 0)) : ∃ v, ci = .axiomInfo v := by
  obtain ⟨-, h2⟩ := h
  cases ci with
  | axiomInfo v => exact ⟨v, rfl⟩
  | defnInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | thmInfo => rw [h2] at ht; exact absurd ht (by decide)
  | indInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | ctorInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | recInfo => rw [h2.1] at ht; exact absurd ht (by decide)

theorem cie_tag3 {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci)
    (ht : H[o]? = some (BitVec.ofNat 64 3)) : ∃ v caps, ci = .indInfo v caps := by
  obtain ⟨-, h2⟩ := h
  cases ci with
  | indInfo v caps => exact ⟨v, caps, rfl⟩
  | axiomInfo => rw [h2] at ht; exact absurd ht (by decide)
  | defnInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | thmInfo => rw [h2] at ht; exact absurd ht (by decide)
  | ctorInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | recInfo => rw [h2.1] at ht; exact absurd ht (by decide)

theorem cie_tag4 {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci)
    (ht : H[o]? = some (BitVec.ofNat 64 4)) : ∃ v np nf T, ci = .ctorInfo v np nf T := by
  obtain ⟨-, h2⟩ := h
  cases ci with
  | ctorInfo v np nf T => exact ⟨v, np, nf, T, rfl⟩
  | axiomInfo => rw [h2] at ht; exact absurd ht (by decide)
  | defnInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | thmInfo => rw [h2] at ht; exact absurd ht (by decide)
  | indInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | recInfo => rw [h2.1] at ht; exact absurd ht (by decide)

theorem cie_tag5 {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci)
    (ht : H[o]? = some (BitVec.ofNat 64 5)) : ∃ v mi rp k rs, ci = .recInfo v mi rp k rs := by
  obtain ⟨-, h2⟩ := h
  cases ci with
  | recInfo v mi rp k rs => exact ⟨v, mi, rp, k, rs, rfl⟩
  | axiomInfo => rw [h2] at ht; exact absurd ht (by decide)
  | defnInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | thmInfo => rw [h2] at ht; exact absurd ht (by decide)
  | indInfo => rw [h2.1] at ht; exact absurd ht (by decide)
  | ctorInfo => rw [h2.1] at ht; exact absurd ht (by decide)

/-- A small count read back. -/
theorem natE_eq {H : List (BitVec 64)} {i n k : Nat} (h : NatE H i n) (w : BitVec 64) (hw : H[i]? = some w)
    (hk : k < 2 ^ 63) (he : w = BitVec.ofNat 64 k) : n = k := by
  rw [h.1] at hw
  have : BitVec.ofNat 64 n = BitVec.ofNat 64 k := (Option.some.inj hw).trans he
  exact (UD.ofNat_eq_iff_small n k (by have := h.2; omega) (by omega)).mp this

/-- **A stored constant at pin `i`'s name of tag `tg`**, else a hang. -/
theorem specR_findTagI {α : Type} {C : Ctx} (hok : CtxOK C)
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (i tg : Nat) (hi : i < pinCount)
    (hD : kqF ∈ D ∧ kqG ∈ D ∧ kqE ∈ D) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ ci o (Γ' : Env), C.fe.find? C.pins.names[i]! = some ci → CIE C.EB C.EH o ci →
      C.EH[o]? = some (BitVec.ofNat 64 tg) → Γ'.get kqG = some (ecell C o) →
      (∀ y, y ≠ kqF → y ≠ kqG → y ≠ kqE → Γ'.get y = Γ.get y) →
      SpecR (Inv C s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (findTagP C i tg rest) s m R := by
  have hi' : i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
  unfold findTagP
  refine specR_envLoadI kqF _ (C.PO + i) _ hD.1 rfl (hok.pinsRel.2.1 i hi') ?_
  refine specR_envFindI hok hcG hcP kqF (vv kqF) C.pins.names[i] hD.1 (by simp [sev, Env.get_cons])
    (by rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide))]; exact hkb) ?_
  have hrel := find_rel hok C.pins.names[i]
  have hb : C.pins.names[i]! = C.pins.names[i] := by simp [hi']
  revert hrel
  rcases hfn : C.fe.find? C.pins.names[i] with _ | ci0
  · intro hrel
    simp only at hrel
    rw [hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  · intro ⟨o', hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI kqG _ (ecell C o') hD.2.1 (by simp [sev, optWG, Env.get_cons, BitVec.add_sub_cancel]) ?_
    have hlt := cie_lt hci
    refine specR_envLoadI kqE (vv kqG) o' _ hD.2.2 (by simp [sev_vv, Env.get_cons])
      (List.getElem?_eq_getElem hlt) ?_
    refine specR_guardNeC kqE _ tg (get_head _ _ _) (fun htg => ?_)
    refine hk ci0 o' _ (by rw [hb, hfn]) hci (by rw [List.getElem?_eq_getElem hlt, htg])
      (by simp +decide [Env.get_cons]) (fun y h1 h2 h3 => ?_)
    simp only [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e h1), ite_eq_right_iff.mpr (fun e => absurd e h2),
      ite_eq_right_iff.mpr (fun e => absurd e h3)]

/-- **A stored count**: word `k` of the stored constant is `n`, else a hang. -/
theorem specR_fieldI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (k n o : Nat) (w : BitVec 64) (hD : kqE ∈ D)
    (hg : Γ.get kqG = some (ecell C o)) (hw : C.EH[o + k]? = some w)
    (hk : w = BitVec.ofNat 64 n → SpecR (Inv C s ((kqE, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (fieldP k n rest) s m R := by
  unfold fieldP
  refine specR_envLoadI kqE _ (o + k) w hD (by simp [sev, sev_vv, hg, ecell_addk]) hw ?_
  exact specR_guardNeC kqE w n (get_head _ _ _) hk

theorem cellA_add16 (C : Ctx) (k : Nat) : cellA C k + 16 = cellA C (k + 2) := by
  rw [show (16 : BitVec 64) = 8 + 8 from rfl, ← BitVec.add_assoc, cellA_add8, cellA_add8]

/-- Two constant values with equal handles. -/
theorem cv_eq_of {v p : IConstantVal} (h1 : v.name = p.name) (h2 : v.levelParams = p.levelParams)
    (h3 : v.type = p.type) : v = p := by
  cases v; cases p; simp_all

/-- The level parameters, read back: `L` of them (`L ≤ 1`), the one handle compared with `qX`. -/
theorem lps_eq_of {a b : List NIdx} {L : Nat} (ha : a.length = L) (hb : b.length = L) (hL : L = 0) : a = b := by
  subst hL; rw [List.length_eq_zero_iff] at ha hb; rw [ha, hb]

/-- **A stored constant is the pin** (`matchesPin`), else a hang. -/
theorem specR_cmpEI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (L : Nat) (hL : L ≤ 1) (o : Nat) (v p : IConstantVal)
    (hD : kdN ∈ D ∧ kqA ∈ D ∧ kqLn ∈ D ∧ kqB ∈ D ∧ kqT2 ∈ D)
    (hg : Γ.get kqG = some (ecell C o)) (hcv : CVE C.EB C.EH (o + 1) v) (hp : PinS Γ p)
    (hpl : p.levelParams.length = L)
    (hk : ∀ Γ' : Env, v = p → (∀ y, y ≠ kdN → y ≠ kqA → y ≠ kqLn → y ≠ kqB → y ≠ kqT2 → Γ'.get y = Γ.get y) →
      SpecR (Inv C s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (cmpEP L rest) s m R := by
  obtain ⟨hn, ⟨w, hw, o', hwo, hblk⟩, ht⟩ := hcv
  obtain ⟨hpN, hpL, hpT⟩ := hp
  unfold cmpEP cmpP
  refine specR_fact (fun t ht => ht.sr.env.1.len) (fun hlen => ?_)
  refine specR_fact (fun t ht => ht.sr.env.1.lay) (fun hlay => ?_)
  refine specR_envLoadI kdN _ (o + 1) _ hD.1 (sev_ecell (sev_vvG hg) 8 1 rfl) hn ?_
  refine specR_guardNe kdN qN _ _ (get_head _ _ _) (by rw [Env.get_cons, if_neg (by decide)]; exact hpN) (fun e1 => ?_)
  refine specR_envLoadI kqA _ (o + 1 + 1) w hD.2.1 (sev_ecell (sev_ecell (sev_vvG (by simp [Env.get_cons]; exact hg)) 8 1 rfl) 8 1 rfl) hw ?_
  refine specR_envLoadI kqLn (vv kqA) o' _ hD.2.2.1 (by simp [sev_vv, hwo]; rfl) hblk.1 ?_
  have hlb : (v.levelParams.map Enc.idxW).length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos (v.levelParams.map Enc.idxW).length with h0 | hpos
    · omega
    · have h1 := hblk.2 ((v.levelParams.map Enc.idxW).length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  refine specR_guardNeC kqLn _ L (get_head _ _ _) (fun e2 => ?_)
  have hvl : v.levelParams.length = L := by
    have := (UD.ofNat_eq_iff_small _ L (by omega) (by omega)).mp e2
    simpa using this
  have en : v.name = p.name := Enc.idxW_inj e1
  -- the level parameters
  have hlps : ∀ (Γ1 : Env), (∀ y, y ≠ kdN → y ≠ kqA → y ≠ kqLn → Γ1.get y = Γ.get y) →
      Γ1.get kqA = some w →
      SpecR (Inv C s Γ1 [] D) (lps1P L (.seq (.assign .local kqT2 (.load .one
        (.op .add [.op .add [vv kqG, .const 8], .const 16]))) (.ite (.cmp .notEqual (vv kqT2) (vv qT)) hang rest)))
        s m R := by
    intro Γ1 g1 hA1
    have hfin : ∀ (Γ2 : Env), (∀ y, y ≠ kdN → y ≠ kqA → y ≠ kqLn → y ≠ kqB → Γ2.get y = Γ.get y) →
        v.levelParams = p.levelParams →
        SpecR (Inv C s Γ2 [] D) (.seq (.assign .local kqT2 (.load .one
          (.op .add [.op .add [vv kqG, .const 8], .const 16]))) (.ite (.cmp .notEqual (vv kqT2) (vv qT)) hang rest))
          s m R := by
      intro Γ2 g2 el
      refine specR_envLoadI kqT2 _ (o + 1 + 2) _ hD.2.2.2.2
        (sev_ecell (sev_ecell (sev_vvG (by rw [g2 kqG (by decide) (by decide) (by decide) (by decide)]; exact hg)) 8 1 rfl) 16 2 rfl) ht ?_
      refine specR_guardNe kqT2 qT _ _ (get_head _ _ _)
        (by simp only [Env.get_cons]; rw [if_neg (by decide), g2 qT (by decide) (by decide) (by decide) (by decide)];
            exact hpT) (fun e3 => ?_)
      refine hk _ (cv_eq_of en el (Enc.idxW_inj e3)) (fun y h1 h2 h3 h4 h5 => ?_)
      rw [Env.get_cons, if_neg h5]; exact g2 y h1 h2 h3 h4
    rcases Nat.lt_or_ge L 1 with hL0 | hL1
    · have hL0' : L = 0 := by omega
      subst hL0'
      exact hfin Γ1 (fun y h1 h2 h3 _ => g1 y h1 h2 h3) (lps_eq_of hvl hpl rfl)
    · have hL1' : L = 1 := by omega
      subst hL1'
      obtain ⟨a, ha⟩ : ∃ a, v.levelParams = [a] := by
        match h : v.levelParams, hvl with
        | [a], _ => exact ⟨a, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, p.levelParams = [b] := by
        match h : p.levelParams, hpl with
        | [b], _ => exact ⟨b, rfl⟩
      have hpX : Γ.get qX = some (Enc.idxW b) := by
        have := hpL; rw [hb] at this; exact this
      simp only [lps1P]
      have hA0 := hblk.2 0 (by simp [ha])
      simp only [ha, List.map_cons, List.map_nil, List.getElem_cons_zero, Nat.add_zero] at hA0
      refine specR_envLoadI kqB _ (o' + 1) _ hD.2.2.2.1 (sev_ecell (sev_vvG (by rw [hA1, hwo]; rfl)) 8 1 rfl) hA0 ?_
      refine specR_guardNe kqB qX _ _ (get_head _ _ _)
        (by simp only [Env.get_cons]; rw [if_neg (by decide), g1 qX (by decide) (by decide) (by decide)]; exact hpX)
        (fun e4 => ?_)
      refine hfin _ (fun y h1 h2 h3 h4 => ?_) (by rw [ha, hb, Enc.idxW_inj e4])
      rw [Env.get_cons, if_neg h4]; exact g1 y h1 h2 h3
  refine hlps _ (fun y h1 h2 h3 => ?_) ?_
  · rw [Env.get_cons, if_neg h3, Env.get_cons, if_neg h2, Env.get_cons, if_neg h1]
  · rw [Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl]

/-- **The record is the pin** (`matchesPin`), else a hang. -/
theorem specR_cmpRI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (L : Nat) (hL : L ≤ 1) (q ol : Nat) (v p : IConstantVal)
    (hD : kdN ∈ D ∧ kqA ∈ D ∧ kqLn ∈ D ∧ kqB ∈ D ∧ kqT2 ∈ D) (hq : Γ.get kdQ = some (cellA C q))
    (hn : C.H[q]? = some (Enc.idxW v.name)) (hl : C.H[q + 1]? = some (cellA C ol))
    (ht : C.H[q + 2]? = some (Enc.idxW v.type)) (hblk : BlkAt C.H ol (v.levelParams.map Enc.idxW))
    (hlen : v.levelParams.length < 2 ^ 59) (hp : PinS Γ p) (hpl : p.levelParams.length = L)
    (hk : ∀ Γ' : Env, v = p → (∀ y, y ≠ kdN → y ≠ kqA → y ≠ kqLn → y ≠ kqB → y ≠ kqT2 → Γ'.get y = Γ.get y) →
      SpecR (Inv C s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (cmpRP L rest) s m R := by
  obtain ⟨hpN, hpL, hpT⟩ := hp
  unfold cmpRP cmpP
  refine UD.specR_heapLoadI' kdN _ q _ hn hD.1 (sev_vvG hq) ?_
  refine specR_guardNe kdN qN _ _ (get_head _ _ _) (by rw [Env.get_cons, if_neg (by decide)]; exact hpN) (fun e1 => ?_)
  refine UD.specR_heapLoadI' kqA _ (q + 1) _ hl hD.2.1 (sev_cellA (sev_vvG (by simp [Env.get_cons]; exact hq)) 8 1 rfl) ?_
  refine UD.specR_heapLoadI' kqLn (vv kqA) ol _ hblk.1 hD.2.2.1 (sev_vvG (get_head _ _ _)) ?_
  refine specR_guardNeC kqLn _ L (get_head _ _ _) (fun e2 => ?_)
  have hvl : v.levelParams.length = L := by
    have := (UD.ofNat_eq_iff_small _ L (by simp; omega) (by omega)).mp e2
    simpa using this
  have en : v.name = p.name := Enc.idxW_inj e1
  have hlps : ∀ (Γ1 : Env), (∀ y, y ≠ kdN → y ≠ kqA → y ≠ kqLn → Γ1.get y = Γ.get y) →
      Γ1.get kqA = some (cellA C ol) →
      SpecR (Inv C s Γ1 [] D) (lps1P L (.seq (.assign .local kqT2 (.load .one
        (.op .add [vv kdQ, .const 16]))) (.ite (.cmp .notEqual (vv kqT2) (vv qT)) hang rest)))
        s m R := by
    intro Γ1 g1 hA1
    have hfin : ∀ (Γ2 : Env), (∀ y, y ≠ kdN → y ≠ kqA → y ≠ kqLn → y ≠ kqB → Γ2.get y = Γ.get y) →
        v.levelParams = p.levelParams →
        SpecR (Inv C s Γ2 [] D) (.seq (.assign .local kqT2 (.load .one
          (.op .add [vv kdQ, .const 16]))) (.ite (.cmp .notEqual (vv kqT2) (vv qT)) hang rest))
          s m R := by
      intro Γ2 g2 el
      refine UD.specR_heapLoadI' kqT2 _ (q + 2) _ ht hD.2.2.2.2
        (sev_cellA (sev_vvG (by rw [g2 kdQ (by decide) (by decide) (by decide) (by decide)]; exact hq)) 16 2 rfl) ?_
      refine specR_guardNe kqT2 qT _ _ (get_head _ _ _)
        (by simp only [Env.get_cons]; rw [if_neg (by decide), g2 qT (by decide) (by decide) (by decide) (by decide)];
            exact hpT) (fun e3 => ?_)
      refine hk _ (cv_eq_of en el (Enc.idxW_inj e3)) (fun y h1 h2 h3 h4 h5 => ?_)
      rw [Env.get_cons, if_neg h5]; exact g2 y h1 h2 h3 h4
    rcases Nat.lt_or_ge L 1 with hL0 | hL1
    · have hL0' : L = 0 := by omega
      subst hL0'
      exact hfin Γ1 (fun y h1 h2 h3 _ => g1 y h1 h2 h3) (lps_eq_of hvl hpl rfl)
    · have hL1' : L = 1 := by omega
      subst hL1'
      obtain ⟨a, ha⟩ : ∃ a, v.levelParams = [a] := by
        match h : v.levelParams, hvl with
        | [a], _ => exact ⟨a, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, p.levelParams = [b] := by
        match h : p.levelParams, hpl with
        | [b], _ => exact ⟨b, rfl⟩
      have hpX : Γ.get qX = some (Enc.idxW b) := by
        have := hpL; rw [hb] at this; exact this
      simp only [lps1P]
      have hA0 := hblk.2 0 (by simp [ha])
      simp only [ha, List.map_cons, List.map_nil, List.getElem_cons_zero, Nat.add_zero] at hA0
      refine UD.specR_heapLoadI' kqB _ (ol + 1) _ hA0 hD.2.2.2.1 (sev_cellA (sev_vvG hA1) 8 1 rfl) ?_
      refine specR_guardNe kqB qX _ _ (get_head _ _ _)
        (by simp only [Env.get_cons]; rw [if_neg (by decide), g1 qX (by decide) (by decide) (by decide)]; exact hpX)
        (fun e4 => ?_)
      refine hfin _ (fun y h1 h2 h3 h4 => ?_) (by rw [ha, hb, Enc.idxW_inj e4])
      rw [Env.get_cons, if_neg h4]; exact g1 y h1 h2 h3
  refine hlps _ (fun y h1 h2 h3 => ?_) ?_
  · rw [Env.get_cons, if_neg h3, Env.get_cons, if_neg h2, Env.get_cons, if_neg h1]
  · rw [Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl]

/-! ## The pins -/

theorem keep_q {Γ Γ' : Env} (ha : AgreeQ ((ocD, 0) :: (ocC, 0) :: (ocB, 0) :: (ocA, 0) :: Γ) Γ') :
    ∀ y, y = kdQ ∨ y = lKb ∨ y = kqG → Γ'.get y = Γ.get y := by
  intro y hy
  have hg : ∀ c j, y ≠ gv c j := by
    rcases hy with rfl | rfl | rfl
    · exact fun c j e => gv_ne_of (m := kdQ) (by simp [kdQ, ofString]) e.symm
    · exact fun c j e => gv_ne_of (m := lKb) (by simp [lKb, ofString]) e.symm
    · exact fun c j e => gv_ne_of (m := kqG) (by simp [kqG, ofString]) e.symm
  rw [ha y hg (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide)
    (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide)
    (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide)
    (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide)]
  rw [Env.get_cons, if_neg (by rcases hy with rfl | rfl | rfl <;> decide), Env.get_cons,
    if_neg (by rcases hy with rfl | rfl | rfl <;> decide), Env.get_cons,
    if_neg (by rcases hy with rfl | rfl | rfl <;> decide), Env.get_cons,
    if_neg (by rcases hy with rfl | rfl | rfl <;> decide)]

theorem internCV_of_plain {cv : ConLeche.ConstantVal} {s s' : AState} {r : IConstantVal}
    (ho : InternRerun.Off s.store) (h : plainCV cv s = .ok (r, s')) : ConRon.Arena.internCV cv s = .ok (r, s') := by
  obtain ⟨-, m', e, -⟩ := internCV_plain cv ∅ s r s' ho (memoOK_empty s) h
  unfold ConRon.Arena.internCV
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e]

theorem internCI_of_plain {ci : ConLeche.ConstantInfo} {s s' : AState} {r : IConstantInfo}
    (ho : InternRerun.Off s.store) (h : plainCI ci s = .ok (r, s')) : ConRon.Arena.internCI ci s = .ok (r, s') := by
  obtain ⟨-, m', e, -⟩ := internCI_plain ci ∅ s r s' ho (memoOK_empty s) h
  unfold ConRon.Arena.internCI
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e]

/-- **A standard pin `internCV`'d** (the scratch tier off, else a hang). -/
theorem specR_pinI (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} (G : GenEnv C D 12)
    (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) (hoc : ocA ∈ D ∧ ocB ∈ D ∧ ocC ∈ D ∧ ocD ∈ D)
    (cv : ConLeche.ConstantVal) (hcv : CVLit 0 12 cv) (hl : cv.levelParams.length ≤ 1)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantVal → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H', H0 <+: H' → (∀ y, y = kdQ ∨ y = lKb ∨ y = kqG → Γ'.get y = Γ.get y) →
      plainCV cv s = .ok (r, s') → PinS Γ' r → r.levelParams.length = cv.levelParams.length →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (pinP C cv rest) s (ConRon.Arena.internCV cv >>= k) R := by
  unfold pinP
  refine specR_offCheckI hoc (fun ho => ?_)
  refine specR_okImp (m' := plainCV cv >>= k) (fun a s' h => ?_) ?_
  · obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok h
    exact bind_ok_of (internCV_of_plain ho h1) h2
  exact genSCV_spec ra G hq cv hcv hl H0 rest _ M s (fun r s' Γ' H' hp ag hr hP hlr =>
    hk r s' Γ' H' hp (keep_q ag) hr hP hlr)

/-- **A standard pin `internCI`'d** whose extra parts intern nothing. -/
theorem specR_pinCII (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} (G : GenEnv C D 12)
    (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) (hoc : ocA ∈ D ∧ ocB ∈ D ∧ ocC ∈ D ∧ ocD ∈ D)
    (ci : ConLeche.ConstantInfo) (f : IConstantVal → IConstantInfo)
    (hf : ∀ s r s', plainCV ci.toConstantVal s = .ok (r, s') → plainCI ci s = .ok (f r, s'))
    (hcv : CVLit 0 12 ci.toConstantVal) (hl : ci.toConstantVal.levelParams.length ≤ 1)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H', H0 <+: H' → (∀ y, y = kdQ ∨ y = lKb ∨ y = kqG → Γ'.get y = Γ.get y) →
      plainCV ci.toConstantVal s = .ok (r, s') → PinS Γ' r →
      r.levelParams.length = ci.toConstantVal.levelParams.length →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k (f r)) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (pinP C ci.toConstantVal rest) s (ConRon.Arena.internCI ci >>= k) R := by
  unfold pinP
  refine specR_offCheckI hoc (fun ho => ?_)
  refine specR_okImp (m' := plainCV ci.toConstantVal >>= fun r => k (f r)) (fun a s' h => ?_) ?_
  · obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok h
    exact bind_ok_of (internCI_of_plain ho (hf s r s1 h1)) h2
  exact genSCV_spec ra G hq _ hcv hl H0 rest _ M s (fun r s' Γ' H' hp ag hr hP hlr =>
    hk r s' Γ' H' hp (keep_q ag) hr hP hlr)

/-- **A constructor pin `internCI`'d**: its value, then its inductive's name. -/
theorem specR_pinCtorI (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} (G : GenEnv C D 12)
    (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D) (hoc : ocA ∈ D ∧ ocB ∈ D ∧ ocC ∈ D ∧ ocD ∈ D)
    (ci : ConLeche.ConstantInfo) (v : ConLeche.ConstantVal) (np nf : Nat) (T : ConLeche.Name)
    (hci : ci = .ctorInfo v np nf T) (hcv : CVLit 0 12 v) (hT : NameLit T)
    (hl : v.levelParams.length ≤ 1)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r t s' Γ' H', H0 <+: H' → (∀ y, y = kdQ ∨ y = lKb ∨ y = kqG → Γ'.get y = Γ.get y) →
      PinS Γ' r → r.levelParams.length = v.levelParams.length →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k (.ctorInfo r np nf t)) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (pinCtorP C v T rest) s
      (ConRon.Arena.internCI ci >>= k) R := by
  subst hci
  unfold pinCtorP
  refine specR_offCheckI hoc (fun ho => ?_)
  refine specR_okImp (m' := plainCI (.ctorInfo v np nf T) >>= k) (fun a s' h => ?_) ?_
  · obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok h
    exact bind_ok_of (internCI_of_plain ho h1) h2
  simp only [plainCI, bind_assoc]
  refine genSCV_spec ra G hq v hcv hl H0 _ _ M s (fun r s1 Γ1 H1 hp1 ag1 hr1 hP1 hlr1 => ?_)
  refine name_stepP ra G T hT H1 rest Γ1 [] s1 (fun t s2 Γ2 hf2 hv2 hr2 => ?_)
  simp only [pure_bind]
  have hk1 := keep_q ag1
  obtain ⟨hpN, hpL, hpT⟩ := hP1
  have hf' : ∀ y, y ≠ ConPanqueque.Start.vPn → y ≠ ConPanqueque.Start.vKa → Γ2.get y = Γ1.get y := hf2
  refine hk r t s2 Γ2 H1 hp1 (fun y hy => by
      rw [hf2 y (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide)]
      exact hk1 y hy) ⟨by rw [hf' qN (by decide) (by decide)]; exact hpN, ?_,
      by rw [hf' qT (by decide) (by decide)]; exact hpT⟩ hlr1
  · revert hpL
    match r.levelParams with
    | [] => exact fun _ => trivial
    | [h] => exact fun hx => by show _ = _; rw [hf' qX (by decide) (by decide)]; exact hx
    | _ :: _ :: _ => exact fun h => h.elim

/-! ## The install -/

/-- The twin's tail past the flush at an axiom record: the reserved names. -/
def stdTail (cv : IConstantVal) (fe₂ : IFEnv) : AM IFEnv := do
  let b ← basisNamesOk (.axiomDecl cv)
  if b = true then pure fe₂ else do
    let e ← basisNamesError (.axiomDecl cv)
    fail e

theorem basisNamesOk_ax {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (cv : IConstantVal)
    (hnq : cv.name ≠ C.pins.names[PIN_QUOT_SOUND]!) :
    basisNamesOk (.axiomDecl cv) s = .ok (!C.pins.reserved.contains cv.name, s) := by
  have hqs : PIN_QUOT_SOUND < C.pins.names.size := by rw [hok.pinsRel.1]; decide
  have hq' : (cv.name == C.pins.names[PIN_QUOT_SOUND]) = false := by
    have : C.pins.names[PIN_QUOT_SOUND]! = C.pins.names[PIN_QUOT_SOUND] := by simp [hqs]
    rw [this] at hnq; simpa using hnq
  have hu := basisUnres_run hok hp cv.name
  simp only [basisNamesOk, pinQuotSound, pinAt]
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, Except.bind, pure, StateT.pure, Except.pure]
  simp only [hp, hqs, dite_true, StateT.pure, pure, Except.pure]
  simp only [hq', Bool.false_eq_true, if_false]
  exact hu

set_option maxHeartbeats 4000000 in
/-- **The reserved names, freshness, the install, the flags, the flush.** -/
theorem stdInst_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (hnq : cv.name ≠ C.pins.names[PIN_QUOT_SOUND]!)
    (H0 : List (BitVec 64)) (hH0 : C.H <+: H0) (s : AState) (Γ : Env) (hB : Base C q Γ) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (stdInstP C) s
      (flushCaches >>= fun _ => stdTail cv (C.fe.push (.axiomInfo cv))) (PostStep C) := by
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := hrc
  have hD : ∀ x ∈ kqLocals, x ∈ ctxLocals ++ kqLocals := fun x hx => List.mem_append_right _ hx
  have hokH := ctxOK_H hok H0
  unfold stdInstP
  refine UD.specR_heapLoadI' kdN (vv kdQ) q _ (get_prefix hn hH0) (hD _ (by simp [kqLocals])) (sev_vvG hB.1) ?_
  obtain ⟨wR, hwR, oR, hwoR, hblkR⟩ := hok.pinsRel.2.2.2.2.2.2
  have hblkR' : EBlk C.EH oR (C.pins.reserved.map Enc.idxW) := hblkR
  refine specR_envLoadI (C := ctxH C H0) kdL _ (C.PO + pinCount + 4) wR (hD _ (by simp [kqLocals])) rfl hwR ?_
  have hlR : (ctxH C H0).EH[oR]? = some (BitVec.ofNat 64 C.pins.reserved.length) := by
    have h := hblkR'.1; simp only [List.length_map] at h; exact h
  refine specR_envLoadI kdLn (vv kdL) oR _ (hD _ (by simp [kqLocals])) (by simp [Env.get, hwoR]; rfl) hlR ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hlenR : C.pins.reserved.length < 2 ^ 62 := by
    have hl2 : C.EH.length ≤ C.EN := ht5.sr.env.1.len
    have hlay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64 := hok.envLay
    rcases Nat.eq_zero_or_pos C.pins.reserved.length with h0 | hpos
    · omega
    · have h1 := hblkR'.2 (C.pins.reserved.length - 1) (by simp; omega)
      have hlt : oR + 1 + (C.pins.reserved.length - 1) < C.EH.length := (List.getElem?_eq_some_iff.mp h1).1
      omega
  refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H0) kdX fRsm rmParams
    [vv kdN, vv kdL, .const 0, vv kdLn] rsmBody
    [Enc.idxW cv.name, ecell C oR, BitVec.ofNat 64 0, BitVec.ofNat 64 C.pins.reserved.length]
    (C.pins.reserved.contains cv.name) (by decide) rfl (hD _ (by simp [kqLocals])) hc.d.rsm
    ⟨by simp +decide [Env.get], by simp [Env.get, hwoR]; rfl, rfl, by simp +decide [Env.get], trivial⟩
    (PostB (ctxH C H0)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk)
      (rsm_spec (ctxH C H0) hc.d.rsm C.pins.reserved oR hblkR' hlenR cv.name _ _ 0
        (ctxH C H0).H (List.prefix_refl _) rfl (Nat.zero_le _)))
    (fun w H6 hp6 hw => ?_)
  subst hw
  have hp06 : C.H <+: H6 := hH0.trans hp6
  refine specR_guardNZ kdX _ (get_head _ _ _) (fun h0 => ?_)
  have hres : C.pins.reserved.contains cv.name = false := by
    cases e : C.pins.reserved.contains cv.name
    · rfl
    · rw [e] at h0; exact absurd h0 (by decide)
  have hok6 := ctxOK_H hok H6
  refine specR_envFindI hok6 hc.d.k.g hc.d.k.p kqF (vv kdN) cv.name (hD _ (by simp [kqLocals]))
    (by simp +decide [sev_vv, Env.get_cons]) (by simp +decide [Env.get_cons]; exact hB.2) ?_
  have hrel := find_rel hok6 cv.name
  revert hrel
  rcases hfn : (ctxH C H6).fe.find? cv.name with _ | ci0
  swap
  · intro ⟨o', hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    exact specR_guardNZ kqF (optWG id (some (ecell (ctxH C H6) o'))) (get_head _ _ _)
      (fun h => absurd h (show ecell (ctxH C H6) o' + 1 ≠ 0 from ecell_succ_ne hok6 hoE))
  intro hrel
  simp only at hrel
  rw [hrel]
  refine specR_guardNZ kqF (optWG id none) (get_head _ _ _) (fun _ => ?_)
  refine specR_fact (fun t ht => ht.sr.floor) (fun hfl => ?_)
  have hden : NewDen (.axiomInfo cv) s.store := by
    refine ⟨fun n hn' => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn'
      exact Option.isSome_iff_exists.mpr ⟨_, denoteN_ext (hks j hj) hfl⟩
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp htyD
      show (denoteE s.store cv.type).isSome = true
      rw [denote_ext hx hfl]; rfl
    · show cv.levelParams.length + 1 < 2 ^ 60; omega
    · intro _ _ _ e; cases e
    · intro _ _ e; cases e
  have hT : ∀ (fe : IFEnv) (s' : AState), s'.pins = C.pins → stdTail cv fe s' = .ok (fe, s') := by
    intro fe s' hp'
    unfold stdTail
    rw [bind_run_of (basisNamesOk_ax hok hp' cv hnq), hres]
    rfl
  show SpecR (Inv (ctxE (ctxH C H6) C.EH) _ _ _ _) _ _ _ _
  refine instQcall_spec mode C hok hc hpl hg hF hL H6 C.EH hp06 (List.prefix_refl _)
    s _ (.axiomInfo cv) q ol (get_prefix hn hp06) (get_prefix hl hp06) (get_prefix ht hp06) (blkAt_mono hb hp06)
    (by show cv.levelParams.length < 2 ^ 60; omega)
    [.const 0, vv kdQ, .const 0, .const 0, .const 0, .const 0, .const 0, .const 0] 0 0 0 0 0 0 0
    ⟨rfl, by simp +decide [Env.get_cons]; exact hB.1, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
    (fun EH ox b hpE hlay => ?_) hfn hden (fun _ _ _ _ _ e => by cases e) (stdTail cv) hT
  obtain ⟨h1, h2, h3, hw, hbl⟩ := hlay
  exact ⟨⟨h1, ⟨ecell C b, h2, b, rfl, hbl⟩, h3⟩, hw 0 (by simp)⟩

theorem Decl.cmpEq_idxW_t' {a b : NIdx} (h : a = b) :
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (Enc.idxW a) (Enc.idxW b) = true := by
  subst h; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem Decl.cmpEq_idxW_f' {a b : NIdx} (h : a ≠ b) :
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (Enc.idxW a) (Enc.idxW b) = false := by
  have : Enc.idxW a ≠ Enc.idxW b := fun e => h (Enc.idxW_inj e)
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]

/-! ## The pins' literals -/

theorem lit_trueCvA : CVLit 0 12 ConLeche.trueCvA := cvLit_of (by decide)
theorem lit_trueIntroCvA : CVLit 0 12 ConLeche.trueIntroCvA := cvLit_of (by decide)
theorem lit_trustCompilerA : CVLit 0 12 ConLeche.trustCompilerA := cvLit_of (by decide)
theorem lit_iffA : CVLit 0 12 ConLeche.iffA.toConstantVal := cvLit_of (by decide)
theorem lit_iffIntroA : CVLit 0 12 ConLeche.iffIntroA.toConstantVal := cvLit_of (by decide)
theorem lit_iffRecA : CVLit 0 12 ConLeche.iffRecA.toConstantVal := cvLit_of (by decide)
theorem lit_propextA : CVLit 0 12 ConLeche.propextA := cvLit_of (by decide)
theorem lit_nonemptyA : CVLit 0 12 ConLeche.nonemptyA.toConstantVal := cvLit_of (by decide)
theorem lit_nonemptyIntroA : CVLit 0 12 ConLeche.nonemptyIntroA.toConstantVal := cvLit_of (by decide)
theorem lit_nonemptyRecA : CVLit 0 12 ConLeche.nonemptyRecA.toConstantVal := cvLit_of (by decide)
theorem lit_choiceA : CVLit 0 12 ConLeche.choiceA := cvLit_of (by decide)
theorem lit_natA : CVLit 0 12 ConLeche.natA.toConstantVal := cvLit_of (by decide)
theorem lit_boolCvA : CVLit 0 12 ConLeche.boolCvA := cvLit_of (by decide)
theorem lit_reduceNatCvA : CVLit 0 12 ConLeche.reduceNatCvA := cvLit_of (by decide)
theorem lit_reduceBoolCvA : CVLit 0 12 ConLeche.reduceBoolCvA := cvLit_of (by decide)
theorem lit_ofReduceNatA : CVLit 0 12 ConLeche.ofReduceNatA := cvLit_of (by decide)
theorem lit_ofReduceBoolA : CVLit 0 12 ConLeche.ofReduceBoolA := cvLit_of (by decide)
theorem lit_iffName : NameLit ConLeche.iffName := nameLit_of (by decide)
theorem lit_nonemptyName : NameLit ConLeche.nonemptyName := nameLit_of (by decide)

theorem plainCI_ind_nil (v : ConLeche.ConstantVal) (c : ConLeche.IndCaps) (h1 : c.all = []) (h2 : c.ctors = [])
    (s : AState) (r : IConstantVal) (s' : AState)
    (h : plainCV (ConLeche.ConstantInfo.indInfo v c).toConstantVal s = .ok (r, s')) :
    plainCI (.indInfo v c) s = .ok (.indInfo r ⟨c.eta, [], c.nparams, c.nIdx, [], c.neverZero⟩, s') := by
  simp only [plainCI]
  refine bind_ok_of h ?_
  simp [Frontend.internCaps, h1, h2, Frontend.internNameList, bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure]

theorem plainCI_rec_nil (v : ConLeche.ConstantVal) (mi rp : Nat) (k : Bool) (s : AState) (r : IConstantVal)
    (s' : AState) (h : plainCV (ConLeche.ConstantInfo.recInfo v mi rp k []).toConstantVal s = .ok (r, s')) :
    plainCI (.recInfo v mi rp k []) s = .ok (.recInfo r mi rp k [], s') := by
  simp only [plainCI]
  refine bind_ok_of h ?_
  simp [plainRules, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

/-! ## The arms -/

theorem matchesPin_self (v : IConstantVal) : v.matchesPin v = pure true := by
  simp [IConstantVal.matchesPin]

theorem matchesPin_self_not {β : Type} (v : IConstantVal) (A B : AM β) :
    (v.matchesPin v >>= fun b => if (!b) = true then A else B) = B := by
  simp [IConstantVal.matchesPin]

theorem matchesPin_self_if {β : Type} (v : IConstantVal) (A B : AM β) :
    (v.matchesPin v >>= fun b => if b = true then A else B) = A := by
  simp [IConstantVal.matchesPin]

theorem base_of {C : Ctx} {q : Nat} {Γ Γ' : Env} (h : Base C q Γ) (h1 : Γ'.get kdQ = Γ.get kdQ)
    (h2 : Γ'.get lKb = Γ.get lKb) : Base C q Γ' := ⟨h1.trans h.1, h2.trans h.2⟩

/-- The locals the arms use. -/
structure StdD (D : List MlS) : Prop where
  f : kqF ∈ D ∧ kqG ∈ D ∧ kqE ∈ D
  c : kdN ∈ D ∧ kqA ∈ D ∧ kqLn ∈ D ∧ kqB ∈ D ∧ kqT2 ∈ D
  q : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D
  o : ocA ∈ D ∧ ocB ∈ D ∧ ocC ∈ D ∧ ocD ∈ D

theorem stdD : StdD (ctxLocals ++ kqLocals) := by
  have hD : ∀ x ∈ kqLocals, x ∈ ctxLocals ++ kqLocals := fun x hx => List.mem_append_right _ hx
  refine ⟨⟨hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals])⟩,
    ⟨hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]),
      hD _ (by simp [kqLocals])⟩, fun x hx => hD x ?_,
    ⟨hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals])⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [kqLocals]

theorem genEnv_kq {C : Ctx} (hok : CtxOK C) (hf : ConPanqueque.Front.FrontOK C)
    (hA : denoteN C.St.ns default = some .anonymous) (hc : ECodes C) : GenEnv C (ctxLocals ++ kqLocals) 12 :=
  have hD : ∀ x ∈ kqLocals, x ∈ ctxLocals ++ kqLocals := fun x hx => List.mem_append_right _ hx
  ⟨hok, hf, hA, hc, hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]),
    fun c hc' j hj => hD _ (List.mem_append_right _ (gv_mem_genLocals hc' hj))⟩

set_option maxHeartbeats 8000000 in
/-- **`Lean.trustCompiler`**: `trustCompilerOk`, then the install. -/
theorem stdTrust_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (hnq : cv.name ≠ C.pins.names[PIN_QUOT_SOUND]!)
    (H0 : List (BitVec 64)) (hH0 : C.H <+: H0) (s : AState) (Γ : Env) (hB : Base C q Γ) (F : AM IFEnv) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (stdP C 2) s
      (trustCompilerOk C.fe cv >>= fun b =>
        if b = true then (flushCaches >>= fun _ => stdTail cv (C.fe.push (.axiomInfo cv))) else F) (PostStep C) := by
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := id hrc
  have G := genEnv_kq hok hf hA hc.e
  have SD := stdD
  simp only [stdP]
  unfold trustCompilerOk trueName trueIntroName trueCvA trueIntroCvA trustCompilerA
  simp only [bind_assoc]
  refine specR_atEntry fun t0 ht0 => ?_
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_TRUE (by decide)) ?_
  refine specR_findTagI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_TRUE 3 (by decide) SD.f hB.2
    (fun ci o Γ1 hfind hcie htag hG1 g1 => ?_)
  obtain ⟨v1, caps1, rfl⟩ := cie_tag3 hcie htag
  have hfind' : C.fe.find? C.pins.names[PIN_TRUE]! = some (.indInfo v1 caps1) := hfind
  have hB1 : Base C q Γ1 := base_of hB (g1 _ (by decide) (by decide) (by decide)) (g1 _ (by decide) (by decide) (by decide))
  rw [hfind']
  simp only [bind_assoc]
  refine specR_pinI ra G SD.q SD.o _ lit_trueCvA (by decide) H0 _ Γ1 [] s
    (fun r1 s1 Γ2 H1 hp1 k2 hr1 hP1 hl1 => ?_)
  refine specR_cmpEI (C := ctxH C H1) 0 (by decide) o v1 r1 SD.c (by rw [k2 kqG (by simp)]; exact hG1) hcie.1 hP1
    (by rw [hl1]; rfl) (fun Γ3 e g3 => ?_)
  subst e
  simp only [matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  have hB3 : Base C q Γ3 := base_of hB1 ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (k2 _ (by simp))) ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (k2 _ (by simp)))
  have hp01 : C.H <+: H1 := hH0.trans hp1
  refine specR_atEntry fun t1 ht1 => ?_
  refine specR_runBind (pinAt_run hok ht1.sr.pins PIN_TRUE_INTRO (by decide)) ?_
  refine specR_findTagI (C := ctxH C H1) (ctxOK_H hok H1) hc.d.k.g hc.d.k.p PIN_TRUE_INTRO 4 (by decide) SD.f hB3.2
    (fun ci o2 Γ4 hfind2 hcie2 htag2 hG4 g4 => ?_)
  obtain ⟨v2, np2, nf2, T2, rfl⟩ := cie_tag4 hcie2 htag2
  have hfind2' : C.fe.find? C.pins.names[PIN_TRUE_INTRO]! = some (.ctorInfo v2 np2 nf2 T2) := hfind2
  have hB4 : Base C q Γ4 := base_of hB3 (g4 _ (by decide) (by decide) (by decide)) (g4 _ (by decide) (by decide) (by decide))
  obtain ⟨hcv2, -, hnp, hnf, -⟩ := hcie2
  refine specR_fieldI 4 0 o2 _ SD.f.2.2 hG4 hnp.1 (fun e4 => ?_)
  refine specR_fieldI 5 0 o2 _ SD.f.2.2 (by rw [Env.get_cons, if_neg (by decide)]; exact hG4) hnf.1 (fun e5 => ?_)
  have h4 := natE_eq hnp _ hnp.1 (by decide) e4
  have h5 := natE_eq hnf _ hnf.1 (by decide) e5
  subst h4 h5
  rw [hfind2']
  simp only [bind_assoc]
  refine specR_pinI ra G SD.q SD.o _ lit_trueIntroCvA (by decide) H1 _ _ [] s1
    (fun r2 s2 Γ5 H2 hp2 k5 hr2 hP2 hl2 => ?_)
  refine specR_cmpEI (C := ctxH C H2) 0 (by decide) o2 v2 r2 SD.c
    (by rw [k5 kqG (by simp), Env.get_cons, if_neg (by decide), Env.get_cons, if_neg (by decide)]; exact hG4)
    hcv2 hP2 (by rw [hl2]; rfl) (fun Γ6 e g6 => ?_)
  subst e
  simp only [matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  have hB6 : Base C q Γ6 := by
    refine base_of hB4 ?_ ?_
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide), k5 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide), k5 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
  have hp02 : C.H <+: H2 := hp01.trans hp2
  refine specR_pinI ra G SD.q SD.o _ lit_trustCompilerA (by decide) H2 _ _ [] s2
    (fun r3 s3 Γ7 H3 hp3 k7 hr3 hP3 hl3 => ?_)
  have hp03 : C.H <+: H3 := hp02.trans hp3
  refine specR_cmpRI (C := ctxH C H3) 0 (by decide) q ol cv r3 SD.c
    (by rw [k7 kdQ (by simp)]; exact hB6.1) (get_prefix hn hp03) (get_prefix hl hp03) (get_prefix ht hp03)
    (blkAt_mono hb hp03) (by omega) hP3 (by rw [hl3]; rfl) (fun Γ8 e g8 => ?_)
  subst e
  simp only [matchesPin_self, pure_bind, ↓reduceIte]
  have hB8 : Base C q Γ8 := by
    refine base_of hB6 ?_ ?_
    · rw [g8 _ (by decide) (by decide) (by decide) (by decide) (by decide), k7 _ (by simp)]
    · rw [g8 _ (by decide) (by decide) (by decide) (by decide) (by decide), k7 _ (by simp)]
  exact stdInst_spec mode C hok hc hpl hg hF hL cv q hrc hnq H3 hp03 s3 Γ8 hB8

set_option maxHeartbeats 8000000 in
/-- **`propext`**: `stdAxiomOk`, then the install. -/
theorem stdPropext_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (hnq : cv.name ≠ C.pins.names[PIN_QUOT_SOUND]!)
    (hpe : cv.name = C.pins.names[PIN_PROPEXT]!)
    (H0 : List (BitVec 64)) (hH0 : C.H <+: H0) (s : AState) (Γ : Env) (hB : Base C q Γ) (F : AM IFEnv) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (stdP C 0) s
      (stdAxiomOk C.fe cv >>= fun b =>
        if b = true then (flushCaches >>= fun _ => stdTail cv (C.fe.push (.axiomInfo cv))) else F) (PostStep C) := by
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := id hrc
  have G := genEnv_kq hok hf hA hc.e
  have SD := stdD
  simp only [stdP]
  unfold stdAxiomOk propextName eqStored iffName iffIntroName iffRecName iffA iffIntroA iffRecA propextA
  simp only [bind_assoc]
  refine specR_atEntry fun t0 ht0 => ?_
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_PROPEXT (by decide)) ?_
  simp only [← hpe, beq_self_eq_true, ↓reduceIte, bind_assoc]
  -- `Eq` stored
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_EQ (by decide)) ?_
  refine specR_predGuardI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_EQ (by decide) SD.f.1 hB.2
    (fun w w' heq => ?_)
  have heq' : (C.fe.find? C.pins.names[PIN_EQ]!).isSome = true := heq
  simp only [heq', pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  have hB0 : Base C q ((kqF, w) :: (kqF, w') :: Γ) :=
    base_of hB (by simp only [Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)])
      (by simp only [Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)])
  -- `Iff`
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_IFF (by decide)) ?_
  refine specR_findTagI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_IFF 3 (by decide) SD.f hB0.2
    (fun ci o Γ1 hfind hcie htag hG1 g1 => ?_)
  obtain ⟨v1, caps1, rfl⟩ := cie_tag3 hcie htag
  have hfind' : C.fe.find? C.pins.names[PIN_IFF]! = some (.indInfo v1 caps1) := hfind
  have hB1 : Base C q Γ1 :=
    base_of hB0 (g1 _ (by decide) (by decide) (by decide)) (g1 _ (by decide) (by decide) (by decide))
  rw [hfind']
  simp only [bind_assoc]
  refine specR_pinCII ra G SD.q SD.o _ _ (plainCI_ind_nil _ _ rfl rfl) lit_iffA (by decide) H0 _ Γ1 [] s
    (fun r1 s1 Γ2 H1 hp1 k2 hr1 hP1 hl1 => ?_)
  refine specR_cmpEI (C := ctxH C H1) 0 (by decide) o v1 r1 SD.c (by rw [k2 kqG (by simp)]; exact hG1) hcie.1 hP1
    (by rw [hl1]; rfl) (fun Γ3 e g3 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB3 : Base C q Γ3 := base_of hB1 ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (k2 _ (by simp))) ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (k2 _ (by simp)))
  have hp01 : C.H <+: H1 := hH0.trans hp1
  -- `Iff.intro`
  refine specR_atEntry fun t1 ht1 => ?_
  refine specR_runBind (pinAt_run hok ht1.sr.pins PIN_IFF_INTRO (by decide)) ?_
  refine specR_findTagI (C := ctxH C H1) (ctxOK_H hok H1) hc.d.k.g hc.d.k.p PIN_IFF_INTRO 4 (by decide) SD.f hB3.2
    (fun ci o2 Γ4 hfind2 hcie2 htag2 hG4 g4 => ?_)
  obtain ⟨v2, np2, nf2, T2, rfl⟩ := cie_tag4 hcie2 htag2
  have hfind2' : C.fe.find? C.pins.names[PIN_IFF_INTRO]! = some (.ctorInfo v2 np2 nf2 T2) := hfind2
  have hB4 : Base C q Γ4 :=
    base_of hB3 (g4 _ (by decide) (by decide) (by decide)) (g4 _ (by decide) (by decide) (by decide))
  obtain ⟨hcv2, -, hnp, hnf, -⟩ := hcie2
  refine specR_fieldI 4 2 o2 _ SD.f.2.2 hG4 hnp.1 (fun e4 => ?_)
  refine specR_fieldI 5 2 o2 _ SD.f.2.2 (by rw [Env.get_cons, if_neg (by decide)]; exact hG4) hnf.1 (fun e5 => ?_)
  have h4 := natE_eq hnp _ hnp.1 (by decide) e4
  have h5 := natE_eq hnf _ hnf.1 (by decide) e5
  subst h4 h5
  rw [hfind2']
  simp only [bind_assoc]
  refine specR_pinCtorI ra G SD.q SD.o _ ConLeche.iffIntroA.toConstantVal 2 2 ConLeche.iffName rfl lit_iffIntroA
    lit_iffName (by decide) H1 _ _ [] s1 (fun r2 t2 s2 Γ5 H2 hp2 k5 hP2 hl2 => ?_)
  refine specR_cmpEI (C := ctxH C H2) 0 (by decide) o2 v2 r2 SD.c
    (by rw [k5 kqG (by simp), Env.get_cons, if_neg (by decide), Env.get_cons, if_neg (by decide)]; exact hG4)
    hcv2 hP2 (by rw [hl2]; rfl) (fun Γ6 e g6 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB6 : Base C q Γ6 := by
    refine base_of hB4 ?_ ?_
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide), k5 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide), k5 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
  have hp02 : C.H <+: H2 := hp01.trans hp2
  -- `Iff.rec`
  refine specR_atEntry fun t2 ht2 => ?_
  refine specR_runBind (pinAt_run hok ht2.sr.pins PIN_IFF_REC (by decide)) ?_
  refine specR_findTagI (C := ctxH C H2) (ctxOK_H hok H2) hc.d.k.g hc.d.k.p PIN_IFF_REC 5 (by decide) SD.f hB6.2
    (fun ci o3 Γ7 hfind3 hcie3 htag3 hG7 g7 => ?_)
  obtain ⟨v3, mi3, rp3, k3, rs3, rfl⟩ := cie_tag5 hcie3 htag3
  have hfind3' : C.fe.find? C.pins.names[PIN_IFF_REC]! = some (.recInfo v3 mi3 rp3 k3 rs3) := hfind3
  have hB7 : Base C q Γ7 :=
    base_of hB6 (g7 _ (by decide) (by decide) (by decide)) (g7 _ (by decide) (by decide) (by decide))
  obtain ⟨hcv3, -, hmi, hrp, -⟩ := hcie3
  refine specR_fieldI 4 4 o3 _ SD.f.2.2 hG7 hmi.1 (fun e6 => ?_)
  refine specR_fieldI 5 4 o3 _ SD.f.2.2 (by rw [Env.get_cons, if_neg (by decide)]; exact hG7) hrp.1 (fun e7 => ?_)
  have h6 := natE_eq hmi _ hmi.1 (by decide) e6
  have h7 := natE_eq hrp _ hrp.1 (by decide) e7
  subst h6 h7
  rw [hfind3']
  simp only [bind_assoc]
  refine specR_pinCII ra G SD.q SD.o _ _ (plainCI_rec_nil _ _ _ _) lit_iffRecA (by decide) H2 _ _ [] s2
    (fun r3 s3 Γ8 H3 hp3 k8 hr3 hP3 hl3 => ?_)
  refine specR_cmpEI (C := ctxH C H3) 1 (by decide) o3 v3 r3 SD.c
    (by rw [k8 kqG (by simp), Env.get_cons, if_neg (by decide), Env.get_cons, if_neg (by decide)]; exact hG7)
    hcv3 hP3 (by rw [hl3]; rfl) (fun Γ9 e g9 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB9 : Base C q Γ9 := by
    refine base_of hB7 ?_ ?_
    · rw [g9 _ (by decide) (by decide) (by decide) (by decide) (by decide), k8 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
    · rw [g9 _ (by decide) (by decide) (by decide) (by decide) (by decide), k8 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
  have hp03 : C.H <+: H3 := hp02.trans hp3
  -- the record
  refine specR_pinI ra G SD.q SD.o _ lit_propextA (by decide) H3 _ _ [] s3
    (fun r4 s4 Γ10 H4 hp4 k10 hr4 hP4 hl4 => ?_)
  have hp04 : C.H <+: H4 := hp03.trans hp4
  refine specR_cmpRI (C := ctxH C H4) 0 (by decide) q ol cv r4 SD.c
    (by rw [k10 kdQ (by simp)]; exact hB9.1) (get_prefix hn hp04) (get_prefix hl hp04) (get_prefix ht hp04)
    (blkAt_mono hb hp04) (by omega) hP4 (by rw [hl4]; rfl) (fun Γ11 e g11 => ?_)
  subst e
  simp only [matchesPin_self, pure_bind, ↓reduceIte]
  have hB11 : Base C q Γ11 := by
    refine base_of hB9 ?_ ?_
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
  exact stdInst_spec mode C hok hc hpl hg hF hL cv q hrc hnq H4 hp04 s4 Γ11 hB11

set_option maxHeartbeats 8000000 in
/-- **`Classical.choice`**: `stdAxiomOk`, then the install. -/
theorem stdChoice_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (hnq : cv.name ≠ C.pins.names[PIN_QUOT_SOUND]!)
    (hne : cv.name ≠ C.pins.names[PIN_PROPEXT]!) (hce : cv.name = C.pins.names[PIN_CHOICE]!)
    (H0 : List (BitVec 64)) (hH0 : C.H <+: H0) (s : AState) (Γ : Env) (hB : Base C q Γ) (F : AM IFEnv) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (stdP C 1) s
      (stdAxiomOk C.fe cv >>= fun b =>
        if b = true then (flushCaches >>= fun _ => stdTail cv (C.fe.push (.axiomInfo cv))) else F) (PostStep C) := by
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := id hrc
  have G := genEnv_kq hok hf hA hc.e
  have SD := stdD
  simp only [stdP]
  unfold stdAxiomOk propextName choiceName nonemptyName nonemptyIntroName nonemptyRecName nonemptyA
    nonemptyIntroA nonemptyRecA choiceA
  simp only [bind_assoc]
  refine specR_atEntry fun t0 ht0 => ?_
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_PROPEXT (by decide)) ?_
  have hne' : (cv.name == C.pins.names[PIN_PROPEXT]!) = false := by simpa using hne
  simp only [hne', Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_CHOICE (by decide)) ?_
  simp only [← hce, beq_self_eq_true, ↓reduceIte, bind_assoc]
  have hB0 := hB
  -- `Nonempty`
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_NONEMPTY (by decide)) ?_
  refine specR_findTagI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_NONEMPTY 3 (by decide) SD.f hB0.2
    (fun ci o Γ1 hfind hcie htag hG1 g1 => ?_)
  obtain ⟨v1, caps1, rfl⟩ := cie_tag3 hcie htag
  have hfind' : C.fe.find? C.pins.names[PIN_NONEMPTY]! = some (.indInfo v1 caps1) := hfind
  have hB1 : Base C q Γ1 :=
    base_of hB0 (g1 _ (by decide) (by decide) (by decide)) (g1 _ (by decide) (by decide) (by decide))
  rw [hfind']
  simp only [bind_assoc]
  refine specR_pinCII ra G SD.q SD.o _ _ (plainCI_ind_nil _ _ rfl rfl) lit_nonemptyA (by decide) H0 _ Γ1 [] s
    (fun r1 s1 Γ2 H1 hp1 k2 hr1 hP1 hl1 => ?_)
  refine specR_cmpEI (C := ctxH C H1) 1 (by decide) o v1 r1 SD.c (by rw [k2 kqG (by simp)]; exact hG1) hcie.1 hP1
    (by rw [hl1]; rfl) (fun Γ3 e g3 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB3 : Base C q Γ3 := base_of hB1 ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (k2 _ (by simp))) ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (k2 _ (by simp)))
  have hp01 : C.H <+: H1 := hH0.trans hp1
  -- `Nonempty.intro`
  refine specR_atEntry fun t1 ht1 => ?_
  refine specR_runBind (pinAt_run hok ht1.sr.pins PIN_NONEMPTY_INTRO (by decide)) ?_
  refine specR_findTagI (C := ctxH C H1) (ctxOK_H hok H1) hc.d.k.g hc.d.k.p PIN_NONEMPTY_INTRO 4 (by decide) SD.f hB3.2
    (fun ci o2 Γ4 hfind2 hcie2 htag2 hG4 g4 => ?_)
  obtain ⟨v2, np2, nf2, T2, rfl⟩ := cie_tag4 hcie2 htag2
  have hfind2' : C.fe.find? C.pins.names[PIN_NONEMPTY_INTRO]! = some (.ctorInfo v2 np2 nf2 T2) := hfind2
  have hB4 : Base C q Γ4 :=
    base_of hB3 (g4 _ (by decide) (by decide) (by decide)) (g4 _ (by decide) (by decide) (by decide))
  obtain ⟨hcv2, -, hnp, hnf, -⟩ := hcie2
  refine specR_fieldI 4 1 o2 _ SD.f.2.2 hG4 hnp.1 (fun e4 => ?_)
  refine specR_fieldI 5 1 o2 _ SD.f.2.2 (by rw [Env.get_cons, if_neg (by decide)]; exact hG4) hnf.1 (fun e5 => ?_)
  have h4 := natE_eq hnp _ hnp.1 (by decide) e4
  have h5 := natE_eq hnf _ hnf.1 (by decide) e5
  subst h4 h5
  rw [hfind2']
  simp only [bind_assoc]
  refine specR_pinCtorI ra G SD.q SD.o _ ConLeche.nonemptyIntroA.toConstantVal 1 1 ConLeche.nonemptyName rfl
    lit_nonemptyIntroA lit_nonemptyName (by decide) H1 _ _ [] s1 (fun r2 t2 s2 Γ5 H2 hp2 k5 hP2 hl2 => ?_)
  refine specR_cmpEI (C := ctxH C H2) 1 (by decide) o2 v2 r2 SD.c
    (by rw [k5 kqG (by simp), Env.get_cons, if_neg (by decide), Env.get_cons, if_neg (by decide)]; exact hG4)
    hcv2 hP2 (by rw [hl2]; rfl) (fun Γ6 e g6 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB6 : Base C q Γ6 := by
    refine base_of hB4 ?_ ?_
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide), k5 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide) (by decide), k5 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
  have hp02 : C.H <+: H2 := hp01.trans hp2
  -- `Nonempty.rec`
  refine specR_atEntry fun t2 ht2 => ?_
  refine specR_runBind (pinAt_run hok ht2.sr.pins PIN_NONEMPTY_REC (by decide)) ?_
  refine specR_findTagI (C := ctxH C H2) (ctxOK_H hok H2) hc.d.k.g hc.d.k.p PIN_NONEMPTY_REC 5 (by decide) SD.f hB6.2
    (fun ci o3 Γ7 hfind3 hcie3 htag3 hG7 g7 => ?_)
  obtain ⟨v3, mi3, rp3, k3, rs3, rfl⟩ := cie_tag5 hcie3 htag3
  have hfind3' : C.fe.find? C.pins.names[PIN_NONEMPTY_REC]! = some (.recInfo v3 mi3 rp3 k3 rs3) := hfind3
  have hB7 : Base C q Γ7 :=
    base_of hB6 (g7 _ (by decide) (by decide) (by decide)) (g7 _ (by decide) (by decide) (by decide))
  obtain ⟨hcv3, -, hmi, hrp, -⟩ := hcie3
  refine specR_fieldI 4 3 o3 _ SD.f.2.2 hG7 hmi.1 (fun e6 => ?_)
  refine specR_fieldI 5 3 o3 _ SD.f.2.2 (by rw [Env.get_cons, if_neg (by decide)]; exact hG7) hrp.1 (fun e7 => ?_)
  have h6 := natE_eq hmi _ hmi.1 (by decide) e6
  have h7 := natE_eq hrp _ hrp.1 (by decide) e7
  subst h6 h7
  rw [hfind3']
  simp only [bind_assoc]
  refine specR_pinCII ra G SD.q SD.o _ _ (plainCI_rec_nil _ _ _ _) lit_nonemptyRecA (by decide) H2 _ _ [] s2
    (fun r3 s3 Γ8 H3 hp3 k8 hr3 hP3 hl3 => ?_)
  refine specR_cmpEI (C := ctxH C H3) 1 (by decide) o3 v3 r3 SD.c
    (by rw [k8 kqG (by simp), Env.get_cons, if_neg (by decide), Env.get_cons, if_neg (by decide)]; exact hG7)
    hcv3 hP3 (by rw [hl3]; rfl) (fun Γ9 e g9 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB9 : Base C q Γ9 := by
    refine base_of hB7 ?_ ?_
    · rw [g9 _ (by decide) (by decide) (by decide) (by decide) (by decide), k8 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
    · rw [g9 _ (by decide) (by decide) (by decide) (by decide) (by decide), k8 _ (by simp), Env.get_cons,
        if_neg (by decide), Env.get_cons, if_neg (by decide)]
  have hp03 : C.H <+: H3 := hp02.trans hp3
  -- the record
  refine specR_pinI ra G SD.q SD.o _ lit_choiceA (by decide) H3 _ _ [] s3
    (fun r4 s4 Γ10 H4 hp4 k10 hr4 hP4 hl4 => ?_)
  have hp04 : C.H <+: H4 := hp03.trans hp4
  refine specR_cmpRI (C := ctxH C H4) 1 (by decide) q ol cv r4 SD.c
    (by rw [k10 kdQ (by simp)]; exact hB9.1) (get_prefix hn hp04) (get_prefix hl hp04) (get_prefix ht hp04)
    (blkAt_mono hb hp04) (by omega) hP4 (by rw [hl4]; rfl) (fun Γ11 e g11 => ?_)
  subst e
  simp only [matchesPin_self, pure_bind, ↓reduceIte]
  have hB11 : Base C q Γ11 := by
    refine base_of hB9 ?_ ?_
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
  exact stdInst_spec mode C hok hc hpl hg hF hL cv q hrc hnq H4 hp04 s4 Γ11 hB11

set_option maxHeartbeats 8000000 in
/-- **`Lean.ofReduceNat`**: `ofReduceAxOk`, then the install. -/
theorem stdOfRedNat_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (hnq : cv.name ≠ C.pins.names[PIN_QUOT_SOUND]!)
    (hon : cv.name = C.pins.names[PIN_OF_REDUCE_NAT]!)
    (H0 : List (BitVec 64)) (hH0 : C.H <+: H0) (s : AState) (Γ : Env) (hB : Base C q Γ) (F : AM IFEnv) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (stdP C 3) s
      (ofReduceAxOk C.fe cv >>= fun b =>
        if b = true then (flushCaches >>= fun _ => stdTail cv (C.fe.push (.axiomInfo cv))) else F) (PostStep C) := by
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := id hrc
  have G := genEnv_kq hok hf hA hc.e
  have SD := stdD
  simp only [stdP, ofRedP]
  unfold ofReduceAxOk ofReduceOp ofReduceNatName reduceNatName reduceBoolName eqStored reduceElemOk reduceStoredOk
    reduceOpCvA ofReducePinA ConRon.Arena.natA reduceNatCvA ofReduceNatA
  simp only [bind_assoc]
  refine specR_atEntry fun t0 ht0 => ?_
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_OF_REDUCE_NAT (by decide)) ?_
  simp only [← hon, beq_self_eq_true, ↓reduceIte, bind_assoc]
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_REDUCE_NAT (by decide)) ?_
  -- `Eq` stored
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_EQ (by decide)) ?_
  refine specR_predGuardI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_EQ (by decide) SD.f.1 hB.2
    (fun w w' heq => ?_)
  have heq' : (C.fe.find? C.pins.names[PIN_EQ]!).isSome = true := heq
  simp only [heq', pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  have hB0 : Base C q ((kqF, w) :: (kqF, w') :: Γ) :=
    base_of hB (by simp only [Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)])
      (by simp only [Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)])
  -- the element inductive
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_REDUCE_NAT (by decide)) ?_
  simp only [beq_self_eq_true, ↓reduceIte, bind_assoc]
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_NAT (by decide)) ?_
  refine specR_findTagI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_NAT 3 (by decide) SD.f hB0.2
    (fun ci o Γ1 hfind hcie htag hG1 g1 => ?_)
  obtain ⟨v1, caps1, rfl⟩ := cie_tag3 hcie htag
  have hfind' : C.fe.find? C.pins.names[PIN_NAT]! = some (.indInfo v1 caps1) := hfind
  have hB1 : Base C q Γ1 :=
    base_of hB0 (g1 _ (by decide) (by decide) (by decide)) (g1 _ (by decide) (by decide) (by decide))
  rw [hfind']
  simp only [bind_assoc]
  refine specR_pinCII ra G SD.q SD.o _ _ (plainCI_ind_nil _ _ rfl rfl) lit_natA (by decide) H0 _ Γ1 [] s
    (fun r1 s1 Γ2 H1 hp1 k2 hr1 hP1 hl1 => ?_)
  refine specR_cmpEI (C := ctxH C H1) 0 (by decide) o v1 r1 SD.c (by rw [k2 kqG (by simp)]; exact hG1) hcie.1 hP1
    (by rw [hl1]; rfl) (fun Γ3 e g3 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB3 : Base C q Γ3 := base_of hB1 ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (k2 _ (by simp))) ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (k2 _ (by simp)))
  have hp01 : C.H <+: H1 := hH0.trans hp1
  -- the reduce operation
  refine specR_atEntry fun t1 ht1 => ?_
  refine specR_findTagI (C := ctxH C H1) (ctxOK_H hok H1) hc.d.k.g hc.d.k.p PIN_REDUCE_NAT 0 (by decide) SD.f hB3.2
    (fun ci o2 Γ4 hfind2 hcie2 htag2 hG4 g4 => ?_)
  obtain ⟨v2, rfl⟩ := cie_tag0 hcie2 htag2
  have hfind2' : C.fe.find? C.pins.names[PIN_REDUCE_NAT]! = some (.axiomInfo v2) := hfind2
  have hB4 : Base C q Γ4 :=
    base_of hB3 (g4 _ (by decide) (by decide) (by decide)) (g4 _ (by decide) (by decide) (by decide))
  rw [hfind2']
  simp only [bind_assoc]
  refine specR_runBind (pinAt_run hok ht1.sr.pins PIN_REDUCE_NAT (by decide)) ?_
  simp only [beq_self_eq_true, ↓reduceIte, bind_assoc]
  refine specR_pinI ra G SD.q SD.o _ lit_reduceNatCvA (by decide) H1 _ _ [] s1
    (fun r2 s2 Γ5 H2 hp2 k5 hr2 hP2 hl2 => ?_)
  refine specR_cmpEI (C := ctxH C H2) 0 (by decide) o2 v2 r2 SD.c (by rw [k5 kqG (by simp)]; exact hG4)
    hcie2.1 hP2 (by rw [hl2]; rfl) (fun Γ6 e g6 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB6 : Base C q Γ6 := base_of hB4 ((g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (k5 _ (by simp))) ((g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (k5 _ (by simp)))
  have hp02 : C.H <+: H2 := hp01.trans hp2
  -- the record
  refine specR_atEntry fun t2 ht2 => ?_
  refine specR_runBind (pinAt_run hok ht2.sr.pins PIN_OF_REDUCE_NAT (by decide)) ?_
  simp only [← hon, beq_self_eq_true, ↓reduceIte, bind_assoc]
  refine specR_pinI ra G SD.q SD.o _ lit_ofReduceNatA (by decide) H2 _ _ [] s2
    (fun r4 s4 Γ10 H4 hp4 k10 hr4 hP4 hl4 => ?_)
  have hp04 : C.H <+: H4 := hp02.trans hp4
  refine specR_cmpRI (C := ctxH C H4) 0 (by decide) q ol cv r4 SD.c
    (by rw [k10 kdQ (by simp)]; exact hB6.1) (get_prefix hn hp04) (get_prefix hl hp04) (get_prefix ht hp04)
    (blkAt_mono hb hp04) (by omega) hP4 (by rw [hl4]; rfl) (fun Γ11 e g11 => ?_)
  subst e
  simp only [matchesPin_self, pure_bind, ↓reduceIte]
  have hB11 : Base C q Γ11 := by
    refine base_of hB6 ?_ ?_
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
  exact stdInst_spec mode C hok hc hpl hg hF hL cv q hrc hnq H4 hp04 s4 Γ11 hB11

set_option maxHeartbeats 8000000 in
/-- **`Lean.ofReduceBool`**: `ofReduceAxOk`, then the install. -/
theorem stdOfRedBool_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (hnq : cv.name ≠ C.pins.names[PIN_QUOT_SOUND]!)
    (hnon : cv.name ≠ C.pins.names[PIN_OF_REDUCE_NAT]!) (hob : cv.name = C.pins.names[PIN_OF_REDUCE_BOOL]!)
    (H0 : List (BitVec 64)) (hH0 : C.H <+: H0) (s : AState) (Γ : Env) (hB : Base C q Γ) (F : AM IFEnv) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (stdP C 4) s
      (ofReduceAxOk C.fe cv >>= fun b =>
        if b = true then (flushCaches >>= fun _ => stdTail cv (C.fe.push (.axiomInfo cv))) else F) (PostStep C) := by
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := id hrc
  have G := genEnv_kq hok hf hA hc.e
  have SD := stdD
  simp only [stdP, ofRedP, pinNeP]
  unfold ofReduceAxOk ofReduceOp ofReduceNatName reduceNatName reduceBoolName eqStored reduceElemOk reduceStoredOk
    reduceOpCvA ofReducePinA boolName boolCvA reduceBoolCvA ofReduceBoolA
  simp only [bind_assoc]
  -- the two reduce pins differ
  have hrb : PIN_REDUCE_BOOL < C.pins.names.size := by rw [hok.pinsRel.1]; decide
  have hrn : PIN_REDUCE_NAT < C.pins.names.size := by rw [hok.pinsRel.1]; decide
  refine specR_envLoadI (C := ctxH C H0) kdN _ (C.PO + PIN_REDUCE_BOOL) _ SD.c.1 rfl (hok.pinsRel.2.1 _ hrb) ?_
  refine specR_envLoadI (C := ctxH C H0) kdL _ (C.PO + PIN_REDUCE_NAT) _ (by simp [kqLocals]) rfl
    (hok.pinsRel.2.1 _ hrn) ?_
  by_cases hbn : C.pins.names[PIN_REDUCE_BOOL] = C.pins.names[PIN_REDUCE_NAT]
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Decl.cmpEq_idxW_t' hbn]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Decl.cmpEq_idxW_f' hbn]) (fun h => absurd rfl h) (fun _ => ?_)
  have hbn' : (C.pins.names[PIN_REDUCE_BOOL]! == C.pins.names[PIN_REDUCE_NAT]!) = false := by
    have e1 : C.pins.names[PIN_REDUCE_BOOL]! = C.pins.names[PIN_REDUCE_BOOL] := by simp [hrb]
    have e2 : C.pins.names[PIN_REDUCE_NAT]! = C.pins.names[PIN_REDUCE_NAT] := by simp [hrn]
    rw [e1, e2]; simpa using hbn
  have hB := base_of (Γ' := (kdL, Enc.idxW C.pins.names[PIN_REDUCE_NAT]) ::
      (kdN, Enc.idxW C.pins.names[PIN_REDUCE_BOOL]) :: Γ) hB
    (by simp only [Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)])
    (by simp only [Env.get_cons]; rw [if_neg (by decide), if_neg (by decide)])
  have hnon' : (cv.name == C.pins.names[PIN_OF_REDUCE_NAT]!) = false := by simpa using hnon
  refine specR_atEntry fun t0 ht0 => ?_
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_OF_REDUCE_NAT (by decide)) ?_
  simp only [hnon', Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_REDUCE_BOOL (by decide)) ?_
  -- `Eq` stored
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_EQ (by decide)) ?_
  refine specR_predGuardI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_EQ (by decide) SD.f.1 hB.2
    (fun w w' heq => ?_)
  have heq' : (C.fe.find? C.pins.names[PIN_EQ]!).isSome = true := heq
  simp only [heq', pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  have hB0 : Base C q ((kqF, w) :: (kqF, w') :: (kdL, Enc.idxW C.pins.names[PIN_REDUCE_NAT]) ::
      (kdN, Enc.idxW C.pins.names[PIN_REDUCE_BOOL]) :: Γ) :=
    base_of hB (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
  -- the element inductive
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_REDUCE_NAT (by decide)) ?_
  simp only [hbn', Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine specR_runBind (pinAt_run hok ht0.sr.pins PIN_BOOL (by decide)) ?_
  refine specR_findTagI (C := ctxH C H0) (ctxOK_H hok H0) hc.d.k.g hc.d.k.p PIN_BOOL 3 (by decide) SD.f hB0.2
    (fun ci o Γ1 hfind hcie htag hG1 g1 => ?_)
  obtain ⟨v1, caps1, rfl⟩ := cie_tag3 hcie htag
  have hfind' : C.fe.find? C.pins.names[PIN_BOOL]! = some (.indInfo v1 caps1) := hfind
  have hB1 : Base C q Γ1 :=
    base_of hB0 (g1 _ (by decide) (by decide) (by decide)) (g1 _ (by decide) (by decide) (by decide))
  rw [hfind']
  simp only [bind_assoc]
  refine specR_pinI ra G SD.q SD.o _ lit_boolCvA (by decide) H0 _ Γ1 [] s
    (fun r1 s1 Γ2 H1 hp1 k2 hr1 hP1 hl1 => ?_)
  refine specR_cmpEI (C := ctxH C H1) 0 (by decide) o v1 r1 SD.c (by rw [k2 kqG (by simp)]; exact hG1) hcie.1 hP1
    (by rw [hl1]; rfl) (fun Γ3 e g3 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB3 : Base C q Γ3 := base_of hB1 ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (k2 _ (by simp))) ((g3 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (k2 _ (by simp)))
  have hp01 : C.H <+: H1 := hH0.trans hp1
  -- the reduce operation
  refine specR_atEntry fun t1 ht1 => ?_
  refine specR_findTagI (C := ctxH C H1) (ctxOK_H hok H1) hc.d.k.g hc.d.k.p PIN_REDUCE_BOOL 0 (by decide) SD.f hB3.2
    (fun ci o2 Γ4 hfind2 hcie2 htag2 hG4 g4 => ?_)
  obtain ⟨v2, rfl⟩ := cie_tag0 hcie2 htag2
  have hfind2' : C.fe.find? C.pins.names[PIN_REDUCE_BOOL]! = some (.axiomInfo v2) := hfind2
  have hB4 : Base C q Γ4 :=
    base_of hB3 (g4 _ (by decide) (by decide) (by decide)) (g4 _ (by decide) (by decide) (by decide))
  rw [hfind2']
  simp only [bind_assoc]
  refine specR_runBind (pinAt_run hok ht1.sr.pins PIN_REDUCE_NAT (by decide)) ?_
  simp only [hbn', Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine specR_pinI ra G SD.q SD.o _ lit_reduceBoolCvA (by decide) H1 _ _ [] s1
    (fun r2 s2 Γ5 H2 hp2 k5 hr2 hP2 hl2 => ?_)
  refine specR_cmpEI (C := ctxH C H2) 0 (by decide) o2 v2 r2 SD.c (by rw [k5 kqG (by simp)]; exact hG4)
    hcie2.1 hP2 (by rw [hl2]; rfl) (fun Γ6 e g6 => ?_)
  subst e
  simp only [IConstantInfo.toConstantVal, matchesPin_self, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind_assoc]
  have hB6 : Base C q Γ6 := base_of hB4 ((g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (k5 _ (by simp))) ((g6 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (k5 _ (by simp)))
  have hp02 : C.H <+: H2 := hp01.trans hp2
  -- the record
  refine specR_atEntry fun t2 ht2 => ?_
  refine specR_runBind (pinAt_run hok ht2.sr.pins PIN_OF_REDUCE_NAT (by decide)) ?_
  simp only [hnon', Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine specR_pinI ra G SD.q SD.o _ lit_ofReduceBoolA (by decide) H2 _ _ [] s2
    (fun r4 s4 Γ10 H4 hp4 k10 hr4 hP4 hl4 => ?_)
  have hp04 : C.H <+: H4 := hp02.trans hp4
  refine specR_cmpRI (C := ctxH C H4) 0 (by decide) q ol cv r4 SD.c
    (by rw [k10 kdQ (by simp)]; exact hB6.1) (get_prefix hn hp04) (get_prefix hl hp04) (get_prefix ht hp04)
    (blkAt_mono hb hp04) (by omega) hP4 (by rw [hl4]; rfl) (fun Γ11 e g11 => ?_)
  subst e
  simp only [matchesPin_self, pure_bind, ↓reduceIte]
  have hB11 : Base C q Γ11 := by
    refine base_of hB6 ?_ ?_
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
    · rw [g11 _ (by decide) (by decide) (by decide) (by decide) (by decide), k10 _ (by simp)]
  exact stdInst_spec mode C hok hc hpl hg hF hL cv q hrc hnq H4 hp04 s4 Γ11 hB11

/-! ## The entry -/

set_option maxHeartbeats 4000000 in
/-- **`kqBody` at kind word `k + 6`**: the standard axiom arm `k`. -/
theorem kqStd_of (C : Ctx) (H0 : List (BitVec 64)) (k : Nat) (hk : k < 5) (q : Nat) (s : AState) {m : AM IFEnv}
    (h : ∀ Γ, Base C q Γ → SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (stdP C k) s m
      (PostStep C)) :
    SpecR (σ := σ) (Pre (ctxH C H0) s (kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0])) (kqBody C) s m
      (PostStep C) := by
  unfold kqBody
  refine specR_prologue (postStep_locals C) (kq_none (ctxH C H0) _) ?_
  have hB0 : Base C q (ctxEnv (ctxH C H0) ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0]) :=
    ⟨by simp +decide [Env.get, kdParams, ctxEnv], by simp +decide [Env.get, kdParams, ctxEnv]; rfl⟩
  have hm := h _ hB0
  have e : ∀ j, j < 5 → j ≠ k → ∀ (c : ProgHOL 64) {P : ProgHOL 64},
      SpecR (σ := σ) (Inv (ctxH C H0) s (ctxEnv (ctxH C H0) ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0])
        [] (ctxLocals ++ kqLocals)) P s m (PostStep C) →
      SpecR (σ := σ) (Inv (ctxH C H0) s (ctxEnv (ctxH C H0) ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0])
        [] (ctxLocals ++ kqLocals)) (.ite (.cmp .equal (vv kdV) (.const (BitVec.ofNat 64 (j + 6)))) c P) s m
        (PostStep C) := by
    intro j hj hne c P hP
    refine specR_ifI _ 0 ?_ (fun h => absurd rfl h) (fun _ => hP)
    have : BitVec.ofNat 64 (k + 6) ≠ BitVec.ofNat 64 (j + 6) := by
      intro he; have := (UD.ofNat_eq_iff_small _ _ (by omega) (by omega)).mp he; omega
    simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  have eq : ∀ (c P : ProgHOL 64), SpecR (σ := σ) (Inv (ctxH C H0) s
        (ctxEnv (ctxH C H0) ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0]) [] (ctxLocals ++ kqLocals)) c s m
        (PostStep C) →
      SpecR (σ := σ) (Inv (ctxH C H0) s (ctxEnv (ctxH C H0) ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0])
        [] (ctxLocals ++ kqLocals)) (.ite (.cmp .equal (vv kdV) (.const (BitVec.ofNat 64 (k + 6)))) c P) s m
        (PostStep C) := by
    intro c P hc
    refine specR_ifI _ 1 ?_ (fun _ => hc) (fun h => absurd h (by decide))
    simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have skip : ∀ (j : Nat), j ∈ [1, 2, 5, 3, 4] → ∀ (c : ProgHOL 64) {P : ProgHOL 64},
      SpecR (σ := σ) (Inv (ctxH C H0) s (ctxEnv (ctxH C H0) ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0])
        [] (ctxLocals ++ kqLocals)) P s m (PostStep C) →
      SpecR (σ := σ) (Inv (ctxH C H0) s (ctxEnv (ctxH C H0) ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (k + 6), 0])
        [] (ctxLocals ++ kqLocals)) (.ite (.cmp .equal (vv kdV) (.const (BitVec.ofNat 64 j))) c P) s m
        (PostStep C) := by
    intro j hj c P hP
    refine specR_ifI _ 0 ?_ (fun h => absurd rfl h) (fun _ => hP)
    have : BitVec.ofNat 64 (k + 6) ≠ BitVec.ofNat 64 j := by
      intro he
      have := (UD.ofNat_eq_iff_small _ _ (by omega) (by simp at hj; omega)).mp he
      simp at hj; omega
    simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  refine skip 1 (by simp) _ (skip 2 (by simp) _ (skip 5 (by simp) _ (skip 3 (by simp) _ (skip 4 (by simp) _ ?_))))
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl
  · exact eq _ _ hm
  · exact e 0 (by decide) (by decide) _ (eq _ _ hm)
  · exact e 0 (by decide) (by decide) _ (e 1 (by decide) (by decide) _ (eq _ _ hm))
  · exact e 0 (by decide) (by decide) _ (e 1 (by decide) (by decide) _ (e 2 (by decide) (by decide) _ (eq _ _ hm)))
  · exact e 0 (by decide) (by decide) _ (e 1 (by decide) (by decide) _ (e 2 (by decide) (by decide) _
      (e 3 (by decide) (by decide) _ (eq _ _ hm))))

end

end ConPanqueque.T.Quot
