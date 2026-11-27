import ConPanqueque.T.LitIntern

/-!
# A quotient pin's slot, interned with its handles kept

The twin's `quotPin k` interns the whole pinned quotient block (`BasisKind.decls .quotK`, its plain interning
with the scratch tier off) and reads slot `k`. The port interns the block literal by literal (`genCIList`),
the slot's constant by `genPinCV`, which keeps the handles the check needs: the name in `qN`, the level
parameters in a fresh value-heap block at `qL`, the type in `qT`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.Start ConPanqueque.T.Lit ConPanqueque.Logic.PlainIntern

def qN := ofString "q_n"
def qL := ofString "q_l"
def qT := ofString "q_t"
def qU := ofString "q_u"
def qX := ofString "q_x"
def qW := ofString "q_w"

/-- The generated locals of the literal interner. -/
def genLocals : List MlS :=
  (['l', 'e', 'k', 's', 'n'].flatMap fun c => (List.range 12).map (gv c))

theorem gv_mem_genLocals {c : Char} (hc : c ∈ ['l', 'e', 'k', 's', 'n']) {j : Nat} (hj : j < 12) :
    gv c j ∈ genLocals := by
  simp only [genLocals, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨c, hc, j, hj, rfl⟩

/-- A one- or two-name literal list into a fresh value-heap block `[n, h₀, …]` at `x`. -/
def genLpsB (C : Ctx) (x : MlS) : List ConLeche.Name → ProgHOL 64 → ProgHOL 64
  | [a], rest => nameP C ((strComps a).getD []) (alloc2 C x (.const 1) (vv vPn) rest)
  | [a, b], rest => nameP C ((strComps a).getD []) (.seq (.assign .local qU (vv vPn))
      (nameP C ((strComps b).getD []) (alloc3 C x (.const 2) (vv qU) (vv vPn) rest)))
  | _, _ => hang

/-- A pin's constant value, its handles kept in `qN`, `qL`, `qT`. -/
def genPinCV (C : Ctx) (cv : ConLeche.ConstantVal) (rest : ProgHOL 64) : ProgHOL 64 :=
  nameP C ((strComps cv.name).getD []) (.seq (.assign .local qN (vv vPn))
    (genLpsB C qL cv.levelParams (genE C 0 cv.type (.seq (.assign .local qT (vv (ge 0))) rest))))

/-- `Γ'` agrees with `Γ` off the generated locals, the name interner's two and the pin's. -/
def AgreeQ (Γ Γ' : Env) : Prop :=
  ∀ y, (∀ c j, y ≠ gv c j) → y ≠ vPn → y ≠ vKa → y ≠ qN → y ≠ qL → y ≠ qT → y ≠ qU → y ≠ qX → y ≠ qW →
    Γ'.get y = Γ.get y

theorem agreeQ_refl (Γ : Env) : AgreeQ Γ Γ := fun _ _ _ _ _ _ _ _ _ _ => rfl

theorem agreeQ_trans {Γ1 Γ2 Γ3 : Env} (h1 : AgreeQ Γ1 Γ2) (h2 : AgreeQ Γ2 Γ3) : AgreeQ Γ1 Γ3 :=
  fun y a b c d e f g i j => (h2 y a b c d e f g i j).trans (h1 y a b c d e f g i j)

theorem agreeQ_of_L {Γ Γ' : Env} (h : AgreeL Γ Γ' 0) : AgreeQ Γ Γ' :=
  fun y hy h1 h2 _ _ _ _ _ _ => h y (fun c j _ => hy c j) h1 h2

theorem agreeQ_cons {Γ : Env} {x : MlS} (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) (w : BitVec 64) :
    AgreeQ Γ ((x, w) :: Γ) := fun y _ _ _ h1 h2 h3 h4 h5 h6 => by
  have hne : y ≠ x := by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hne)]

section
variable {σ : Type}

/-- A name interned, its handle in `vPn`. -/
theorem name_stepP (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (n : ConLeche.Name) (hn : NameLit n) (H0 : List (BitVec 64)) (rest : ProgHOL 64)
    (Γ : Env) (M : Mem) (s : AState) {β : Type} {k : NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ h s' Γ', (∀ y, y ≠ vPn → y ≠ vKa → Γ'.get y = Γ.get y) → Γ'.get vPn = some (Enc.idxW h) →
      internName n s = .ok (h, s') → SpecR (Inv (ctxH C H0) s' Γ' [] D) rest s' (k h) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (nameP C ((strComps n).getD []) rest) s (internName n >>= k) R := by
  obtain ⟨cs, hcs, hcok⟩ := hn
  rw [hcs, Option.getD_some]
  refine specR_atEntry fun t0 ht0 => ?_
  rw [show nameP C cs = nameP (ctxH C H0) cs from by funext r; simp only [nameP, stepsP_ctxH]]
  exact name_spec ra (ctxH C H0) (ctxOK_H G.hok H0) (by ctx_tr G.hf) G.hc.l.n D G.hPn G.hKa n cs hcs hcok s
    ⟨ht0.sr.twf⟩ (denoteN_ext G.hA ht0.sr.floor) Γ M _ hk

theorem gv_ne_q (c : Char) (j : Nat) : gv c j ≠ qN ∧ gv c j ≠ qL ∧ gv c j ≠ qT ∧ gv c j ≠ qU ∧ gv c j ≠ qX ∧
    gv c j ≠ qW :=
  ⟨gv_ne_of (by simp [qN, ofString]), gv_ne_of (by simp [qL, ofString]), gv_ne_of (by simp [qT, ofString]),
    gv_ne_of (by simp [qU, ofString]), gv_ne_of (by simp [qX, ofString]), gv_ne_of (by simp [qW, ofString])⟩

/-- **`genLpsB`**: the names interned (`internNameList`), their handles a fresh block at `x`. -/
theorem genLpsB_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS} {N : Nat}
    (G : GenEnv C D N) (hqU : qU ∈ D) (x : MlS) (hx : x ∈ D) (hxv : x ≠ vPn ∧ x ≠ vKa ∧ x ≠ qU)
    (ns : List ConLeche.Name) (hns : ∀ n ∈ ns, NameLit n) (hl : ns.length = 1 ∨ ns.length = 2)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : List NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ hs s' Γ' H' o, H0 <+: H' → (∀ y, y ≠ vPn → y ≠ vKa → y ≠ qU → y ≠ x → Γ'.get y = Γ.get y) →
      Frontend.internNameList ns s = .ok (hs, s') →
      Γ'.get x = some (cellA C o) → BlkAt H' o (hs.map Enc.idxW) →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k hs) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genLpsB C x ns rest) s (Frontend.internNameList ns >>= k) R := by
  match ns, hl with
  | [a], _ =>
    simp only [genLpsB, Frontend.internNameList, bind_assoc, pure_bind]
    refine name_stepP ra G a (hns a (by simp)) H0 _ Γ M s (fun h s1 Γ1 hf1 hv1 hr1 => ?_)
    refine specR_alloc2I (C := ctxH C H0) (ctxOK_H G.hok H0) x (.const 1) (vv vPn) _ _ hx (fun _ => rfl)
      (fun v => by simp only [sev_vv, Env.get_cons, ite_eq_right_iff.mpr (fun (e : vPn = x) => absurd e.symm hxv.1), hv1];
                   rfl) (fun H2 ws hp hws => ?_)
    obtain ⟨g0, g1⟩ := img2_get H2 ws (BitVec.ofNat 64 1) (Enc.idxW h) hws
    have hp' : H0 <+: _ := hp.trans (img2_prefix H2 ws (BitVec.ofNat 64 1) (Enc.idxW h) hws)
    have e : ctxH (ctxH C H0) (((H2 ++ ws).set H2.length (BitVec.ofNat 64 1)).set (H2.length + 1) (Enc.idxW h)) =
        ctxH C (((H2 ++ ws).set H2.length (BitVec.ofNat 64 1)).set (H2.length + 1) (Enc.idxW h)) := rfl
    show SpecR (Inv (ctxH C _) _ _ _ _) _ _ _ _
    refine hk [h] s1 _ _ H2.length hp' (fun y h1 h2 _ hyx => ?_) (bind_ok_of hr1 rfl)
      (by simp [Env.get_cons]; rfl) ⟨by simpa using g0, fun i hi => by
        simp at hi; subst hi; simpa using g1⟩
    · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hyx)]
      exact hf1 y h1 h2
  | [a, b], _ =>
    simp only [genLpsB, Frontend.internNameList, bind_assoc, pure_bind]
    refine name_stepP ra G a (hns a (by simp)) H0 _ Γ M s (fun h s1 Γ1 hf1 hv1 hr1 => ?_)
    refine specR_assignI qU (vv vPn) (Enc.idxW h) hqU (by simp only [sev, sev_vv, hv1]) ?_
    refine name_stepP ra G b (hns b (by simp)) H0 _ _ [] s1 (fun h' s2 Γ2 hf2 hv2 hr2 => ?_)
    have hu2 : Γ2.get qU = some (Enc.idxW h) := by
      rw [hf2 qU (by decide) (by decide)]; simp [Env.get_cons]
    refine specR_alloc3I (C := ctxH C H0) (ctxOK_H G.hok H0) x (.const 2) (vv qU) (vv vPn) _ _ _ hx (fun _ => rfl)
      (fun v => by simp only [sev, sev_vv, Env.get_cons, ite_eq_right_iff.mpr (fun (e : qU = x) => absurd e.symm hxv.2.2), hu2];
                   rfl)
      (fun v => by simp only [sev_vv, Env.get_cons, ite_eq_right_iff.mpr (fun (e : vPn = x) => absurd e.symm hxv.1), hv2];
                   rfl) (fun H2 ws hp hws => ?_)
    obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (BitVec.ofNat 64 2) (Enc.idxW h) (Enc.idxW h') hws
    have hp' : H0 <+: _ := hp.trans (img3_prefix H2 ws (BitVec.ofNat 64 2) (Enc.idxW h) (Enc.idxW h') hws)
    refine hk [h, h'] s2 _ _ H2.length hp' (fun y h1 h2 hU hyx => ?_)
      (by simp only [Frontend.internNameList, bind_assoc, pure_bind]; exact bind_ok_of hr1 (bind_ok_of hr2 rfl))
      (by simp [Env.get_cons]; rfl) ⟨by simpa using g0, fun i hi => by
        simp at hi
        rcases i with _ | _ | i
        · simpa using g1
        · simpa using g2
        · omega⟩
    · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hyx), hf2 y h1 h2, Env.get_cons,
        ite_eq_right_iff.mpr (fun e => absurd e hU)]
      exact hf1 y h1 h2

/-- **`genPinCV`**: the pin's constant value interned (`plainCV`), its handles in `qN`, `qL`, `qT`. -/
theorem genPinCV_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D)
    (cv : ConLeche.ConstantVal) (hcv : CVLit 0 12 cv) (hl : cv.levelParams.length = 1 ∨ cv.levelParams.length = 2)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantVal → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H' o, H0 <+: H' → AgreeQ Γ Γ' → plainCV cv s = .ok (r, s') →
      Γ'.get qN = some (Enc.idxW r.name) → Γ'.get qL = some (cellA C o) → BlkAt H' o (r.levelParams.map Enc.idxW) →
      Γ'.get qT = some (Enc.idxW r.type) → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genPinCV C cv rest) s (plainCV cv >>= k) R := by
  obtain ⟨hn, hls, he, hde⟩ := hcv
  unfold genPinCV
  simp only [plainCV, bind_assoc]
  refine name_stepP ra G _ hn H0 _ Γ M s (fun h1 s1 Γ1 hf1 hv1 hr1 => ?_)
  refine specR_assignI qN (vv vPn) (Enc.idxW h1) (hq qN (by simp)) (by simp only [sev, sev_vv, hv1]) ?_
  refine genLpsB_spec ra G (hq qU (by simp)) qL (hq qL (by simp)) ⟨by decide, by decide, by decide⟩
    _ hls hl H0 _ _ [] s1 (fun hs s2 Γ2 H2 o hp2 ag2 hr2 hx2 hb2 => ?_)
  refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa 12 G.hD _ 0 H2 _ Γ2 [] s2 he (by omega)
    (fun h3 s3 Γ3 H3 hp3 ag3 hv3 hr3 => ?_)
  refine specR_assignI qT (vv (ge 0)) (Enc.idxW h3) (hq qT (by simp)) (by simp only [sev, sev_vv, hv3]) ?_
  simp only [pure_bind]
  have hne : ∀ (x : MlS), (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) → ∀ c j, x ≠ gv c j := by
    intro x hx c j e; subst e
    have := gv_ne_q c j
    rcases hx with h | h | h | h | h | h <;> simp_all
  have k3 : ∀ x, (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) → Γ3.get x = Γ2.get x := fun x hx =>
    ag3 x (fun c j _ => hne x hx c j) (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine hk ⟨h1, hs, h3⟩ s3 _ H3 o (hp2.trans hp3) ?_ (bind_ok_of hr1 (bind_ok_of hr2 (bind_ok_of hr3 rfl)))
    ?_ ?_ (blkAt_mono hb2 hp3) (by simp [Env.get_cons])
  · refine agreeQ_trans ?_ (agreeQ_trans (agreeQ_of_L ag3) (agreeQ_cons (Or.inr (Or.inr (Or.inl rfl))) _))
    refine fun y hy h1' h2' hN hL _ hU _ _ => ?_
    rw [ag2 y h1' h2' hU hL, Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hN)]
    exact hf1 y h1' h2'
  · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)), k3 qN (Or.inl rfl),
      ag2 qN (by decide) (by decide) (by decide) (by decide)]
    simp [Env.get_cons]
  · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)), k3 qL (Or.inr (Or.inl rfl))]
    exact hx2

end

end ConPanqueque.T.Quot
