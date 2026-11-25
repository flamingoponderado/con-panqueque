import ConPanqueque.T.Ind.PiSortTele
import ConPanqueque.T.Decl.NameNodup
import ConPanqueque.T.Decl.EnvGrow

/-!
# Inductive blocks in the value heap, and `indParamsOk`

A block (`IndBlk`): a heap block of record pointers `[n, cellA o₀, …]`, record `i` at `oᵢ` in the
environment's own layout (`CIE`), so a checked member installs as it is.

`indParamsOk nP block` (the stream's declared parameter count, checked as official checks it): every
inductive member's type has at least `nP` leading `∀`s before its sort (when it ends in a sort), and every
constructor declares exactly `nP` parameters.  `ipo(p, j, n, nP)` walks the block from index `j`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- The block's records in the value heap: pointer block at `ob`, record `i` at `os[i]`. -/
def IndBlk (C : Ctx) (H : List (BitVec 64)) (ob : Nat) (blk : List IConstantInfo) : Prop :=
  ∃ os : List Nat, os.length = blk.length ∧ BlkAt H ob (os.map (cellA C)) ∧
    ∀ i (hi : i < blk.length) (ho : i < os.length), CIE C.HB H os[i] blk[i]

theorem indBlk_mono {C : Ctx} {H H' : List (BitVec 64)} {ob : Nat} {blk : List IConstantInfo}
    (h : IndBlk C H ob blk) (hp : H <+: H') : IndBlk C H' ob blk :=
  let ⟨os, hl, hb, hc⟩ := h; ⟨os, hl, blkAt_mono hb hp, fun i hi ho => cie_mono hp (hc i hi ho)⟩

def ipP := ofString "ip_p"
def ipJ := ofString "ip_j"
def ipN := ofString "ip_n"
def ipNP := ofString "ip_np"
def ipQ := ofString "ip_q"
def ipT := ofString "ip_t"
def ipR := ofString "ip_r"
def fIpo := ofString "indParamsOk"

def ipoParams : List MlS := [ipP, ipJ, ipN, ipNP]
def ipoLocals : List MlS := [ipQ, ipT, ipR]

/-- The rest of the block. -/
def ipoCont : ProgHOL 64 :=
  .seq (.call (some (some (.local, ipR), none)) fIpo [vv ipP, .op .add [vv ipJ, .const 1], vv ipN, vv ipNP])
    (.return (vv ipR))

def ipoBody : ProgHOL 64 := prologue ipoLocals
  (.ite (.cmp .lower (vv ipJ) (vv ipN))
    (.seq (.assign .local ipQ (.load .one (.op .add [vv ipP, .op .add [.panop .mul [vv ipJ, .const 8], .const 8]])))
    (.seq (.assign .local ipT (.load .one (vv ipQ)))
    (.ite (.cmp .equal (vv ipT) (.const 3))
      (.seq (.assign .local ipT (.load .one (.op .add [vv ipQ, .const (BitVec.ofNat 64 (8 * 3))])))
        (.seq (.call (some (some (.local, ipR), none)) fPiSortTele [.const (BitVec.ofNat 64 coreWalkFuel), vv ipT])
          (.ite (.cmp .equal (vv ipR) (.const 0)) ipoCont
            (.ite (.cmp .lower (.op .sub [vv ipR, .const 1]) (vv ipNP)) (.return (.const 0)) ipoCont))))
      (.ite (.cmp .equal (vv ipT) (.const 4))
        (.seq (.assign .local ipT (.load .one (.op .add [vv ipQ, .const (BitVec.ofNat 64 (8 * 4))])))
          (.ite (.cmp .equal (vv ipT) (vv ipNP)) ipoCont (.return (.const 0))))
        ipoCont))))
    (.return (.const 1)))

section
variable {σ : Type}

theorem ipo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ipoLocals → (ctxEnv C ++ ipoParams.zip vals).get x = none :=
  Knot.params_none C ipoLocals ipoParams vals (by decide) (by decide)

theorem indParamsOk_drop {nP : Nat} {blk : List IConstantInfo} {j : Nat} (hj : j < blk.length) :
    indParamsOk nP (blk.drop j) = (do
      let ok ← match blk[j] with
        | .indInfo cvT _ => do
          match ← piSortTeleLen? coreWalkFuel cvT.type with
          | some n => pure (decide (nP ≤ n))
          | none => pure true
        | .ctorInfo _ nPc _ _ => pure (nPc == nP)
        | _ => pure true
      if ok then indParamsOk nP (blk.drop (j + 1)) else pure false) := by
  rw [List.drop_eq_getElem_cons hj]; rfl

theorem ofNat_eq_small (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp at this; omega
  · intro e; rw [e]

theorem cellA_mulIdx (C : Ctx) (o j : Nat) (hj : j < 2 ^ 61) :
    cellA C o + (BitVec.ofNat 64 j * 8#64 + 8#64) = cellA C (o + 1 + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem cellA_plus (C : Ctx) (o k : Nat) : cellA C o + BitVec.ofNat 64 (8 * k) = cellA C (o + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [cellA, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **`indParamsOk`** over the block from index `j`. -/
theorem ipo_spec (C : Ctx) (hc : C.code.lookup fIpo = some (ipoParams.map (fun p => (p, ShapeHOL.one)), ipoBody, .one))
    (hcp : C.code.lookup fPiSortTele = some ([(pFu, .one), (pH, .one)], pstBody fPiSortTele, .one))
    (blk : List IConstantInfo) (ob nP : Nat) (hnP : nP < 2 ^ 63) (hlen : blk.length < 2 ^ 59) :
    ∀ k j (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → blk.length - j = k →
      j ≤ blk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ipoParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 blk.length,
        BitVec.ofNat 64 nP])) ipoBody s (indParamsOk nP (blk.drop j)) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro j H s hp hb hk hj
    have hjl : j = blk.length := by omega
    subst hjl
    refine specR_prologue (postB_locals _) (ipo_none _ _) ?_
    have hlw := nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ipoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW, indParamsOk], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j H s hp hb hk hj
    have hjl : j < blk.length := by omega
    obtain ⟨os, hosl, hblk, hcie⟩ := id hb
    have hoj : j < os.length := by omega
    refine specR_prologue (postB_locals _) (ipo_none _ _) ?_
    have hlw := nd_lt_iff j blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ipoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    -- the member's record pointer
    have hw : (ctxH C H).H[ob + 1 + j]? = some (cellA C os[j]) := by
      show H[ob + 1 + j]? = _
      have := hblk.2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) ipQ _ (ob + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, ipoParams, ctxEnv]; exact cellA_mulIdx C ob j (by omega)) ?_
    have hci := hcie j hjl hoj
    -- the continuation: the rest of the block
    have cont : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env), H <+: H1 → Γ.get ipP = some (cellA C ob) →
        Γ.get ipJ = some (BitVec.ofNat 64 j) → Γ.get ipN = some (BitVec.ofNat 64 blk.length) →
        Γ.get ipNP = some (BitVec.ofNat 64 nP) →
        SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ ipoLocals)) ipoCont s1 (indParamsOk nP (blk.drop (j + 1)))
          (PostB (ctxH C H)) := by
      intro H1 s1 Γ hp1 g1 g2 g3 g4
      refine specR_congr (m' := (indParamsOk nP (blk.drop (j + 1)) : AM Bool) >>= fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) ipR fIpo ipoParams [vv ipP, .op .add [vv ipJ, .const 1], vv ipN, vv ipNP]
        ipoBody [cellA C ob, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 blk.length, BitVec.ofNat 64 nP] (by decide) rfl
        (by simp +decide [ctxLocals, ipoLocals]) hc
        ⟨by simpa [sev] using g1, by simp only [sev, sev_vv, g2]; simp; exact word_add1_eq j,
          by simpa [sev] using g3, by simpa [sev] using g4, trivial⟩
        (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipoParams _ rfl hlk)
          (ih (j + 1) H1 s1 (hp.trans hp1) (indBlk_mono hb hp1) (by omega) (by omega)))
        (fun b w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW b) (by simp +decide [Env.get])
        (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    -- the member's tag word
    rw [indParamsOk_drop hjl]
    generalize hcj : blk[j] = ci at hci
    have hsQ : ∀ (Γ : Env), Γ.get ipQ = some (cellA C os[j]) → ∀ m, sev Γ (.op .add [vv ipQ, .const (BitVec.ofNat 64 (8 * m))]) =
        some (cellA C (os[j] + m)) := by
      intro Γ hq m; simp only [sev, sev_vv, hq]; simp; exact cellA_plus C _ m
    let Γ1 : Env := (ipQ, cellA C os[j]) :: (ctxEnv (ctxH C H) ++ ipoParams.zip [cellA C ob, BitVec.ofNat 64 j,
      BitVec.ofNat 64 blk.length, BitVec.ofNat 64 nP])
    have g1 : ∀ y, y ≠ ipQ → Γ1.get y = (ctxEnv (ctxH C H) ++ ipoParams.zip [cellA C ob, BitVec.ofNat 64 j,
        BitVec.ofNat 64 blk.length, BitVec.ofNat 64 nP]).get y := fun y h => by simp only [Γ1, Env.get_cons, ite_eq_right h]
    have hP1 : Γ1.get ipP = some (cellA C ob) := by simp +decide [Γ1, Env.get, ipoParams, ctxEnv]
    have hJ1 : Γ1.get ipJ = some (BitVec.ofNat 64 j) := by simp +decide [Γ1, Env.get, ipoParams, ctxEnv]
    have hN1 : Γ1.get ipN = some (BitVec.ofNat 64 blk.length) := by simp +decide [Γ1, Env.get, ipoParams, ctxEnv]
    have hNP1 : Γ1.get ipNP = some (BitVec.ofNat 64 nP) := by simp +decide [Γ1, Env.get, ipoParams, ctxEnv]
    have hQ1 : Γ1.get ipQ = some (cellA C os[j]) := by simp [Γ1, Env.get_cons]
    have ld : ∀ (Γ : Env), Γ.get ipQ = some (cellA C os[j]) → ∀ (m : Nat) (w : BitVec 64), H[os[j] + m]? = some w →
        ∀ {α : Type} {mm : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64},
        SpecR (σ := σ) (Inv (ctxH C H) s ((ipT, w) :: Γ) [] (ctxLocals ++ ipoLocals)) rest s mm R →
        SpecR (Inv (ctxH C H) s Γ [] (ctxLocals ++ ipoLocals))
          (.seq (.assign .local ipT (.load .one (.op .add [vv ipQ, .const (BitVec.ofNat 64 (8 * m))]))) rest) s mm R :=
      fun Γ hq m w hw {_} {_} {_} {_} h => UD.specR_heapLoadI' (C := ctxH C H) ipT _ (os[j] + m) w hw (by decide)
        (hsQ Γ hq m) h
    have tagW : ∀ (n : Nat), H[os[j]]? = some (BitVec.ofNat 64 n) → n < 16 →
        ∀ c, c < 16 → sev ((ipT, BitVec.ofNat 64 n) :: Γ1) (.cmp .equal (vv ipT) (.const (BitVec.ofNat 64 c))) =
          some (if n = c then 1 else 0) := by
      intro n _ hn c hc
      simp only [sev, sev_vv, Env.get_cons, ite_true]; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        ofNat_eq_small n c (by omega) (by omega)]
    have ldTag : ∀ (n : Nat), H[os[j]]? = some (BitVec.ofNat 64 n) → ∀ {α : Type} {mm : AM α}
        {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64},
        SpecR (σ := σ) (Inv (ctxH C H) s ((ipT, BitVec.ofNat 64 n) :: Γ1) [] (ctxLocals ++ ipoLocals)) rest s mm R →
        SpecR (Inv (ctxH C H) s Γ1 [] (ctxLocals ++ ipoLocals)) (.seq (.assign .local ipT (.load .one (vv ipQ))) rest) s mm R :=
      fun n hw {_} {_} {_} {_} h => UD.specR_heapLoadI' (C := ctxH C H) (Γ := Γ1) ipT (vv ipQ) os[j] _ hw (by decide)
        (by simp only [sev, sev_vv]; exact hQ1) h
    have contHere : ∀ (Γ : Env), (∀ y, y ≠ ipT → y ≠ ipQ → Γ.get y = Γ1.get y ∨ y = ipR) →
        Γ.get ipP = some (cellA C ob) → Γ.get ipJ = some (BitVec.ofNat 64 j) →
        Γ.get ipN = some (BitVec.ofNat 64 blk.length) → Γ.get ipNP = some (BitVec.ofNat 64 nP) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ ipoLocals)) ipoCont s (indParamsOk nP (blk.drop (j + 1)))
          (PostB (ctxH C H)) :=
      fun Γ _ g1 g2 g3 g4 => cont H s Γ (List.prefix_refl _) g1 g2 g3 g4
    have skipKind : ∀ (n : Nat), H[os[j]]? = some (BitVec.ofNat 64 n) → n < 16 → n ≠ 3 → n ≠ 4 →
        ∀ {mm : AM Bool}, mm s = indParamsOk nP (blk.drop (j + 1)) s →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ1 [] (ctxLocals ++ ipoLocals))
          (.seq (.assign .local ipT (.load .one (vv ipQ))) (.ite (.cmp .equal (vv ipT) (.const 3))
            (.seq (.assign .local ipT (.load .one (.op .add [vv ipQ, .const (BitVec.ofNat 64 (8 * 3))])))
              (.seq (.call (some (some (.local, ipR), none)) fPiSortTele [.const (BitVec.ofNat 64 coreWalkFuel), vv ipT])
                (.ite (.cmp .equal (vv ipR) (.const 0)) ipoCont
                  (.ite (.cmp .lower (.op .sub [vv ipR, .const 1]) (vv ipNP)) (.return (.const 0)) ipoCont))))
            (.ite (.cmp .equal (vv ipT) (.const 4))
              (.seq (.assign .local ipT (.load .one (.op .add [vv ipQ, .const (BitVec.ofNat 64 (8 * 4))])))
                (.ite (.cmp .equal (vv ipT) (vv ipNP)) ipoCont (.return (.const 0))))
              ipoCont))) s mm (PostB (ctxH C H)) := by
      intro n htag hn16 h3 h4 mm hmm
      refine ldTag n htag ?_
      have tg : ∀ c : Nat, c < 16 → c ≠ n → sev ((ipT, BitVec.ofNat 64 n) :: Γ1)
          (.cmp .equal (vv ipT) (.const (BitVec.ofNat 64 c))) = some 0 := by
        intro c hc hcn
        simp only [sev, sev_vv, Env.get_cons, ite_true]
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_eq_small n c (by omega) (by omega), Ne.symm hcn]
      refine specR_ifI _ 0 (tg 3 (by decide) (Ne.symm h3)) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (tg 4 (by decide) (Ne.symm h4)) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_congr hmm ?_
      exact cont H s _ (List.prefix_refl _) (by simp +decide [Env.get_cons]; exact hP1)
        (by simp +decide [Env.get_cons]; exact hJ1) (by simp +decide [Env.get_cons]; exact hN1)
        (by simp +decide [Env.get_cons]; exact hNP1)
    cases ci with
    | indInfo cvT caps =>
      obtain ⟨hcv, htag, -⟩ := hci
      refine ldTag 3 htag ?_
      refine specR_ifI _ 1 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      have hty : H[os[j] + 3]? = some (Enc.idxW cvT.type) := by
        have := hcv.2.2; rw [show os[j] + 1 + 2 = os[j] + 3 by omega] at this; exact this
      refine ld _ (by simp +decide [Env.get_cons]; exact hQ1) 3 _ hty ?_
      let Γ3 : Env := (ipT, Enc.idxW cvT.type) :: (ipT, BitVec.ofNat 64 3) :: Γ1
      refine specR_congr (m' := piSortTeleLen? coreWalkFuel cvT.type >>= fun o => match o with
          | some n => if nP ≤ n then indParamsOk nP (blk.drop (j + 1)) else pure false
          | none => indParamsOk nP (blk.drop (j + 1))) (by
        dsimp only
        simp only [pure_bind, decide_eq_true_eq, ite_true]) ?_
      refine specR_callNIH (C := ctxH C H) ipR fPiSortTele [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ipT]
        (pstBody fPiSortTele) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cvT.type] (by decide) rfl
        (by simp +decide [ctxLocals, ipoLocals]) hcp
        ⟨rfl, by simp only [sev, sev_vv, Env.get_cons, ite_true], trivial⟩
        (PostPST (ctxH C H) coreWalkFuel) (fun o w _ _ => w = optW o ∧ ∀ n, o = some n → n < coreWalkFuel)
        (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
          (pst_spec C hcp coreWalkFuel (by decide) H s cvT.type))
        (fun o wy s1 H1 hp1 ⟨hwy, hbd⟩ => ?_)
      have hpH : H <+: H1 := hp1
      have cgo : ∀ (Γ : Env), Γ = (ipR, wy) :: Γ3 → SpecR (σ := σ) (Inv (ctxH (ctxH C H) H1) s1 Γ [] (ctxLocals ++ ipoLocals))
          ipoCont s1 (indParamsOk nP (blk.drop (j + 1))) (PostB (ctxH C H)) := by
        intro Γ hΓ; subst hΓ
        exact cont H1 s1 _ hpH (by simp +decide [Γ3, Env.get_cons]; exact hP1)
          (by simp +decide [Γ3, Env.get_cons]; exact hJ1) (by simp +decide [Γ3, Env.get_cons]; exact hN1)
          (by simp +decide [Γ3, Env.get_cons]; exact hNP1)
      rcases o with _ | n
      · subst hwy
        refine specR_ifI _ 1 (by simp [sev, Env.get_cons, optW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact cgo _ rfl
      · subst hwy
        have hn := hbd n rfl
        have hcw : coreWalkFuel < 2 ^ 63 := by decide
        refine specR_ifI _ 0 (by
            simp only [sev, sev_vv, Env.get_cons, ite_true, optW]
            simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_eq_small (n + 1) 0 (by omega) (by omega)])
          (fun h => absurd rfl h) (fun _ => ?_)
        have hsub : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        have hlt : sev ((ipR, optW (some n)) :: Γ3) (.cmp .lower (.op .sub [vv ipR, .const 1]) (vv ipNP)) =
            some (if n < nP then 1 else 0) := by
          simp only [sev, sev_vv, Env.get_cons, ite_true, optW, ite_eq_right (show ipNP ≠ ipR by decide), Γ3,
            ite_eq_right (show ipNP ≠ ipT by decide), hNP1, Option.bind_eq_bind, Option.bind_some, Option.pure_def, hsub]
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nd_lt_iff n nP (by omega) (by omega)]
        by_cases hnl : n < nP
        · refine specR_ifI _ _ hlt (fun _ => ?_) (fun h => by simp [hnl] at h)
          simp only [show ¬ nP ≤ n by omega, ite_false]
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hpH, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ _ hlt (fun h => by simp [hnl] at h) (fun _ => ?_)
          simp only [show nP ≤ n by omega, ite_true]
          exact cgo _ rfl
    | ctorInfo cv np nf ind =>
      obtain ⟨-, htag, ⟨hnp, hnp63⟩, -⟩ := hci
      refine ldTag 4 htag ?_
      refine specR_ifI _ 0 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine ld _ (by simp +decide [Env.get_cons]; exact hQ1) 4 _ hnp ?_
      have hcmp : sev ((ipT, BitVec.ofNat 64 np) :: (ipT, BitVec.ofNat 64 4) :: Γ1) (.cmp .equal (vv ipT) (vv ipNP)) =
          some (if np = nP then 1 else 0) := by
        simp only [sev, sev_vv, Env.get_cons, ite_true, ite_eq_right (show ipNP ≠ ipT by decide), hNP1]
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_eq_small np nP (by omega) (by omega)]
      by_cases he : np = nP
      · refine specR_ifI _ _ hcmp (fun _ => ?_) (fun h => by simp [he] at h)
        refine specR_congr (m' := indParamsOk nP (blk.drop (j + 1))) (by simp [he]) ?_
        exact cont H s _ (List.prefix_refl _) (by simp +decide [Env.get_cons]; exact hP1)
          (by simp +decide [Env.get_cons]; exact hJ1) (by simp +decide [Env.get_cons]; exact hN1)
          (by simp +decide [Env.get_cons]; exact hNP1)
      · refine specR_ifI _ _ hcmp (fun h => by simp [he] at h) (fun _ => ?_)
        refine specR_congr (m' := pure false) (by simp [he]) ?_
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | axiomInfo cv => exact skipKind 0 hci.2 (by decide) (by decide) (by decide) (by simp)
    | defnInfo cv v hint => exact skipKind 1 hci.2.1 (by decide) (by decide) (by decide) (by simp)
    | thmInfo cv => exact skipKind 2 hci.2 (by decide) (by decide) (by decide) (by simp)
    | recInfo cv mi rp isK rules => exact skipKind 5 hci.2.1 (by decide) (by decide) (by decide) (by simp)

end

end ConPanqueque.T.Ind
