import ConPanqueque.T.Ind.Groups
import ConPanqueque.T.Ex.BinderPair

/-!
# The recursors' shapes (`readBlock`'s `recsL`)

Every recursor record becomes a `RecShape`: its constant, rule prefix, major index, the member its major
names (`recTargetOf`) and its rules and K flag.  `recsFill(p, j, n, k, o, b)` builds the records `j … n - 1`
as six-word blocks, the pointer of record `j` in slot `j - b` of the block at `o`; `recShapes` allocates the
pointer block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI

/-- One recursor record's shape (`readBlock`'s `recsL` step). -/
def recShapeOf (names : List NIdx) (r : IConstantVal × Nat × Nat × Bool × List IRecRule) : AM RecShape := do
  let tgt ← recTargetOf names r.2.1 r.1.type
  pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.2, r.2.2.2.1⟩ : RecShape)

def alloc6 (C : Ctx) (x : MlS) (e0 e1 e2 e3 e4 e5 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 48) (.seq (.store (vv x) e0)
    (.seq (.store (.op .add [vv x, .const 8]) e1) (.seq (.store (.op .add [vv x, .const 16]) e2)
    (.seq (.store (.op .add [vv x, .const 24]) e3) (.seq (.store (.op .add [vv x, .const 32]) e4)
    (.seq (.store (.op .add [vv x, .const 40]) e5) rest))))))

/-- The image after writing six words at `H2.length …`. -/
def img6 (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 w5 : BitVec 64) : List (BitVec 64) :=
  ((((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2).set (H2.length + 3) w3).set
    (H2.length + 4) w4).set (H2.length + 5) w5

section
variable {σ : Type}

theorem specR_alloc6I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (e0 e1 e2 e3 e4 e5 : ExpHOL 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) (hx : x ∈ D)
    (h0 : ∀ v, sev ((x, v) :: Γ) e0 = some w0) (h1 : ∀ v, sev ((x, v) :: Γ) e1 = some w1)
    (h2 : ∀ v, sev ((x, v) :: Γ) e2 = some w2) (h3 : ∀ v, sev ((x, v) :: Γ) e3 = some w3)
    (h4 : ∀ v, sev ((x, v) :: Γ) e4 = some w4) (h5 : ∀ v, sev ((x, v) :: Γ) e5 = some w5)
    (hk : ∀ (H2 ws : List (BitVec 64)), C.H <+: H2 → ws.length = 6 → H2.length + 6 ≤ C.HN →
      SpecR (Inv (ctxH C (img6 H2 ws w0 w1 w2 w3 w4 w5)) s ((x, cellA C H2.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (alloc6 C x e0 e1 e2 e3 e4 e5 rest) s m R := by
  unfold alloc6
  refine specR_allocI x _ 6 (by decide) hx (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) e0 H2.length (by simp [ctxH, hws]) w0 (by simp [cellA, ctxH])
    (h0 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e1 (H2.length + 1) (by simp [ctxH, hws]) w1
    (by simp [sev]; exact cellA_add_ofNat C H2.length 1) (h1 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e2 (H2.length + 2) (by simp [ctxH, hws]) w2
    (by simp [sev]; exact cellA_add_ofNat C H2.length 2) (h2 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e3 (H2.length + 3) (by simp [ctxH, hws]) w3
    (by simp [sev]; exact cellA_add_ofNat C H2.length 3) (h3 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e4 (H2.length + 4) (by simp [ctxH, hws]) w4
    (by simp [sev]; exact cellA_add_ofNat C H2.length 4) (h4 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e5 (H2.length + 5) (by simp [ctxH, hws]) w5
    (by simp [sev]; exact cellA_add_ofNat C H2.length 5) (h5 _) ?_
  exact hk H2 ws hp hws hroom

theorem img6_len (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 w5 : BitVec 64) (h : ws.length = 6) :
    (img6 H2 ws w0 w1 w2 w3 w4 w5).length = H2.length + 6 := by simp [img6, h]

theorem img6_prefix (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 w5 : BitVec 64) (h : ws.length = 6) :
    H2 <+: img6 H2 ws w0 w1 w2 w3 w4 w5 :=
  prefix_of_get? (by simp [img6, h]) (fun k hk => by
    simp only [img6]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_append_left hk])

theorem img6_get (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 w5 : BitVec 64) (h : ws.length = 6) :
    (img6 H2 ws w0 w1 w2 w3 w4 w5)[H2.length]? = some w0 ∧ (img6 H2 ws w0 w1 w2 w3 w4 w5)[H2.length + 1]? = some w1 ∧
    (img6 H2 ws w0 w1 w2 w3 w4 w5)[H2.length + 2]? = some w2 ∧ (img6 H2 ws w0 w1 w2 w3 w4 w5)[H2.length + 3]? = some w3 ∧
    (img6 H2 ws w0 w1 w2 w3 w4 w5)[H2.length + 4]? = some w4 ∧ (img6 H2 ws w0 w1 w2 w3 w4 w5)[H2.length + 5]? = some w5 := by
  have hl : (H2 ++ ws).length = H2.length + 6 := by simp [h]
  simp only [img6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hl]; omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hl]; omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hl]; omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hl]; omega)]
  · rw [List.getElem?_set_self (by simp [hl]; omega)]

end

/-- A recursor block at `og`, the constant and the rules read in the base heap `Hc`. -/
def RecW (C : Ctx) (Hc H : List (BitVec 64)) (og : Nat) (r : RecShape) : Prop :=
  (∃ oc, H[og]? = some (cellA C oc) ∧ CVRep C Hc oc r.cvR) ∧ NatE H (og + 1) r.rP ∧ NatE H (og + 2) r.mI ∧
    NatE H (og + 3) r.tgt ∧ (∃ w, H[og + 4]? = some w ∧ RulesE C.HB Hc w r.rules) ∧ H[og + 5]? = some (boolW r.isK)

theorem recW_prefix {C : Ctx} {Hc H H' : List (BitVec 64)} {og : Nat} {r : RecShape} (h : RecW C Hc H og r)
    (hp : H <+: H') : RecW C Hc H' og r := by
  obtain ⟨⟨oc, a1, a2⟩, b, c, d, ⟨w, e1, e2⟩, f⟩ := h
  exact ⟨⟨oc, get_prefix a1 hp, a2⟩, natE_mono hp b, natE_mono hp c, natE_mono hp d, ⟨w, get_prefix e1 hp, e2⟩,
    get_prefix f hp⟩

theorem recW_set {C : Ctx} {Hc H : List (BitVec 64)} {og : Nat} {r : RecShape} (h : RecW C Hc H og r) (j : Nat)
    (hj : j < og ∨ og + 6 ≤ j) (v : BitVec 64) : RecW C Hc (H.set j v) og r := by
  obtain ⟨⟨oc, a1, a2⟩, ⟨b, b'⟩, ⟨c, c'⟩, ⟨d, d'⟩, ⟨w, e1, e2⟩, f⟩ := h
  refine ⟨⟨oc, ?_, a2⟩, ⟨?_, b'⟩, ⟨?_, c'⟩, ⟨?_, d'⟩, ⟨w, ?_, e2⟩, ?_⟩ <;> rw [List.getElem?_set_ne (by omega)] <;>
    assumption

theorem recRep_of_recW {C : Ctx} {Hc H : List (BitVec 64)} {og : Nat} {r : RecShape} (h : RecW C Hc H og r)
    (hp : Hc <+: H) : RecRep C H og r := by
  obtain ⟨⟨oc, a1, a2⟩, b, c, d, ⟨w, e1, e2⟩, f⟩ := h
  exact ⟨⟨oc, a1, cvRep_mono hp a2⟩, b, c, d, ⟨w, e1, ConPanqueque.T.Decl.rulesE_mono hp e2⟩, f⟩

/-- Slots `0 … |rs| - 1` of the pointer block at `o`: each a recursor block above `lo`. -/
def RSlots (C : Ctx) (Hc H : List (BitVec 64)) (o lo : Nat) (rs : List RecShape) : Prop :=
  ∀ i (hi : i < rs.length), ∃ og, lo ≤ og ∧ H[o + 1 + i]? = some (cellA C og) ∧ RecW C Hc H og rs[i]

def rcP := ofString "rc_p"
def rcJ := ofString "rc_j"
def rcN := ofString "rc_n"
def rcK := ofString "rc_k"
def rcO := ofString "rc_o"
def rcB := ofString "rc_b"
def rcQ := ofString "rc_q"
def rcT := ofString "rc_t"
def rcM := ofString "rc_m"
def rcX := ofString "rc_x"
def rcRP := ofString "rc_rp"
def rcRL := ofString "rc_rl"
def rcIK := ofString "rc_ik"
def rcR := ofString "rc_r"
def fRecsFill := ofString "recsFill"

def rcParams : List MlS := [rcP, rcJ, rcN, rcK, rcO, rcB]
def rcLocals : List MlS := [rcQ, rcT, rcM, rcX, rcRP, rcRL, rcIK, rcR]

def rcLoad (x : MlS) (k : Nat) : ProgHOL 64 → ProgHOL 64 :=
  .seq (.assign .local x (.load .one (.op .add [vv rcQ, .const (BitVec.ofNat 64 (8 * k))])))

def rcBody (C : Ctx) : ProgHOL 64 := prologue rcLocals
  (.ite (.cmp .lower (vv rcJ) (vv rcN))
    (.seq (.assign .local rcQ (.load .one (.op .add [vv rcP, .op .add [.panop .mul [vv rcJ, .const 8], .const 8]])))
    (rcLoad rcT 3 (rcLoad rcM 4
    (.seq (.call (some (some (.local, rcX), none)) fRecTarget [vv rcP, vv rcK, vv rcM, vv rcT])
    (rcLoad rcRP 5 (rcLoad rcRL 7 (rcLoad rcIK 6
    (alloc6 C rcR (.op .add [vv rcQ, .const (BitVec.ofNat 64 (8 * 1))]) (vv rcRP) (vv rcM) (vv rcX) (vv rcRL) (vv rcIK)
    (.seq (.store (.op .add [vv rcO, .op .add [.panop .mul [.op .sub [vv rcJ, vv rcB], .const 8], .const 8]]) (vv rcR))
    (.seq (.call (some (some (.local, rcX), none)) fRecsFill
        [vv rcP, .op .add [vv rcJ, .const 1], vv rcN, vv rcK, vv rcO, vv rcB])
      (.return (.const 0))))))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem rc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rcLocals → (ctxEnv C ++ rcParams.zip vals).get x = none :=
  Knot.params_none C rcLocals rcParams vals (by decide) (by decide)

def PostRC (C : Ctx) (Hc : List (BitVec 64)) (o lo kk : Nat) (done rs : List RecShape) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ RSlots C Hc H' o lo (done ++ rs) ∧ (done ++ rs).length = kk

theorem postRC_locals (C : Ctx) (Hc : List (BitVec 64)) (o lo kk : Nat) (done : List RecShape) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostRC C Hc o lo kk done a w s' st → PostRC C Hc o lo kk done a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h, hl⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h, hl⟩

/-- **`recsFill`** from record `j`, the shapes `done` of records `b … j - 1` in their slots. -/
theorem rc_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fRecsFill = some (rcParams.map (fun p => (p, ShapeHOL.one)), rcBody C, .one))
    (hcr : C.code.lookup fRecTarget = some (rtParams.map (fun p => (p, ShapeHOL.one)), rtBody C, .one))
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k b o : Nat) (Hc : List (BitVec 64))
    (hk : k ≤ blk.length) (hb : b ≤ blk.length) (hlen : blk.length < 2 ^ 59)
    (hrk : ∀ i, b ≤ i → i < blk.length → kindAt blk i = some 5)
    (hCc : C.H <+: Hc) (hblk : IndBlk C Hc ob blk) (hco1 : Hc.length ≤ o + 1) :
    ∀ f j (done : List RecShape) (H : List (BitVec 64)) (s : AState),
      Hc <+: H → o + 1 + (blk.length - b) ≤ H.length → done.length = j - b → b ≤ j →
      RSlots C Hc H o (o + 1 + (blk.length - b)) done → blk.length - j = f → j ≤ blk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (rcParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 blk.length,
        BitVec.ofNat 64 k, cellA C o, BitVec.ofNat 64 b])) (rcBody C) s
        (((blk.drop j).map recT).mapM (recShapeOf ((blk.take k).map (fun (c : IConstantInfo) => c.name))))
        (PostRC C Hc o (o + 1 + (blk.length - b)) (blk.length - b) done) := by
  intro f
  induction f with
  | zero =>
    intro j done H s hcH hroom hdl hbj hsl hf hj
    have hjn : j = blk.length := by omega
    subst hjn
    refine specR_prologue (postRC_locals _ _ _ _ _ _) (rc_none _ _) ?_
    have hlw := nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, List.map_nil, List.mapM_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hcH, sr_of_eq ht.sr rfl rfl rfl rfl, by simpa using hsl,
      by simp; omega⟩)
  | succ f ih =>
    intro j done H s hcH hroom hdl hbj hsl hf hj
    have hjn : j < blk.length := by omega
    refine specR_prologue (postRC_locals _ _ _ _ _ _) (rc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff j blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjn])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hjn, List.map_cons, List.mapM_cons]
    have hcH' := hcH
    obtain ⟨os, hosl, hblkp, hcie⟩ := id hblk
    have hoj : j < os.length := by omega
    have hci := hcie j hjn hoj
    have hk5 := hrk j hbj hjn
    let Γ0 : Env := ctxEnv (ctxH C H) ++ rcParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 blk.length,
      BitVec.ofNat 64 k, cellA C o, BitVec.ofNat 64 b]
    have vP : Γ0.get rcP = some (cellA C ob) := by simp +decide [Γ0, Env.get, rcParams, ctxEnv]
    have vJ : Γ0.get rcJ = some (BitVec.ofNat 64 j) := by simp +decide [Γ0, Env.get, rcParams, ctxEnv]
    have vN : Γ0.get rcN = some (BitVec.ofNat 64 blk.length) := by simp +decide [Γ0, Env.get, rcParams, ctxEnv]
    have vK : Γ0.get rcK = some (BitVec.ofNat 64 k) := by simp +decide [Γ0, Env.get, rcParams, ctxEnv]
    have vO : Γ0.get rcO = some (cellA C o) := by simp +decide [Γ0, Env.get, rcParams, ctxEnv]
    have vB : Γ0.get rcB = some (BitVec.ofNat 64 b) := by simp +decide [Γ0, Env.get, rcParams, ctxEnv]
    -- the parameters, through any locals
    have pk : ∀ (Γ : Env), (∀ z, z ∉ rcLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ rcParams → ∀ v,
        Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
      have hyl : y ∉ rcLocals := by
        simp only [rcParams, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simp only [sev, sev_vv, hΓ y hyl, h]
    have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ rcLocals → z ∉ rcLocals →
        Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
      have hne : z ≠ x := fun e => hz (e ▸ hx)
      simp only [Env.get_cons, hne, ite_false]
    have hw : (ctxH C H).H[ob + 1 + j]? = some (cellA C os[j]) := by
      show H[ob + 1 + j]? = _
      have := hblkp.2 j (by simp; omega); exact get_prefix (by simpa using this) hcH
    refine UD.specR_heapLoadI' (C := ctxH C H) rcQ _ (ob + 1 + j) _ hw (by simp +decide [ctxLocals, rcLocals])
      (by
        have e : sev Γ0 (.op .add [vv rcP, .op .add [.panop .mul [vv rcJ, .const 8], .const 8]]) =
            some (cellA C (ob + 1 + j)) := by
          simp only [sev, sev_vv, vP, vJ]; simp; exact cellA_mulIdx C ob j (by omega)
        exact e) ?_
    generalize hcj : blk[j] = ci at hci hk5 ⊢
    cases ci with
    | recInfo cvR mI rP isK rules =>
      obtain ⟨hcv, -, ⟨hmi, hmi63⟩, ⟨hrp, hrp63⟩, hik, ⟨wr, hwr, hrul⟩⟩ := hci
      have hrt : recT (.recInfo cvR mI rP isK rules) = (cvR, mI, rP, isK, rules) := rfl
      rw [hrt]
      have hsQ : ∀ (Γ : Env), Γ.get rcQ = some (cellA C os[j]) → ∀ q, sev Γ (.op .add [vv rcQ,
          .const (BitVec.ofNat 64 (8 * q))]) = some (cellA C (os[j] + q)) := by
        intro Γ hq q; simp only [sev, sev_vv, hq]; simp; exact cellA_plus C _ q
      have hty : (ctxH C H).H[os[j] + 3]? = some (Enc.idxW cvR.type) := by
        have := hcv.2.2; rw [show os[j] + 1 + 2 = os[j] + 3 by omega] at this; exact get_prefix this hcH
      refine UD.specR_heapLoadI' (C := ctxH C H) rcT _ (os[j] + 3) _ hty (by simp +decide [ctxLocals, rcLocals])
        (hsQ _ (by simp [Env.get_cons]) 3) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) rcM _ (os[j] + 4) _ (get_prefix hmi hcH)
        (by simp +decide [ctxLocals, rcLocals]) (hsQ _ (by simp +decide [Env.get_cons]) 4) ?_
      let Γ2 : Env := (rcM, BitVec.ofNat 64 mI) :: (rcT, Enc.idxW cvR.type) :: (rcQ, cellA C os[j]) :: Γ0
      have hΓ2 : ∀ z, z ∉ rcLocals → Γ2.get z = Γ0.get z := fun z hz => by
        simp only [Γ2]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]
      unfold recShapeOf
      simp only [bind_assoc]
      refine specR_callNIH (C := ctxH C H) rcX fRecTarget rtParams [vv rcP, vv rcK, vv rcM, vv rcT] (rtBody C)
        [cellA C ob, BitVec.ofNat 64 k, BitVec.ofNat 64 mI, Enc.idxW cvR.type] (by decide) rfl
        (by simp +decide [ctxLocals, rcLocals]) hcr
        ⟨pk Γ2 hΓ2 rcP (by decide) _ vP, pk Γ2 hΓ2 rcK (by decide) _ vK, by simp [Γ2, sev, Env.get_cons],
          by simp +decide [Γ2, sev, Env.get_cons], trivial⟩
        (fun a w s' st => PostN (ctxH C H) a w s' st ∧ a ≤ k) (fun a w _ _ => w = BitVec.ofNat 64 a ∧ a ≤ k)
        (fun a w s' st ⟨⟨H', hp', hw', hsr⟩, hak⟩ => ⟨H', hp', ⟨hw', hak⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rtParams _ rfl hlk)
          (rt_spec C hok hcs hcg hcn blk ob k mI cvR.type hk hlen (by omega) H s (hCc.trans hcH)
            (indBlk_mono hblk hcH)))
        (fun tgt wx s1 H1 hp1 ⟨hwx, htk⟩ => ?_)
      subst hwx
      simp only [pure_bind]
      have hpH1 : H <+: H1 := hp1
      have hc1 : Hc <+: H1 := hcH.trans hpH1
      let Γ3 : Env := (rcX, BitVec.ofNat 64 tgt) :: Γ2
      have hΓ3 : ∀ z, z ∉ rcLocals → Γ3.get z = Γ0.get z := fun z hz => by
        simp only [Γ3]; rw [cnl (by decide) hz]; exact hΓ2 z hz
      have gQ3 : Γ3.get rcQ = some (cellA C os[j]) := by simp +decide [Γ3, Γ2, Env.get_cons]
      refine UD.specR_heapLoadI' (C := ctxH C H1) rcRP _ (os[j] + 5) _ (get_prefix hrp hc1)
        (by simp +decide [ctxLocals, rcLocals]) (hsQ _ gQ3 5) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H1) rcRL _ (os[j] + 7) _ (get_prefix hwr hc1)
        (by simp +decide [ctxLocals, rcLocals]) (hsQ _ (by simp +decide [Env.get_cons, gQ3]) 7) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H1) rcIK _ (os[j] + 6) _ (get_prefix hik hc1)
        (by simp +decide [ctxLocals, rcLocals]) (hsQ _ (by simp +decide [Env.get_cons, gQ3]) 6) ?_
      let Γ4 : Env := (rcIK, boolW isK) :: (rcRL, wr) :: (rcRP, BitVec.ofNat 64 rP) :: Γ3
      have hΓ4 : ∀ z, z ∉ rcLocals → Γ4.get z = Γ0.get z := fun z hz => by
        simp only [Γ4]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ3 z hz
      have hok1 := ctxOK_H hok H1
      refine specR_alloc6I (C := ctxH C H1) hok1 rcR _ _ _ _ _ _ (cellA C (os[j] + 1)) (BitVec.ofNat 64 rP)
        (BitVec.ofNat 64 mI) (BitVec.ofNat 64 tgt) wr (boolW isK) (by simp +decide [ctxLocals, rcLocals])
        (fun v => hsQ _ (by simp +decide [Env.get_cons, Γ4, gQ3]) 1)
        (fun v => by simp +decide [sev, Env.get_cons, Γ4])
        (fun v => by simp +decide [sev, Env.get_cons, Γ4, Γ3, Γ2])
        (fun v => by simp +decide [sev, Env.get_cons, Γ4, Γ3])
        (fun v => by simp +decide [sev, Env.get_cons, Γ4])
        (fun v => by simp +decide [sev, Env.get_cons, Γ4])
        (fun H2 ws hp2 hws hroom2 => ?_)
      have hpH2 : H1 <+: H2 := hp2
      have hl1 := hpH1.length_le
      have hl2 := hpH2.length_le
      let I6 := img6 H2 ws (cellA C (os[j] + 1)) (BitVec.ofNat 64 rP) (BitVec.ofNat 64 mI) (BitVec.ofNat 64 tgt) wr
        (boolW isK)
      have hI6l : I6.length = H2.length + 6 := img6_len _ _ _ _ _ _ _ _ hws
      have hI6p : H2 <+: I6 := img6_prefix _ _ _ _ _ _ _ _ hws
      obtain ⟨g0, g1, g2, g3, g4, g5⟩ := img6_get H2 ws (cellA C (os[j] + 1)) (BitVec.ofNat 64 rP) (BitVec.ofNat 64 mI)
        (BitVec.ofNat 64 tgt) wr (boolW isK) hws
      let Γ5 : Env := (rcR, cellA (ctxH C H1) H2.length) :: Γ4
      have hΓ5 : ∀ z, z ∉ rcLocals → Γ5.get z = Γ0.get z := fun z hz => by
        simp only [Γ5]; rw [cnl (by decide) hz]; exact hΓ4 z hz
      have gO := pk Γ5 hΓ5 rcO (by decide) _ vO
      have gJ := pk Γ5 hΓ5 rcJ (by decide) _ vJ
      have gB := pk Γ5 hΓ5 rcB (by decide) _ vB
      have hslot : o + 1 + (j - b) < I6.length := by omega
      refine specR_heapStoreI (ctxOK_H hok I6) (.op .add [vv rcO, .op .add [.panop .mul [.op .sub [vv rcJ, vv rcB],
          .const 8], .const 8]]) (vv rcR) (o + 1 + (j - b)) hslot (cellA C H2.length)
        (by
          have e : sev Γ5 (.op .add [vv rcO, .op .add [.panop .mul [.op .sub [vv rcJ, vv rcB], .const 8], .const 8]]) =
              some (cellA C (o + 1 + (j - b))) := by
            simp only [sev] at gO gJ gB ⊢; rw [gO, gJ, gB]; simp
            rw [ofNat_sub_small j b hbj (by omega)]; exact cellA_mulIdx C o (j - b) (by omega)
          exact e)
        (by simp [Γ5, sev, Env.get_cons]; rfl) ?_
      let H3 := I6.set (o + 1 + (j - b)) (cellA C H2.length)
      have hl3 : H3.length = H2.length + 6 := by simp [H3, hI6l]
      have hcI : H <+: I6 := (hpH1.trans hpH2).trans hI6p
      have hc3 : Hc <+: H3 := prefix_set (hcH.trans hcI) (by omega) _
      let r : RecShape := ⟨cvR, rP, mI, tgt, rules, isK⟩
      have hsl3 : RSlots C Hc H3 o (o + 1 + (blk.length - b)) (done ++ [r]) := by
        intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases e : i < done.length
        · obtain ⟨og, hlo, h1, h2⟩ := hsl i e
          rw [List.getElem_append_left e]
          refine ⟨og, hlo, ?_, recW_set (recW_prefix h2 hcI) _ (Or.inl (by omega)) _⟩
          rw [List.getElem?_set_ne (by omega)]; exact get_prefix h1 hcI
        · have : i = done.length := by omega
          subst this
          simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
          refine ⟨H2.length, by omega, ?_, recW_set ?_ _ (Or.inl (by omega)) _⟩
          · rw [hdl, List.getElem?_set_self (by omega)]
          · exact ⟨⟨os[j] + 1, g0, hcv⟩, ⟨g1, hrp63⟩, ⟨g2, hmi63⟩, ⟨g3, Nat.lt_of_le_of_lt htk (by omega)⟩, ⟨wr, g4, hrul⟩, g5⟩
      let Γ6 : Env := Γ5
      have gP := pk Γ5 hΓ5 rcP (by decide) _ vP
      have gN := pk Γ5 hΓ5 rcN (by decide) _ vN
      have gK := pk Γ5 hΓ5 rcK (by decide) _ vK
      refine specR_callNIG (C := ctxH (ctxH C I6) H3) rcX fRecsFill rcParams
        [vv rcP, .op .add [vv rcJ, .const 1], vv rcN, vv rcK, vv rcO, vv rcB] (rcBody C)
        [cellA C ob, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 blk.length, BitVec.ofNat 64 k, cellA C o,
          BitVec.ofNat 64 b] (by decide) rfl (by simp +decide [ctxLocals, rcLocals]) hc
        ⟨gP, by
          have e : sev Γ5 (.op .add [vv rcJ, .const 1]) = some (BitVec.ofNat 64 (j + 1)) := by
            simp only [sev] at gJ ⊢; rw [gJ]; simp; exact word_add1_eq j
          exact e, gN, gK, gO, gB, trivial⟩
        (PostRC C Hc o (o + 1 + (blk.length - b)) (blk.length - b) (done ++ [r]))
        (fun rs2 _ _ H4 => Hc <+: H4 ∧ RSlots C Hc H4 o (o + 1 + (blk.length - b)) (done ++ [r] ++ rs2) ∧
          (done ++ [r] ++ rs2).length = blk.length - b)
        (fun rs2 w s' st ⟨H', hp', hs', h', hl'⟩ => ⟨H', ⟨hp', h', hl'⟩, hs'⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rcParams _ rfl hlk)
          (ih (j + 1) (done ++ [r]) H3 s1 hc3 (by omega) (by simp [hdl]; omega) (by omega) hsl3 (by omega) (by omega)))
        (fun rs2 w4 s4 H4 ⟨hc4, hsl4, hl4⟩ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hc4, sr_of_eq ht.sr rfl rfl rfl rfl, by simpa using hsl4,
        by simpa using hl4⟩)
    | _ => simp [kindAt, List.getElem?_eq_getElem hjn, hcj, kindOf] at hk5

end

def rhP := ofString "rh_p"
def rhB := ofString "rh_b"
def rhN := ofString "rh_n"
def rhK := ofString "rh_k"
def rhO := ofString "rh_o"
def rhX := ofString "rh_x"
def fRecShapes := ofString "recShapes"

def rhParams : List MlS := [rhP, rhB, rhN, rhK]
def rhLocals : List MlS := [rhO, rhX]

/-- The pointer block `[n - b, rec_b, …]`. -/
def rhBody (C : Ctx) : ProgHOL 64 := prologue rhLocals
  (allocP C rhO (.op .add [.panop .mul [.op .sub [vv rhN, vv rhB], .const 8], .const 8])
  (.seq (.store (vv rhO) (.op .sub [vv rhN, vv rhB]))
  (.seq (.call (some (some (.local, rhX), none)) fRecsFill [vv rhP, vv rhB, vv rhN, vv rhK, vv rhO, vv rhB])
    (.return (vv rhO)))))

section
variable {σ : Type}

theorem rh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rhLocals → (ctxEnv C ++ rhParams.zip vals).get x = none :=
  Knot.params_none C rhLocals rhParams vals (by decide) (by decide)

/-- The recursors: a pointer block of `RecRep` blocks, in a bigger heap. -/
def PostRH (C : Ctx) (rs : List RecShape) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ o, w = cellA C o ∧ PtrsRep C H' o (fun og r => RecRep C H' og r) rs

theorem postRH_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRH C a w s' st → PostRH C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

/-- **`recShapes`**: the recursor records `b …` of the block. -/
theorem rh_spec (C : Ctx) (hok : CtxOK C)
    (hch : C.code.lookup fRecShapes = some (rhParams.map (fun p => (p, ShapeHOL.one)), rhBody C, .one))
    (hc : C.code.lookup fRecsFill = some (rcParams.map (fun p => (p, ShapeHOL.one)), rcBody C, .one))
    (hcr : C.code.lookup fRecTarget = some (rtParams.map (fun p => (p, ShapeHOL.one)), rtBody C, .one))
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k b : Nat)
    (hk : k ≤ blk.length) (hb : b ≤ blk.length) (hlen : blk.length < 2 ^ 59)
    (hrk : ∀ i, b ≤ i → i < blk.length → kindAt blk i = some 5)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hblk : IndBlk C H ob blk) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rhParams.zip [cellA C ob, BitVec.ofNat 64 b, BitVec.ofNat 64 blk.length,
        BitVec.ofNat 64 k])) (rhBody C) s
      (((blk.drop b).map recT).mapM (recShapeOf ((blk.take k).map (fun (c : IConstantInfo) => c.name))))
      (PostRH (ctxH C H)) := by
  refine specR_prologue (postRH_locals _) (rh_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  let Γ0 : Env := ctxEnv (ctxH C H) ++ rhParams.zip [cellA C ob, BitVec.ofNat 64 b, BitVec.ofNat 64 blk.length,
    BitVec.ofNat 64 k]
  have vB : Γ0.get rhB = some (BitVec.ofNat 64 b) := by simp +decide [Γ0, Env.get, rhParams, ctxEnv]
  have vN : Γ0.get rhN = some (BitVec.ofNat 64 blk.length) := by simp +decide [Γ0, Env.get, rhParams, ctxEnv]
  have hsub : ∀ (Γ : Env), sev Γ (vv rhN) = some (BitVec.ofNat 64 blk.length) → sev Γ (vv rhB) = some (BitVec.ofNat 64 b) →
      sev Γ (.op .sub [vv rhN, vv rhB]) = some (BitVec.ofNat 64 (blk.length - b)) := fun Γ h1 h2 => by
    simp only [sev] at h1 h2 ⊢; rw [h1, h2]; simp; exact ofNat_sub_small _ _ hb (by omega)
  have gv0 : ∀ y v, y ≠ rhO → Γ0.get y = some v → ∀ w, sev ((rhO, w) :: Γ0) (vv y) = some v := fun y v hy h w => by
    simp only [sev, sev_vv, Env.get_cons, hy, ite_false, h]
  refine specR_allocI (C := ctxH C H) rhO _ (blk.length - b + 1) (by omega) (by simp +decide [ctxLocals, rhLocals])
    (fun v => by
      have h1 := hsub _ (gv0 rhN _ (by decide) vN v) (gv0 rhB _ (by decide) vB v)
      simp only [sev] at h1 ⊢; rw [h1]; simp; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H1 ws hp1 hws hroom1 => ?_)
  have hp1' : H <+: H1 := hp1
  have hroom1' : H1.length + (blk.length - b + 1) ≤ C.HN := hroom1
  have hl1 := hp1'.length_le
  let Γ1 : Env := (rhO, cellA (ctxH C H) H1.length) :: Γ0
  have gv : ∀ y v, y ≠ rhO → Γ0.get y = some v → sev Γ1 (vv y) = some v := fun y v hy h => gv0 y v hy h _
  refine specR_heapStoreI (ctxOK_H hok (H1 ++ ws)) (vv rhO) (.op .sub [vv rhN, vv rhB]) H1.length
    (by show _ < (H1 ++ ws).length; simp; omega) (BitVec.ofNat 64 (blk.length - b)) (by simp [Γ1, sev, Env.get_cons]; rfl)
    (hsub _ (gv rhN _ (by decide) vN) (gv rhB _ (by decide) vB)) ?_
  let H2 := (H1 ++ ws).set H1.length (BitVec.ofNat 64 (blk.length - b))
  let Hc := H2.take (H1.length + 1)
  have hl2 : H2.length = H1.length + (blk.length - b + 1) := by simp [H2, hws]
  have hcH2 : Hc <+: H2 := List.take_prefix _ _
  have hHH2 : H <+: H2 := prefix_set (hp1'.trans (List.prefix_append _ _)) hl1 _
  have hHc : H <+: Hc := prefix_take_of hHH2 (by omega)
  have hHcl : Hc.length = H1.length + 1 := by simp [Hc]; omega
  have hco0 : Hc[H1.length]? = some (BitVec.ofNat 64 (blk.length - b)) := by
    simp only [Hc, H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by simp; omega)
  refine specR_congr (m' := ((blk.drop b).map recT).mapM (recShapeOf ((blk.take k).map (fun (c : IConstantInfo) => c.name)))
      >>= fun r => pure r) (by rw [bind_pure]) ?_
  refine specR_callNIG (C := ctxH (ctxH C (H1 ++ ws)) H2) (D := ctxLocals ++ rhLocals) rhX fRecsFill rcParams
    [vv rhP, vv rhB, vv rhN, vv rhK, vv rhO, vv rhB] (rcBody C)
    [cellA C ob, BitVec.ofNat 64 b, BitVec.ofNat 64 blk.length, BitVec.ofNat 64 k, cellA C H1.length,
      BitVec.ofNat 64 b] (by decide) rfl (by simp +decide [ctxLocals, rhLocals]) hc
    ⟨gv rhP _ (by decide) (by simp +decide [Γ0, Env.get, rhParams, ctxEnv]), gv rhB _ (by decide) vB,
      gv rhN _ (by decide) vN, gv rhK _ (by decide) (by simp +decide [Γ0, Env.get, rhParams, ctxEnv]),
      by simp [Γ1, sev, Env.get_cons]; rfl, gv rhB _ (by decide) vB, trivial⟩
    (PostRC C Hc H1.length (H1.length + 1 + (blk.length - b)) (blk.length - b) []) (fun rs _ _ H4 => Hc <+: H4 ∧
      RSlots C Hc H4 H1.length (H1.length + 1 + (blk.length - b)) ([] ++ rs) ∧ ([] ++ rs).length = blk.length - b)
    (fun rs w s' (st : PState σ) ⟨H', hp', hs', h', hl'⟩ => ⟨H', ⟨hp', h', hl'⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rcParams _ rfl hlk)
      (rc_spec C hok hc hcr hcs hcg hcn blk ob k b H1.length Hc hk hb hlen hrk (hp.trans hHc) (indBlk_mono hblk hHc)
        (by omega) (blk.length - b) b [] H2 s hcH2 (by omega) (by simp) (Nat.le_refl _)
        (fun i hi => absurd hi (by simp)) rfl hb))
    (fun rs w s4 H4 ⟨hc4, hsl4, hl4⟩ => ?_)
  simp only [List.nil_append] at hsl4 hl4
  refine specR_returnI _ (cellA C H1.length) (by simp [sev, Env.get_cons, Γ1]; rfl) (fun t ht => ⟨H4, hHc.trans hc4,
    sr_of_eq ht.sr rfl rfl rfl rfl, H1.length, rfl, ?_, fun i hi => ?_⟩)
  · rw [hl4]; exact get_prefix hco0 hc4
  · obtain ⟨og, -, h1, h2⟩ := hsl4 i hi
    exact ⟨og, h1, recRep_of_recW h2 hc4⟩

end

end ConPanqueque.T.Ind
