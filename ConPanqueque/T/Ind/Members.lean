import ConPanqueque.T.Ind.RecShapes

/-!
# The members' shapes (`readBlock`'s `members`)

`readBlock` zips the inductive types, their index counts and their constructor groups into `MemberShape`s
(`⟨cvT, cvT, nIdx, group⟩`).  `membersFill(p, m, k, a, g, o)` builds members `m … k - 1` as four-word blocks
(the type record's constant, twice, the index count from the array at `a`, the group pointer from slot `m` of
the block at `g`), the pointer of member `m` in slot `m` of the block at `o`; `membersOf` allocates the
pointer block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- `readBlock`'s members, from the block's records, index counts and groups. -/
def memberList (blk : List IConstantInfo) (k : Nat) (nIdxs : List Nat) (gs : List (List (IConstantVal × Nat))) :
    List MemberShape :=
  ((((blk.take k).map (·.toConstantVal)).zip nIdxs).zip gs).map fun a => ⟨a.1.1, a.1.1, a.1.2, a.2⟩

def alloc4 (C : Ctx) (x : MlS) (e0 e1 e2 e3 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 32) (.seq (.store (vv x) e0)
    (.seq (.store (.op .add [vv x, .const 8]) e1) (.seq (.store (.op .add [vv x, .const 16]) e2)
    (.seq (.store (.op .add [vv x, .const 24]) e3) rest))))

/-- The image after writing four words at `H2.length …`. -/
def img4 (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 : BitVec 64) : List (BitVec 64) :=
  ((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2).set (H2.length + 3) w3

section
variable {σ : Type}

theorem specR_alloc4I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (e0 e1 e2 e3 : ExpHOL 64) (w0 w1 w2 w3 : BitVec 64) (hx : x ∈ D)
    (h0 : ∀ v, sev ((x, v) :: Γ) e0 = some w0) (h1 : ∀ v, sev ((x, v) :: Γ) e1 = some w1)
    (h2 : ∀ v, sev ((x, v) :: Γ) e2 = some w2) (h3 : ∀ v, sev ((x, v) :: Γ) e3 = some w3)
    (hk : ∀ (H2 ws : List (BitVec 64)), C.H <+: H2 → ws.length = 4 → H2.length + 4 ≤ C.HN →
      SpecR (Inv (ctxH C (img4 H2 ws w0 w1 w2 w3)) s ((x, cellA C H2.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (alloc4 C x e0 e1 e2 e3 rest) s m R := by
  unfold alloc4
  refine specR_allocI x _ 4 (by decide) hx (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) e0 H2.length (by simp [ctxH, hws]) w0 (by simp [cellA, ctxH])
    (h0 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e1 (H2.length + 1) (by simp [ctxH, hws]) w1
    (by simp [sev]; exact cellA_add_ofNat C H2.length 1) (h1 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e2 (H2.length + 2) (by simp [ctxH, hws]) w2
    (by simp [sev]; exact cellA_add_ofNat C H2.length 2) (h2 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e3 (H2.length + 3) (by simp [ctxH, hws]) w3
    (by simp [sev]; exact cellA_add_ofNat C H2.length 3) (h3 _) ?_
  exact hk H2 ws hp hws hroom

theorem img4_len (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 : BitVec 64) (h : ws.length = 4) :
    (img4 H2 ws w0 w1 w2 w3).length = H2.length + 4 := by simp [img4, h]

theorem img4_prefix (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 : BitVec 64) (h : ws.length = 4) :
    H2 <+: img4 H2 ws w0 w1 w2 w3 :=
  prefix_of_get? (by simp [img4, h]) (fun k hk => by
    simp only [img4]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_append_left hk])

theorem img4_get (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 : BitVec 64) (h : ws.length = 4) :
    (img4 H2 ws w0 w1 w2 w3)[H2.length]? = some w0 ∧ (img4 H2 ws w0 w1 w2 w3)[H2.length + 1]? = some w1 ∧
    (img4 H2 ws w0 w1 w2 w3)[H2.length + 2]? = some w2 ∧ (img4 H2 ws w0 w1 w2 w3)[H2.length + 3]? = some w3 := by
  have hl : (H2 ++ ws).length = H2.length + 4 := by simp [h]
  simp only [img4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hl]; omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hl]; omega)]
  · rw [List.getElem?_set_self (by simp [hl]; omega)]

end

/-- A member block at `om`, its constants and group read in the base heap `Hc`. -/
def MemW (C : Ctx) (Hc H : List (BitVec 64)) (om : Nat) (m : MemberShape) : Prop :=
  (∃ oc, H[om]? = some (cellA C oc) ∧ CVRep C Hc oc m.cvT) ∧
  (∃ od, H[om + 1]? = some (cellA C od) ∧ CVRep C Hc od m.declared) ∧
  H[om + 2]? = some (BitVec.ofNat 64 m.nIdx) ∧
  (∃ ol, H[om + 3]? = some (cellA C ol) ∧ CtorsRep C Hc ol m.ctors)

theorem memW_prefix {C : Ctx} {Hc H H' : List (BitVec 64)} {om : Nat} {m : MemberShape} (h : MemW C Hc H om m)
    (hp : H <+: H') : MemW C Hc H' om m := by
  obtain ⟨⟨oc, a1, a2⟩, ⟨od, b1, b2⟩, c, ⟨ol, d1, d2⟩⟩ := h
  exact ⟨⟨oc, get_prefix a1 hp, a2⟩, ⟨od, get_prefix b1 hp, b2⟩, get_prefix c hp, ⟨ol, get_prefix d1 hp, d2⟩⟩

theorem memW_set {C : Ctx} {Hc H : List (BitVec 64)} {om : Nat} {m : MemberShape} (h : MemW C Hc H om m) (j : Nat)
    (hj : j < om ∨ om + 4 ≤ j) (v : BitVec 64) : MemW C Hc (H.set j v) om m := by
  obtain ⟨⟨oc, a1, a2⟩, ⟨od, b1, b2⟩, c, ⟨ol, d1, d2⟩⟩ := h
  refine ⟨⟨oc, ?_, a2⟩, ⟨od, ?_, b2⟩, ?_, ⟨ol, ?_, d2⟩⟩ <;> rw [List.getElem?_set_ne (by omega)] <;> assumption

theorem memberRep_of_memW {C : Ctx} {Hc H : List (BitVec 64)} {om : Nat} {m : MemberShape} (h : MemW C Hc H om m)
    (hp : Hc <+: H) : MemberRep C H om m := by
  obtain ⟨⟨oc, a1, a2⟩, ⟨od, b1, b2⟩, c, ⟨ol, d1, d2⟩⟩ := h
  exact ⟨⟨oc, a1, cvRep_mono hp a2⟩, ⟨od, b1, cvRep_mono hp b2⟩, c, ⟨ol, d1, ctorsRep_mono hp d2⟩⟩

/-- Slots `0 … |ms| - 1` of the pointer block at `o`: each a member block above `lo`. -/
def MSlots (C : Ctx) (Hc H : List (BitVec 64)) (o lo : Nat) (ms : List MemberShape) : Prop :=
  ∀ i (hi : i < ms.length), ∃ om, lo ≤ om ∧ H[o + 1 + i]? = some (cellA C om) ∧ MemW C Hc H om ms[i]

def mfP := ofString "mf_p"
def mfM := ofString "mf_m"
def mfK := ofString "mf_k"
def mfA := ofString "mf_a"
def mfG := ofString "mf_g"
def mfO := ofString "mf_o"
def mfQ := ofString "mf_q"
def mfX := ofString "mf_x"
def mfY := ofString "mf_y"
def mfR := ofString "mf_r"
def fMembersFill := ofString "membersFill"

def mfParams : List MlS := [mfP, mfM, mfK, mfA, mfG, mfO]
def mfLocals : List MlS := [mfQ, mfX, mfY, mfR]

def mfBody (C : Ctx) : ProgHOL 64 := prologue mfLocals
  (.ite (.cmp .lower (vv mfM) (vv mfK))
    (.seq (.assign .local mfQ (.load .one (.op .add [vv mfP, .op .add [.panop .mul [vv mfM, .const 8], .const 8]])))
    (.seq (.assign .local mfX (.load .one (.op .add [vv mfA, .panop .mul [vv mfM, .const 8]])))
    (.seq (.assign .local mfY (.load .one (.op .add [vv mfG, .op .add [.panop .mul [vv mfM, .const 8], .const 8]])))
    (alloc4 C mfR (.op .add [vv mfQ, .const (BitVec.ofNat 64 (8 * 1))]) (.op .add [vv mfQ, .const (BitVec.ofNat 64 (8 * 1))])
      (vv mfX) (vv mfY)
    (.seq (.store (.op .add [vv mfO, .op .add [.panop .mul [vv mfM, .const 8], .const 8]]) (vv mfR))
    (.seq (.call (some (some (.local, mfX), none)) fMembersFill
        [vv mfP, .op .add [vv mfM, .const 1], vv mfK, vv mfA, vv mfG, vv mfO])
      (.return (.const 0))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem mf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mfLocals → (ctxEnv C ++ mfParams.zip vals).get x = none :=
  Knot.params_none C mfLocals mfParams vals (by decide) (by decide)

def PostMF (C : Ctx) (Hc : List (BitVec 64)) (o lo kk : Nat) (done ms : List MemberShape) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ MSlots C Hc H' o lo (done ++ ms) ∧ (done ++ ms).length = kk

theorem postMF_locals (C : Ctx) (Hc : List (BitVec 64)) (o lo kk : Nat) (done : List MemberShape) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostMF C Hc o lo kk done a w s' st → PostMF C Hc o lo kk done a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h, hl⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h, hl⟩

theorem memberList_length (blk : List IConstantInfo) (k : Nat) (nIdxs : List Nat) (gs : List (List (IConstantVal × Nat)))
    (hk : k ≤ blk.length) (hn : nIdxs.length = k) (hg : gs.length = k) : (memberList blk k nIdxs gs).length = k := by
  simp [memberList, hn, hg]; omega

theorem memberList_get (blk : List IConstantInfo) (k : Nat) (nIdxs : List Nat) (gs : List (List (IConstantVal × Nat)))
    (hk : k ≤ blk.length) (hn : nIdxs.length = k) (hg : gs.length = k) (m : Nat) (hm : m < k) :
    (memberList blk k nIdxs gs)[m]'(by rw [memberList_length blk k nIdxs gs hk hn hg]; exact hm) =
      ⟨blk[m].toConstantVal, blk[m].toConstantVal, nIdxs[m], gs[m]⟩ := by
  simp [memberList]

/-- **`membersFill`** from member `m`, the members `done` of `0 … m - 1` in their slots. -/
theorem mf_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMembersFill = some (mfParams.map (fun p => (p, ShapeHOL.one)), mfBody C, .one))
    (blk : List IConstantInfo) (ob k oa og o : Nat) (nIdxs : List Nat) (gs : List (List (IConstantVal × Nat)))
    (Hc : List (BitVec 64)) (hk : k ≤ blk.length) (hlen : blk.length < 2 ^ 59) (hn : nIdxs.length = k)
    (hg : gs.length = k) (hblk : IndBlk C Hc ob blk)
    (hidx : ∀ i (hi : i < k), Hc[oa + i]? = some (BitVec.ofNat 64 (nIdxs[i]'(by omega))))
    (hgs : PtrsRep C Hc og (fun og' cs => CtorsRep C Hc og' cs) gs) (hco1 : Hc.length ≤ o + 1) :
    ∀ f m (done : List MemberShape) (H : List (BitVec 64)) (s : AState),
      Hc <+: H → o + 1 + k ≤ H.length → done.length = m → MSlots C Hc H o (o + 1 + k) done → k - m = f → m ≤ k →
      SpecR (σ := σ) (Pre (ctxH C H) s (mfParams.zip [cellA C ob, BitVec.ofNat 64 m, BitVec.ofNat 64 k, cellA C oa,
        cellA C og, cellA C o])) (mfBody C) s (pure ((memberList blk k nIdxs gs).drop m))
        (PostMF C Hc o (o + 1 + k) k done) := by
  have hML := memberList_length blk k nIdxs gs hk hn hg
  intro f
  induction f with
  | zero =>
    intro m done H s hcH hroom hdl hsl hf hm
    have hmk : m = k := by omega
    subst hmk
    refine specR_prologue (postMF_locals _ _ _ _ _ _) (mf_none _ _) ?_
    have hlw := nd_lt_iff m m (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_eq_nil_of_le (by omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hcH, sr_of_eq ht.sr rfl rfl rfl rfl, by simpa using hsl,
      by simp; omega⟩)
  | succ f ih =>
    intro m done H s hcH hroom hdl hsl hf hm
    have hmk : m < k := by omega
    refine specR_prologue (postMF_locals _ _ _ _ _ _) (mf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff m k (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hmk])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons (by omega), memberList_get blk k nIdxs gs hk hn hg m hmk]
    obtain ⟨os, hosl, hblkp, hcie⟩ := id hblk
    have hom : m < os.length := by omega
    have hcv := (hcie m (by omega) hom).1
    obtain ⟨og', hgo, hgrep⟩ := hgs.2 m (by omega)
    let Γ0 : Env := ctxEnv (ctxH C H) ++ mfParams.zip [cellA C ob, BitVec.ofNat 64 m, BitVec.ofNat 64 k, cellA C oa,
      cellA C og, cellA C o]
    have vP : Γ0.get mfP = some (cellA C ob) := by simp +decide [Γ0, Env.get, mfParams, ctxEnv]
    have vM : Γ0.get mfM = some (BitVec.ofNat 64 m) := by simp +decide [Γ0, Env.get, mfParams, ctxEnv]
    have vK : Γ0.get mfK = some (BitVec.ofNat 64 k) := by simp +decide [Γ0, Env.get, mfParams, ctxEnv]
    have vA : Γ0.get mfA = some (cellA C oa) := by simp +decide [Γ0, Env.get, mfParams, ctxEnv]
    have vG : Γ0.get mfG = some (cellA C og) := by simp +decide [Γ0, Env.get, mfParams, ctxEnv]
    have vO : Γ0.get mfO = some (cellA C o) := by simp +decide [Γ0, Env.get, mfParams, ctxEnv]
    have pk : ∀ (Γ : Env), (∀ z, z ∉ mfLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ mfParams → ∀ v,
        Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
      have hyl : y ∉ mfLocals := by
        simp only [mfParams, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simp only [sev, sev_vv, hΓ y hyl, h]
    have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ mfLocals → z ∉ mfLocals →
        Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
      have hne : z ≠ x := fun e => hz (e ▸ hx)
      simp only [Env.get_cons, hne, ite_false]
    have hw : (ctxH C H).H[ob + 1 + m]? = some (cellA C os[m]) := by
      show H[ob + 1 + m]? = _
      have := hblkp.2 m (by simp; omega); exact get_prefix (by simpa using this) hcH
    refine UD.specR_heapLoadI' (C := ctxH C H) mfQ _ (ob + 1 + m) _ hw (by simp +decide [ctxLocals, mfLocals])
      (by
        have e : sev Γ0 (.op .add [vv mfP, .op .add [.panop .mul [vv mfM, .const 8], .const 8]]) =
            some (cellA C (ob + 1 + m)) := by
          simp only [sev, sev_vv, vP, vM]; simp; exact cellA_mulIdx C ob m (by omega)
        exact e) ?_
    let Γ1 : Env := (mfQ, cellA C os[m]) :: Γ0
    have hΓ1 : ∀ z, z ∉ mfLocals → Γ1.get z = Γ0.get z := fun z hz => cnl (by decide) hz
    have hx : (ctxH C H).H[oa + m]? = some (BitVec.ofNat 64 nIdxs[m]) := get_prefix (hidx m hmk) hcH
    refine UD.specR_heapLoadI' (C := ctxH C H) mfX _ (oa + m) _ hx (by simp +decide [ctxLocals, mfLocals])
      (by
        have gA := pk Γ1 hΓ1 mfA (by decide) _ vA
        have gM := pk Γ1 hΓ1 mfM (by decide) _ vM
        have e : sev Γ1 (.op .add [vv mfA, .panop .mul [vv mfM, .const 8]]) = some (cellA C (oa + m)) := by
          simp only [sev] at gA gM ⊢; rw [gA, gM]; simp; exact cellA_mulOff C oa m (by omega)
        exact e) ?_
    let Γ2 : Env := (mfX, BitVec.ofNat 64 nIdxs[m]) :: Γ1
    have hΓ2 : ∀ z, z ∉ mfLocals → Γ2.get z = Γ0.get z := fun z hz => by
      simp only [Γ2]; rw [cnl (by decide) hz]; exact hΓ1 z hz
    have hy : (ctxH C H).H[og + 1 + m]? = some (cellA C og') := get_prefix hgo hcH
    refine UD.specR_heapLoadI' (C := ctxH C H) mfY _ (og + 1 + m) _ hy (by simp +decide [ctxLocals, mfLocals])
      (by
        have gG := pk Γ2 hΓ2 mfG (by decide) _ vG
        have gM := pk Γ2 hΓ2 mfM (by decide) _ vM
        have e : sev Γ2 (.op .add [vv mfG, .op .add [.panop .mul [vv mfM, .const 8], .const 8]]) =
            some (cellA C (og + 1 + m)) := by
          simp only [sev] at gG gM ⊢; rw [gG, gM]; simp; exact cellA_mulIdx C og m (by omega)
        exact e) ?_
    let Γ3 : Env := (mfY, cellA C og') :: Γ2
    have hΓ3 : ∀ z, z ∉ mfLocals → Γ3.get z = Γ0.get z := fun z hz => by
      simp only [Γ3]; rw [cnl (by decide) hz]; exact hΓ2 z hz
    have gQ3 : Γ3.get mfQ = some (cellA C os[m]) := by simp +decide [Γ3, Γ2, Γ1, Env.get_cons]
    have hsQ : ∀ v, sev ((mfR, v) :: Γ3) (.op .add [vv mfQ, .const (BitVec.ofNat 64 (8 * 1))]) =
        some (cellA C (os[m] + 1)) := fun v => by
      have : Env.get ((mfR, v) :: Γ3) mfQ = some (cellA C os[m]) := by
        simp only [Env.get_cons, show mfQ ≠ mfR by decide, ite_false]; exact gQ3
      simp only [sev, sev_vv, this]; simp; exact cellA_plus C _ 1
    refine specR_alloc4I (C := ctxH C H) (ctxOK_H hok H) mfR _ _ _ _ (cellA C (os[m] + 1)) (cellA C (os[m] + 1))
      (BitVec.ofNat 64 nIdxs[m]) (cellA C og') (by simp +decide [ctxLocals, mfLocals]) hsQ hsQ
      (fun v => by simp +decide [sev, Env.get_cons, Γ3, Γ2])
      (fun v => by simp +decide [sev, Env.get_cons, Γ3])
      (fun H2 ws hp2 hws hroom2 => ?_)
    have hpH2 : H <+: H2 := hp2
    have hl2 := hpH2.length_le
    let I4 := img4 H2 ws (cellA C (os[m] + 1)) (cellA C (os[m] + 1)) (BitVec.ofNat 64 nIdxs[m]) (cellA C og')
    have hI4l : I4.length = H2.length + 4 := img4_len _ _ _ _ _ _ hws
    have hI4p : H2 <+: I4 := img4_prefix _ _ _ _ _ _ hws
    obtain ⟨g0, g1, g2, g3⟩ := img4_get H2 ws (cellA C (os[m] + 1)) (cellA C (os[m] + 1)) (BitVec.ofNat 64 nIdxs[m])
      (cellA C og') hws
    let Γ4 : Env := (mfR, cellA (ctxH C H) H2.length) :: Γ3
    have hΓ4 : ∀ z, z ∉ mfLocals → Γ4.get z = Γ0.get z := fun z hz => by
      simp only [Γ4]; rw [cnl (by decide) hz]; exact hΓ3 z hz
    have gO := pk Γ4 hΓ4 mfO (by decide) _ vO
    have gM := pk Γ4 hΓ4 mfM (by decide) _ vM
    refine specR_heapStoreI (ctxOK_H hok I4) (.op .add [vv mfO, .op .add [.panop .mul [vv mfM, .const 8], .const 8]])
      (vv mfR) (o + 1 + m) (by show o + 1 + m < I4.length; omega) (cellA C H2.length)
      (by
        have e : sev Γ4 (.op .add [vv mfO, .op .add [.panop .mul [vv mfM, .const 8], .const 8]]) =
            some (cellA C (o + 1 + m)) := by
          simp only [sev] at gO gM ⊢; rw [gO, gM]; simp; exact cellA_mulIdx C o m (by omega)
        exact e)
      (by simp [Γ4, sev, Env.get_cons]; rfl) ?_
    let H3 := I4.set (o + 1 + m) (cellA C H2.length)
    have hcI : H <+: I4 := hpH2.trans hI4p
    have hc3 : Hc <+: H3 := prefix_set (hcH.trans hcI) (by omega) _
    let mem : MemberShape := ⟨blk[m].toConstantVal, blk[m].toConstantVal, nIdxs[m], gs[m]⟩
    have hsl3 : MSlots C Hc H3 o (o + 1 + k) (done ++ [mem]) := by
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases e : i < done.length
      · obtain ⟨om, hlo, h1, h2⟩ := hsl i e
        rw [List.getElem_append_left e]
        refine ⟨om, hlo, ?_, memW_set (memW_prefix h2 hcI) _ (Or.inl (by omega)) _⟩
        rw [List.getElem?_set_ne (by omega)]; exact get_prefix h1 hcI
      · have : i = done.length := by omega
        subst this
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
        refine ⟨H2.length, by omega, ?_, memW_set ?_ _ (Or.inl (by omega)) _⟩
        · rw [hdl, List.getElem?_set_self (by omega)]
        · exact ⟨⟨os[m] + 1, g0, hcv⟩, ⟨os[m] + 1, g1, hcv⟩, g2, ⟨og', g3, hgrep⟩⟩
    have gP := pk Γ4 hΓ4 mfP (by decide) _ vP
    have gK := pk Γ4 hΓ4 mfK (by decide) _ vK
    have gA := pk Γ4 hΓ4 mfA (by decide) _ vA
    have gG := pk Γ4 hΓ4 mfG (by decide) _ vG
    refine specR_congr (m' := (pure ((memberList blk k nIdxs gs).drop (m + 1)) : AM (List MemberShape)) >>=
        fun rest => pure (mem :: rest)) rfl ?_
    refine specR_callNIG (C := ctxH (ctxH C I4) H3) mfX fMembersFill mfParams
      [vv mfP, .op .add [vv mfM, .const 1], vv mfK, vv mfA, vv mfG, vv mfO] (mfBody C)
      [cellA C ob, BitVec.ofNat 64 (m + 1), BitVec.ofNat 64 k, cellA C oa, cellA C og, cellA C o] (by decide) rfl
      (by simp +decide [ctxLocals, mfLocals]) hc
      ⟨gP, by
        have e : sev Γ4 (.op .add [vv mfM, .const 1]) = some (BitVec.ofNat 64 (m + 1)) := by
          simp only [sev] at gM ⊢; rw [gM]; simp; exact word_add1_eq m
        exact e, gK, gA, gG, gO, trivial⟩
      (PostMF C Hc o (o + 1 + k) k (done ++ [mem]))
      (fun ms2 _ _ H4 => Hc <+: H4 ∧ MSlots C Hc H4 o (o + 1 + k) (done ++ [mem] ++ ms2) ∧
        (done ++ [mem] ++ ms2).length = k)
      (fun ms2 w s' st ⟨H', hp', hs', h', hl'⟩ => ⟨H', ⟨hp', h', hl'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mfParams _ rfl hlk)
        (ih (m + 1) (done ++ [mem]) H3 s hc3 (by simp [H3]; omega) (by simp [hdl]) hsl3 (by omega) (by omega)))
      (fun ms2 w4 s4 H4 ⟨hc4, hsl4, hl4⟩ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hc4, sr_of_eq ht.sr rfl rfl rfl rfl, by simpa using hsl4,
      by simpa using hl4⟩)

end

def moP := ofString "mo_p"
def moK := ofString "mo_k"
def moA := ofString "mo_a"
def moG := ofString "mo_g"
def moO := ofString "mo_o"
def moX := ofString "mo_x"
def fMembersOf := ofString "membersOf"

def moParams : List MlS := [moP, moK, moA, moG]
def moLocals : List MlS := [moO, moX]

/-- The pointer block `[k, member₀, …]`. -/
def moBody (C : Ctx) : ProgHOL 64 := prologue moLocals
  (allocP C moO (.op .add [.panop .mul [vv moK, .const 8], .const 8])
  (.seq (.store (vv moO) (vv moK))
  (.seq (.call (some (some (.local, moX), none)) fMembersFill [vv moP, .const 0, vv moK, vv moA, vv moG, vv moO])
    (.return (vv moO)))))

section
variable {σ : Type}

theorem mo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ moLocals → (ctxEnv C ++ moParams.zip vals).get x = none :=
  Knot.params_none C moLocals moParams vals (by decide) (by decide)

/-- The members: a pointer block of `MemberRep` blocks, in a bigger heap. -/
def PostMO (C : Ctx) (ms : List MemberShape) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ o, w = cellA C o ∧ PtrsRep C H' o (fun om m => MemberRep C H' om m) ms

theorem postMO_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostMO C a w s' st → PostMO C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

/-- **`membersOf`**: the block's members. -/
theorem mo_spec (C : Ctx) (hok : CtxOK C)
    (hcm : C.code.lookup fMembersOf = some (moParams.map (fun p => (p, ShapeHOL.one)), moBody C, .one))
    (hc : C.code.lookup fMembersFill = some (mfParams.map (fun p => (p, ShapeHOL.one)), mfBody C, .one))
    (blk : List IConstantInfo) (ob k oa og : Nat) (nIdxs : List Nat) (gs : List (List (IConstantVal × Nat)))
    (hk : k ≤ blk.length) (hlen : blk.length < 2 ^ 59) (hn : nIdxs.length = k) (hg : gs.length = k)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hblk : IndBlk C H ob blk)
    (hidx : ∀ i (hi : i < k), H[oa + i]? = some (BitVec.ofNat 64 (nIdxs[i]'(by omega))))
    (hgs : PtrsRep C H og (fun og' cs => CtorsRep C H og' cs) gs) :
    SpecR (σ := σ) (Pre (ctxH C H) s (moParams.zip [cellA C ob, BitVec.ofNat 64 k, cellA C oa, cellA C og]))
      (moBody C) s (pure (memberList blk k nIdxs gs)) (PostMO (ctxH C H)) := by
  refine specR_prologue (postMO_locals _) (mo_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  let Γ0 : Env := ctxEnv (ctxH C H) ++ moParams.zip [cellA C ob, BitVec.ofNat 64 k, cellA C oa, cellA C og]
  have vK : Γ0.get moK = some (BitVec.ofNat 64 k) := by simp +decide [Γ0, Env.get, moParams, ctxEnv]
  refine specR_allocI (C := ctxH C H) moO _ (k + 1) (by omega) (by simp +decide [ctxLocals, moLocals])
    (fun v => by
      have h1 : sev ((moO, v) :: Γ0) (vv moK) = some (BitVec.ofNat 64 k) := by
        simp only [sev, sev_vv, Env.get_cons, show moK ≠ moO by decide, ite_false]; exact vK
      simp only [sev] at h1 ⊢; rw [h1]; simp; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H1 ws hp1 hws hroom1 => ?_)
  have hp1' : H <+: H1 := hp1
  have hroom1' : H1.length + (k + 1) ≤ C.HN := hroom1
  have hl1 := hp1'.length_le
  let Γ1 : Env := (moO, cellA (ctxH C H) H1.length) :: Γ0
  have gv : ∀ y v, y ≠ moO → Γ0.get y = some v → sev Γ1 (vv y) = some v := fun y v hy h => by
    simp only [sev, sev_vv, Γ1, Env.get_cons, hy, ite_false, h]
  refine specR_heapStoreI (ctxOK_H hok (H1 ++ ws)) (vv moO) (vv moK) H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    (BitVec.ofNat 64 k) (by simp [Γ1, sev, Env.get_cons]; rfl) (gv moK _ (by decide) vK) ?_
  let H2 := (H1 ++ ws).set H1.length (BitVec.ofNat 64 k)
  let Hc := H2.take (H1.length + 1)
  have hl2 : H2.length = H1.length + (k + 1) := by simp [H2, hws]
  have hcH2 : Hc <+: H2 := List.take_prefix _ _
  have hHH2 : H <+: H2 := prefix_set (hp1'.trans (List.prefix_append _ _)) hl1 _
  have hHc : H <+: Hc := prefix_take_of hHH2 (by omega)
  have hHcl : Hc.length = H1.length + 1 := by simp [Hc]; omega
  have hco0 : Hc[H1.length]? = some (BitVec.ofNat 64 k) := by
    simp only [Hc, H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by simp; omega)
  have hgsc : PtrsRep C Hc og (fun og' cs => CtorsRep C Hc og' cs) gs :=
    ptrsRep_mono hHc (fun _ _ h => ctorsRep_mono hHc h) hgs
  refine specR_congr (m' := (pure (memberList blk k nIdxs gs) : AM (List MemberShape)) >>= fun r => pure r)
    (by rw [bind_pure]) ?_
  have hd0 : memberList blk k nIdxs gs = (memberList blk k nIdxs gs).drop 0 := by simp
  refine specR_callNIG (C := ctxH (ctxH C (H1 ++ ws)) H2) (D := ctxLocals ++ moLocals) moX fMembersFill mfParams
    [vv moP, .const 0, vv moK, vv moA, vv moG, vv moO] (mfBody C)
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 k, cellA C oa, cellA C og, cellA C H1.length] (by decide) rfl
    (by simp +decide [ctxLocals, moLocals]) hc
    ⟨gv moP _ (by decide) (by simp +decide [Γ0, Env.get, moParams, ctxEnv]), rfl, gv moK _ (by decide) vK,
      gv moA _ (by decide) (by simp +decide [Γ0, Env.get, moParams, ctxEnv]),
      gv moG _ (by decide) (by simp +decide [Γ0, Env.get, moParams, ctxEnv]),
      by simp [Γ1, sev, Env.get_cons]; rfl, trivial⟩
    (PostMF C Hc H1.length (H1.length + 1 + k) k []) (fun ms _ _ H4 => Hc <+: H4 ∧
      MSlots C Hc H4 H1.length (H1.length + 1 + k) ([] ++ ms) ∧ ([] ++ ms).length = k)
    (fun ms w s' (st : PState σ) ⟨H', hp', hs', h', hl'⟩ => ⟨H', ⟨hp', h', hl'⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mfParams _ rfl hlk) (by
      rw [hd0]
      exact mf_spec C hok hc blk ob k oa og H1.length nIdxs gs Hc hk hlen hn hg (indBlk_mono hblk hHc)
        (fun i hi => get_prefix (hidx i hi) hHc) hgsc (by omega) k 0 [] H2 s hcH2 (by omega) rfl
        (fun i hi => absurd hi (by simp)) (by omega) (by omega)))
    (fun ms w s4 H4 ⟨hc4, hsl4, hl4⟩ => ?_)
  simp only [List.nil_append] at hsl4 hl4
  refine specR_returnI _ (cellA C H1.length) (by simp [sev, Env.get_cons, Γ1]; rfl) (fun t ht => ⟨H4, hHc.trans hc4,
    sr_of_eq ht.sr rfl rfl rfl rfl, H1.length, rfl, ?_, fun i hi => ?_⟩)
  · rw [hl4]; exact get_prefix hco0 hc4
  · obtain ⟨om, -, h1, h2⟩ := hsl4 i hi
    exact ⟨om, h1, memberRep_of_memW h2 hc4⟩

end

end ConPanqueque.T.Ind
