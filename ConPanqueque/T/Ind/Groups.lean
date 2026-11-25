import ConPanqueque.T.Ind.CtorMember
import ConPanqueque.T.Ind.MemberCounts
import ConPanqueque.T.Ind.Shape

/-!
# A member's constructors (`blockGroups`, one group)

`blockGroups` sorts the block's constructors by the member their result names (`ctorMember?`); a one-member
block takes them all.  `grpFill(p, j, n, k, lvls, nP, m, g, c)` walks the constructor records `j … n - 1`
and appends each one of member `m` (every one when `m = k`) to the `CtorsRep` block at `g`, whose first `c`
entries are written; at the end it writes the count.  The twin is `filterAuxM`, `filterM`'s worker.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI

/-- A constructor record as `readBlock`'s `(constant, field count)`. -/
def ctorPair (ci : IConstantInfo) : IConstantVal × Nat := ((ctorT ci).1, (ctorT ci).2.2)

/-- Member `m`'s group test (`m = k`: every constructor). -/
def grpP (names : List NIdx) (lvls : LsIdx) (nP k m : Nat) (c : IConstantVal × Nat) : AM Bool :=
  if m = k then pure true else do
    match ← ctorMember? names lvls nP c with
    | some t => pure (t == m)
    | none => pure false

theorem filterAuxM_cons {α : Type} (p : α → AM Bool) (a : α) (l acc : List α) :
    List.filterAuxM p (a :: l) acc = (do let b ← p a; List.filterAuxM p l (cond b (a :: acc) acc)) := rfl

theorem filterAuxM_nil {α : Type} (p : α → AM Bool) (acc : List α) : List.filterAuxM p [] acc = pure acc := rfl

/-- The written entries `0 … |cs| - 1` of a `CtorsRep` block at `g`, the constants read in the base heap. -/
def Ents (C : Ctx) (Hb H : List (BitVec 64)) (g : Nat) (cs : List (IConstantVal × Nat)) : Prop :=
  ∀ i (hi : i < cs.length), ∃ oc, H[g + 1 + 2 * i]? = some (cellA C oc) ∧ CVRep C Hb oc cs[i].1 ∧
    NatE H (g + 2 + 2 * i) cs[i].2

theorem ents_prefix {C : Ctx} {Hb H H' : List (BitVec 64)} {g : Nat} {cs : List (IConstantVal × Nat)}
    (h : Ents C Hb H g cs) (hp : H <+: H') : Ents C Hb H' g cs := fun i hi =>
  let ⟨oc, h1, h2, h3⟩ := h i hi; ⟨oc, get_prefix h1 hp, h2, natE_mono hp h3⟩

theorem ents_set {C : Ctx} {Hb H : List (BitVec 64)} {g : Nat} {cs : List (IConstantVal × Nat)}
    (h : Ents C Hb H g cs) (j : Nat) (hj : j = g ∨ g + 1 + 2 * cs.length ≤ j) (v : BitVec 64) :
    Ents C Hb (H.set j v) g cs := fun i hi => by
  obtain ⟨oc, h1, h2, h3, h4⟩ := h i hi
  refine ⟨oc, ?_, h2, ?_, h4⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h1
  · rw [List.getElem?_set_ne (by omega)]; exact h3

theorem ents_snoc {C : Ctx} {Hb H : List (BitVec 64)} {g : Nat} {cs : List (IConstantVal × Nat)}
    (h : Ents C Hb H g cs) (c : IConstantVal × Nat) (oc : Nat) (h1 : H[g + 1 + 2 * cs.length]? = some (cellA C oc))
    (h2 : CVRep C Hb oc c.1) (h3 : NatE H (g + 2 + 2 * cs.length) c.2) : Ents C Hb H g (cs ++ [c]) := fun i hi => by
  simp only [List.length_append, List.length_singleton] at hi
  by_cases e : i < cs.length
  · rw [List.getElem_append_left e]; exact h i e
  · have : i = cs.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
    exact ⟨oc, h1, h2, h3⟩

theorem ctorsRep_of_ents {C : Ctx} {Hb H : List (BitVec 64)} {g : Nat} {cs : List (IConstantVal × Nat)}
    (h0 : H[g]? = some (BitVec.ofNat 64 cs.length)) (h : Ents C Hb H g cs) (hp : Hb <+: H) : CtorsRep C H g cs :=
  ⟨h0, fun i hi => let ⟨oc, h1, h2, h3⟩ := h i hi; ⟨oc, h1, cvRep_mono hp h2, h3⟩⟩

/-- A group block at `g`: its count, and its entries (the constants read in `Hb`). -/
def GrpRep (C : Ctx) (Hb H : List (BitVec 64)) (g : Nat) (cs : List (IConstantVal × Nat)) : Prop :=
  H[g]? = some (BitVec.ofNat 64 cs.length) ∧ Ents C Hb H g cs

theorem grpRep_prefix {C : Ctx} {Hb H H' : List (BitVec 64)} {g : Nat} {cs : List (IConstantVal × Nat)}
    (h : GrpRep C Hb H g cs) (hp : H <+: H') : GrpRep C Hb H' g cs := ⟨get_prefix h.1 hp, ents_prefix h.2 hp⟩

theorem grpRep_set {C : Ctx} {Hb H : List (BitVec 64)} {g : Nat} {cs : List (IConstantVal × Nat)}
    (h : GrpRep C Hb H g cs) (j : Nat) (hj : j < g ∨ g + 1 + 2 * cs.length ≤ j) (v : BitVec 64) :
    GrpRep C Hb (H.set j v) g cs := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h.1
  · obtain ⟨oc, h1, h2, h3, h4⟩ := h.2 i hi
    exact ⟨oc, by rw [List.getElem?_set_ne (by omega)]; exact h1, h2, by rw [List.getElem?_set_ne (by omega)]; exact h3, h4⟩

theorem ctorsRep_of_grp {C : Ctx} {Hb H : List (BitVec 64)} {g : Nat} {cs : List (IConstantVal × Nat)}
    (h : GrpRep C Hb H g cs) (hp : Hb <+: H) : CtorsRep C H g cs := ctorsRep_of_ents h.1 h.2 hp

theorem cellA_mul16 (C : Ctx) (o j : Nat) (hj : j < 2 ^ 60) :
    cellA C o + (BitVec.ofNat 64 j * 16#64 + 8#64) = cellA C (o + 1 + 2 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem cellA_mul16' (C : Ctx) (o j : Nat) (hj : j < 2 ^ 60) :
    cellA C o + (BitVec.ofNat 64 j * 16#64 + 16#64) = cellA C (o + 2 + 2 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem drop_take_cons {α : Type} (l : List α) (j n : Nat) (hj : j < n) (hn : n ≤ l.length) :
    (l.drop j).take (n - j) = l[j]'(by omega) :: (l.drop (j + 1)).take (n - (j + 1)) := by
  rw [List.drop_eq_getElem_cons (by omega), show n - j = (n - (j + 1)) + 1 by omega, List.take_succ_cons]

def gfP := ofString "gf_p"
def gfJ := ofString "gf_j"
def gfN := ofString "gf_n"
def gfK := ofString "gf_k"
def gfL := ofString "gf_l"
def gfNP := ofString "gf_np"
def gfM := ofString "gf_m"
def gfG := ofString "gf_g"
def gfCt := ofString "gf_c"
def gfQ := ofString "gf_q"
def gfW := ofString "gf_w"
def gfT := ofString "gf_t"
def gfX := ofString "gf_x"
def fGrpFill := ofString "grpFill"

def gfParams : List MlS := [gfP, gfJ, gfN, gfK, gfL, gfNP, gfM, gfG, gfCt]
def gfLocals : List MlS := [gfQ, gfW, gfT, gfX]

def gfRec (cnt : ExpHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, gfX), none)) fGrpFill
    [vv gfP, .op .add [vv gfJ, .const 1], vv gfN, vv gfK, vv gfL, vv gfNP, vv gfM, vv gfG, cnt]) (.return (.const 0))

def gfTake : ProgHOL 64 :=
  .seq (.store (.op .add [vv gfG, .op .add [.panop .mul [vv gfCt, .const 16], .const 8]])
      (.op .add [vv gfQ, .const (BitVec.ofNat 64 (8 * 1))]))
  (.seq (.store (.op .add [vv gfG, .op .add [.panop .mul [vv gfCt, .const 16], .const 16]]) (vv gfW))
    (gfRec (.op .add [vv gfCt, .const 1])))

def gfBody (C : Ctx) : ProgHOL 64 := prologue gfLocals
  (.ite (.cmp .lower (vv gfJ) (vv gfN))
    (.seq (.assign .local gfQ (.load .one (.op .add [vv gfP, .op .add [.panop .mul [vv gfJ, .const 8], .const 8]])))
    (.seq (.assign .local gfW (.load .one (.op .add [vv gfQ, .const (BitVec.ofNat 64 (8 * 5))])))
    (.ite (.cmp .equal (vv gfM) (vv gfK)) gfTake
      (.seq (.assign .local gfT (.load .one (.op .add [vv gfQ, .const (BitVec.ofNat 64 (8 * 3))])))
      (.seq (.call (some (some (.local, gfX), none)) fCtorMember
          [vv gfP, vv gfK, vv gfL, .op .add [vv gfNP, vv gfW], vv gfT])
        (.ite (.cmp .equal (vv gfX) (vv gfM)) gfTake (gfRec (vv gfCt))))))))
    (.seq (.store (vv gfG) (vv gfCt)) (.return (.const 0))))

section
variable {σ : Type}

theorem gf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gfLocals → (ctxEnv C ++ gfParams.zip vals).get x = none :=
  Knot.params_none C gfLocals gfParams vals (by decide) (by decide)

/-- The post: the block at `g` holds the group; the base heap `H0` (below `g`) stays a prefix. -/
def PostG (C : Ctx) (Hb H0 : List (BitVec 64)) (g : Nat) (cs : List (IConstantVal × Nat)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', H0 <+: H' ∧ SR (ctxH C H') s' st ∧ GrpRep C Hb H' g cs

theorem postG_locals (C : Ctx) (Hb H0 : List (BitVec 64)) (g : Nat) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostG C Hb H0 g a w s' st → PostG C Hb H0 g a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem get_cons_nl {Γ : Env} {x z : MlS} {v : BitVec 64} (hx : x ∈ gfLocals) (hz : z ∉ gfLocals) :
    Env.get ((x, v) :: Γ) z = Env.get Γ z := by
  have hne : z ≠ x := fun e => hz (e ▸ hx)
  simp only [Env.get_cons, hne, ite_false]

end

section
variable {σ : Type}

/-- **`grpFill`** over the constructor records `j … n - 1`, the first `|acc|` entries written. -/
theorem gf_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fGrpFill = some (gfParams.map (fun p => (p, ShapeHOL.one)), gfBody C, .one))
    (hcm : C.code.lookup fCtorMember = some (cmParams.map (fun p => (p, ShapeHOL.one)), cmBody C, .one))
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcmi : C.code.lookup fMemberIdx = some (miParams.map (fun p => (p, ShapeHOL.one)), miBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k n nP m g : Nat) (lvls : LsIdx) (Hb : List (BitVec 64))
    (hn : n ≤ blk.length) (hlen : blk.length < 2 ^ 59) (hnP : nP < 2 ^ 59) (hm : m ≤ k)
    (hkind : ∀ i, k ≤ i → i < n → kindAt blk i = some 4)
    (hCb : C.H <+: Hb) (hblk : IndBlk C Hb ob blk) :
    ∀ f j (acc : List (IConstantVal × Nat)) (H0 H : List (BitVec 64)) (s : AState),
      Hb <+: H0 → H0 <+: H → H0.length ≤ g → g + 1 + 2 * (acc.length + (n - j)) ≤ H.length →
      Ents C Hb H g acc.reverse → n - j = f → k ≤ j → j ≤ n →
      SpecR (σ := σ) (Pre (ctxH C H) s (gfParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 n,
        BitVec.ofNat 64 k, Enc.idxW lvls, BitVec.ofNat 64 nP, BitVec.ofNat 64 m, cellA C g,
        BitVec.ofNat 64 acc.length])) (gfBody C) s
        (List.filterAuxM (grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k m)
          (((blk.drop j).take (n - j)).map ctorPair) acc >>= fun r => pure r.reverse) (PostG C Hb H0 g) := by
  intro f
  induction f with
  | zero =>
    intro j acc H0 H s hb0 h0 hg hroom hents hf hkj hjn
    have hjn' : j = n := by omega
    subst hjn'
    refine specR_prologue (postG_locals _ _ _ _) (gf_none _ _) ?_
    have hlw := nd_lt_iff j j (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, gfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Nat.sub_self, List.take_zero, List.map_nil, filterAuxM_nil, pure_bind]
    refine specR_heapStoreI (ctxOK_H hok H) (vv gfG) (vv gfCt) g (by show g < H.length; omega)
      (BitVec.ofNat 64 acc.length) (by simp +decide [Env.get, gfParams, ctxEnv]; rfl)
      (by simp +decide [sev, Env.get, gfParams, ctxEnv]) ?_
    refine specR_returnI _ 0 rfl (fun t ht => ⟨H.set g (BitVec.ofNat 64 acc.length), prefix_set h0 hg _,
      sr_of_eq ht.sr rfl rfl rfl rfl, ?_, ents_set hents g (Or.inl rfl) _⟩)
    rw [List.getElem?_set_self (by omega), List.length_reverse]
  | succ f ih =>
    intro j acc H0 H s hb0 h0 hg hroom hents hf hkj hjn
    have hjn' : j < n := by omega
    refine specR_prologue (postG_locals _ _ _ _) (gf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff j n (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, gfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjn'])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [drop_take_cons blk j n hjn' hn, List.map_cons, filterAuxM_cons]
    have hbH : Hb <+: H := hb0.trans h0
    obtain ⟨os, hosl, hblkp, hcie⟩ := id hblk
    have hoj : j < os.length := by omega
    have hci := hcie j (by omega) hoj
    have hk4 := hkind j hkj hjn'
    let Γ0 : Env := ctxEnv (ctxH C H) ++ gfParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 n,
        BitVec.ofNat 64 k, Enc.idxW lvls, BitVec.ofNat 64 nP, BitVec.ofNat 64 m, cellA C g, BitVec.ofNat 64 acc.length]
    have hw : (ctxH C H).H[ob + 1 + j]? = some (cellA C os[j]) := by
      show H[ob + 1 + j]? = _
      have := hblkp.2 j (by simp; omega); exact get_prefix (by simpa using this) hbH
    refine UD.specR_heapLoadI' (C := ctxH C H) gfQ _ (ob + 1 + j) _ hw (by simp +decide [ctxLocals, gfLocals])
      (by simp +decide [sev, Env.get, gfParams, ctxEnv]; exact cellA_mulIdx C ob j (by omega)) ?_
    generalize hcr : blk[j] = ci at hci hk4 ⊢
    cases ci with
    | ctorInfo cv np nf ind =>
      obtain ⟨hcv, -, -, ⟨hnf, hnf63⟩, -⟩ := hci
      have hcp : ctorPair (.ctorInfo cv np nf ind) = (cv, nf) := rfl
      rw [hcp]
      have hsQ : ∀ (Γ : Env), Γ.get gfQ = some (cellA C os[j]) → ∀ q, sev Γ (.op .add [vv gfQ,
          .const (BitVec.ofNat 64 (8 * q))]) = some (cellA C (os[j] + q)) := by
        intro Γ hq q; simp only [sev, sev_vv, hq]; simp; exact cellA_plus C _ q
      refine UD.specR_heapLoadI' (C := ctxH C H) gfW _ (os[j] + 5) _ (get_prefix hnf hbH)
        (by simp +decide [ctxLocals, gfLocals]) (hsQ _ (by simp [Env.get_cons]) 5) ?_
      -- the parameters, through any locals
      have pk : ∀ (Γ : Env), (∀ z, z ∉ gfLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ gfParams → ∀ v,
          Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
        have hyl : y ∉ gfLocals := by
          simp only [gfParams, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
        simp only [sev, sev_vv, hΓ y hyl, h]
      have vP : Γ0.get gfP = some (cellA C ob) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vJ : Γ0.get gfJ = some (BitVec.ofNat 64 j) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vN : Γ0.get gfN = some (BitVec.ofNat 64 n) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vK : Γ0.get gfK = some (BitVec.ofNat 64 k) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vL : Γ0.get gfL = some (Enc.idxW lvls) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vNP : Γ0.get gfNP = some (BitVec.ofNat 64 nP) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vM : Γ0.get gfM = some (BitVec.ofNat 64 m) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vG : Γ0.get gfG = some (cellA C g) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have vC : Γ0.get gfCt = some (BitVec.ofNat 64 acc.length) := by simp +decide [Γ0, Env.get, gfParams, ctxEnv]
      have hacc : acc.length < 2 ^ 60 := by omega
      -- the recursive call, from any heap whose block is written up to `acc'`
      have recur : ∀ (acc' : List (IConstantVal × Nat)) (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env),
          H0 <+: H1 → g + 1 + 2 * (acc'.length + (n - (j + 1))) ≤ H1.length → Ents C Hb H1 g acc'.reverse →
          (∀ z, z ∉ gfLocals → z ≠ gfCt → Γ.get z = Γ0.get z) → ∀ (ec : ExpHOL 64),
          sev Γ ec = some (BitVec.ofNat 64 acc'.length) →
          SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ gfLocals)) (gfRec ec) s1
            (List.filterAuxM (grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k m)
              (((blk.drop (j + 1)).take (n - (j + 1))).map ctorPair) acc' >>= fun r => pure r.reverse)
            (PostG C Hb H0 g) := by
        intro acc' H1 s1 Γ h01 hroom1 hents1 hΓ ec hec
        have pk' : ∀ y, y ∈ gfParams → y ≠ gfCt → ∀ v, Γ0.get y = some v → sev Γ (vv y) = some v :=
          fun y hy hyc v h => by
            have hyl : y ∉ gfLocals := by
              simp only [gfParams, List.mem_cons, List.not_mem_nil, or_false] at hy
              rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
            simp only [sev, sev_vv, hΓ y hyl hyc, h]
        have gJ := pk' gfJ (by decide) (by decide) _ vJ
        refine specR_congr (m' := (List.filterAuxM (grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k m)
              (((blk.drop (j + 1)).take (n - (j + 1))).map ctorPair) acc' >>= fun r => pure r.reverse) >>= fun r => pure r)
          (by simp) ?_
        refine specR_callNIG gfX fGrpFill gfParams
          [vv gfP, .op .add [vv gfJ, .const 1], vv gfN, vv gfK, vv gfL, vv gfNP, vv gfM, vv gfG, ec] (gfBody C)
          [cellA C ob, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 n, BitVec.ofNat 64 k, Enc.idxW lvls, BitVec.ofNat 64 nP,
            BitVec.ofNat 64 m, cellA C g, BitVec.ofNat 64 acc'.length] (by decide) rfl
          (by simp +decide [ctxLocals, gfLocals]) hc
          ⟨pk' gfP (by decide) (by decide) _ vP, by simp only [sev] at gJ ⊢; rw [gJ]; simp; exact word_add1_eq j,
            pk' gfN (by decide) (by decide) _ vN, pk' gfK (by decide) (by decide) _ vK,
            pk' gfL (by decide) (by decide) _ vL, pk' gfNP (by decide) (by decide) _ vNP,
            pk' gfM (by decide) (by decide) _ vM, pk' gfG (by decide) (by decide) _ vG, hec, trivial⟩
          (PostG C Hb H0 g) (fun cs _ _ H' => H0 <+: H' ∧ GrpRep C Hb H' g cs)
          (fun cs w s' st ⟨H', hp', hs', hc'⟩ => ⟨H', ⟨hp', hc'⟩, hs'⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gfParams _ rfl hlk)
            (ih (j + 1) acc' H0 H1 s1 hb0 h01 hg hroom1 hents1 (by omega) (by omega) (by omega)))
          (fun cs w s2 H2 ⟨h02, hcs⟩ => ?_)
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, h02, sr_of_eq ht.sr rfl rfl rfl rfl, hcs⟩)
      -- take the constructor, from any heap extending `H`
      have take : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env), H <+: H1 →
          (∀ z, z ∉ gfLocals → Γ.get z = Γ0.get z) → Γ.get gfQ = some (cellA C os[j]) →
          Γ.get gfW = some (BitVec.ofNat 64 nf) →
          SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ gfLocals)) gfTake s1
            (List.filterAuxM (grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k m)
              (((blk.drop (j + 1)).take (n - (j + 1))).map ctorPair) ((cv, nf) :: acc) >>= fun r => pure r.reverse)
            (PostG C Hb H0 g) := by
        intro H1 s1 Γ hp1 hΓ gQ gW
        have hl1 := hp1.length_le
        have gG := pk Γ hΓ gfG (by decide) _ vG
        have gC := pk Γ hΓ gfCt (by decide) _ vC
        refine specR_heapStoreI (ctxOK_H hok H1) _ _ (g + 1 + 2 * acc.length) (by show _ < H1.length; omega)
          (cellA C (os[j] + 1))
          (by simp only [sev] at gG gC ⊢; rw [gG, gC]; simp; exact cellA_mul16 C g acc.length hacc)
          (hsQ Γ gQ 1) ?_
        refine specR_heapStoreI (ctxOK_H hok _) _ _ (g + 2 + 2 * acc.length)
          (by show _ < (H1.set _ _).length; simp; omega) (BitVec.ofNat 64 nf)
          (by simp only [sev] at gG gC ⊢; rw [gG, gC]; simp; exact cellA_mul16' C g acc.length hacc)
          (by simp only [sev, sev_vv, gW]) ?_
        have h01 : H0 <+: H1 := h0.trans hp1
        have hH0g : H0.length ≤ g := hg
        refine recur ((cv, nf) :: acc) _ s1 Γ
          (prefix_set (prefix_set h01 (by omega) _) (by omega) _) (by simp; omega) ?_
          (fun z hz _ => hΓ z hz) _ ?_
        · rw [List.reverse_cons]
          have e1 := ents_set (ents_set (ents_prefix hents hp1) (g + 1 + 2 * acc.length) (Or.inr (by simp))
            (cellA C (os[j] + 1))) (g + 2 + 2 * acc.length) (Or.inr (by simp)) (BitVec.ofNat 64 nf)
          refine ents_snoc e1 (cv, nf) (os[j] + 1) ?_ hcv ?_
          · rw [List.length_reverse, List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
          · rw [List.length_reverse]
            exact ⟨List.getElem?_set_self (by simp; omega), hnf63⟩
        · simp only [sev] at gC ⊢; rw [gC]; simp; exact word_add1_eq acc.length
      have hmk := ConPanqueque.T.WC.sev_eqNatB (Γ := (gfW, BitVec.ofNat 64 nf) :: (gfQ, cellA C os[j]) :: Γ0) (a := vv gfM) (b := vv gfK)
        (x := m) (y := k) (by omega) (by omega) (pk _ (fun z hz => by rw [get_cons_nl (by decide) hz,
          get_cons_nl (by decide) hz]) gfM (by decide) _ vM)
        (pk _ (fun z hz => by rw [get_cons_nl (by decide) hz, get_cons_nl (by decide) hz]) gfK (by decide) _ vK)
      by_cases emk : m = k
      · -- every constructor
        have hgp : grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k m (cv, nf) = pure true := by
          simp [grpP, emk]
        rw [hgp, pure_bind]
        refine specR_ifI _ _ hmk (fun _ => ?_) (fun h => by simp [boolW, emk] at h)
        exact take H s _ (List.prefix_refl _)
          (fun z hz => by rw [get_cons_nl (by decide) hz, get_cons_nl (by decide) hz])
          (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
      · -- the constructor's member
        refine specR_ifI _ _ hmk (fun h => by simp [boolW, emk] at h) (fun _ => ?_)
        have hty : (ctxH C H).H[os[j] + 3]? = some (Enc.idxW cv.type) := by
          have := hcv.2.2; rw [show os[j] + 1 + 2 = os[j] + 3 by omega] at this; exact get_prefix this hbH
        refine UD.specR_heapLoadI' (C := ctxH C H) gfT _ (os[j] + 3) _ hty (by simp +decide [ctxLocals, gfLocals])
          (hsQ _ (by simp +decide [Env.get_cons]) 3) ?_
        let Γ3 : Env := (gfT, Enc.idxW cv.type) :: (gfW, BitVec.ofNat 64 nf) :: (gfQ, cellA C os[j]) :: Γ0
        have hΓ3 : ∀ z, z ∉ gfLocals → Γ3.get z = Γ0.get z := fun z hz => by
          simp only [Γ3]; rw [get_cons_nl (by decide) hz, get_cons_nl (by decide) hz, get_cons_nl (by decide) hz]
        have gNP := pk Γ3 hΓ3 gfNP (by decide) _ vNP
        refine specR_congr (m' := ctorMember? ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP (cv, nf) >>=
            fun a => List.filterAuxM (grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k m)
              (((blk.drop (j + 1)).take (n - (j + 1))).map ctorPair) (if a = some m then (cv, nf) :: acc else acc) >>=
                fun r => pure r.reverse) ?_ ?_
        · refine congrFun ?_ s
          simp only [grpP, emk, ite_false, bind_assoc]
          refine congrArg (_ >>= ·) (funext fun a => ?_)
          cases a with
          | none => simp
          | some t => by_cases et : t = m <;> simp [et]
        refine specR_callNIH (C := ctxH C H) gfX fCtorMember cmParams
          [vv gfP, vv gfK, vv gfL, .op .add [vv gfNP, vv gfW], vv gfT] (cmBody C)
          [cellA C ob, BitVec.ofNat 64 k, Enc.idxW lvls, BitVec.ofNat 64 (nP + nf), Enc.idxW cv.type] (by decide) rfl
          (by simp +decide [ctxLocals, gfLocals]) hcm
          ⟨pk Γ3 hΓ3 gfP (by decide) _ vP, pk Γ3 hΓ3 gfK (by decide) _ vK, pk Γ3 hΓ3 gfL (by decide) _ vL,
            by simp only [sev] at gNP ⊢; rw [gNP]; simp +decide [Γ3, Env.get_cons]; exact ofNat_add_small nP nf (by omega),
            by simp +decide [Γ3, sev, Env.get_cons], trivial⟩
          (PostMI (ctxH C H) k) (fun a w _ _ => w = BitVec.ofNat 64 (optIdx k a) ∧ ∀ t, a = some t → t < k)
          (fun a w s' st ⟨⟨H', hp', hw, hsr⟩, hbd⟩ => ⟨H', hp', ⟨hw, hbd⟩, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmParams _ rfl hlk)
            (cm_spec C hok hcs hcg hcmi hcn blk ob k nP lvls (cv, nf) (by omega) hlen (by simp; omega) H s
              (hCb.trans hbH) (indBlk_mono hblk hbH)))
          (fun a wx s1 H1 hp1 ⟨hwx, hbd⟩ => ?_)
        subst hwx
        let Γ4 : Env := (gfX, BitVec.ofNat 64 (optIdx k a)) :: Γ3
        have hΓ4 : ∀ z, z ∉ gfLocals → Γ4.get z = Γ0.get z := fun z hz => by
          simp only [Γ4]; rw [get_cons_nl (by decide) hz]; exact hΓ3 z hz
        have hoi : optIdx k a ≤ k := by cases a with | none => simp [optIdx] | some t => have := hbd t rfl; simp [optIdx]; omega
        have hxm := ConPanqueque.T.WC.sev_eqNatB (Γ := Γ4) (a := vv gfX) (b := vv gfM) (x := optIdx k a) (y := m) (by omega) (by omega)
          (by simp [Γ4, sev, Env.get_cons]) (pk Γ4 hΓ4 gfM (by decide) _ vM)
        by_cases ea : a = some m
        · subst ea
          simp only [ite_true]
          refine specR_ifI _ _ hxm (fun _ => ?_) (fun h => by simp [boolW, optIdx] at h)
          exact take H1 s1 Γ4 hp1 hΓ4 (by simp +decide [Γ4, Γ3, Env.get_cons]) (by simp +decide [Γ4, Γ3, Env.get_cons])
        · simp only [ea, ite_false]
          have hne : (optIdx k a == m) = false := by
            cases a with
            | none => simp [optIdx]; omega
            | some t => simp [optIdx]; intro e; exact ea (by rw [e])
          refine specR_ifI _ _ hxm (fun h => by simp [hne, boolW] at h) (fun _ => ?_)
          exact recur acc H1 s1 Γ4 (h0.trans hp1) (by have : H.length ≤ H1.length := hp1.length_le; omega) (ents_prefix hents hp1)
            (fun z hz _ => hΓ4 z hz) _ (pk Γ4 hΓ4 gfCt (by decide) _ vC)
    | _ => simp [kindAt, List.getElem?_eq_getElem (show j < blk.length by omega), hcr, kindOf] at hk4

end

def boP := ofString "bo_p"
def boM := ofString "bo_m"
def boK := ofString "bo_k"
def boNC := ofString "bo_nc"
def boL := ofString "bo_l"
def boNP := ofString "bo_np"
def boO := ofString "bo_o"
def boG := ofString "bo_g"
def boX := ofString "bo_x"
def fBgOuter := ofString "bgOuter"

def boParams : List MlS := [boP, boM, boK, boNC, boL, boNP, boO]
def boLocals : List MlS := [boG, boX]

/-- Groups `m … k - 1`: a block per member, filled, its pointer in slot `m` of the block at `o`. The member
argument is `m + (k == 1)`: the one-member block's group takes every constructor. -/
def boBody (C : Ctx) : ProgHOL 64 := prologue boLocals
  (.ite (.cmp .lower (vv boM) (vv boK))
    (allocP C boG (.op .add [.panop .mul [vv boNC, .const 16], .const 8])
    (.seq (.call (some (some (.local, boX), none)) fGrpFill
        [vv boP, vv boK, .op .add [vv boK, vv boNC], vv boK, vv boL, vv boNP,
          .op .add [vv boM, .cmp .equal (vv boK) (.const 1)], vv boG, .const 0])
    (.seq (.store (.op .add [vv boO, .op .add [.panop .mul [vv boM, .const 8], .const 8]]) (vv boG))
    (.seq (.call (some (some (.local, boX), none)) fBgOuter
        [vv boP, .op .add [vv boM, .const 1], vv boK, vv boNC, vv boL, vv boNP, vv boO])
      (.return (.const 0))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem bo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ boLocals → (ctxEnv C ++ boParams.zip vals).get x = none :=
  Knot.params_none C boLocals boParams vals (by decide) (by decide)

/-- Slots `0 … |gs| - 1` of the pointer block at `o`: each a group block above `lo`. -/
def SlotsRep (C : Ctx) (Hc H : List (BitVec 64)) (o lo : Nat) (gs : List (List (IConstantVal × Nat))) : Prop :=
  ∀ i (hi : i < gs.length), ∃ og, lo ≤ og ∧ H[o + 1 + i]? = some (cellA C og) ∧ GrpRep C Hc H og gs[i]

def PostBO (C : Ctx) (Hc : List (BitVec 64)) (o lo kk : Nat) (done gs : List (List (IConstantVal × Nat)))
    (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ SlotsRep C Hc H' o lo (done ++ gs) ∧ (done ++ gs).length = kk

theorem postBO_locals (C : Ctx) (Hc : List (BitVec 64)) (o lo kk : Nat) (done : List (List (IConstantVal × Nat))) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostBO C Hc o lo kk done a w s' st → PostBO C Hc o lo kk done a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h, hl⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h, hl⟩

theorem filterM_unfold {α : Type} (p : α → AM Bool) (l : List α) :
    List.filterM p l = (List.filterAuxM p l [] >>= fun r => pure r.reverse) := rfl

/-- **`bgOuter`** from member `m`, the groups `done` of members `0 … m - 1` in their slots. -/
theorem bo_spec (C : Ctx) (hok : CtxOK C)
    (hco : C.code.lookup fBgOuter = some (boParams.map (fun p => (p, ShapeHOL.one)), boBody C, .one))
    (hc : C.code.lookup fGrpFill = some (gfParams.map (fun p => (p, ShapeHOL.one)), gfBody C, .one))
    (hcm : C.code.lookup fCtorMember = some (cmParams.map (fun p => (p, ShapeHOL.one)), cmBody C, .one))
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcmi : C.code.lookup fMemberIdx = some (miParams.map (fun p => (p, ShapeHOL.one)), miBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k nC nP o : Nat) (lvls : LsIdx) (Hc : List (BitVec 64))
    (hn : k + nC ≤ blk.length) (hlen : blk.length < 2 ^ 59) (hnP : nP < 2 ^ 59)
    (hkind : ∀ i, k ≤ i → i < k + nC → kindAt blk i = some 4)
    (hCc : C.H <+: Hc) (hblk : IndBlk C Hc ob blk) (hco1 : Hc.length ≤ o + 1) :
    ∀ f m (done : List (List (IConstantVal × Nat))) (H : List (BitVec 64)) (s : AState),
      Hc <+: H → o + 1 + k ≤ H.length → done.length = m → SlotsRep C Hc H o (o + 1 + k) done → k - m = f → m ≤ k →
      SpecR (σ := σ) (Pre (ctxH C H) s (boParams.zip [cellA C ob, BitVec.ofNat 64 m, BitVec.ofNat 64 k,
        BitVec.ofNat 64 nC, Enc.idxW lvls, BitVec.ofNat 64 nP, cellA C o])) (boBody C) s
        ((List.range' m (k - m)).mapM (fun m' => (((blk.drop k).take nC).map ctorPair).filterM
          (grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k (m' + (if k = 1 then 1 else 0)))))
        (PostBO C Hc o (o + 1 + k) k done) := by
  intro f
  induction f with
  | zero =>
    intro m done H s hcH hroom hdl hsl hf hm
    have hmk : m = k := by omega
    subst hmk
    refine specR_prologue (postBO_locals _ _ _ _ _ _) (bo_none _ _) ?_
    have hlw := nd_lt_iff m m (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, boParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Nat.sub_self, List.range'_zero, List.mapM_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hcH, sr_of_eq ht.sr rfl rfl rfl rfl, by simpa using hsl, by simp; omega⟩)
  | succ f ih =>
    intro m done H s hcH hroom hdl hsl hf hm
    have hmk : m < k := by omega
    refine specR_prologue (postBO_locals _ _ _ _ _ _) (bo_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff m k (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, boParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hmk])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [show k - m = (k - (m + 1)) + 1 by omega, List.range'_succ, List.mapM_cons, filterM_unfold]
    let Γ0 : Env := ctxEnv (ctxH C H) ++ boParams.zip [cellA C ob, BitVec.ofNat 64 m, BitVec.ofNat 64 k,
        BitVec.ofNat 64 nC, Enc.idxW lvls, BitVec.ofNat 64 nP, cellA C o]
    have vNC : Γ0.get boNC = some (BitVec.ofNat 64 nC) := by simp +decide [Γ0, Env.get, boParams, ctxEnv]
    refine specR_allocI (C := ctxH C H) boG _ (1 + 2 * nC) (by omega) (by simp +decide [ctxLocals, boLocals])
      (fun v => by
        have h1 : sev ((boG, v) :: Γ0) (vv boNC) = some (BitVec.ofNat 64 nC) := by
          simp only [sev, sev_vv, Env.get_cons, show boNC ≠ boG by decide, ite_false]; exact vNC
        simp only [sev] at h1 ⊢; rw [h1]; simp; apply BitVec.eq_of_toNat_eq; simp; omega)
      (fun H1 ws hp1 hws hroom1 => ?_)
    have hp1' : H <+: H1 := hp1
    have hroom1' : H1.length + (1 + 2 * nC) ≤ C.HN := hroom1
    have hl1 := hp1'.length_le
    have hc1 : Hc <+: H1 := hcH.trans hp1'
    let Γ1 : Env := (boG, cellA C H1.length) :: Γ0
    have hΓ1 : ∀ z, z ≠ boG → Γ1.get z = Γ0.get z := fun z hz => by simp only [Γ1, Env.get_cons, hz, ite_false]
    have gv : ∀ y v, y ≠ boG → Γ0.get y = some v → sev Γ1 (vv y) = some v := fun y v hy h => by
      simp only [sev, sev_vv, hΓ1 y hy, h]
    have gP := gv boP (cellA C ob) (by decide) (by simp +decide [Γ0, Env.get, boParams, ctxEnv])
    have gK := gv boK (BitVec.ofNat 64 k) (by decide) (by simp +decide [Γ0, Env.get, boParams, ctxEnv])
    have gNC := gv boNC _ (by decide) vNC
    have gL := gv boL (Enc.idxW lvls) (by decide) (by simp +decide [Γ0, Env.get, boParams, ctxEnv])
    have gNP := gv boNP (BitVec.ofNat 64 nP) (by decide) (by simp +decide [Γ0, Env.get, boParams, ctxEnv])
    have gM := gv boM (BitVec.ofNat 64 m) (by decide) (by simp +decide [Γ0, Env.get, boParams, ctxEnv])
    have gO := gv boO (cellA C o) (by decide) (by simp +decide [Γ0, Env.get, boParams, ctxEnv])
    have hgf := gf_spec (σ := σ) C hok hc hcm hcs hcg hcmi hcn blk ob k (k + nC) nP (m + (if k = 1 then 1 else 0))
      H1.length lvls Hc hn hlen hnP (by split <;> omega) hkind hCc hblk nC k [] H1 (H1 ++ ws)
    rw [Nat.add_sub_cancel_left] at hgf
    have hmA : sev Γ1 (.op .add [vv boM, .cmp .equal (vv boK) (.const 1)]) =
        some (BitVec.ofNat 64 (m + (if k = 1 then 1 else 0))) := by
      have := ConPanqueque.T.WC.sev_eqNatB (Γ := Γ1) (a := vv boK) (b := .const 1) (x := k) (y := 1) (by omega) (by omega)
        gK rfl
      simp only [sev] at gM this ⊢; rw [gM, this]
      by_cases e : k = 1 <;> simp [e, boolW]
      exact word_add1_eq m
    refine specR_callNIG (C := ctxH C (H1 ++ ws)) boX fGrpFill gfParams
      [vv boP, vv boK, .op .add [vv boK, vv boNC], vv boK, vv boL, vv boNP,
        .op .add [vv boM, .cmp .equal (vv boK) (.const 1)], vv boG, .const 0] (gfBody C)
      [cellA C ob, BitVec.ofNat 64 k, BitVec.ofNat 64 (k + nC), BitVec.ofNat 64 k, Enc.idxW lvls, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 (m + (if k = 1 then 1 else 0)), cellA C H1.length, BitVec.ofNat 64 0] (by decide) rfl
      (by simp +decide [ctxLocals, boLocals]) hc
      ⟨gP, gK, by
          have e : sev Γ1 (.op .add [vv boK, vv boNC]) = some (BitVec.ofNat 64 (k + nC)) := by
            simp only [sev] at gK gNC ⊢; rw [gK, gNC]; simp; exact ofNat_add_small k nC (by omega)
          exact e, gK, gL, gNP,
        hmA, by simp [Γ1, sev, Env.get_cons]; rfl, rfl, trivial⟩
      (PostG C Hc H1 H1.length) (fun gs _ _ H2 => H1 <+: H2 ∧ GrpRep C Hc H2 H1.length gs)
      (fun gs w s' st ⟨H', hp', hs', hg'⟩ => ⟨H', ⟨hp', hg'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gfParams _ rfl hlk)
        (hgf s hc1 (List.prefix_append _ _) (Nat.le_refl _) (by simp [hws]; omega) (fun i hi => absurd hi (by simp))
          rfl (Nat.le_refl _) (by omega)))
      (fun gs w s2 H2 ⟨hp2, hgr⟩ => ?_)
    have hl2 := hp2.length_le
    let Γ2 : Env := (boX, w) :: Γ1
    have u2 : ∀ y v, y ≠ boX → sev Γ1 (vv y) = some v → sev Γ2 (vv y) = some v := fun y v hy h => by
      simp only [sev, sev_vv, Γ2, Env.get_cons, hy, ite_false] at h ⊢; exact h
    have gM2 := u2 boM _ (by decide) gM
    have gO2 := u2 boO _ (by decide) gO
    have eA : sev Γ2 (.op .add [vv boO, .op .add [.panop .mul [vv boM, .const 8], .const 8]]) =
        some (cellA C (o + 1 + m)) := by
      simp only [sev] at gO2 gM2 ⊢; rw [gO2, gM2]; simp; exact cellA_mulIdx C o m (by omega)
    refine specR_heapStoreI (ctxOK_H hok H2) (.op .add [vv boO, .op .add [.panop .mul [vv boM, .const 8], .const 8]])
      (vv boG) (o + 1 + m) (by show _ < H2.length; omega) (cellA C H1.length) eA
      (by simp +decide [sev, Env.get_cons, Γ2, Γ1]; rfl) ?_
    let H3 := H2.set (o + 1 + m) (cellA C H1.length)
    have hc3 : Hc <+: H3 := prefix_set (hc1.trans hp2) (by omega) _
    have hsl3 : SlotsRep C Hc H3 o (o + 1 + k) (done ++ [gs]) := by
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases e : i < done.length
      · obtain ⟨og, hlo, h1, h2⟩ := hsl i e
        rw [List.getElem_append_left e]
        refine ⟨og, hlo, ?_, grpRep_set (grpRep_prefix h2 (hp1'.trans hp2)) _ (Or.inl (by omega)) _⟩
        rw [List.getElem?_set_ne (by omega)]; exact get_prefix h1 (hp1'.trans hp2)
      · have : i = done.length := by omega
        subst this
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
        refine ⟨H1.length, by omega, ?_, grpRep_set hgr _ (Or.inl (by omega)) _⟩
        rw [hdl, List.getElem?_set_self (by omega)]
    refine specR_callNIG (C := ctxH (ctxH C H2) H3) boX fBgOuter boParams
      [vv boP, .op .add [vv boM, .const 1], vv boK, vv boNC, vv boL, vv boNP, vv boO] (boBody C)
      [cellA C ob, BitVec.ofNat 64 (m + 1), BitVec.ofNat 64 k, BitVec.ofNat 64 nC, Enc.idxW lvls, BitVec.ofNat 64 nP,
        cellA C o] (by decide) rfl (by simp +decide [ctxLocals, boLocals]) hco
      ⟨u2 _ _ (by decide) gP, by
          have e : sev Γ2 (.op .add [vv boM, .const 1]) = some (BitVec.ofNat 64 (m + 1)) := by
            simp only [sev] at gM2 ⊢; rw [gM2]; simp; exact word_add1_eq m
          exact e,
        u2 _ _ (by decide) gK, u2 _ _ (by decide) gNC, u2 _ _ (by decide) gL, u2 _ _ (by decide) gNP,
        u2 _ _ (by decide) gO, trivial⟩
      (PostBO C Hc o (o + 1 + k) k (done ++ [gs])) (fun gs2 _ _ H4 => Hc <+: H4 ∧
        SlotsRep C Hc H4 o (o + 1 + k) (done ++ [gs] ++ gs2) ∧ (done ++ [gs] ++ gs2).length = k)
      (fun gs2 w s' st ⟨H', hp', hs', h', hl'⟩ => ⟨H', ⟨hp', h', hl'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu boParams _ rfl hlk)
        (ih (m + 1) (done ++ [gs]) H3 s2 hc3 (by simp [H3]; omega) (by simp [hdl]) hsl3 (by omega) (by omega)))
      (fun gs2 w4 s4 H4 ⟨hc4, hsl4, hl4⟩ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hc4, sr_of_eq ht.sr rfl rfl rfl rfl, by simpa using hsl4,
      by simpa using hl4⟩)

end

def bgP := ofString "bg_p"
def bgK := ofString "bg_k"
def bgNC := ofString "bg_nc"
def bgL := ofString "bg_l"
def bgNP := ofString "bg_np"
def bgO := ofString "bg_o"
def bgX := ofString "bg_x"
def fBlockGroups := ofString "blockGroups"

def bgParams : List MlS := [bgP, bgK, bgNC, bgL, bgNP]
def bgLocals : List MlS := [bgO, bgX]

/-- The pointer block `[k, group₀, …]`. -/
def bgBody (C : Ctx) : ProgHOL 64 := prologue bgLocals
  (allocP C bgO (.op .add [.panop .mul [vv bgK, .const 8], .const 8])
  (.seq (.store (vv bgO) (vv bgK))
  (.seq (.call (some (some (.local, bgX), none)) fBgOuter [vv bgP, .const 0, vv bgK, vv bgNC, vv bgL, vv bgNP, vv bgO])
    (.return (vv bgO)))))

theorem filterAuxM_true {α : Type} : ∀ (l acc : List α),
    List.filterAuxM (fun _ => (pure true : AM Bool)) l acc = pure (l.reverse ++ acc)
  | [], acc => rfl
  | a :: l, acc => by
    rw [filterAuxM_cons, pure_bind, cond_true, filterAuxM_true l (a :: acc)]; simp

theorem mapM_congr_mem {α β : Type} (f g : α → AM β) : ∀ l : List α, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a (by simp), mapM_congr_mem f g l (fun x hx => h x (by simp [hx]))]

/-- `blockGroups` as the loop runs it. -/
theorem blockGroups_eq (names : List NIdx) (lvls : LsIdx) (nP k : Nat) (ctors : List (IConstantVal × Nat)) :
    blockGroups names lvls nP k ctors = (List.range' 0 (k - 0)).mapM
      (fun m' => ctors.filterM (grpP names lvls nP k (m' + (if k = 1 then 1 else 0)))) := by
  unfold blockGroups
  by_cases hk : k = 1
  · subst hk
    have hg : grpP names lvls nP 1 1 = fun _ => pure true := by funext c; simp [grpP]
    simp [filterM_unfold, hg, filterAuxM_true]
  · simp only [beq_iff_eq, hk, ite_false, Nat.sub_zero, Nat.add_zero, List.range_eq_range']
    refine mapM_congr_mem _ _ _ (fun m hm => ?_)
    have : m < k := by simpa using hm
    congr 1; funext c
    simp only [grpP, show m ≠ k by omega, ite_false]
    rfl

section
variable {σ : Type}

theorem bg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bgLocals → (ctxEnv C ++ bgParams.zip vals).get x = none :=
  Knot.params_none C bgLocals bgParams vals (by decide) (by decide)

/-- The groups: a pointer block of `CtorsRep` blocks, in a bigger heap. -/
def PostBG (C : Ctx) (gs : List (List (IConstantVal × Nat))) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ o, w = cellA C o ∧ PtrsRep C H' o (fun og cs => CtorsRep C H' og cs) gs

theorem postBG_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBG C a w s' st → PostBG C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

/-- **`blockGroups`**: the constructors of records `k … k + nC - 1`, by member. -/
theorem bg_spec (C : Ctx) (hok : CtxOK C)
    (hcb : C.code.lookup fBlockGroups = some (bgParams.map (fun p => (p, ShapeHOL.one)), bgBody C, .one))
    (hco : C.code.lookup fBgOuter = some (boParams.map (fun p => (p, ShapeHOL.one)), boBody C, .one))
    (hc : C.code.lookup fGrpFill = some (gfParams.map (fun p => (p, ShapeHOL.one)), gfBody C, .one))
    (hcm : C.code.lookup fCtorMember = some (cmParams.map (fun p => (p, ShapeHOL.one)), cmBody C, .one))
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcg : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcmi : C.code.lookup fMemberIdx = some (miParams.map (fun p => (p, ShapeHOL.one)), miBody, .one))
    (hcn : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k nC nP : Nat) (lvls : LsIdx)
    (hn : k + nC ≤ blk.length) (hlen : blk.length < 2 ^ 59) (hnP : nP < 2 ^ 59)
    (hkind : ∀ i, k ≤ i → i < k + nC → kindAt blk i = some 4)
    (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) (hblk : IndBlk C H ob blk) :
    SpecR (σ := σ) (Pre (ctxH C H) s (bgParams.zip [cellA C ob, BitVec.ofNat 64 k, BitVec.ofNat 64 nC, Enc.idxW lvls,
        BitVec.ofNat 64 nP])) (bgBody C) s
      (blockGroups ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k (((blk.drop k).take nC).map ctorPair))
      (PostBG (ctxH C H)) := by
  refine specR_prologue (postBG_locals _) (bg_none _ _) ?_
  rw [blockGroups_eq]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  let Γ0 : Env := ctxEnv (ctxH C H) ++ bgParams.zip [cellA C ob, BitVec.ofNat 64 k, BitVec.ofNat 64 nC, Enc.idxW lvls,
    BitVec.ofNat 64 nP]
  have vK : Γ0.get bgK = some (BitVec.ofNat 64 k) := by simp +decide [Γ0, Env.get, bgParams, ctxEnv]
  refine specR_allocI (C := ctxH C H) bgO _ (1 + k) (by omega) (by simp +decide [ctxLocals, bgLocals])
    (fun v => by
      have h1 : sev ((bgO, v) :: Γ0) (vv bgK) = some (BitVec.ofNat 64 k) := by
        simp only [sev, sev_vv, Env.get_cons, show bgK ≠ bgO by decide, ite_false]; exact vK
      simp only [sev] at h1 ⊢; rw [h1]; simp; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H1 ws hp1 hws hroom1 => ?_)
  have hp1' : H <+: H1 := hp1
  have hroom1' : H1.length + (1 + k) ≤ C.HN := hroom1
  have hl1 := hp1'.length_le
  let Γ1 : Env := (bgO, cellA (ctxH C H) H1.length) :: Γ0
  have gv : ∀ y v, y ≠ bgO → Γ0.get y = some v → sev Γ1 (vv y) = some v := fun y v hy h => by
    simp only [sev, sev_vv, Γ1, Env.get_cons, hy, ite_false, h]
  refine specR_heapStoreI (ctxOK_H hok (H1 ++ ws)) (vv bgO) (vv bgK) H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    (BitVec.ofNat 64 k) (by simp [Γ1, sev, Env.get_cons]; rfl) (gv bgK _ (by decide) vK) ?_
  let H2 := (H1 ++ ws).set H1.length (BitVec.ofNat 64 k)
  let Hc := H2.take (H1.length + 1)
  have hl2 : H2.length = H1.length + (1 + k) := by simp [H2, hws]
  have hcH2 : Hc <+: H2 := List.take_prefix _ _
  have hHH2 : H <+: H2 := prefix_set (hp1'.trans (List.prefix_append _ _)) hl1 _
  have hHc : H <+: Hc := prefix_take_of hHH2 (by omega)
  have hHcl : Hc.length = H1.length + 1 := by simp [Hc]; omega
  have hco0 : Hc[H1.length]? = some (BitVec.ofNat 64 k) := by
    simp only [Hc, H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by simp; omega)
  refine specR_congr (m' := (List.range' 0 (k - 0)).mapM (fun m' => (((blk.drop k).take nC).map ctorPair).filterM
      (grpP ((blk.take k).map (fun (c : IConstantInfo) => c.name)) lvls nP k (m' + (if k = 1 then 1 else 0)))) >>=
      fun r => pure r) (by rw [bind_pure]) ?_
  refine specR_callNIG (C := ctxH (ctxH C (H1 ++ ws)) H2) (D := ctxLocals ++ bgLocals) bgX fBgOuter boParams
    [vv bgP, .const 0, vv bgK, vv bgNC, vv bgL, vv bgNP, vv bgO] (boBody C)
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 k, BitVec.ofNat 64 nC, Enc.idxW lvls, BitVec.ofNat 64 nP,
      cellA C H1.length] (by decide) rfl (by simp +decide [ctxLocals, bgLocals]) hco
    ⟨gv bgP _ (by decide) (by simp +decide [Γ0, Env.get, bgParams, ctxEnv]), rfl, gv bgK _ (by decide) vK,
      gv bgNC _ (by decide) (by simp +decide [Γ0, Env.get, bgParams, ctxEnv]),
      gv bgL _ (by decide) (by simp +decide [Γ0, Env.get, bgParams, ctxEnv]),
      gv bgNP _ (by decide) (by simp +decide [Γ0, Env.get, bgParams, ctxEnv]),
      by simp [Γ1, sev, Env.get_cons]; rfl, trivial⟩
    (PostBO C Hc H1.length (H1.length + 1 + k) k []) (fun gs _ _ H4 => Hc <+: H4 ∧
      SlotsRep C Hc H4 H1.length (H1.length + 1 + k) ([] ++ gs) ∧ ([] ++ gs).length = k)
    (fun gs w s' (st : PState σ) ⟨H', hp', hs', h', hl'⟩ => ⟨H', ⟨hp', h', hl'⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu boParams _ rfl hlk)
      (bo_spec C hok hco hc hcm hcs hcg hcmi hcn blk ob k nC nP H1.length lvls Hc hn hlen hnP hkind
        (hp.trans hHc) (indBlk_mono hblk hHc) (by omega) k 0 [] H2 s hcH2 (by omega) rfl
        (fun i hi => absurd hi (by simp)) (by omega) (by omega)))
    (fun gs w s4 H4 ⟨hc4, hsl4, hl4⟩ => ?_)
  simp only [List.nil_append] at hsl4 hl4
  refine specR_returnI _ (cellA C H1.length) (by simp [sev, Env.get_cons, Γ1]; rfl) (fun t ht => ⟨H4, hHc.trans hc4,
    sr_of_eq ht.sr rfl rfl rfl rfl, H1.length, rfl, ?_, fun i hi => ?_⟩)
  · rw [hl4]; exact get_prefix hco0 hc4
  · obtain ⟨og, -, h1, h2⟩ := hsl4 i hi
    exact ⟨og, h1, ctorsRep_of_grp h2 hc4⟩

end

end ConPanqueque.T.Ind
