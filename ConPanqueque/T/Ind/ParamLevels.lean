import ConPanqueque.T.Ind.Groups
import ConPanqueque.T.LsInternT
import ConPanqueque.T.LInternLv
import ConPanqueque.T.SubstLsTop
import ConRon.Arena.Inductives.StructParts

/-!
# The block's own universe arguments (`paramLevels`)

`paramLevels lps`: each parameter name interned as a `.param` level, the list interned.  `plFill(l, w, i, n)`
interns names `i … n - 1` of the list block at `l` into the key block at `w`; `paramLevels(l)` allocates the
key block, fills it and interns it (`internLs`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

theorem eblk_mono {H H' : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : EBlk H o xs) (hp : H <+: H') :
    EBlk H' o xs := ⟨get_prefix h.1 hp, fun i hi => get_prefix (h.2 i hi) hp⟩

theorem paramLevels_go_cons (n : NIdx) (ns : List NIdx) : paramLevels.go (n :: ns) =
    (do let u ← internLNode (.param n); let rest ← paramLevels.go ns; pure (u :: rest)) := rfl

theorem paramLevels_go_nil : paramLevels.go [] = pure [] := rfl

def pfL := ofString "pf_l"
def pfW := ofString "pf_w"
def pfI := ofString "pf_i"
def pfN := ofString "pf_n"
def pfX := ofString "pf_x"
def pfH := ofString "pf_h"
def fPlFill := ofString "plFill"

def pfParams : List MlS := [pfL, pfW, pfI, pfN]
def pfLocals : List MlS := [pfX, pfH]

def pfBody : ProgHOL 64 := prologue pfLocals
  (.ite (.cmp .lower (vv pfI) (vv pfN))
    (.seq (.assign .local pfX (.load .one (.op .add [vv pfL, .op .add [.panop .mul [vv pfI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, pfH), none)) fInternLParam [vv pfX])
    (.seq (.store (.op .add [vv pfW, .panop .mul [vv pfI, .const 8]]) (vv pfH))
    (.seq (.call (some (some (.local, pfX), none)) fPlFill [vv pfL, vv pfW, .op .add [vv pfI, .const 1], vv pfN])
      (.return (.const 0))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem pf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pfLocals → (ctxEnv C ++ pfParams.zip vals).get x = none :=
  Knot.params_none C pfLocals pfParams vals (by decide) (by decide)

/-- The fill's post: the handles of names `i …` in the key block from `ow + i`; the heap's length kept, the
base `H0` a prefix. -/
def PostPF (C : Ctx) (H0 : List (BitVec 64)) (len ow i n : Nat) (us : List LIdx) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', H0 <+: H' ∧ H'.length = len ∧ SR (ctxH C H') s' st ∧ us.length = n - i ∧
    ∀ j (hj : j < us.length), H'[ow + i + j]? = some (Enc.idxW us[j])

theorem postPF_locals (C : Ctx) (H0 : List (BitVec 64)) (len ow i n : Nat) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostPF C H0 len ow i n a w s' st →
      PostPF C H0 len ow i n a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hl, hs, h1, h2⟩ => ⟨H', hp, hl, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

/-- **`plFill`** from name `i`. -/
theorem pf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one))
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (lps : List NIdx) (ol ow : Nat) (hn : lps.length < 2 ^ 59) :
    ∀ f i (H0 H : List (BitVec 64)) (s : AState), EBlk H0 ol (lps.map Enc.idxW) → H0 <+: H → H0.length ≤ ow + i →
      ow + lps.length ≤ H.length → lps.length - i = f → i ≤ lps.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (pfParams.zip [cellA C ol, cellA C ow, BitVec.ofNat 64 i,
        BitVec.ofNat 64 lps.length])) pfBody s (paramLevels.go (lps.drop i))
        (PostPF C H0 H.length ow i lps.length) := by
  intro f
  induction f with
  | zero =>
    intro i H0 H s hb h0 hl0 hroom hf hi
    have hin : i = lps.length := by omega
    subst hin
    refine specR_prologue (postPF_locals _ _ _ _ _ _) (pf_none _ _) ?_
    have hlw := nd_lt_iff lps.length lps.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, paramLevels_go_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, h0, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, by simp,
      fun j hj => absurd hj (by simp)⟩)
  | succ f ih =>
    intro i H0 H s hb h0 hl0 hroom hf hi
    have hin : i < lps.length := by omega
    refine specR_prologue (postPF_locals _ _ _ _ _ _) (pf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff i lps.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, paramLevels_go_cons]
    let Γ0 : Env := ctxEnv (ctxH C H) ++ pfParams.zip [cellA C ol, cellA C ow, BitVec.ofNat 64 i, BitVec.ofNat 64 lps.length]
    have vL : Γ0.get pfL = some (cellA C ol) := by simp +decide [Γ0, Env.get, pfParams, ctxEnv]
    have vW : Γ0.get pfW = some (cellA C ow) := by simp +decide [Γ0, Env.get, pfParams, ctxEnv]
    have vI : Γ0.get pfI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, pfParams, ctxEnv]
    have vN : Γ0.get pfN = some (BitVec.ofNat 64 lps.length) := by simp +decide [Γ0, Env.get, pfParams, ctxEnv]
    have hx : (ctxH C H).H[ol + 1 + i]? = some (Enc.idxW lps[i]) := by
      show H[ol + 1 + i]? = _
      have := hb.2 i (by simp; omega); simp only [List.getElem_map] at this; exact get_prefix this h0
    refine UD.specR_heapLoadI' (C := ctxH C H) pfX _ (ol + 1 + i) _ hx (by simp +decide [ctxLocals, pfLocals])
      (by
        have e : sev Γ0 (.op .add [vv pfL, .op .add [.panop .mul [vv pfI, .const 8], .const 8]]) =
            some (cellA C (ol + 1 + i)) := by
          simp only [sev, sev_vv, vL, vI]; simp; exact cellA_mulIdx C ol i (by omega)
        exact e) ?_
    let Γ1 : Env := (pfX, Enc.idxW lps[i]) :: Γ0
    have g1 : ∀ y v, y ≠ pfX → Γ0.get y = some v → sev Γ1 (vv y) = some v := fun y v hy h => by
      simp only [sev, sev_vv, Γ1, Env.get_cons, hy, ite_false, h]
    refine callLN (C := ctxH C H) pfH fInternLParam [lEn] [vv pfX] internLParamBody [Enc.idxW lps[i]] (by decide) rfl
      (by simp +decide [ctxLocals, pfLocals]) hcP ⟨by simp [Γ1, sev, Env.get_cons], trivial⟩ (.param lps[i])
      (internLParam_body_spec ra (ctxH C H) (ctxOK_H hok H) s lps[i]) (fun h s1 _ => ?_)
    let Γ2 : Env := (pfH, Enc.idxW h) :: Γ1
    have g2 : ∀ y v, y ≠ pfX → y ≠ pfH → Γ0.get y = some v → sev Γ2 (vv y) = some v := fun y v hy hy' h => by
      have := g1 y v hy h
      simp only [sev, sev_vv, Γ2, Env.get_cons, hy', ite_false] at this ⊢; exact this
    have gW := g2 pfW _ (by decide) (by decide) vW
    have gI := g2 pfI _ (by decide) (by decide) vI
    refine specR_heapStoreI (ctxOK_H hok H) (.op .add [vv pfW, .panop .mul [vv pfI, .const 8]]) (vv pfH) (ow + i)
      (by show _ < H.length; omega) (Enc.idxW h)
      (by
        have e : sev Γ2 (.op .add [vv pfW, .panop .mul [vv pfI, .const 8]]) = some (cellA C (ow + i)) := by
          simp only [sev] at gW gI ⊢; rw [gW, gI]; simp; exact cellA_mulOff C ow i (by omega)
        exact e)
      (by simp [Γ2, sev, Env.get_cons]) ?_
    let H2 := H.set (ow + i) (Enc.idxW h)
    have hl2 : H2.length = H.length := by simp [H2]
    have h02 : H0 <+: H2 := prefix_set h0 hl0 _
    let H0' := H2.take (ow + i + 1)
    have h00' : H0 <+: H0' := prefix_take_of h02 (by omega)
    have h0'2 : H0' <+: H2 := List.take_prefix _ _
    have hH0'l : H0'.length = ow + i + 1 := by simp only [H0', List.length_take, hl2]; omega
    have hcell : H0'[ow + i]? = some (Enc.idxW h) := by
      simp only [H0', H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by omega)
    have gL := g2 pfL _ (by decide) (by decide) vL
    have gN := g2 pfN _ (by decide) (by decide) vN
    refine specR_congr (m' := paramLevels.go (lps.drop (i + 1)) >>= fun rest => pure (h :: rest)) rfl ?_
    refine specR_callNIG (C := ctxH (ctxH C H) H2) pfX fPlFill pfParams
      [vv pfL, vv pfW, .op .add [vv pfI, .const 1], vv pfN] pfBody
      [cellA C ol, cellA C ow, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 lps.length] (by decide) rfl
      (by simp +decide [ctxLocals, pfLocals]) hc
      ⟨gL, gW, by
        have e : sev Γ2 (.op .add [vv pfI, .const 1]) = some (BitVec.ofNat 64 (i + 1)) := by
          simp only [sev] at gI ⊢; rw [gI]; simp; exact word_add1_eq i
        exact e, gN, trivial⟩
      (PostPF C H0' H2.length ow (i + 1) lps.length) (fun us _ _ H' => H0' <+: H' ∧ H'.length = H2.length ∧
        us.length = lps.length - (i + 1) ∧ ∀ j (hj : j < us.length), H'[ow + (i + 1) + j]? = some (Enc.idxW us[j]))
      (fun us w s' st ⟨H', hp', hl', hs', h1, h2⟩ => ⟨H', ⟨hp', hl', h1, h2⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pfParams _ rfl hlk)
        (ih (i + 1) H0' H2 s1 (eblk_mono hb h00') h0'2 (by omega) (by omega) (by omega) (by omega)))
      (fun us w s3 H4 ⟨h0'4, hl4, hus, hcells⟩ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, h00'.trans h0'4, by rw [hl4, hl2], sr_of_eq ht.sr rfl rfl rfl rfl,
      by simp; omega, fun j hj => by
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        exact get_prefix hcell h0'4
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [show ow + i + (j + 1) = ow + (i + 1) + j by omega]
        exact hcells j (by simpa using hj)⟩)

end

def plQ := ofString "pl_q"
def plK := ofString "pl_k"
def plY := ofString "pl_y"
def plR := ofString "pl_r"
def fParamLevels := ofString "paramLevels"

def plParams : List MlS := [plQ]
def plLocals : List MlS := [plK, plY, plR]

def plBody (C : Ctx) : ProgHOL 64 := prologue plLocals
  (.seq (.assign .local plK (.load .one (vv plQ)))
  (allocP C plY (.op .add [.panop .mul [vv plK, .const 8], .const 8])
  (.seq (.call (some (some (.local, plR), none)) fPlFill [vv plQ, vv plY, .const 0, vv plK])
  (.seq (.call (some (some (.local, plR), none)) fInternLs [vv plY, vv plK])
    (.return (vv plR))))))

section
variable {σ : Type}

theorem pl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ plLocals → (ctxEnv C ++ plParams.zip vals).get x = none :=
  Knot.params_none C plLocals plParams vals (by decide) (by decide)

/-- A level-list handle, in a bigger heap. -/
def PostLsH (C : Ctx) (h : LsIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW h ∧ SR (ctxH C H') s' st

theorem postLsH_locals (C : Ctx) : ∀ (a : LsIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLsH C a w s' st → PostLsH C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hs⟩ => ⟨H', hp, hw, sr_of_eq hs rfl rfl rfl rfl⟩

/-- **`paramLevels`** of the list block at `ol`. -/
theorem pl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one))
    (hc : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one))
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (hcIs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (lps : List NIdx) (ol : Nat) (hn : lps.length < 2 ^ 59) (H : List (BitVec 64)) (s : AState)
    (hb : EBlk H ol (lps.map Enc.idxW)) :
    SpecR (σ := σ) (Pre (ctxH C H) s (plParams.zip [cellA C ol])) (plBody C) s (paramLevels lps)
      (PostLsH (ctxH C H)) := by
  refine specR_prologue (postLsH_locals _) (pl_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  let Γ0 : Env := ctxEnv (ctxH C H) ++ plParams.zip [cellA C ol]
  have vQ : Γ0.get plQ = some (cellA C ol) := by simp +decide [Γ0, Env.get, plParams, ctxEnv]
  have hk0 : (ctxH C H).H[ol]? = some (BitVec.ofNat 64 lps.length) := by
    have := hb.1; simp only [List.length_map] at this; exact this
  refine UD.specR_heapLoadI' (C := ctxH C H) plK (vv plQ) ol _ hk0 (by simp +decide [ctxLocals, plLocals])
    (by simp only [sev, sev_vv, vQ]; rfl) ?_
  let Γ1 : Env := (plK, BitVec.ofNat 64 lps.length) :: Γ0
  refine specR_allocI (C := ctxH C H) plY _ (lps.length + 1) (by omega) (by simp +decide [ctxLocals, plLocals])
    (fun v => by
      have h1 : sev ((plY, v) :: Γ1) (vv plK) = some (BitVec.ofNat 64 lps.length) := by
        simp +decide [sev, Env.get_cons, Γ1]
      simp only [sev] at h1 ⊢; rw [h1]; simp; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H1 ws hp1 hws hroom1 => ?_)
  have hp1' : H <+: H1 := hp1
  have hroom1' : H1.length + (lps.length + 1) ≤ C.HN := hroom1
  let Γ2 : Env := (plY, cellA (ctxH C H) H1.length) :: Γ1
  have gQ : sev Γ2 (vv plQ) = some (cellA C ol) := by
    simp only [sev, sev_vv, Γ2, Γ1, Env.get_cons, show plQ ≠ plY by decide, show plQ ≠ plK by decide, ite_false, vQ]
  have gK : sev Γ2 (vv plK) = some (BitVec.ofNat 64 lps.length) := by
    simp only [sev, sev_vv, Γ2, Γ1, Env.get_cons, show plK ≠ plY by decide, ite_false, ite_true]
  have gY : sev Γ2 (vv plY) = some (cellA C H1.length) := by simp [sev, Γ2, Env.get_cons]; rfl
  refine specR_callNIG (C := ctxH C (H1 ++ ws)) plR fPlFill pfParams [vv plQ, vv plY, .const 0, vv plK] pfBody
    [cellA C ol, cellA C H1.length, BitVec.ofNat 64 0, BitVec.ofNat 64 lps.length] (by decide) rfl
    (by simp +decide [ctxLocals, plLocals]) hc ⟨gQ, gY, rfl, gK, trivial⟩
    (PostPF C H1 (H1 ++ ws).length H1.length 0 lps.length) (fun us _ _ H' => H1 <+: H' ∧
      H'.length = (H1 ++ ws).length ∧ us.length = lps.length - 0 ∧
      ∀ j (hj : j < us.length), H'[H1.length + 0 + j]? = some (Enc.idxW us[j]))
    (fun us w s' st ⟨H', hp', hl', hs', h1, h2⟩ => ⟨H', ⟨hp', hl', h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pfParams _ rfl hlk) (by
      have := pf_spec (σ := σ) ra C hok hc hcP lps ol H1.length hn lps.length 0 H1 (H1 ++ ws) s (eblk_mono hb hp1')
        (List.prefix_append _ _) (by omega) (by simp [hws]) (by omega) (by omega)
      rw [List.drop_zero] at this
      exact this))
    (fun us w s1 H3 ⟨h13, hl3, hus, hcells⟩ => ?_)
  simp only [Nat.sub_zero, Nat.add_zero] at hus hcells
  refine specR_congr (m' := internLsNode us >>= fun r => pure r) (by rw [bind_pure]) ?_
  have gY' : sev ((plR, w) :: Γ2) (vv plY) = some (cellA C H1.length) := by
    simp only [sev, sev_vv, Env.get_cons, show plY ≠ plR by decide, ite_false] at gY ⊢; exact gY
  have gK' : sev ((plR, w) :: Γ2) (vv plK) = some (BitVec.ofNat 64 us.length) := by
    rw [hus]; simp only [sev, sev_vv, Env.get_cons, show plK ≠ plR by decide, ite_false] at gK ⊢; exact gK
  refine specR_callNIA (C := ctxH (ctxH C (H1 ++ ws)) H3) plR fInternLs [pKey, lEc] [vv plY, vv plK] internLsBody
    [cellA C H1.length, BitVec.ofNat 64 us.length] (by decide) rfl (by simp +decide [ctxLocals, plLocals]) hcIs
    ⟨gY', gK', trivial⟩
    (fun a w s' st => internLsNode us s1 = .ok (a, s') ∧ PostLs (ctxH (ctxH C H3) H1) a w s' st)
    (fun a w s' H' => H' = H1 ∧ internLsNode us s1 = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H1, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact internLs_body_spec ra (ctxH C H3) (ctxOK_H hok H3) s1 us H1.length H1 h13 (Nat.le_refl _)
        (by show H1.length + us.length ≤ H3.length; rw [hl3]; simp [hws]; omega) (by omega)
        (fun j hj => hcells j hj) _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
    (fun h w2 s2 H' ⟨e, hr2, hw⟩ => ?_)
  subst e; subst hw
  exact specR_returnI (vv plR) (Enc.idxW h) (by simp) (fun t ht => ⟨_, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
