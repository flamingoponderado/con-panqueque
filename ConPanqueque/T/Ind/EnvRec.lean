import ConPanqueque.T.Ind.BlockCaps
import ConPanqueque.T.Decl.Install

/-!
# Environment-heap records for the block's constants

The block's constants get `CIE` records in the environment heap (appended, the index untouched), so the readers
find them through the block table. `envBlkP`: a value-heap block copied into a fresh environment block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- Stores of `es` at the words `i, i + 1, …` of the environment record at `x`. -/
def envStoresP (x : MlS) : Nat → List (ExpHOL 64) → ProgHOL 64 → ProgHOL 64
  | _, [], rest => rest
  | i, e :: es, rest => .seq (.store (.op .add [vv x, .const (BitVec.ofNat 64 (8 * i))]) e) (envStoresP x (i + 1) es rest)

/-- A fresh environment record of the words `es`, its pointer in `x`. -/
def envRecP (C : Ctx) (x : MlS) (es : List (ExpHOL 64)) (rest : ProgHOL 64) : ProgHOL 64 :=
  envAllocP C x (.const (BitVec.ofNat 64 (8 * es.length))) (envStoresP x 0 es rest)

/-- A fresh environment block holding the value-heap block at `src` (`n` words), its pointer in `x`. -/
def envBlkP (C : Ctx) (x src n r : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  envAllocP C x (.op .add [.panop .mul [vv n, .const 8], .const 8])
  (.seq (.store (vv x) (vv n))
  (.seq (.call (some (some (.local, r), none)) fCpy [vv src, vv x, .const 0, vv n]) rest))

section
variable {σ : Type}

theorem specR_envBlkI {α : Type} {C : Ctx} (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop}
    (x src n r : MlS) (o : Nat) (xs : List (BitVec 64)) (hb : BlkAt C.H o xs) (hlen : xs.length < 2 ^ 60)
    (hx : x ∈ D) (hr : r ∈ D) (hsx : src ≠ x) (hnx : n ≠ x)
    (hsrc : Γ.get src = some (cellA C o)) (hn : Γ.get n = some (BitVec.ofNat 64 xs.length))
    (hk : ∀ EH' w, C.EH <+: EH' → EBlk EH' C.EH.length xs →
      SpecR (Inv (ctxE C EH') s ((r, w) :: (x, ecell C C.EH.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (envBlkP C x src n r rest) s m R := by
  unfold envBlkP
  refine specR_envAllocI x _ (xs.length + 1) (by omega) hx
    (fun v => by simp +decide [sev, Env.get_cons, hnx, hn]; exact len8_eq xs.length) (fun ws1 hws1 hroom1 => ?_)
  have hp1 : C.EH <+: C.EH ++ ws1 := List.prefix_append _ _
  have hj1 : C.EH.length < (ctxE C (C.EH ++ ws1)).EH.length := by show _ < (C.EH ++ ws1).length; simp; omega
  refine specR_envStoreI (ctxOK_E hok hp1) (vv x) (vv n) C.EH.length hj1 (BitVec.ofNat 64 xs.length)
    (by simp [Env.get_cons] <;> rfl) (by simp [Env.get_cons, hnx, hn]) ?_
  have hp2 : C.EH <+: (C.EH ++ ws1).set C.EH.length (BitVec.ofNat 64 xs.length) :=
    ConPanqueque.T.Big.prefix_set_ge hp1 C.EH.length (le_refl _) _
  have hE2len : ((C.EH ++ ws1).set C.EH.length (BitVec.ofNat 64 xs.length)).length = C.EH.length + (xs.length + 1) := by
    simp [hws1]
  set E2 := (C.EH ++ ws1).set C.EH.length (BitVec.ofNat 64 xs.length) with hE2
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => m) rfl ?_
  refine specR_callNC (C := ctxE C E2) (D := D) r fCpy cpParams
    [vv src, vv x, .const 0, vv n] cpyBody
    [cellA C o, ecell C C.EH.length, BitVec.ofNat 64 0, BitVec.ofNat 64 xs.length]
    (by decide) rfl hr hcp ?_ (fun a w s' st => PostCp C C.EH.length xs 0 E2 a w s' st ∧ s' = s)
    (fun _ w s' C' => s' = s ∧ ∃ EH', C' = ctxE C EH' ∧ EH'.length = E2.length ∧
      (∀ p, p < C.EH.length + 1 + 0 → EH'[p]? = E2[p]?) ∧
      (∀ j (hj : j < xs.length), 0 ≤ j → EH'[C.EH.length + 1 + j]? = some xs[j]))
    (fun a w s' st ⟨⟨EH', h1, h2, h3, h4⟩, hs⟩ => ⟨ctxE C EH', ⟨hs, EH', rfl, h1, h2, h3⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cpParams _ rfl hlk)
      (specR_pureState (cpy_spec C hok hcp o C.EH.length xs hb (le_refl _) (by omega) s _ 0 E2
        hp2 (by simp [hE2len]; omega) rfl (Nat.zero_le _))))
    (fun _ w s3 C3 ⟨hs3, E3, eC, h1, h2, h3⟩ => ?_)
  · exact ⟨by simp [Env.get_cons, hsx, hsrc], by simp [Env.get_cons], rfl, by simp [Env.get_cons, hnx, hn], trivial⟩
  subst eC hs3
  have hp3 : C.EH <+: E3 := by
    refine List.prefix_iff_eq_take.mpr ?_
    apply List.ext_getElem?
    intro p
    by_cases hpl : p < C.EH.length
    · rw [List.getElem?_take, ite_eq_left hpl, h2 p (by omega), List.getElem?_eq_getElem hpl,
        get_prefix (List.getElem?_eq_getElem hpl) hp2]
    · rw [List.getElem?_take, ite_eq_right hpl, List.getElem?_eq_none (by omega)]
  refine hk E3 w hp3 ⟨?_, fun j hj => h3 j hj (Nat.zero_le _)⟩
  rw [h2 _ (by omega), hE2]
  simp [List.getElem?_set_self, hws1]

theorem specR_envStoresI {α : Type} {C0 : Ctx} (hok : CtxOK C0) (x : MlS) (b : Nat)
    {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (hx : Γ.get x = some (ecell C0 b)) (hb : C0.EH.length ≤ b) :
    ∀ (es : List (ExpHOL 64)) (vs : List (BitVec 64)) (i : Nat) (EH : List (BitVec 64)) (M : Mem),
      C0.EH <+: EH → b + i + es.length ≤ EH.length → es.length = vs.length →
      (∀ j (hj : j < es.length) (hj' : j < vs.length), sev Γ es[j] = some vs[j]) →
      (∀ EH', C0.EH <+: EH' → EH'.length = EH.length → (∀ p, (p < b + i ∨ b + i + es.length ≤ p) → EH'[p]? = EH[p]?) →
        (∀ j (hj : j < vs.length), EH'[b + i + j]? = some vs[j]) →
        SpecR (Inv (ctxE C0 EH') s Γ [] D) rest s m R) →
      SpecR (Inv (ctxE C0 EH) s Γ M D) (envStoresP x i es rest) s m R := by
  intro es
  induction es with
  | nil =>
    intro vs i EH M hp hl hlen hev hk
    cases vs with
    | cons _ _ => simp at hlen
    | nil =>
    exact specR_dropMem (hk EH hp rfl (fun _ _ => rfl) (fun j hj => absurd hj (by simp)))
  | cons e es ih =>
    intro vs i EH M hp hl hlen hev hk
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
    simp only [List.length_cons] at hl hlen
    have hj : b + i < (ctxE C0 EH).EH.length := by show b + i < EH.length; omega
    refine specR_envStoreI (ctxOK_E hok hp) _ e (b + i) hj v
      (by simp [sev, hx]; exact ecell_addk C0 b i) (hev 0 (by simp) (by simp)) ?_
    have hp' : C0.EH <+: EH.set (b + i) v := ConPanqueque.T.Big.prefix_set_ge hp _ (by omega) _
    refine ih vs (i + 1) (EH.set (b + i) v) [] hp' (by simp; omega) (by omega)
      (fun j hj hj' => hev (j + 1) (by simp; omega) (by simp; omega)) (fun EH' hp2 hl2 hpres hvals => ?_)
    refine hk EH' hp2 (by rw [hl2]; simp) (fun p hpr => ?_) (fun j hj => ?_)
    · simp only [List.length_cons] at hpr
      rw [hpres p (by omega), List.getElem?_set_ne (by omega)]
    · rcases j with _ | j
      · rw [hpres (b + i + 0) (by omega)]; simp [List.getElem?_set_self, show b + i < EH.length by omega]
      · have := hvals j (by simp at hj; omega)
        rw [show b + (i + 1) + j = b + i + (j + 1) by omega] at this
        simpa using this

theorem specR_envRecI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (es : List (ExpHOL 64)) (vs : List (BitVec 64)) (hx : x ∈ D) (hlen : es.length = vs.length)
    (hk8 : 8 * es.length < 2 ^ 64)
    (hev : ∀ w j (hj : j < es.length) (hj' : j < vs.length), sev ((x, w) :: Γ) es[j] = some vs[j])
    (hk : ∀ EH', C.EH <+: EH' → EH'.length = C.EH.length + es.length →
      (∀ j (hj : j < vs.length), EH'[C.EH.length + j]? = some vs[j]) →
      SpecR (Inv (ctxE C EH') s ((x, ecell C C.EH.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (envRecP C x es rest) s m R := by
  unfold envRecP
  refine specR_envAllocI x _ es.length hk8 hx (fun v => rfl) (fun ws hws hroom => ?_)
  refine specR_envStoresI hok x C.EH.length (by simp [Env.get_cons]) (le_refl _) es vs 0 (C.EH ++ ws) M
    (List.prefix_append _ _) (by simp [hws]) hlen (fun j hj hj' => hev _ j hj hj')
    (fun EH' hp' hl' hpres hvals => hk EH' hp' (by rw [hl']; simp [hws]) (fun j hj => by simpa using hvals j hj))

end

def crC := ofString "cr_c"
def crNp := ofString "cr_np"
def crNf := ofString "cr_nf"
def crInd := ofString "cr_ind"
def crN := ofString "cr_n"
def crL := ofString "cr_l"
def crLn := ofString "cr_ln"
def crTy := ofString "cr_ty"
def crB := ofString "cr_b"
def crX := ofString "cr_x"
def crR := ofString "cr_r"
def fCtorRec := ofString "ctorRecW"

def crParams : List MlS := [crC, crNp, crNf, crInd]
def crLocals : List MlS := [crN, crL, crLn, crTy, crB, crX, crR]

/-- A constructor's environment record `[4, name, lps, type, np, nf, induct]` from its value-heap constant. -/
def crBody (C : Ctx) : ProgHOL 64 := prologue crLocals
  (.seq (.assign .local crN (.load .one (vv crC)))
  (.seq (.assign .local crL (.load .one (.op .add [vv crC, .const 8])))
  (.seq (.assign .local crTy (.load .one (.op .add [vv crC, .const 16])))
  (.seq (.assign .local crLn (.load .one (vv crL)))
  (envBlkP C crB crL crLn crR
  (envRecP C crX [.const 4, vv crN, vv crB, vv crTy, vv crNp, vv crNf, vv crInd]
    (.return (vv crX))))))))

section
variable {σ : Type}

/-- A fresh environment record of `ci` at `o`, appended past the context's environment heap. -/
def PostRec (C : Ctx) (ci : IConstantInfo) (s : AState) (_ : Unit) (w : BitVec 64) (s' : AState) (st : PState σ) :
    Prop :=
  s' = s ∧ ∃ EH o, C.EH <+: EH ∧ C.EH.length ≤ o ∧ w = ecell C o ∧ CIE C.EB EH o ci ∧ SR (ctxE C EH) s st

theorem postRec_locals (C : Ctx) (ci : IConstantInfo) (s : AState) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostRec C ci s a w s' st → PostRec C ci s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, EH, o, h1, h2, h3, h4, h5⟩ => ⟨h0, EH, o, h1, h2, h3, h4, sr_of_eq h5 rfl rfl rfl rfl⟩

theorem cr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crLocals → (ctxEnv C ++ crParams.zip vals).get x = none :=
  Knot.params_none C crLocals crParams vals (by decide) (by decide)

/-- **A constructor's record**, written into the environment heap. -/
theorem cr_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (cv : IConstantVal) (oc : Nat) (hcv : CVRep C C.H oc cv) (hlps : cv.levelParams.length < 2 ^ 60)
    (np nf : Nat) (hnp : np < 2 ^ 63) (hnf : nf < 2 ^ 63) (ind : NIdx) (s : AState) :
    SpecR (σ := σ) (Pre C s (crParams.zip [cellA C oc, BitVec.ofNat 64 np, BitVec.ofNat 64 nf, Enc.idxW ind]))
      (crBody C) s (pure ()) (PostRec C (.ctorInfo cv np nf ind) s) := by
  refine specR_prologue (postRec_locals _ _ _) (cr_none _ _) ?_
  obtain ⟨hn0, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcv
  have hbl : BlkAt C.H ol (cv.levelParams.map Enc.idxW) := hebl
  refine UD.specR_heapLoadI' (C := C) crN _ oc _ hn0 (by decide) (by simp +decide [Env.get, crParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) crL _ (oc + 1) _ hwl (by decide)
    (by simp +decide [sev, Env.get, crParams, ctxEnv]; exact cellA_add8 C oc) ?_
  refine UD.specR_heapLoadI' (C := C) crTy _ (oc + 2) _ hty (by decide)
    (by simp +decide [sev, Env.get, crParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  have hb1 : C.H[ol]? = some (BitVec.ofNat 64 (cv.levelParams.map Enc.idxW).length) := hbl.1
  refine UD.specR_heapLoadI' (C := C) crLn _ ol _ hb1 (by decide)
    (by simp +decide [Env.get, hwlo]; rfl) ?_
  refine specR_envBlkI hok hcp crB crL crLn crR ol _ hbl (by simpa using hlps) (by decide) (by decide)
    (by decide) (by decide) (by simp +decide [Env.get, hwlo]; rfl) (by simp +decide [Env.get])
    (fun EH1 w1 hp1 heb1 => ?_)
  have hok1 := ctxOK_E hok hp1
  refine specR_envRecI hok1 crX [.const 4, vv crN, vv crB, vv crTy, vv crNp, vv crNf, vv crInd]
    [4, Enc.idxW cv.name, ecell C C.EH.length, Enc.idxW cv.type, BitVec.ofNat 64 np, BitVec.ofNat 64 nf, Enc.idxW ind]
    (by decide) rfl (by decide)
    (fun w j hj hj' => by
      rcases j with _ | _ | _ | _ | _ | _ | _ | j <;>
        first | rfl | (simp +decide [sev, Env.get, crParams, ctxEnv]; done) |
          (simp +decide [sev, Env.get, crParams, ctxEnv]; rfl) | (simp at hj; omega))
    (fun EH2 hp2 hl2 hv2 => ?_)
  have hp12 : C.EH <+: EH2 := hp1.trans hp2
  have hE1 : (ctxE C EH1).EH.length = EH1.length := rfl
  have hlen1 := hp1.length_le
  have g : ∀ j (hj : j < 7), EH2[EH1.length + j]? = some ([4, Enc.idxW cv.name, ecell C C.EH.length,
      Enc.idxW cv.type, BitVec.ofNat 64 np, BitVec.ofNat 64 nf, Enc.idxW ind] : List (BitVec 64))[j] :=
    fun j hj => hv2 j (by simpa using hj)
  exact specR_returnI _ (ecell C EH1.length) (by simp [Env.get] <;> rfl)
    (fun t ht => ⟨rfl, EH2, EH1.length, hp12, hlen1, rfl, by
      refine ⟨⟨?_, ⟨ecell C C.EH.length, ?_, C.EH.length, rfl, eblk_mono heb1 hp2⟩, ?_⟩, ?_, ⟨?_, hnp⟩, ⟨?_, hnf⟩, ?_⟩
      · exact g 1 (by decide)
      · exact g 2 (by decide)
      · exact g 3 (by decide)
      · exact g 0 (by decide)
      · exact g 4 (by decide)
      · exact g 5 (by decide)
      · exact g 6 (by decide), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def cwC := ofString "cw_c"
def cwT := ofString "cw_t"
def cwF4 := ofString "cw_f4"
def cwF5 := ofString "cw_f5"
def cwF6 := ofString "cw_f6"
def cwF7 := ofString "cw_f7"
def cwF8 := ofString "cw_f8"
def cwF9 := ofString "cw_f9"
def cwN := ofString "cw_n"
def cwL := ofString "cw_l"
def cwLn := ofString "cw_ln"
def cwTy := ofString "cw_ty"
def cwB := ofString "cw_b"
def cwX := ofString "cw_x"
def cwR := ofString "cw_r"
def fConstRec := ofString "constRecW"

def cwParams : List MlS := [cwC, cwT, cwF4, cwF5, cwF6, cwF7, cwF8, cwF9]
def cwLocals : List MlS := [cwN, cwL, cwLn, cwTy, cwB, cwX, cwR]

/-- A constant's ten-word environment record `[tag, name, lps, type, f₄ … f₉]` from its value-heap constant. -/
def cwBody (C : Ctx) : ProgHOL 64 := prologue cwLocals
  (.seq (.assign .local cwN (.load .one (vv cwC)))
  (.seq (.assign .local cwL (.load .one (.op .add [vv cwC, .const 8])))
  (.seq (.assign .local cwTy (.load .one (.op .add [vv cwC, .const 16])))
  (.seq (.assign .local cwLn (.load .one (vv cwL)))
  (envBlkP C cwB cwL cwLn cwR
  (envRecP C cwX [vv cwT, vv cwN, vv cwB, vv cwTy, vv cwF4, vv cwF5, vv cwF6, vv cwF7, vv cwF8, vv cwF9]
    (.return (vv cwX))))))))

section
variable {σ : Type}

/-- A fresh ten-word record: the constant's three words, the tag and the six fields. -/
def PostCW (C : Ctx) (cv : IConstantVal) (tg : BitVec 64) (fs : List (BitVec 64)) (s : AState) (_ : Unit)
    (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ EH o, C.EH <+: EH ∧ C.EH.length ≤ o ∧ w = ecell C o ∧ CVE C.EB EH (o + 1) cv ∧ EH[o]? = some tg ∧
    (∀ j (hj : j < fs.length), EH[o + 4 + j]? = some fs[j]) ∧ SR (ctxE C EH) s st

theorem postCW_locals (C : Ctx) (cv : IConstantVal) (tg : BitVec 64) (fs : List (BitVec 64)) (s : AState) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCW C cv tg fs s a w s' st → PostCW C cv tg fs s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, EH, o, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h0, EH, o, h1, h2, h3, h4, h5, h6, sr_of_eq h7 rfl rfl rfl rfl⟩

theorem cw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cwLocals → (ctxEnv C ++ cwParams.zip vals).get x = none :=
  Knot.params_none C cwLocals cwParams vals (by decide) (by decide)

/-- **A constant's ten-word record**, written into the environment heap. -/
theorem cw_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (cv : IConstantVal) (oc : Nat) (hcv : CVRep C C.H oc cv) (hlps : cv.levelParams.length < 2 ^ 60)
    (tg f4 f5 f6 f7 f8 f9 : BitVec 64) (s : AState) :
    SpecR (σ := σ) (Pre C s (cwParams.zip [cellA C oc, tg, f4, f5, f6, f7, f8, f9]))
      (cwBody C) s (pure ()) (PostCW C cv tg [f4, f5, f6, f7, f8, f9] s) := by
  refine specR_prologue (postCW_locals _ _ _ _ _) (cw_none _ _) ?_
  obtain ⟨hn0, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcv
  have hbl : BlkAt C.H ol (cv.levelParams.map Enc.idxW) := hebl
  refine UD.specR_heapLoadI' (C := C) cwN _ oc _ hn0 (by decide) (by simp +decide [Env.get, cwParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cwL _ (oc + 1) _ hwl (by decide)
    (by simp +decide [sev, Env.get, cwParams, ctxEnv]; exact cellA_add8 C oc) ?_
  refine UD.specR_heapLoadI' (C := C) cwTy _ (oc + 2) _ hty (by decide)
    (by simp +decide [sev, Env.get, cwParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  have hb1 : C.H[ol]? = some (BitVec.ofNat 64 (cv.levelParams.map Enc.idxW).length) := hbl.1
  refine UD.specR_heapLoadI' (C := C) cwLn _ ol _ hb1 (by decide)
    (by simp +decide [Env.get, hwlo]; rfl) ?_
  refine specR_envBlkI hok hcp cwB cwL cwLn cwR ol _ hbl (by simpa using hlps) (by decide) (by decide)
    (by decide) (by decide) (by simp +decide [Env.get, hwlo]; rfl) (by simp +decide [Env.get])
    (fun EH1 w1 hp1 heb1 => ?_)
  have hok1 := ctxOK_E hok hp1
  refine specR_envRecI hok1 cwX [vv cwT, vv cwN, vv cwB, vv cwTy, vv cwF4, vv cwF5, vv cwF6, vv cwF7, vv cwF8, vv cwF9]
    [tg, Enc.idxW cv.name, ecell C C.EH.length, Enc.idxW cv.type, f4, f5, f6, f7, f8, f9]
    (by decide) rfl (by decide)
    (fun w j hj hj' => by
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
        first | rfl | (simp +decide [sev, Env.get, cwParams, ctxEnv]; done) |
          (simp +decide [sev, Env.get, cwParams, ctxEnv]; rfl) | (simp at hj; omega))
    (fun EH2 hp2 hl2 hv2 => ?_)
  have hp12 : C.EH <+: EH2 := hp1.trans hp2
  have hlen1 := hp1.length_le
  have g : ∀ j (hj : j < 10), EH2[EH1.length + j]? = some ([tg, Enc.idxW cv.name, ecell C C.EH.length,
      Enc.idxW cv.type, f4, f5, f6, f7, f8, f9] : List (BitVec 64))[j] :=
    fun j hj => hv2 j (by simpa using hj)
  exact specR_returnI _ (ecell C EH1.length) (by simp [Env.get] <;> rfl)
    (fun t ht => ⟨rfl, EH2, EH1.length, hp12, hlen1, rfl,
      ⟨g 1 (by decide), ⟨ecell C C.EH.length, g 2 (by decide), C.EH.length, rfl, eblk_mono heb1 hp2⟩, g 3 (by decide)⟩,
      g 0 (by decide),
      fun j hj => by
        have := g (4 + j) (by simp at hj; omega)
        rw [show EH1.length + (4 + j) = EH1.length + 4 + j by omega] at this
        rw [this]; simp at hj
        rcases j with _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
