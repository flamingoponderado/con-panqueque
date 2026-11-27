import ConPanqueque.T.Ind.BasisHit
import ConPanqueque.T.Ind.AndCanon

/-!
# The pinned `And` block (`andPinOk`'s `canonEqList` branch)

`anmBody(o, n)`: the block's names are exactly the pinned `And` names `[And, And.intro, And.rec]` (pins `11`,
`48`, `49`): `1`, else `0` (`AndNames`).

`apkBody(o, nP, a)`: at `a = 0` nothing (the twin's test passes off the names' freshness). At `a ≠ 0`: `nP = 2`
(else hang), the scratch tier off (else hang), the pinned block interned (`genPinBlk`, the twin's `andPinDecls`),
the block's records against the pin's, word by word (`CanonAgree`, a mismatch hangs), and the recursor's
numbered level-parameter name `.num .anonymous 0` interned (the twin's `canonNames 1`). Then `canonEqList block
pinned` is `true` (`canonEqList_and`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl
open ConPanqueque.Start ConPanqueque.Logic.PlainIntern ConPanqueque.T.Lit ConPanqueque.T.Quot

/-- The block's names are the pinned `And` block's. -/
def AndNames (C : Ctx) (blk : List IConstantInfo) : Prop :=
  blk.map (·.name) = [C.pins.names[11]!, C.pins.names[48]!, C.pins.names[49]!]

instance (C : Ctx) (blk : List IConstantInfo) : Decidable (AndNames C blk) := by
  unfold AndNames; infer_instance

def amO := ofString "am_o"
def amN := ofString "am_n"
def amP := ofString "am_p"
def amM := ofString "am_m"
def amX := ofString "am_x"
def fAnm := ofString "andNamesHit"

def anmParams : List MlS := [amO, amN]
def anmLocals : List MlS := [amP, amM, amX]

/-- Record `i`'s name against pin `j` (`0` on a mismatch). -/
def anmStep (C : Ctx) (i j : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local amP (.load .one (.op .add [vv amO, .const (BitVec.ofNat 64 (8 * (i + 1)))])))
  (.seq (.assign .local amM (.load .one (.op .add [vv amP, .const 8])))
  (.seq (.assign .local amX (.load .one (.const (ecell C (C.PO + j)))))
  (.ite (.cmp .notEqual (vv amM) (vv amX)) (.return (.const 0)) rest)))

def anmBody (C : Ctx) : ProgHOL 64 := prologue anmLocals
  (.ite (.cmp .equal (vv amN) (.const 3))
    (anmStep C 0 11 (anmStep C 1 48 (anmStep C 2 49 (.return (.const 1)))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem anm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ anmLocals → (ctxEnv C ++ anmParams.zip vals).get x = none :=
  Knot.params_none C anmLocals anmParams vals (by decide) (by decide)

/-- One name test. -/
theorem specR_anmStep (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64}
    (b : Bool) (blk : List IConstantInfo) (ob : Nat) (hblk : IndBlk C C.H ob blk) (i j : Nat) (hi : i < blk.length)
    (hj : j < pinCount) (hob : Γ.get amO = some (cellA C ob)) (hD : amP ∈ D ∧ amM ∈ D ∧ amX ∈ D)
    (hne : blk[i].name ≠ C.pins.names[j]! → b = false)
    (hk : ∀ Γ' : Env, (∀ x, x ≠ amP → x ≠ amM → x ≠ amX → Γ'.get x = Γ.get x) → blk[i].name = C.pins.names[j]! →
      SpecR (σ := σ) (Inv C s Γ' [] D) rest s (pure b) (PostB C)) :
    SpecR (σ := σ) (Inv C s Γ [] D) (anmStep C i j rest) s (pure b) (PostB C) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := hblk
  unfold anmStep
  have hio : i < os.length := by omega
  have h1 := hosb.2 i (by simp; omega)
  simp only [List.getElem_map] at h1
  refine UD.specR_heapLoadI' (C := C) amP _ (ob + 1 + i) _ h1 hD.1
    (by simp only [sev, sev_vv, hob]; rw [show ob + 1 + i = ob + (i + 1) by omega, ← cellA_add_ofNat]; rfl) ?_
  have hcv := (hosr i hi hio).1
  refine UD.specR_heapLoadI' (C := C) amM _ (os[i] + 1) _ hcv.1 hD.2.1
    (by simp [sev, sev_vv, Env.get_cons]; exact cellA_add8 C _) ?_
  refine specR_envLoadI (C := C) amX _ (C.PO + j) _ hD.2.2 rfl (pin_cell hok j hj) ?_
  by_cases e : blk[i].name = C.pins.names[j]!
  · have e' : blk[i].toConstantVal.name = C.pins.names[j]! := by rw [← ci_name_eq]; exact e
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get_cons, e', Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => hk _ (fun x h1 h2 h3 => by simp [Env.get_cons, h1, h2, h3]) e)
  · have hw : Enc.idxW blk[i].toConstantVal.name ≠ Enc.idxW C.pins.names[j]! := fun h => e (by rw [ci_name_eq]; exact Enc.idxW_inj h)
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get_cons, hw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [hne e]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by
      rw [ConPanqueque.Front.ctxH_self]; exact sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem andNames_len {C : Ctx} {blk : List IConstantInfo} (h : AndNames C blk) : blk.length = 3 := by
  have := congrArg List.length h; simpa using this

/-- **The `And` names test.** -/
theorem anm_spec (C : Ctx) (hok : CtxOK C) (blk : List IConstantInfo) (ob : Nat) (hblk : IndBlk C C.H ob blk)
    (hbl : blk.length < 2 ^ 61) (s : AState) :
    SpecR (σ := σ) (Pre C s (anmParams.zip [cellA C ob, BitVec.ofNat 64 blk.length])) (anmBody C) s
      (pure (decide (AndNames C blk))) (PostB C) := by
  refine specR_prologue (postB_locals _) (anm_none _ _) ?_
  have hD : amP ∈ ctxLocals ++ anmLocals ∧ amM ∈ ctxLocals ++ anmLocals ∧ amX ∈ ctxLocals ++ anmLocals := by decide
  have hob : (ctxEnv C ++ anmParams.zip [cellA C ob, BitVec.ofNat 64 blk.length]).get amO = some (cellA C ob) := by
    simp +decide [Env.get, anmParams, ctxEnv]
  by_cases h3 : blk.length = 3
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, anmParams, ctxEnv, h3,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hpc : pinCount = 52 := rfl
    refine specR_anmStep C hok _ blk ob hblk 0 11 (by omega) (by omega) hob hD
      (fun e => decide_eq_false (fun h => e (by
        have := congrArg (·[0]?) h; simp [List.getElem?_eq_getElem (show 0 < blk.length by omega)] at this; exact this))) (fun Γ1 g1 e0 => ?_)
    refine specR_anmStep C hok _ blk ob hblk 1 48 (by omega) (by omega)
      (by rw [g1 _ (by decide) (by decide) (by decide)]; exact hob) hD
      (fun e => decide_eq_false (fun h => e (by
        have := congrArg (·[1]?) h; simp [List.getElem?_eq_getElem (show 1 < blk.length by omega)] at this; exact this))) (fun Γ2 g2 e1 => ?_)
    refine specR_anmStep C hok _ blk ob hblk 2 49 (by omega) (by omega)
      (by rw [g2 _ (by decide) (by decide) (by decide), g1 _ (by decide) (by decide) (by decide)]; exact hob) hD
      (fun e => decide_eq_false (fun h => e (by
        have := congrArg (·[2]?) h; simp [List.getElem?_eq_getElem (show 2 < blk.length by omega)] at this; exact this))) (fun Γ3 g3 e2 => ?_)
    have hA : AndNames C blk := by
      match blk, h3, e0, e1, e2 with
      | [c0, c1, c2], _, e0, e1, e2 =>
        simp only [AndNames, List.map_cons, List.map_nil]
        exact congrArg₂ _ e0 (congrArg₂ _ e1 (congrArg₂ _ e2 rfl))
    rw [decide_eq_true hA]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by
      rw [ConPanqueque.Front.ctxH_self]; exact sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get, anmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact fun h => h3 ((ofNat_eq_small61 hbl (by decide)).mp h)) (fun h => absurd rfl h) (fun _ => ?_)
    rw [decide_eq_false (fun h => h3 (andNames_len h))]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by
      rw [ConPanqueque.Front.ctxH_self]; exact sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The pin's comparison -/

def akO := ofString "ak_o"
def akNp := ofString "ak_np"
def akA := ofString "ak_a"
def akQ := ofString "ak_q"
def akB := ofString "ak_b"
def akC := ofString "ak_c"
def akL := ofString "ak_l"
def akM := ofString "ak_m"
def akU := ofString "ak_u"
def akV := ofString "ak_v"
def akK := ofString "ak_k"
def akH := ofString "ak_h"
def fApk := ofString "andPinCheck"

def apkParams : List MlS := [akO, akNp, akA]
def apkLocals : List MlS := [akQ, akB, akC, akL, akM, akU, akV, akK, akH, ocA, ocB, ocC, ocD, qN, qL, qT, qU, qX, qW,
  vPn, vKa] ++ pbLocs ++ genLocals

/-- Word `k` of the records at `x` and `y` compared (a mismatch hangs). -/
def cw (x y : MlS) (k : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  cmpW akU akV (.op .add [vv x, .const (BitVec.ofNat 64 (8 * k))]) (.op .add [vv y, .const (BitVec.ofNat 64 (8 * k))])
    rest

/-- Record `i` of the block and of the pin: kind, name, level-parameter count. -/
def recHead (i : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local akB (.load .one (.op .add [vv akO, .const (BitVec.ofNat 64 (8 * (i + 1)))])))
  (.seq (.assign .local akC (.load .one (.op .add [vv akQ, .const (BitVec.ofNat 64 (8 * (i + 1)))])))
  (cw akB akC 0 (cw akB akC 1
  (.seq (.assign .local akL (.load .one (.op .add [vv akB, .const 16])))
  (.seq (.assign .local akM (.load .one (.op .add [vv akC, .const 16])))
  (cw akL akM 0 rest))))))

/-- The rule blocks: one rule each, its constructor, field count, firing tag and right-hand side. -/
def rulesCmp (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local akL (.load .one (.op .add [vv akB, .const 56])))
  (.seq (.assign .local akM (.load .one (.op .add [vv akC, .const 56])))
  (cw akL akM 0
  (.seq (.assign .local akL (.load .one (.op .add [vv akL, .const 8])))
  (.seq (.assign .local akM (.load .one (.op .add [vv akM, .const 8])))
  (cw akL akM 0 (cw akL akM 1 (cw akL akM 2 (cw akL akM 5 rest))))))))

/-- The recursor's numbered level-parameter name `.num .anonymous 0` interned, then `1`. -/
def numTail (C : Ctx) : ProgHOL 64 :=
  allocWr C akK [.const (Enc.idxW anonH)]
    (.seq (.call (some (some (.local, akH), none)) Front.fInternNNum
        [vv akK, .const 1, .const (Enc.idxW anonH), .const 0])
      (.return (.const 1)))

/-- The three records against the pin's. -/
def andCmp (C : Ctx) : ProgHOL 64 :=
  recHead 0 (cw akB akC 3
  (recHead 1 (cw akB akC 3 (cw akB akC 4 (cw akB akC 5 (cw akB akC 6
  (recHead 2 (cw akL akM 1 (cw akB akC 3 (cw akB akC 4 (cw akB akC 5 (cw akB akC 6
  (rulesCmp (numTail C))))))))))))))

/-- **The `And` pin's test at a block named `[And, And.intro, And.rec]`** (`a ≠ 0`; hang unless it holds). -/
def apkBody (C : Ctx) : ProgHOL 64 := prologue apkLocals
  (.ite (.cmp .equal (vv akA) (.const 0)) (.return (.const 1))
  (.ite (.cmp .notEqual (vv akNp) (.const (BitVec.ofNat 64 2))) hang
  (offCheckP C (genPinBlk C akQ ConLeche.andPin (andCmp C)))))

section
variable {σ : Type}

/-- One word compared. -/
theorem specR_cw {α : Type} {Cx : Ctx} {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (x y : MlS) (ox oy k : Nat) (wx wy : BitVec 64)
    (hx : Γ.get x = some (cellA Cx ox)) (hy : Γ.get y = some (cellA Cx oy)) (hyU : y ≠ akU)
    (hD : akU ∈ D ∧ akV ∈ D) (h1 : Cx.H[ox + k]? = some wx) (h2 : Cx.H[oy + k]? = some wy)
    (hk : ∀ Γ' : Env, (∀ z, z ≠ akU → z ≠ akV → Γ'.get z = Γ.get z) → wx = wy →
      SpecR (Inv Cx s Γ' [] D) rest s m R) :
    SpecR (Inv Cx s Γ [] D) (cw x y k rest) s m R := by
  unfold cw cmpW
  refine UD.specR_heapLoadI' (C := Cx) akU _ (ox + k) _ h1 hD.1
    (by simp only [sev, sev_vv, hx]; rw [← cellA_add_ofNat]; rfl) ?_
  refine UD.specR_heapLoadI' (C := Cx) akV _ (oy + k) _ h2 hD.2
    (by simp only [sev, sev_vv]; rw [Env.get_cons, if_neg hyU, hy, ← cellA_add_ofNat]; rfl) ?_
  refine Quot.specR_guardNe akU akV wx wy (by rw [Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl])
    (by rw [Env.get_cons, if_pos rfl]) (fun e => hk _ (fun z h1 h2 => by
      rw [Env.get_cons, if_neg h2, Env.get_cons, if_neg h1]) e)

theorem eblk_len_le {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : EBlk H o xs) :
    o + xs.length < H.length + 1 := by
  rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
  · have := (List.getElem?_eq_some_iff.mp h.1).1; omega
  · have := (List.getElem?_eq_some_iff.mp (h.2 (xs.length - 1) (by omega))).1; omega

/-- The locals the comparison writes. -/
def akW : List MlS := [akB, akC, akL, akM, akU, akV]

/-- **A record's head**: kind, name and level-parameter count agree with the pin's (else hang). -/
theorem specR_recHead {α : Type} {Cx : Ctx} (hok : CtxOK Cx) {s : AState} {Γ : Env} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (blk pins : List IConstantInfo) (ob oq : Nat) (hblk : IndBlk Cx Cx.H ob blk) (hpb : PinBlk Cx Cx.H oq pins)
    (i : Nat) (hi : i < blk.length) (hip : i < pins.length)
    (hlb : blk[i].toConstantVal.levelParams.length < 2 ^ 61) (hlp : pins[i].toConstantVal.levelParams.length < 2 ^ 61)
    (hO : Γ.get akO = some (cellA Cx ob)) (hQ : Γ.get akQ = some (cellA Cx oq)) (hD : ∀ x ∈ akW, x ∈ D)
    (hk : ∀ (Γ' : Env) (ob' op' ol ol' : Nat), (∀ z, z ∉ akW → Γ'.get z = Γ.get z) →
      Γ'.get akB = some (cellA Cx ob') → Γ'.get akC = some (cellA Cx op') →
      Γ'.get akL = some (cellA Cx ol) → Γ'.get akM = some (cellA Cx ol') →
      CIE Cx.HB Cx.H ob' blk[i] → PinRec Cx.HB Cx.H op' pins[i] →
      EBlk Cx.H ol (blk[i].toConstantVal.levelParams.map Enc.idxW) →
      EBlk Cx.H ol' (pins[i].toConstantVal.levelParams.map Enc.idxW) →
      ciTag blk[i] = ciTag pins[i] → blk[i].toConstantVal.name = pins[i].toConstantVal.name →
      blk[i].toConstantVal.levelParams.length = pins[i].toConstantVal.levelParams.length →
      SpecR (Inv Cx s Γ' [] D) rest s m R) :
    SpecR (Inv Cx s Γ [] D) (recHead i rest) s m R := by
  obtain ⟨os, hosl, hosb, hosr⟩ := hblk
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hpb
  have hio : i < os.length := by omega
  have hipo : i < ps.length := by omega
  have hU : akU ∈ D ∧ akV ∈ D := ⟨hD _ (by decide), hD _ (by decide)⟩
  have hb1 := hosb.2 i (by simp; omega)
  have hp1 := hpsb.2 i (by simp; omega)
  simp only [List.getElem_map] at hb1 hp1
  have hci := hosr i hi hio
  have hpi := hpsr i hip hipo
  unfold recHead
  refine UD.specR_heapLoadI' (C := Cx) akB _ (ob + 1 + i) _ hb1 (hD _ (by decide))
    (by simp only [sev, sev_vv, hO]; rw [show ob + 1 + i = ob + (i + 1) by omega, ← cellA_add_ofNat]; rfl) ?_
  refine UD.specR_heapLoadI' (C := Cx) akC _ (oq + 1 + i) _ hp1 (hD _ (by decide))
    (by simp only [sev, sev_vv]; rw [Env.get_cons, if_neg (by decide), hQ,
      show oq + 1 + i = oq + (i + 1) by omega, ← cellA_add_ofNat]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  have gB : Env.get ((akC, cellA Cx ps[i]) :: (akB, cellA Cx os[i]) :: Γ) akB = some (cellA Cx os[i]) := by
    rw [Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl]
  have gC : Env.get ((akC, cellA Cx ps[i]) :: (akB, cellA Cx os[i]) :: Γ) akC = some (cellA Cx ps[i]) := by
    rw [Env.get_cons, if_pos rfl]
  refine specR_cw akB akC os[i] ps[i] 0 _ _ gB gC (by decide) hU (cie_tag hci) (pinRec_tag hpi)
    (fun Γ1 g1 etag => ?_)
  have htag : ciTag blk[i] = ciTag pins[i] := natW_inj (by have := ciTag_lt blk[i]; omega)
    (by have := ciTag_lt pins[i]; omega) etag
  have hcv := hci.1
  have hpv := hpi.1
  refine specR_cw akB akC os[i] ps[i] 1 _ _ (by rw [g1 _ (by decide) (by decide)]; exact gB)
    (by rw [g1 _ (by decide) (by decide)]; exact gC) (by decide) hU hcv.1 hpv.1 (fun Γ2 g2 ename => ?_)
  have hname := Enc.idxW_inj ename
  obtain ⟨wl, hwl, ol, rfl, hel⟩ := hcv.2.1
  obtain ⟨wl', hwl', ol', rfl, hel'⟩ := hpv.2.1
  refine UD.specR_heapLoadI' (C := Cx) akL _ (os[i] + 1 + 1) _ hwl (hD _ (by decide))
    (by simp only [sev, sev_vv]; rw [g2 _ (by decide) (by decide), g1 _ (by decide) (by decide), gB,
      show os[i] + 1 + 1 = os[i] + 2 by omega, ← cellA_add_ofNat]; rfl) ?_
  refine UD.specR_heapLoadI' (C := Cx) akM _ (ps[i] + 1 + 1) _ hwl' (hD _ (by decide))
    (by simp only [sev, sev_vv]; rw [Env.get_cons, if_neg (by decide), g2 _ (by decide) (by decide),
      g1 _ (by decide) (by decide), gC, show ps[i] + 1 + 1 = ps[i] + 2 by omega, ← cellA_add_ofNat]; rfl) ?_
  refine specR_cw akL akM ol ol' 0 _ _ (by rw [Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl]; rfl)
    (by rw [Env.get_cons, if_pos rfl]; rfl) (by decide) hU (by simpa using hel.1) (by simpa using hel'.1)
    (fun Γ3 g3 elen => ?_)
  have hlen : blk[i].toConstantVal.levelParams.length = pins[i].toConstantVal.levelParams.length :=
    natW_inj (by omega) (by omega) (by simpa using elen)
  have gx : ∀ z, z ≠ akU → z ≠ akV → z ≠ akL → z ≠ akM → z ≠ akB → z ≠ akC →
      Γ3.get z = Γ.get z := fun z a b c d e f => by
    rw [g3 z a b, Env.get_cons, if_neg d, Env.get_cons, if_neg c, g2 z a b, g1 z a b, Env.get_cons, if_neg f,
      Env.get_cons, if_neg e]
  refine hk Γ3 os[i] ps[i] ol ol' (fun z hz => ?_) ?_ ?_ ?_ ?_ hci hpi hel hel' htag hname hlen
  · simp only [akW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
    exact gx z h5 h6 h3 h4 h1 h2
  · rw [g3 _ (by decide) (by decide), Env.get_cons, if_neg (by decide), Env.get_cons, if_neg (by decide),
      g2 _ (by decide) (by decide), g1 _ (by decide) (by decide), gB]
  · rw [g3 _ (by decide) (by decide), Env.get_cons, if_neg (by decide), Env.get_cons, if_neg (by decide),
      g2 _ (by decide) (by decide), g1 _ (by decide) (by decide), gC]
  · rw [g3 _ (by decide) (by decide), Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl]; rfl
  · rw [g3 _ (by decide) (by decide), Env.get_cons, if_pos rfl]; rfl

theorem cv_eq_of {cv cv' : IConstantVal} (h1 : cv.name = cv'.name) (h2 : cv.levelParams = cv'.levelParams)
    (h3 : cv.type = cv'.type) : cv = cv' := by
  cases cv; cases cv'; simp_all

theorem nil_of_len {xs : List NIdx} (h : xs.length = 0) : xs = [] := List.eq_nil_of_length_eq_zero h

theorem idxW_ne_get {H : List (BitVec 64)} {o : Nat} {xs : List NIdx} (h : EBlk H o (xs.map Enc.idxW))
    (hl : xs.length = 1) : H[o + 1]? = some (Enc.idxW xs[0]) := by
  have := h.2 0 (by simp; omega)
  simpa using this

theorem single_eq {xs ys : List NIdx} (hx : xs.length = 1) (hy : ys.length = 1) (h : xs[0] = ys[0]) : xs = ys := by
  match xs, ys, hx, hy with
  | [a], [b], _, _ => simp at h; rw [h]

/-- **Record `0`** (the pin's inductive, no level parameters): the block's agrees (else hang). -/
theorem specR_rec0 {α : Type} {Cx : Ctx} (hok : CtxOK Cx) {s : AState} {Γ : Env} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (b0 b1 b2 p0 p1 p2 : IConstantInfo) (ob oq : Nat) (hblk : IndBlk Cx Cx.H ob [b0, b1, b2])
    (hpb : PinBlk Cx Cx.H oq [p0, p1, p2]) (hlb : b0.toConstantVal.levelParams.length < 2 ^ 61)
    (cv : IConstantVal) (caps : IIndCaps) (hp0 : p0 = .indInfo cv caps) (hl0 : cv.levelParams.length = 0)
    (hO : Γ.get akO = some (cellA Cx ob)) (hQ : Γ.get akQ = some (cellA Cx oq)) (hD : ∀ x ∈ akW, x ∈ D)
    (hk : ∀ Γ' : Env, (∀ z, z ∉ akW → Γ'.get z = Γ.get z) → CanonAgree b0 p0 →
      SpecR (Inv Cx s Γ' [] D) rest s m R) :
    SpecR (Inv Cx s Γ [] D) (recHead 0 (cw akB akC 3 rest)) s m R := by
  subst hp0
  refine specR_recHead hok _ _ ob oq hblk hpb 0 (by simp) (by simp) hlb (by simp [IConstantInfo.toConstantVal]; omega)
    hO hQ hD (fun Γ1 ob' op' ol ol' g1 hB hC _ _ hci hpi _ _ htag hname hlen => ?_)
  have hU : akU ∈ D ∧ akV ∈ D := ⟨hD _ (by decide), hD _ (by decide)⟩
  have hct := hci.1.2.2
  have hpt := hpi.1.2.2
  refine specR_cw akB akC ob' op' 3 _ _ hB hC (by decide) hU (by simpa [show ob' + 1 + 2 = ob' + 3 by omega] using hct)
    (by simpa [show op' + 1 + 2 = op' + 3 by omega] using hpt) (fun Γ2 g2 ety => ?_)
  refine hk Γ2 (fun z hz => by
    rw [g2 z (fun e => hz (by simp [e, akW])) (fun e => hz (by simp [e, akW])), g1 z hz]) ?_
  change CIE _ _ ob' b0 at hci
  change ciTag b0 = 3 at htag
  cases b0 with
  | indInfo cvb capsb =>
    change cvb.name = cv.name at hname
    change cvb.levelParams.length = cv.levelParams.length at hlen
    exact cv_eq_of hname (by rw [nil_of_len (by omega : cvb.levelParams.length = 0), nil_of_len hl0])
      (Enc.idxW_inj ety)
  | _ => simp [ciTag] at htag

/-- **Record `1`** (the pin's constructor, no level parameters). -/
theorem specR_rec1 {α : Type} {Cx : Ctx} (hok : CtxOK Cx) {s : AState} {Γ : Env} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (b0 b1 b2 p0 p1 p2 : IConstantInfo) (ob oq : Nat) (hblk : IndBlk Cx Cx.H ob [b0, b1, b2])
    (hpb : PinBlk Cx Cx.H oq [p0, p1, p2]) (hlb : b1.toConstantVal.levelParams.length < 2 ^ 61)
    (cv : IConstantVal) (a b : Nat) (T : NIdx) (hp1 : p1 = .ctorInfo cv a b T) (hl1 : cv.levelParams.length = 0)
    (hO : Γ.get akO = some (cellA Cx ob)) (hQ : Γ.get akQ = some (cellA Cx oq)) (hD : ∀ x ∈ akW, x ∈ D)
    (hk : ∀ Γ' : Env, (∀ z, z ∉ akW → Γ'.get z = Γ.get z) → CanonAgree b1 p1 →
      SpecR (Inv Cx s Γ' [] D) rest s m R) :
    SpecR (Inv Cx s Γ [] D) (recHead 1 (cw akB akC 3 (cw akB akC 4 (cw akB akC 5 (cw akB akC 6 rest))))) s m R := by
  subst hp1
  refine specR_recHead hok _ _ ob oq hblk hpb 1 (by simp) (by simp) hlb (by simp [IConstantInfo.toConstantVal]; omega)
    hO hQ hD (fun Γ1 ob' op' ol ol' g1 hB hC _ _ hci hpi _ _ htag hname hlen => ?_)
  have hU : akU ∈ D ∧ akV ∈ D := ⟨hD _ (by decide), hD _ (by decide)⟩
  change CIE _ _ ob' b1 at hci
  change ciTag b1 = 4 at htag
  cases b1 with
  | ctorInfo cvb ab bb Tb =>
    change cvb.name = cv.name at hname
    change cvb.levelParams.length = cv.levelParams.length at hlen
    obtain ⟨hcv, -, hc4, hc5, hc6⟩ := hci
    obtain ⟨hpv, -, hp4, hp5, hp6⟩ := hpi
    have gU : ∀ (Γa : Env), (∀ z, z ≠ akU → z ≠ akV → Γa.get z = Γ1.get z) →
        Γa.get akB = some (cellA Cx ob') ∧ Γa.get akC = some (cellA Cx op') := fun Γa g =>
      ⟨by rw [g _ (by decide) (by decide)]; exact hB, by rw [g _ (by decide) (by decide)]; exact hC⟩
    refine specR_cw akB akC ob' op' 3 _ _ hB hC (by decide) hU
      (by simpa [show ob' + 1 + 2 = ob' + 3 by omega] using hcv.2.2)
      (by simpa [show op' + 1 + 2 = op' + 3 by omega] using hpv.2.2) (fun Γ2 g2 ety => ?_)
    refine specR_cw akB akC ob' op' 4 _ _ (gU Γ2 g2).1 (gU Γ2 g2).2 (by decide) hU hc4.1 hp4.1 (fun Γ3 g3 e4 => ?_)
    have g3' : ∀ z, z ≠ akU → z ≠ akV → Γ3.get z = Γ1.get z := fun z h1 h2 => (g3 z h1 h2).trans (g2 z h1 h2)
    refine specR_cw akB akC ob' op' 5 _ _ (gU Γ3 g3').1 (gU Γ3 g3').2 (by decide) hU hc5.1 hp5.1
      (fun Γ4 g4 e5 => ?_)
    have g4' : ∀ z, z ≠ akU → z ≠ akV → Γ4.get z = Γ1.get z := fun z h1 h2 => (g4 z h1 h2).trans (g3' z h1 h2)
    refine specR_cw akB akC ob' op' 6 _ _ (gU Γ4 g4').1 (gU Γ4 g4').2 (by decide) hU hc6 hp6
      (fun Γ5 g5 e6 => ?_)
    refine hk Γ5 (fun z hz => by
      rw [g5 z (fun e => hz (by simp [e, akW])) (fun e => hz (by simp [e, akW])),
        g4' z (fun e => hz (by simp [e, akW])) (fun e => hz (by simp [e, akW])), g1 z hz]) ?_
    exact ⟨cv_eq_of hname (by rw [nil_of_len (by omega : cvb.levelParams.length = 0), nil_of_len hl1])
      (Enc.idxW_inj ety), natW_inj hc4.2 hp4.2 e4, natW_inj hc5.2 hp5.2 e5, Enc.idxW_inj e6⟩
  | _ => simp [ciTag] at htag

theorem fire_plain_of_tag {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {f : IRecRuleFire} (h : FireE EB H o f)
    (h0 : H[o]? = some 0) : f = .plain := by
  cases f with
  | plain => rfl
  | nested l p => rw [h.1] at h0; cases h0
  | levels l => rw [h.1] at h0; cases h0

theorem rule_eq_of {r r' : IRecRule} (h1 : r.ctor = r'.ctor) (h2 : r.nfields = r'.nfields) (h3 : r.fire = r'.fire)
    (h4 : r.rhs = r'.rhs) : r = r' := by
  cases r; cases r'; simp_all

/-- **Record `2`** (the pin's recursor, one level parameter, one plain rule). -/
theorem specR_rec2 {α : Type} {Cx : Ctx} (hok : CtxOK Cx) {s : AState} {Γ : Env} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (b0 b1 b2 p0 p1 p2 : IConstantInfo) (ob oq : Nat) (hblk : IndBlk Cx Cx.H ob [b0, b1, b2])
    (hpb : PinBlk Cx Cx.H oq [p0, p1, p2]) (hlb : b2.toConstantVal.levelParams.length < 2 ^ 61)
    (cv : IConstantVal) (mi rp : Nat) (k : Bool) (r : IRecRule) (hp2 : p2 = .recInfo cv mi rp k [r])
    (hfr : r.fire = .plain) (hl2 : cv.levelParams.length = 1)
    (hO : Γ.get akO = some (cellA Cx ob)) (hQ : Γ.get akQ = some (cellA Cx oq)) (hD : ∀ x ∈ akW, x ∈ D)
    (hk : ∀ Γ' : Env, (∀ z, z ∉ akW → Γ'.get z = Γ.get z) → CanonAgree b2 p2 →
      SpecR (Inv Cx s Γ' [] D) rest s m R) :
    SpecR (Inv Cx s Γ [] D) (recHead 2 (cw akL akM 1 (cw akB akC 3 (cw akB akC 4 (cw akB akC 5 (cw akB akC 6
      (rulesCmp rest))))))) s m R := by
  subst hp2
  refine specR_recHead hok _ _ ob oq hblk hpb 2 (by simp) (by simp) hlb (by simp [IConstantInfo.toConstantVal]; omega)
    hO hQ hD (fun Γ1 ob' op' ol ol' g1 hB hC hL hM hci hpi hel hel' htag hname hlen => ?_)
  have hU : akU ∈ D ∧ akV ∈ D := ⟨hD _ (by decide), hD _ (by decide)⟩
  change CIE _ _ ob' b2 at hci
  change ciTag b2 = 5 at htag
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  cases b2 with
  | recInfo cvb mib rpb kb rsb =>
    change cvb.name = cv.name at hname
    change cvb.levelParams.length = cv.levelParams.length at hlen
    change EBlk _ ol (cvb.levelParams.map Enc.idxW) at hel
    change EBlk _ ol' (cv.levelParams.map Enc.idxW) at hel'
    obtain ⟨hcv, -, hc4, hc5, hc6, ⟨wcr, hwcr, ocr, rfl, hcrl, hcrs⟩⟩ := hci
    obtain ⟨hpv, -, hp4, hp5, hp6, ⟨wpr, hwpr, opr, rfl, hprl, hprs⟩⟩ := hpi
    have gU : ∀ (Γa : Env), (∀ z, z ≠ akU → z ≠ akV → Γa.get z = Γ1.get z) →
        Γa.get akB = some (cellA Cx ob') ∧ Γa.get akC = some (cellA Cx op') :=
      fun Γa g => ⟨by rw [g _ (by decide) (by decide)]; exact hB, by rw [g _ (by decide) (by decide)]; exact hC⟩
    refine specR_cw akL akM ol ol' 1 _ _ hL hM (by decide) hU (idxW_ne_get hel (by omega)) (idxW_ne_get hel' hl2)
      (fun Γ2 g2 elp => ?_)
    refine specR_cw akB akC ob' op' 3 _ _ (gU Γ2 g2).1 (gU Γ2 g2).2 (by decide) hU
      (by simpa [show ob' + 1 + 2 = ob' + 3 by omega] using hcv.2.2)
      (by simpa [show op' + 1 + 2 = op' + 3 by omega] using hpv.2.2) (fun Γ3 g3 ety => ?_)
    have g3' : ∀ z, z ≠ akU → z ≠ akV → Γ3.get z = Γ1.get z := fun z h1 h2 => (g3 z h1 h2).trans (g2 z h1 h2)
    refine specR_cw akB akC ob' op' 4 _ _ (gU Γ3 g3').1 (gU Γ3 g3').2 (by decide) hU hc4.1 hp4.1 (fun Γ4 g4 e4 => ?_)
    have g4' : ∀ z, z ≠ akU → z ≠ akV → Γ4.get z = Γ1.get z := fun z h1 h2 => (g4 z h1 h2).trans (g3' z h1 h2)
    refine specR_cw akB akC ob' op' 5 _ _ (gU Γ4 g4').1 (gU Γ4 g4').2 (by decide) hU hc5.1 hp5.1 (fun Γ5 g5 e5 => ?_)
    have g5' : ∀ z, z ≠ akU → z ≠ akV → Γ5.get z = Γ1.get z := fun z h1 h2 => (g5 z h1 h2).trans (g4' z h1 h2)
    refine specR_cw akB akC ob' op' 6 _ _ (gU Γ5 g5').1 (gU Γ5 g5').2 (by decide) hU hc6 hp6 (fun Γ6 g6 e6 => ?_)
    have g6' : ∀ z, z ≠ akU → z ≠ akV → Γ6.get z = Γ1.get z := fun z h1 h2 => (g6 z h1 h2).trans (g5' z h1 h2)
    -- the rule blocks
    unfold rulesCmp
    refine UD.specR_heapLoadI' (C := Cx) akL _ (ob' + 7) _ hwcr (hD _ (by decide))
      (by simp only [sev, sev_vv]; rw [(gU Γ6 g6').1, ← cellA_add_ofNat]; rfl) ?_
    refine UD.specR_heapLoadI' (C := Cx) akM _ (op' + 7) _ hwpr (hD _ (by decide))
      (by simp only [sev, sev_vv]; rw [Env.get_cons, if_neg (by decide), (gU Γ6 g6').2, ← cellA_add_ofNat]; rfl) ?_
    have hcrlen : rsb.length < 2 ^ 61 := by
      rcases Nat.eq_zero_or_pos rsb.length with h0 | hpos
      · omega
      · obtain ⟨q, hq, -⟩ := hcrs (rsb.length - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp hq).1
        have : (ctxH Cx Cx.H).H.length ≤ Cx.HN := hHN
        simp only [ctxH] at this; omega
    refine specR_cw akL akM ocr opr 0 _ _ (by rw [Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl]; rfl)
      (by rw [Env.get_cons, if_pos rfl]; rfl) (by decide) hU (by simpa using hcrl) (by simpa using hprl)
      (fun Γ7 g7 ecnt => ?_)
    have hcnt : rsb.length = 1 := natW_inj (by omega) (by simp) (by simpa using ecnt)
    obtain ⟨qc, hqc, hrc⟩ := hcrs 0 (by omega)
    obtain ⟨qp, hqp, hrp⟩ := hprs 0 (by simp)
    refine UD.specR_heapLoadI' (C := Cx) akL _ (ocr + 1 + 0) _ hqc (hD _ (by decide))
      (by simp only [sev, sev_vv]; rw [g7 _ (by decide) (by decide), Env.get_cons, if_neg (by decide),
        Env.get_cons, if_pos rfl]; rw [show ocr + 1 + 0 = ocr + 1 by omega]; exact congrArg some (cellA_add8 Cx ocr)) ?_
    refine UD.specR_heapLoadI' (C := Cx) akM _ (opr + 1 + 0) _ hqp (hD _ (by decide))
      (by simp only [sev, sev_vv]; rw [Env.get_cons, if_neg (by decide), g7 _ (by decide) (by decide),
        Env.get_cons, if_pos rfl]; rw [show opr + 1 + 0 = opr + 1 by omega]; exact congrArg some (cellA_add8 Cx opr)) ?_
    have gL : Env.get ((akM, Cx.HB + BitVec.ofNat 64 (8 * qp)) :: (akL, Cx.HB + BitVec.ofNat 64 (8 * qc)) :: Γ7) akL =
        some (cellA Cx qc) := by rw [Env.get_cons, if_neg (by decide), Env.get_cons, if_pos rfl]; rfl
    have gM : Env.get ((akM, Cx.HB + BitVec.ofNat 64 (8 * qp)) :: (akL, Cx.HB + BitVec.ofNat 64 (8 * qc)) :: Γ7) akM =
        some (cellA Cx qp) := by rw [Env.get_cons, if_pos rfl]; rfl
    obtain ⟨hr0, hr1, hr2, hr5⟩ := hrc
    obtain ⟨hs0, hs1, hs2, hs5⟩ := hrp
    refine specR_cw akL akM qc qp 0 _ _ gL gM (by decide) hU (by simpa using hr0) (by simpa using hs0)
      (fun Γ8 g8 ec => ?_)
    refine specR_cw akL akM qc qp 1 _ _ (by rw [g8 _ (by decide) (by decide)]; exact gL)
      (by rw [g8 _ (by decide) (by decide)]; exact gM) (by decide) hU hr1.1 hs1.1 (fun Γ9 g9 enf => ?_)
    have g9' : ∀ z, z ≠ akU → z ≠ akV → Γ9.get z = Env.get ((akM, Cx.HB + BitVec.ofNat 64 (8 * qp)) ::
        (akL, Cx.HB + BitVec.ofNat 64 (8 * qc)) :: Γ7) z := fun z h1 h2 => (g9 z h1 h2).trans (g8 z h1 h2)
    have hpl0 : Cx.H[qp + 2]? = some 0 := by
      have := hs2; simp only [List.getElem_cons_zero] at this; rw [hfr] at this; exact this
    obtain ⟨wf, hwf, hwf0⟩ := fire_tag hr2
    refine specR_cw akL akM qc qp 2 _ _ (by rw [g9' _ (by decide) (by decide)]; exact gL)
      (by rw [g9' _ (by decide) (by decide)]; exact gM) (by decide) hU hwf hpl0
      (fun Γ10 g10 ef => ?_)
    have g10' : ∀ z, z ≠ akU → z ≠ akV → Γ10.get z = Env.get ((akM, Cx.HB + BitVec.ofNat 64 (8 * qp)) ::
        (akL, Cx.HB + BitVec.ofNat 64 (8 * qc)) :: Γ7) z := fun z h1 h2 => (g10 z h1 h2).trans (g9' z h1 h2)
    refine specR_cw akL akM qc qp 5 _ _ (by rw [g10' _ (by decide) (by decide)]; exact gL)
      (by rw [g10' _ (by decide) (by decide)]; exact gM) (by decide) hU hr5 hs5 (fun Γ11 g11 erh => ?_)
    refine hk Γ11 (fun z hz => ?_) ?_
    · have h1 : z ≠ akU := fun e => hz (by simp [e, akW])
      have h2 : z ≠ akV := fun e => hz (by simp [e, akW])
      have h3 : z ≠ akL := fun e => hz (by simp [e, akW])
      have h4 : z ≠ akM := fun e => hz (by simp [e, akW])
      rw [g11 z h1 h2, g10' z h1 h2, Env.get_cons, if_neg h4, Env.get_cons, if_neg h3, g7 z h1 h2, Env.get_cons,
        if_neg h4, Env.get_cons, if_neg h3, g6' z h1 h2, g1 z hz]
    · have e0 := hwf0 ef
      refine ⟨cv_eq_of hname (single_eq (by omega) hl2 (Enc.idxW_inj elp)) (Enc.idxW_inj ety),
        natW_inj hc4.2 hp4.2 e4, natW_inj hc5.2 hp5.2 e5, boolW_inj e6, ?_⟩
      obtain ⟨rb, rfl⟩ : ∃ rb, rsb = [rb] := by
        match rsb, hcnt with
        | [rb], _ => exact ⟨rb, rfl⟩
      exact congrArg (· :: []) (rule_eq_of (Enc.idxW_inj ec) (natW_inj hr1.2 hs1.2 enf)
        (by rw [hfr]; exact e0) (Enc.idxW_inj erh))
  | _ => simp [ciTag] at htag

/-- **The numbered name**: `.num .anonymous 0` interned (the anonymous name's handle a constant), then `1`. -/
theorem numTail_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hcN : C.code.lookup Front.fInternNNum =
      some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lNw, .one)], Front.nameNumBody, .one))
    (s : AState) (Γ : Env) (D : List MlS) (hK : akK ∈ D) (hH : akH ∈ D) (H0 H : List (BitVec 64)) (hp : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ [] D) (numTail C) s (internNNode (.num anonH 0) >>= fun _ => pure true)
      (PostPin (ctxH C H0) (fun b => b = true)) := by
  unfold numTail
  have hokH := ctxOK_H hok H
  have hlay := hokH.heapLay
  refine specR_allocWrI (C := ctxH C H) hokH akK hK [.const (Enc.idxW anonH)] [Enc.idxW anonH] rfl (by simp)
    (fun v i hi => by
      simp only [List.length_cons, List.length_nil] at hi
      obtain rfl : i = 0 := by omega
      rfl)
    (fun H' r hp' hle hcap hget => ?_)
  have hkl : (Enc.encNum ⟨anonH, 0⟩).length = 1 := by simp [Enc.encNum, Front.limbs_zero]
  have hkey : ∀ j (hj : j < (Enc.encNum ⟨anonH, 0⟩).length),
      (ctxH C H').H[r + j]? = some ((Enc.encNum ⟨anonH, 0⟩)[j]) := by
    intro j hj
    rw [hkl] at hj
    obtain rfl : j = 0 := by omega
    have := hget 0 (by simp)
    change H'[r + 0]? = some ((Enc.encNum ⟨anonH, 0⟩)[0])
    simpa [Enc.encNum] using this
  refine specR_callNIA (C := ctxH C H') akH Front.fInternNNum [Front.pKeyN, lEn, lEp, lNw]
    [vv akK, .const 1, .const (Enc.idxW anonH), .const 0] Front.nameNumBody
    [cellA C r, BitVec.ofNat 64 (Enc.encNum ⟨anonH, 0⟩).length, Enc.idxW anonH, (UInt64.ofNat 0).toBitVec]
    (by decide) rfl hH hcN
    ⟨by simp [sev, vv, Env.get_cons]; rfl, by rw [hkl]; rfl, rfl, rfl, trivial⟩
    (fun a w s' st => internNNode (.num anonH 0) s = .ok (a, s') ∧ Front.PostNm (ctxH (ctxH C H') H) a w s' st)
    (fun a w s' H'' => H'' = H ∧ internNNode (.num anonH 0) s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact Front.nameNum_body_spec (σ := σ) ra (ctxH C H') (ctxOK_H hok _) (Front.frontOK_H hf _) s anonH 0 r H
        hp' hle (by rw [hkl]; show r + 1 ≤ H'.length; simpa using hcap) (by rw [hkl]; decide) hkey _
        (pre_of_lookups hu [Front.pKeyN, lEn, lEp, lNw] _ rfl hlk)))
    (fun h w s2 H2 ⟨e, hr2, hw⟩ => ?_)
  subst e
  exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H2, hp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-! ## The twin's `And` pin at the block -/

theorem blockAndNamed_and {C : Ctx} {blk : List IConstantInfo} (h : AndNames C blk) :
    blockAndNamed [C.pins.names[11]!, C.pins.names[48]!, C.pins.names[49]!] blk = true := by
  match blk, h with
  | c :: cs, h =>
    simp only [AndNames, List.map_cons, List.cons.injEq] at h
    simp [blockAndNamed, h.1]

/-- **`andPinOk` at a block named `[And, And.intro, And.rec]` with two parameters**: the pin interned, then
`canonEqList`. -/
theorem andPinOk_and {C : Ctx} (hok : CtxOK C) {s : AState} (hps : s.pins = C.pins) (blk : List IConstantInfo)
    (hn : AndNames C blk) :
    andPinOk (.indDecl blk 2) s = (andPinDecls >>= fun pinned => canonEqList blk pinned) s := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hps i hi
  unfold andPinOk andPinNameHs
  simp only [pinAnd, pinAndIntro, pinAndRec, PIN_AND, PIN_AND_INTRO, PIN_AND_REC, bind_assoc]
  rw [bind_ok_l (h _ (show 11 < pinCount by decide)), bind_ok_l (h _ (show 48 < pinCount by decide)),
    bind_ok_l (h _ (show 49 < pinCount by decide))]
  simp only [pure_bind, blockAndNamed_and hn, beq_self_eq_true, ite_true]

theorem canonNames_one_run {s s3 : AState} {h : NIdx} (ha : internNNode .anonymous s = .ok (anonH, s))
    (hn : internNNode (.num anonH 0) s = .ok (h, s3)) : canonNames 1 s = .ok ([h], s3) := by
  rw [canonNames_one_eq]
  simp only [internName, bind_assoc]
  rw [bind_ok_l ha, bind_ok_l hn]; rfl

set_option maxRecDepth 100000 in
theorem and_pinLits : ∀ c ∈ ConLeche.andPin, pinLitB c = true := by decide

/-- The `And` pin's code. -/
structure AKCodes (C : Ctx) : Prop where
  e : ECodes C
  cN : C.code.lookup Front.fInternNNum =
    some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lNw, .one)], Front.nameNumBody, .one)
  anm : C.code.lookup fAnm = some (anmParams.map (fun p => (p, ShapeHOL.one)), anmBody C, .one)
  self : C.code.lookup fApk = some (apkParams.map (fun p => (p, ShapeHOL.one)), apkBody C, .one)

theorem akQ_notQ : NotQ akQ :=
  notQ_of (by decide) ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem akO_notQ : NotQ akO :=
  notQ_of (by decide) ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem apk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ apkLocals → (ctxEnv C ++ apkParams.zip vals).get x = none :=
  Knot.params_none C apkLocals apkParams vals (by decide) (by decide)

theorem specR_guardNeK {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (a : BitVec 64) (n : Nat)
    (ha : Γ.get x = some a) (hk : a = BitVec.ofNat 64 n → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .notEqual (vv x) (.const (BitVec.ofNat 64 n))) hang rest) s m R := by
  by_cases e : a = BitVec.ofNat 64 n
  · subst e
    exact specR_ifI _ 0 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => hk rfl)
  · exact specR_ifI _ 1 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))

set_option maxHeartbeats 16000000 in
/-- **The `And` pin's test**: at `a`, the block named `[And, And.intro, And.rec]`, the twin's `andPinOk` (hang
unless it holds); off it, the test as the caller has it. -/
theorem apk_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : AKCodes C)
    (hf : Front.FrontOK C) (hA0 : denoteN C.St.ns default = some .anonymous)
    (hAn : denoteN C.St.ns anonH = some .anonymous)
    (blk : List IConstantInfo) (nP ob : Nat) (a : Bool) (H : List (BitVec 64)) (s : AState) (hpH : C.H <+: H)
    (hblk : IndBlk C H ob blk) (hlb : ∀ c ∈ blk, c.toConstantVal.levelParams.length < 2 ^ 59) (hnP : nP < 2 ^ 59)
    (hAt : a = true → AndNames C blk) (hAf : a = false → andPinOk (.indDecl blk nP) s = .ok (true, s)) :
    SpecR (σ := σ) (Pre (ctxH C H) s (apkParams.zip [cellA C ob, BitVec.ofNat 64 nP, boolW a])) (apkBody C) s
      (andPinOk (.indDecl blk nP)) (PostPin (ctxH C H) (fun b => b = true)) := by
  refine specR_prologue (postPin_locals _ _) (apk_none _ _) ?_
  have hD : ∀ x ∈ apkLocals, x ∈ ctxLocals ++ apkLocals := fun x hx => List.mem_append_right _ hx
  cases a with
  | false =>
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, apkParams, ctxEnv, boolW,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_okImp (m' := pure true) (fun x s' h => by obtain ⟨rfl, rfl⟩ := AM.pure_ok h; exact hAf rfl) ?_
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | true =>
    have hn := hAt rfl
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, apkParams, ctxEnv, boolW,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_guardNeK akNp (BitVec.ofNat 64 nP) 2 (by simp +decide [Env.get, apkParams, ctxEnv]) (fun e => ?_)
    obtain rfl : nP = 2 := natW_inj (by omega) (by decide) e
    refine specR_atEntry fun t0 ht0 => ?_
    have hps : s.pins = C.pins := ht0.sr.pins
    have hst : StateOK s := sr_stateOK ht0.sr
    refine specR_offCheckI ⟨hD _ (by simp [apkLocals]), hD _ (by simp [apkLocals]), hD _ (by simp [apkLocals]),
      hD _ (by simp [apkLocals])⟩ (fun hoff => ?_)
    refine specR_okImp (m' := ConPanqueque.Logic.PlainIntern.plainCIList ConLeche.andPin >>=
      fun r => canonEqList blk r) (fun x s' h => by
        rw [andPinOk_and hok hps blk hn]
        obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok h
        rw [bind_ok_l (andPinDecls_plain hoff h1)]; exact h2) ?_
    have G : GenEnv C (ctxLocals ++ apkLocals) 12 :=
      ⟨hok, hf, hA0, hc.e, hD _ (by simp [apkLocals]), hD _ (by simp [apkLocals]),
        fun c hc' j hj => hD _ (by
          have := gv_mem_genLocals hc' hj
          simp only [apkLocals, List.mem_append]; exact Or.inr this)⟩
    have hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ ctxLocals ++ apkLocals := fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [apkLocals])
    have hpb : ∀ l ∈ pbLocs, l ∈ ctxLocals ++ apkLocals := fun l hl => hD l (by simp [apkLocals, hl])
    have hO0 : Env.get (((ocD, 0) :: (ocC, 0) :: (ocB, 0) :: (ocA, 0) ::
        (ctxEnv C ++ apkParams.zip [cellA C ob, BitVec.ofNat 64 2, boolW true])) : Env) akO = some (cellA C ob) := by
      simp +decide [Env.get_cons, Env.get, apkParams, ctxEnv]
    refine genPinBlk_spec ra G hq hpb akQ (hD _ (by simp [apkLocals])) akQ_notQ (by decide) _ and_pinLits (by decide)
      H _ _ [] s (fun r s' Γ' H' o hp ag hr hres hpinb => ?_)
    -- the pin's interning
    have hdec := andPinDecls_plain hoff hr
    simp only [andPinDecls, ConRon.Arena.internCIList] at hdec
    obtain ⟨pr, s₃, hgo, hrest⟩ := AM.bind_ok hdec
    obtain ⟨m1, cis⟩ := pr
    obtain ⟨hv, hs3⟩ := AM.pure_ok hrest
    subst hv; subst hs3
    obtain ⟨hstep, hdp, -⟩ := Frontend.internCIList_sstep ConLeche.andPin hst (Frontend.EMemoOK.empty _) hgo
    obtain ⟨p0, p1, p2, hr3, l0, l1, l2, sh0, sh1, sh2, hk0, hk1, hk2⟩ := andPin_facts hdp
    subst hr3
    obtain ⟨cv0, caps0, e0⟩ := hk0
    obtain ⟨cv1, a1, b1, T1, e1⟩ := hk1
    obtain ⟨cv2, mi2, rp2, k2, r2, e2, hfr⟩ := hk2
    obtain ⟨b0, b1', b2, rfl⟩ : ∃ b0 b1 b2, blk = [b0, b1, b2] := by
      have := andNames_len hn
      match blk, this with
      | [b0, b1, b2], _ => exact ⟨b0, b1, b2, rfl⟩
    have hokH := ctxOK_H hok H'
    have hblkH : IndBlk (ctxH C H') (ctxH C H').H ob [b0, b1', b2] := indBlk_mono hblk hp
    have hO : Γ'.get akO = some (cellA C ob) := by rw [ag akO akO_notQ (by decide)]; exact hO0
    have hW : ∀ x ∈ akW, x ∈ ctxLocals ++ apkLocals := fun x hx => hD x (by
      simp only [akW, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [apkLocals])
    have ha0 : ∀ (Γa : Env), (∀ z, z ∉ akW → Γa.get z = Γ'.get z) →
        Γa.get akO = some (cellA (ctxH C H') ob) ∧ Γa.get akQ = some (cellA (ctxH C H') o) := fun Γa g =>
      ⟨by rw [g _ (by decide)]; exact hO, by rw [g _ (by decide)]; exact hres⟩
    have hl0 : cv0.levelParams.length = 0 := by subst e0; exact l0
    have hl1 : cv1.levelParams.length = 0 := by subst e1; exact l1
    have hl2 : cv2.levelParams.length = 1 := by subst e2; exact l2
    unfold andCmp
    refine specR_rec0 hokH b0 b1' b2 p0 p1 p2 ob o hblkH hpinb (by have := hlb b0 (by simp); omega) cv0 caps0 e0 hl0
      (ha0 Γ' (fun _ _ => rfl)).1 (ha0 Γ' (fun _ _ => rfl)).2 hW (fun Γ1 g1 ag0 => ?_)
    refine specR_rec1 hokH b0 b1' b2 p0 p1 p2 ob o hblkH hpinb (by have := hlb b1' (by simp); omega) cv1 a1 b1 T1 e1
      hl1 (ha0 Γ1 g1).1 (ha0 Γ1 g1).2 hW (fun Γ2 g2 ag1 => ?_)
    have g2' : ∀ z, z ∉ akW → Γ2.get z = Γ'.get z := fun z h => (g2 z h).trans (g1 z h)
    refine specR_rec2 hokH b0 b1' b2 p0 p1 p2 ob o hblkH hpinb (by have := hlb b2 (by simp); omega) cv2 mi2 rp2 k2 r2
      e2 hfr hl2 (ha0 Γ2 g2').1 (ha0 Γ2 g2').2 hW (fun Γ3 g3 ag2 => ?_)
    -- the comparison's verdict
    refine specR_atEntry fun t3 ht3 => ?_
    have hanon : internNNode .anonymous s' = .ok (anonH, s') := internAnon_run (C := ctxH C H') ht3.sr hAn
    refine specR_okImp (m' := internNNode (.num anonH 0) >>= fun _ => pure true) (fun x s3 h => by
      obtain ⟨hh, s4, h1, h2⟩ := AM.bind_ok h
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact canonEqList_and hstep.ok ag0 ag1 ag2 l0 l1 l2 sh0 sh1 sh2 (canonNames_one_run hanon h1)) ?_
    exact numTail_spec ra C hok hf hc.cN s' Γ3 _ (hD _ (by simp [apkLocals])) (hD _ (by simp [apkLocals])) H H' hp

end

/-! ## For the record's arm -/

theorem block_all_res {C : Ctx} : ∀ (block : List IConstantInfo), (∀ c ∈ block, C.pins.reserved.contains c.name = false) →
    (block.all fun c => !C.pins.reserved.contains c.name) = true
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by rw [h c (by simp)]; rfl, block_all_res cs (fun x hx => h x (by simp [hx]))⟩

/-- **`basisNamesOk` at a block of unreserved names, none of the pinned ones**: `true`, the state kept. -/
theorem basisNamesOk_res {σ : Type} {C : Ctx} (hok : CtxOK C) (hb : BasisInv C) {s : AState} {t : PState σ}
    (hsr : SR C s t) (hoff : InternRerun.Off s.store) (block : List IConstantInfo) (nP : Nat)
    (hres : ∀ c ∈ block, C.pins.reserved.contains c.name = false) (hnh : NoHit C block) :
    basisNamesOk (.indDecl block nP) s = .ok (true, s) := by
  obtain ⟨r1, h1, n1⟩ := basis_at hb hsr hoff .eqK (by decide)
  obtain ⟨r2, h2, n2⟩ := basis_at hb hsr hoff .natK (by decide)
  obtain ⟨r3, h3, n3⟩ := basis_at hb hsr hoff .emptyK (by decide)
  obtain ⟨r4, h4, n4⟩ := basis_at hb hsr hoff .falseK (by decide)
  have e1 : (blockNames r1 == blockNames block) = false := by
    simp only [blockNames, n1, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have e2 : (blockNames r2 == blockNames block) = false := by
    simp only [blockNames, n2, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have e3 : (blockNames r3 == blockNames block) = false := by
    simp only [blockNames, n3, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have e4 : (blockNames r4 == blockNames block) = false := by
    simp only [blockNames, n4, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have hr := reserved_run hok hsr.pins
  unfold basisNamesOk basisNameHit
  simp only [basisNameHitGo, bind, StateT.bind, Except.bind, h1, h2, h3, h4, e1, e2, e3, e4,
    Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure, hr, block_all_res block hres]

/-- The pinned `And` names are not reserved. -/
theorem andNames_res {C : Ctx} (hok : CtxOK C) {s : AState} (hp : PinsOK s) (hps : s.pins = C.pins)
    {block : List IConstantInfo} (hn : AndNames C block) : ∀ c ∈ block, C.pins.reserved.contains c.name = false := by
  intro c hc
  have hm : c.name ∈ [C.pins.names[11]!, C.pins.names[48]!, C.pins.names[49]!] := by
    rw [← hn]; exact List.mem_map_of_mem hc
  cases e : C.pins.reserved.contains c.name with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨f1, f2, f3⟩ := reserved_not_and hok hp hps c.name (List.contains_iff_mem.mp e)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h
    · exact f1 h
    · exact f2 h
    · exact f3 h

theorem ofNat_add_boolW (a : Nat) (b : Bool) :
    BitVec.ofNat 64 a + boolW b = BitVec.ofNat 64 (a + if b then 1 else 0) := by
  cases b <;> simp [boolW, BitVec.ofNat_add_ofNat] <;> rfl

end ConPanqueque.T.Ind
