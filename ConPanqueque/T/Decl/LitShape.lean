import ConPanqueque.T.Decl.CheckConst
import ConPanqueque.T.Str.StrCtor
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `litShapeOk`: a declaration at a literal's name has the literal's shape

The shapes intern their expected parts exactly as the twin does (so the stores stay in step) and compare
handles. `arr t X Y`: `t` is the arrow `X → Y` (a `forallE` node with those two children).
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The twin's arrow test, as `natSuccOk` and its kin write it inline. -/
def arrT (t X Y : EIdx) : AM Bool :=
  if t.tag == ETag.forallE then do
    match ← view t with
    | .forallE d b => pure (d == X && b == Y)
    | _ => pure false
  else pure false

def arT := ofString "ar_t"
def arX := ofString "ar_x"
def arY := ofString "ar_y"
def arD := ofString "ar_d"
def arB := ofString "ar_b"
def fArr := ofString "litArrow"
def arParams : List MlS := [arT, arX, arY]
def arLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, arD, arB]

def arrBody : ProgHOL 64 := prologue arLocals
  (.ite (tagIsE arT 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv arT)) (.seq eViewP
    (.seq (.assign .local arD (.load .one (vv lRp)))
    (.seq (.assign .local arB (.load .one (.op .add [vv lRp, .const 8])))
      (.return (.op .and [.cmp .equal (vv arD) (vv arX), .cmp .equal (vv arB) (vv arY)]))))))) 
    (.return (.const 0)))

def lsN := ofString "ls_n"
def lsT := ofString "ls_t"
def lsS := ofString "ls_s"
def lsA := ofString "ls_a"
def lsE := ofString "ls_e"
def lsC := ofString "ls_c"
def fLss := ofString "litShapeSort"
def fLsz := ofString "litShapeZero"
def lsParams : List MlS := [lsN, lsT]

/-- `lps = []` and the type is `Sort 1` (`Nat`, `String`, `Char`). -/
def lssBody (C : Ctx) : ProgHOL 64 := prologue [lsS]
  (.seq (.assign .local lsS (.load .one (.const (ecell C (C.PO + pinCount + 2)))))
  (.return (.op .and [.cmp .equal (vv lsN) (.const 0), .cmp .equal (vv lsT) (vv lsS)])))

/-- `lps = []` and the type is the constant `Nat` (`Nat.zero`). -/
def lszBody (C : Ctx) : ProgHOL 64 := prologue [lsA, lsE, lsC]
  (.seq (.assign .local lsA (.load .one (.const (ecell C (C.PO + PIN_NAT)))))
  (.seq (.assign .local lsE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, lsC), none)) fInternConst [vv lsA, vv lsE])
  (.return (.op .and [.cmp .equal (vv lsN) (.const 0), .cmp .equal (vv lsT) (vv lsC)])))))

def lsB := ofString "ls_b"
def lsR := ofString "ls_r"
def fLsu := ofString "litShapeSucc"
def fLco := ofString "litShapeCharOfNat"

/-- `lps = []` and the type is `Nat → Nat` (`Nat.succ`). -/
def lsuBody (C : Ctx) : ProgHOL 64 := prologue [lsA, lsE, lsC, lsR]
  (.ite (.cmp .notEqual (vv lsN) (.const 0)) (.return (.const 0))
  (.seq (.assign .local lsA (.load .one (.const (ecell C (C.PO + PIN_NAT)))))
  (.seq (.assign .local lsE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, lsC), none)) fInternConst [vv lsA, vv lsE])
  (.seq (.call (some (some (.local, lsR), none)) fArr [vv lsT, vv lsC, vv lsC])
  (.return (vv lsR)))))))

/-- `lps = []` and the type is `Nat → Char` (`Char.ofNat`). -/
def lscBody (C : Ctx) : ProgHOL 64 := prologue [lsA, lsE, lsC, lsB, lsR]
  (.ite (.cmp .notEqual (vv lsN) (.const 0)) (.return (.const 0))
  (.seq (.assign .local lsA (.load .one (.const (ecell C (C.PO + PIN_NAT)))))
  (.seq (.assign .local lsE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, lsC), none)) fInternConst [vv lsA, vv lsE])
  (.seq (.assign .local lsA (.load .one (.const (ecell C (C.PO + PIN_CHAR)))))
  (.seq (.assign .local lsE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, lsB), none)) fInternConst [vv lsA, vv lsE])
  (.seq (.call (some (some (.local, lsR), none)) fArr [vv lsT, vv lsC, vv lsB])
  (.return (vv lsR))))))))))

def lsK := ofString "ls_k"
def lsZ := ofString "ls_z"
def lsD := ofString "ls_d"
def fLsl := ofString "litShapeStrOfList"

/-- `lps = []` and the type is `List.{0} Char → String` (`String.ofList`). -/
def lslBody (C : Ctx) : ProgHOL 64 := prologue [lsA, lsE, lsK, lsZ, lsC, lsB, lsD, lsS, lsR]
  (.ite (.cmp .notEqual (vv lsN) (.const 0)) (.return (.const 0))
  (.seq (.assign .local lsZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (allocP C lsK (.const 8)
  (.seq (.store (vv lsK) (vv lsZ))
  (.seq (.call (some (some (.local, lsZ), none)) fInternLs [vv lsK, .const 1])
  (.seq (.assign .local lsA (.load .one (.const (ecell C (C.PO + PIN_LIST)))))
  (.seq (.call (some (some (.local, lsC), none)) fInternConst [vv lsA, vv lsZ])
  (.seq (.assign .local lsA (.load .one (.const (ecell C (C.PO + PIN_CHAR)))))
  (.seq (.assign .local lsE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, lsB), none)) fInternConst [vv lsA, vv lsE])
  (.seq (.call (some (some (.local, lsD), none)) fInternApp [vv lsC, vv lsB])
  (.seq (.assign .local lsA (.load .one (.const (ecell C (C.PO + PIN_STRING)))))
  (.seq (.assign .local lsE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, lsS), none)) fInternConst [vv lsA, vv lsE])
  (.seq (.call (some (some (.local, lsR), none)) fArr [vv lsT, vv lsD, vv lsS])
  (.return (vv lsR)))))))))))))))))

def lsP := ofString "ls_p"
def fLli := ofString "litShapeList"
def lpParams : List MlS := [lsN, lsP, lsT]

/-- `lps = [p]` and the type is `Sort (p+1) → Sort (p+1)` (`List`). -/
def lliBody : ProgHOL 64 := prologue [lsA, lsC, lsB, lsR]
  (.ite (.cmp .notEqual (vv lsN) (.const 1)) (.return (.const 0))
  (.seq (.assign .local lsA (.load .one (.op .add [vv lsP, .const 8])))
  (.seq (.call (some (some (.local, lsC), none)) fInternLParam [vv lsA])
  (.seq (.call (some (some (.local, lsC), none)) fInternLSucc [vv lsC])
  (.seq (.call (some (some (.local, lsB), none)) fInternSort [vv lsC])
  (.seq (.call (some (some (.local, lsR), none)) fArr [vv lsT, vv lsB, vv lsB])
  (.return (vv lsR))))))))

section
variable {σ : Type}

theorem eqIdx_w' {k : IdxKind} (a b : Idx k) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal (Enc.idxW a) (Enc.idxW b) = true then (1#64 : BitVec 64) else 0#64)
      = boolW (a == b) := by
  by_cases h : a = b
  · subst h; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]
  · have h' : Enc.idxW a ≠ Enc.idxW b := fun e => h (idxW_inj e)
    have h'' : (a == b) = false := beq_false_of_ne h
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h', h'', boolW]

theorem len0_w (n : Nat) (hn : n < 2 ^ 64) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal (BitVec.ofNat 64 n) 0#64 = true then (1#64 : BitVec 64) else 0#64)
      = boolW (decide (n = 0)) := by
  by_cases h : n = 0
  · subst h; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]
  · have h' : BitVec.ofNat 64 n ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h', h, boolW]

theorem isEmpty_len {α : Type} (l : List α) : l.isEmpty = decide (l.length = 0) := by
  cases l <;> simp

theorem ar_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ arLocals → (ctxEnv C ++ arParams.zip vals).get x = none :=
  Knot.params_none C arLocals arParams vals (by decide) (by decide)

/-- **`arr`**: the arrow test. -/
theorem arr_spec (C : Ctx) (s : AState) (t X Y : EIdx) :
    SpecR (σ := σ) (Pre C s (arParams.zip [Enc.idxW t, Enc.idxW X, Enc.idxW Y])) arrBody s (arrT t X Y) (PostB C) := by
  refine specR_prologue (postB_locals C) (ar_none C _) ?_
  unfold arrT
  refine Knot.specR_tagIteV arT t 6 (by decide) (by decide) (by simp +decide [Env.get, arParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
  · rw [if_pos (show (t.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv arT) (Enc.idxW t) (by decide) (by simp +decide [Env.get, arParams, ctxEnv]) ?_
    refine specR_viewP (C := C) t (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
    refine specR_congr (view_bind_eq t vw _ s hv) ?_
    have h6 : vw.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨d, b, rfl⟩ : ∃ d b, vw = .forallE d b := by cases vw <;> simp [ENodeView.tagN] at h6 ⊢
    refine specR_loadI' arD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW d) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW d) [Enc.idxW b] []) ?_
    refine specR_loadI' arB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW d) (Enc.idxW b) [] []) ?_
    exact specR_returnI _ (boolW (d == X && b == Y))
      (by simp +decide [sev, Env.get, arParams, ctxEnv]; rw [eqIdx_w', eqIdx_w']; exact and_w _ _)
      (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [if_neg (show ¬ (t.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
    exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`Sort 1` shape**. -/
theorem lss_spec (C : Ctx) (hok : CtxOK C) (s : AState) (lps : List NIdx) (hl : lps.length < 2 ^ 62) (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lsParams.zip [BitVec.ofNat 64 lps.length, Enc.idxW t])) (lssBody C) s
      (do let s1 ← sortOne; pure (lps.isEmpty && t == s1)) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [lsS] lsParams _ (by decide) (by decide)) ?_
  unfold sortOne
  refine specR_pinXI hok pinSortOne 2 C.pins.sortOne _ (fun s hp => pinSortOne_run hok hp) (pin_sortOne_cell hok)
    lsS (by decide) ?_
  exact specR_returnI _ (boolW (lps.isEmpty && t == C.pins.sortOne))
    (by simp +decide [sev, Env.get, lsParams, ctxEnv]; rw [len0_w _ (by omega), eqIdx_w', isEmpty_len]; exact and_w _ _)
    (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`Nat.zero` shape**. -/
theorem lsz_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (s : AState) (lps : List NIdx) (hl : lps.length < 2 ^ 62) (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lsParams.zip [BitVec.ofNat 64 lps.length, Enc.idxW t])) (lszBody C) s
      (do let nt ← pinNat; let nc ← constE nt; pure (lps.isEmpty && t == nc)) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [lsA, lsE, lsC] lsParams _ (by decide) (by decide)) ?_
  simp only [pinNat, constE, emptyLevels, bind_assoc]
  refine specR_pinAtI hok PIN_NAT (by decide) lsA (by decide) ?_
  refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
    (pin_emptyLevels_cell hok) lsE (by decide) ?_
  refine ILP.callE_spec lsC fInternConst [lEn, lEus] [vv lsA, vv lsE] constBody
    [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hic
    ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
    (by exact const_body_spec ra C hok s _ _) (fun nc s1 => ?_)
  exact specR_returnI _ (boolW (lps.isEmpty && t == nc))
    (by simp +decide [sev, Env.get, lsParams, ctxEnv]; rw [len0_w _ (by omega), eqIdx_w', isEmpty_len]; exact and_w _ _)
    (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


theorem specR_arrI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Bool → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hca : C.code.lookup fArr = some (arParams.map (fun p => (p, ShapeHOL.one)), arrBody, .one))
    (x : MlS) (e1 e2 e3 : ExpHOL 64) (t X Y : EIdx) (hx : x ∈ D)
    (h1 : sev Γ e1 = some (Enc.idxW t)) (h2 : sev Γ e2 = some (Enc.idxW X)) (h3 : sev Γ e3 = some (Enc.idxW Y))
    (hk : ∀ b H' s', C.H <+: H' → SpecR (Inv (ctxH C H') s' ((x, boolW b) :: Γ) [] D) rest s' (k b) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fArr [e1, e2, e3]) rest) s (arrT t X Y >>= k) R :=
  specR_callNIH x fArr arParams [e1, e2, e3] arrBody [Enc.idxW t, Enc.idxW X, Enc.idxW Y] (by decide) rfl hx hca
    ⟨h1, h2, h3, trivial⟩ (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu arParams _ rfl hlk) (arr_spec C s t X Y))
    (fun b w s' H' hp hw => by subst hw; exact hk b H' s' hp)

theorem notEmpty_w (lps : List NIdx) (hl : lps.length < 2 ^ 62) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.notEqual (BitVec.ofNat 64 lps.length) 0#64 = true then (1#64 : BitVec 64) else 0#64)
      = boolW (!lps.isEmpty) := by
  cases lps with
  | nil => simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]
  | cons a l =>
    have hl' : l.length + 1 < 2 ^ 62 := by simpa using hl
    have h' : BitVec.ofNat 64 (l.length + 1) ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h', boolW]

/-- **`Nat.succ` shape**. -/
theorem lsu_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (hca : C.code.lookup fArr = some (arParams.map (fun p => (p, ShapeHOL.one)), arrBody, .one))
    (s : AState) (lps : List NIdx) (hl : lps.length < 2 ^ 62) (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lsParams.zip [BitVec.ofNat 64 lps.length, Enc.idxW t])) (lsuBody C) s
      (if !lps.isEmpty then pure false else do let nt ← pinNat; let nc ← constE nt; arrT t nc nc) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [lsA, lsE, lsC, lsR] lsParams _ (by decide) (by decide)) ?_
  refine specR_ifI _ (boolW (!lps.isEmpty)) (by simp +decide [sev, Env.get, lsParams, ctxEnv]; exact notEmpty_w lps hl)
    (fun h => ?_) (fun h => ?_)
  · have he : (!lps.isEmpty) = true := by cases e : (!lps.isEmpty) <;> simp_all [boolW]
    rw [if_pos he]
    exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have he : (!lps.isEmpty) = false := by cases e : (!lps.isEmpty) <;> simp_all [boolW]
    rw [if_neg (by simp [he])]
    simp only [pinNat, constE, emptyLevels, bind_assoc]
    refine specR_pinAtI hok PIN_NAT (by decide) lsA (by decide) ?_
    refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
      (pin_emptyLevels_cell hok) lsE (by decide) ?_
    refine ILP.callE_spec lsC fInternConst [lEn, lEus] [vv lsA, vv lsE] constBody
      [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra C hok s _ _) (fun nc s1 => ?_)
    refine specR_congr (m' := arrT t nc nc >>= fun b => pure b) (by simp) ?_
    refine specR_arrI hca lsR (vv lsT) (vv lsC) (vv lsC) t nc nc (by decide) (by simp +decide [Env.get, lsParams, ctxEnv]) (by simp) (by simp)
      (fun b H' s' hp => ?_)
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`Char.ofNat` shape**. -/
theorem lsc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (hca : C.code.lookup fArr = some (arParams.map (fun p => (p, ShapeHOL.one)), arrBody, .one))
    (s : AState) (lps : List NIdx) (hl : lps.length < 2 ^ 62) (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lsParams.zip [BitVec.ofNat 64 lps.length, Enc.idxW t])) (lscBody C) s
      (if !lps.isEmpty then pure false else do
        let nt ← pinNat; let nc ← constE nt; let ch ← pinChar; let cc ← constE ch; arrT t nc cc) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [lsA, lsE, lsC, lsB, lsR] lsParams _ (by decide) (by decide)) ?_
  refine specR_ifI _ (boolW (!lps.isEmpty)) (by simp +decide [sev, Env.get, lsParams, ctxEnv]; exact notEmpty_w lps hl)
    (fun h => ?_) (fun h => ?_)
  · have he : (!lps.isEmpty) = true := by cases e : (!lps.isEmpty) <;> simp_all [boolW]
    rw [if_pos he]
    exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have he : (!lps.isEmpty) = false := by cases e : (!lps.isEmpty) <;> simp_all [boolW]
    rw [if_neg (by simp [he])]
    simp only [pinNat, pinChar, constE, emptyLevels, bind_assoc]
    refine specR_pinAtI hok PIN_NAT (by decide) lsA (by decide) ?_
    refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
      (pin_emptyLevels_cell hok) lsE (by decide) ?_
    refine ILP.callE_spec lsC fInternConst [lEn, lEus] [vv lsA, vv lsE] constBody
      [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra C hok s _ _) (fun nc s1 => ?_)
    refine specR_pinAtI hok PIN_CHAR (by decide) lsA (by decide) ?_
    refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
      (pin_emptyLevels_cell hok) lsE (by decide) ?_
    refine ILP.callE_spec lsB fInternConst [lEn, lEus] [vv lsA, vv lsE] constBody
      [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra C hok s1 _ _) (fun cc s2 => ?_)
    refine specR_congr (m' := arrT t nc cc >>= fun b => pure b) (by simp) ?_
    refine specR_arrI hca lsR (vv lsT) (vv lsC) (vv lsB) t nc cc (by decide) (by simp +decide [Env.get, lsParams, ctxEnv]) (by simp +decide [Env.get]) (by simp)
      (fun b H' s' hp => ?_)
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


structure LsCodes (C : Ctx) : Prop where
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  ia : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  ar : C.code.lookup fArr = some (arParams.map (fun p => (p, ShapeHOL.one)), arrBody, .one)

/-- **`String.ofList` shape**. -/
theorem lsl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : LsCodes C)
    (s : AState) (lps : List NIdx) (hl : lps.length < 2 ^ 62) (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lsParams.zip [BitVec.ofNat 64 lps.length, Enc.idxW t])) (lslBody C) s
      (if !lps.isEmpty then pure false else do
        let z ← zeroLevel
        let zs ← internLsNode [z]
        let li ← pinList
        let lc ← internE (.const li zs)
        let ch ← pinChar
        let cc ← constE ch
        let dom ← internE (.app lc cc)
        let st ← pinString
        let sc ← constE st
        arrT t dom sc) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [lsA, lsE, lsK, lsZ, lsC, lsB, lsD, lsS, lsR] lsParams _
    (by decide) (by decide)) ?_
  refine specR_ifI _ (boolW (!lps.isEmpty)) (by simp +decide [sev, Env.get, lsParams, ctxEnv]; exact notEmpty_w lps hl)
    (fun h => ?_) (fun h => ?_)
  · have he : (!lps.isEmpty) = true := by cases e : (!lps.isEmpty) <;> simp_all [boolW]
    rw [if_pos he]
    exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have he : (!lps.isEmpty) = false := by cases e : (!lps.isEmpty) <;> simp_all [boolW]
    rw [if_neg (by simp [he])]
    simp only [zeroLevel, pinList, pinChar, pinString, constE, emptyLevels, bind_assoc]
    refine specR_pinXI hok pinZeroLevel 1 C.pins.zeroLevel _ (fun s hp => pinZeroLevel_run hok hp)
      (pin_zeroLevel_cell hok) lsZ (by decide) ?_
    refine specR_allocI (C := C) lsK (.const 8) 1 (by norm_num) (by decide) (fun _ => by simp [sev])
      (fun H3 ws3 hpre hwl hcap => ?_)
    have hpl := hpre.length_le
    have hj : H3.length < (ctxH (ctxH C C.H) (H3 ++ ws3)).H.length := by show _ < (H3 ++ ws3).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv lsK) (vv lsZ) _ hj (Enc.idxW C.pins.zeroLevel)
      (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get] <;> rfl) ?_
    let H4 := (H3 ++ ws3).set H3.length (Enc.idxW C.pins.zeroLevel)
    have hp34 : H3 <+: H4 := prefix_set_ge (List.prefix_append _ _) _ (le_refl _) _
    have hp13 : C.H <+: H3 := hpre
    refine specR_callNIA (C := ctxH C H4) lsZ fInternLs [pKey, lEc] [vv lsK, .const 1] internLsBody
      [cellA C H3.length, BitVec.ofNat 64 1] (by decide) rfl (by decide) hc.ls
      ⟨by simp +decide [Env.get] <;> rfl, rfl, trivial⟩
      (fun a w s' st => internLsNode [C.pins.zeroLevel] s = .ok (a, s') ∧ PostLs (ctxH (ctxH C H4) H3) a w s' st)
      (fun a w s' H' => H' = H3 ∧ internLsNode [C.pins.zeroLevel] s = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H3, ⟨rfl, hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact internLs_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s [C.pins.zeroLevel] H3.length H3 hp34
          (le_refl _) (by show H3.length + 1 ≤ H4.length; simp [H4]; omega) (by norm_num)
          (fun j hj => by
            have : j = 0 := by simpa using hj
            subst this
            show ((H3 ++ ws3).set H3.length _)[H3.length + 0]? = _
            rw [Nat.add_zero, List.getElem?_set_self (by simp; omega)]; rfl)
          _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
      (fun zs w s2 H' ⟨e, hr2, hw⟩ => ?_)
    subst H'; subst hw
    have hok3 := ctxOK_H hok H3
    refine specR_pinAtI (C := ctxH C H3) hok3 PIN_LIST (by decide) lsA (by decide) ?_
    refine ILP.callE_spec (C := ctxH C H3) lsC fInternConst [lEn, lEus] [vv lsA, vv lsZ] constBody
      [_, Enc.idxW zs] (by decide) rfl (by decide) hc.ic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra (ctxH C H3) hok3 s2 _ _) (fun lc s3 => ?_)
    refine specR_pinAtI (C := ctxH C H3) hok3 PIN_CHAR (by decide) lsA (by decide) ?_
    refine specR_pinXI (C := ctxH C H3) hok3 pinEmptyLevels 0 C.pins.emptyLevels _
      (fun s hp => pinEmptyLevels_run (C := ctxH C H3) hok3 hp) (pin_emptyLevels_cell hok3) lsE (by decide) ?_
    refine ILP.callE_spec (C := ctxH C H3) lsB fInternConst [lEn, lEus] [vv lsA, vv lsE] constBody
      [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hc.ic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra (ctxH C H3) hok3 s3 _ _) (fun cc s4 => ?_)
    refine specR_internAppI (C := ctxH C H3) ra hok3 hc.ia lsD (vv lsC) (vv lsB) lc cc
      (by decide) (by simp +decide [Env.get]) (by simp) (fun dom s5 => ?_)
    refine specR_pinAtI (C := ctxH C H3) hok3 PIN_STRING (by decide) lsA (by decide) ?_
    refine specR_pinXI (C := ctxH C H3) hok3 pinEmptyLevels 0 C.pins.emptyLevels _
      (fun s hp => pinEmptyLevels_run (C := ctxH C H3) hok3 hp) (pin_emptyLevels_cell hok3) lsE (by decide) ?_
    refine ILP.callE_spec (C := ctxH C H3) lsS fInternConst [lEn, lEus] [vv lsA, vv lsE] constBody
      [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hc.ic
      ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra (ctxH C H3) hok3 s5 _ _) (fun sc s6 => ?_)
    refine specR_congr (m' := arrT t dom sc >>= fun b => pure b) (by simp) ?_
    refine specR_arrI (C := ctxH C H3) hc.ar lsR (vv lsT) (vv lsD) (vv lsS) t dom sc (by decide)
      (by simp +decide [Env.get, lsParams, ctxEnv]) (by simp +decide [Env.get]) (by simp) (fun b H' s' hp => ?_)
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp13.trans hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


structure LlCodes (C : Ctx) : Prop where
  lp : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  lsu : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  so : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ar : C.code.lookup fArr = some (arParams.map (fun p => (p, ShapeHOL.one)), arrBody, .one)

theorem len1_w (lps : List NIdx) (hl : lps.length < 2 ^ 62) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.notEqual (BitVec.ofNat 64 lps.length) 1#64 = true then (1#64 : BitVec 64) else 0#64)
      = boolW (decide (lps.length ≠ 1)) := by
  by_cases h : lps.length = 1
  · rw [h]; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]
  · have h' : BitVec.ofNat 64 lps.length ≠ 1#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h', h, boolW]

/-- **`List` shape**. -/
theorem lli_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : LlCodes C)
    (s : AState) (lps : List NIdx) (o : Nat) (hb : BlkAt C.H o (lps.map Enc.idxW)) (hl : lps.length < 2 ^ 62)
    (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lpParams.zip [BitVec.ofNat 64 lps.length, cellA C o, Enc.idxW t])) lliBody s
      (match lps with
        | [p] => do
          let pl ← internLNode (.param p)
          let sp ← internLNode (.succ pl)
          let sort ← internE (.sort sp)
          arrT t sort sort
        | _ => pure false) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [lsA, lsC, lsB, lsR] lpParams _ (by decide) (by decide)) ?_
  refine specR_ifI _ (boolW (decide (lps.length ≠ 1)))
    (by simp +decide [sev, Env.get, lpParams, ctxEnv]; exact len1_w lps hl) (fun h => ?_) (fun h => ?_)
  · have h1 : lps.length ≠ 1 := by intro e; simp [e, boolW] at h
    have hm : (match lps with
        | [p] => (do
          let pl ← internLNode (.param p)
          let sp ← internLNode (.succ pl)
          let sort ← internE (.sort sp)
          arrT t sort sort : AM Bool)
        | _ => pure false) = pure false := by
      match lps, h1 with
      | [], _ => rfl
      | [_], h1 => exact absurd rfl h1
      | _ :: _ :: _, _ => rfl
    rw [hm]
    exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have h1 : lps.length = 1 := by
      by_contra e; simp [e, boolW] at h
    obtain ⟨p, rfl⟩ : ∃ p, lps = [p] := by
      match lps, h1 with
      | [p], _ => exact ⟨p, rfl⟩
    dsimp only
    have hw : C.H[o + 1 + 0]? = some (Enc.idxW p) := by simpa using hb.2 0 (by simp)
    refine UD.specR_heapLoadI' (C := C) lsA _ (o + 1 + 0) _ hw (by decide)
      (by simp +decide [sev, Env.get, lpParams, ctxEnv]; exact cellA_add8 C o) ?_
    refine callLN lsC fInternLParam [lEn] [vv lsA] internLParamBody [Enc.idxW p] (by decide) rfl (by decide)
      hc.lp ⟨by simp, trivial⟩ (.param p) (internLParam_body_spec ra C hok s p) (fun pl s1 _ => ?_)
    refine callLN lsC fInternLSucc [lEu] [vv lsC] internLSuccBody [Enc.idxW pl] (by decide) rfl (by decide)
      hc.lsu ⟨by simp, trivial⟩ (.succ pl) (internLSucc_body_spec ra C hok s1 pl) (fun sp s2 _ => ?_)
    refine ILP.callE_spec lsB fInternSort [lEu] [vv lsC] sortBody [Enc.idxW sp] (by decide) rfl (by decide) hc.so
      ⟨by simp +decide [Env.get], trivial⟩ (by exact sort_body_spec ra C hok s2 sp) (fun srt s3 => ?_)
    refine specR_congr (m' := arrT t srt srt >>= fun b => pure b) (by simp) ?_
    refine specR_arrI hc.ar lsR (vv lsT) (vv lsB) (vv lsB) t srt srt (by decide)
      (by simp +decide [Env.get, lpParams, ctxEnv]) (by simp) (by simp) (fun b H' s' hp => ?_)
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
