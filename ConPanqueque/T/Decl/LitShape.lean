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

def lsF := ofString "ls_f"
def lsX := ofString "ls_x"
def lsL := ofString "ls_l"
def lsU := ofString "ls_u"
def fLln := ofString "litShapeListNil"
def lnLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, lsA, lsC, lsB, lsK, lsZ, lsS, lsD, lsF, lsX, lsL, lsU, lsR, lsE]

/-- `lps = [p]` and the type is `(α : Sort (p+1)) → List.{p} α` (`List.nil`). -/
def lnBody (C : Ctx) : ProgHOL 64 := prologue lnLocals
  (.ite (.cmp .notEqual (vv lsN) (.const 1)) (.return (.const 0)) (.seq (.assign .local lsA (.load .one (.op .add [vv lsP, .const 8]))) (.seq (.call (some (some (.local, lsC), none)) fInternLParam [vv lsA]) (.seq (.call (some (some (.local, lsD), none)) fInternLSucc [vv lsC]) (.seq (.call (some (some (.local, lsB), none)) fInternSort [vv lsD]) (allocP C lsK (.const 8) (.seq (.store (vv lsK) (vv lsC)) (.seq (.call (some (some (.local, lsZ), none)) fInternLs [vv lsK, .const 1]) (.seq (.assign .local lsS (.load .one (.const (ecell C (C.PO + PIN_LIST))))) (.ite (tagIsE lsT 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv lsT)) (.seq eViewP (.seq (.assign .local lsD (.load .one (vv lRp))) (.seq (.assign .local lsF (.load .one (.op .add [vv lRp, .const 8]))) (.ite (.cmp .notEqual (vv lsD) (vv lsB)) (.return (.const 0)) (.seq (.assign .local lDh (vv lsF)) (.seq eViewP (.ite (.cmp .notEqual (vv lDg) (.const 4)) (.return (.const 0)) (.seq (.assign .local lsF (.load .one (vv lRp))) (.seq (.assign .local lsX (.load .one (.op .add [vv lRp, .const 8]))) (.seq (.assign .local lDh (vv lsF)) (.seq eViewP (.ite (.cmp .notEqual (vv lDg) (.const 3)) (.return (.const 0)) (.seq (.assign .local lsL (.load .one (vv lRp))) (.seq (.assign .local lsU (.load .one (.op .add [vv lRp, .const 8]))) (.seq (.assign .local lDh (vv lsX)) (.seq eViewP (.ite (.cmp .notEqual (vv lDg) (.const 0)) (.return (.const 0)) (.ite (.cmp .notEqual (vv lRn) (.const 0)) (.return (.const 0)) (.return (.op .and [.cmp .equal (vv lsL) (vv lsS), .cmp .equal (vv lsU) (vv lsZ)])))))))))))))))))))))) (.return (.const 0))))))))))))

def fLlc := ofString "litShapeListCons"

/-- `lps = [p]` and the type is `(α : Sort (p+1)) → α → List.{p} α → List.{p} α` (`List.cons`). -/
def lcBody (C : Ctx) : ProgHOL 64 := prologue lnLocals
  (.ite (.cmp .notEqual (vv lsN) (.const 1)) (.return (.const 0)) (.seq (.assign .local lsA (.load .one (.op .add [vv lsP, .const 8]))) (.seq (.call (some (some (.local, lsC), none)) fInternLParam [vv lsA]) (.seq (.call (some (some (.local, lsD), none)) fInternLSucc [vv lsC]) (.seq (.call (some (some (.local, lsB), none)) fInternSort [vv lsD]) (allocP C lsK (.const 8) (.seq (.store (vv lsK) (vv lsC)) (.seq (.call (some (some (.local, lsZ), none)) fInternLs [vv lsK, .const 1]) (.seq (.assign .local lsS (.load .one (.const (ecell C (C.PO + PIN_LIST))))) (.seq (.call (some (some (.local, lsE), none)) fInternBVar [.const 0]) (.seq (.call (some (some (.local, lsF), none)) fInternBVar [.const 1]) (.seq (.call (some (some (.local, lsX), none)) fInternBVar [.const 2]) (.seq (.call (some (some (.local, lsL), none)) fInternConst [vv lsS, vv lsZ]) (.seq (.call (some (some (.local, lsU), none)) fInternApp [vv lsL, vv lsF]) (.seq (.call (some (some (.local, lsL), none)) fInternApp [vv lsL, vv lsX]) (.ite (tagIsE lsT 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv lsT)) (.seq eViewP (.seq (.assign .local lsD (.load .one (vv lRp))) (.seq (.assign .local lsF (.load .one (.op .add [vv lRp, .const 8]))) (.ite (.cmp .notEqual (vv lsD) (vv lsB)) (.return (.const 0)) (.ite (tagIsE lsF 6) (.seq (.assign .local lDh (vv lsF)) (.seq eViewP (.seq (.assign .local lsD (.load .one (vv lRp))) (.seq (.assign .local lsF (.load .one (.op .add [vv lRp, .const 8]))) (.ite (.cmp .notEqual (vv lsD) (vv lsE)) (.return (.const 0)) (.seq (.call (some (some (.local, lsR), none)) fArr [vv lsF, vv lsU, vv lsL]) (.return (vv lsR)))))))) (.return (.const 0))))))))) (.return (.const 0))))))))))))))))))

def fLso' := fLso

/-- `litShapeOk`: dispatch on the declaration's name (the record's constant value at `lsQ`). -/
def lsoBody (C : Ctx) : ProgHOL 64 := prologue [lsA, lsP, lsT, lsN, lsX, lsR]
  (.seq (.assign .local lsA (.load .one (vv lsQ))) (.seq (.assign .local lsP (.load .one (.op .add [vv lsQ, .const 8]))) (.seq (.assign .local lsT (.load .one (.op .add [vv lsQ, .const 16]))) (.seq (.assign .local lsN (.load .one (vv lsP))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_NAT))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLss [vv lsN, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_NAT_ZERO))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLsz [vv lsN, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_NAT_SUCC))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLsu [vv lsN, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_STRING))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLss [vv lsN, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_STRING_OF_LIST))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLsl [vv lsN, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_LIST))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLli [vv lsN, vv lsP, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_LIST_NIL))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLln [vv lsN, vv lsP, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_LIST_CONS))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLlc [vv lsN, vv lsP, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_CHAR))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLss [vv lsN, vv lsT]) (.return (vv lsR))) (.seq (.assign .local lsX (.load .one (.const (ecell C (C.PO + PIN_CHAR_OF_NAT))))) (.ite (.cmp .equal (vv lsA) (vv lsX)) (.seq (.call (some (some (.local, lsR), none)) fLco [vv lsN, vv lsT]) (.return (vv lsR))) (.return (.const 1))))))))))))))))))))))))))

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


theorem limbs_len0 (i : Nat) : (Enc.limbs i).length = 0 ↔ i = 0 := by
  constructor
  · intro h; by_contra e; rw [Enc.limbs, dif_neg e] at h; simp at h
  · intro e; subst e; rw [Enc.limbs]; simp

theorem neIdx_w {k : IdxKind} (a b : Idx k) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.notEqual (Enc.idxW a) (Enc.idxW b) = true then (1#64 : BitVec 64) else 0#64)
      = boolW (a != b) := by
  by_cases h : a = b
  · subst h; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]
  · have h' : Enc.idxW a ≠ Enc.idxW b := fun e => h (idxW_inj e)
    have h'' : (a != b) = true := by simp [bne, h]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h', h'', boolW]

structure LnCodes (C : Ctx) : Prop where
  ll : LlCodes C
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)

/-- **`List.nil` shape**. -/
theorem lln_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : LnCodes C)
    (s : AState) (lps : List NIdx) (o : Nat) (hb : BlkAt C.H o (lps.map Enc.idxW)) (hl : lps.length < 2 ^ 62)
    (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lpParams.zip [BitVec.ofNat 64 lps.length, cellA C o, Enc.idxW t])) (lnBody C) s
      (match lps with
        | [p] => do
          let pl ← internLNode (.param p)
          let sp ← internLNode (.succ pl)
          let sort ← internE (.sort sp)
          let ps ← internLsNode [pl]
          let li ← pinList
          if t.tag == ETag.forallE then
            match ← view t with
            | .forallE d b => do
              if d != sort then pure false else
              if b.tag == ETag.app then
                match ← view b with
                | .app f a =>
                  if f.tag == ETag.const then
                    match ← view f with
                    | .const l1 us1 =>
                      if a.tag == ETag.bvar then
                        match ← view a with
                        | .bvar 0 => pure (l1 == li && us1 == ps)
                        | _ => pure false
                      else pure false
                    | _ => pure false
                  else pure false
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C lnLocals lpParams _ (by decide) (by decide)) ?_
  refine specR_ifI _ (boolW (decide (lps.length ≠ 1)))
    (by simp +decide [sev, Env.get, lpParams, ctxEnv]; exact len1_w lps hl) (fun h => ?_) (fun h => ?_)
  · have h1 : lps.length ≠ 1 := by intro e; simp [e, boolW] at h
    match lps, h1 with
    | [], _ => exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | [_], h1 => exact absurd rfl h1
    | _ :: _ :: _, _ => exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      hc.ll.lp ⟨by simp, trivial⟩ (.param p) (internLParam_body_spec ra C hok s p) (fun pl s1 _ => ?_)
    refine callLN lsD fInternLSucc [lEu] [vv lsC] internLSuccBody [Enc.idxW pl] (by decide) rfl (by decide)
      hc.ll.lsu ⟨by simp +decide [Env.get], trivial⟩ (.succ pl) (internLSucc_body_spec ra C hok s1 pl) (fun sp s2 _ => ?_)
    refine ILP.callE_spec lsB fInternSort [lEu] [vv lsD] sortBody [Enc.idxW sp] (by decide) rfl (by decide) hc.ll.so
      ⟨by simp +decide [Env.get], trivial⟩ (by exact sort_body_spec ra C hok s2 sp) (fun srt s3 => ?_)
    refine specR_allocI (C := C) lsK (.const 8) 1 (by norm_num) (by decide) (fun _ => by simp [sev])
      (fun H3 ws3 hpre hwl hcap => ?_)
    have hpl := hpre.length_le
    have hj : H3.length < (ctxH (ctxH C C.H) (H3 ++ ws3)).H.length := by show _ < (H3 ++ ws3).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv lsK) (vv lsC) _ hj (Enc.idxW pl)
      (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get] <;> rfl) ?_
    let H4 := (H3 ++ ws3).set H3.length (Enc.idxW pl)
    have hp34 : H3 <+: H4 := prefix_set_ge (List.prefix_append _ _) _ (le_refl _) _
    have hp13 : C.H <+: H3 := hpre
    refine specR_callNIA (C := ctxH C H4) lsZ fInternLs [pKey, lEc] [vv lsK, .const 1] internLsBody
      [cellA C H3.length, BitVec.ofNat 64 1] (by decide) rfl (by decide) hc.ls
      ⟨by simp +decide [Env.get] <;> rfl, rfl, trivial⟩
      (fun a w s' st => internLsNode [pl] s3 = .ok (a, s') ∧ PostLs (ctxH (ctxH C H4) H3) a w s' st)
      (fun a w s' H' => H' = H3 ∧ internLsNode [pl] s3 = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H3, ⟨rfl, hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact internLs_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s3 [pl] H3.length H3 hp34
          (le_refl _) (by show H3.length + 1 ≤ H4.length; simp [H4]; omega) (by norm_num)
          (fun j hj => by
            have : j = 0 := by simpa using hj
            subst this
            show ((H3 ++ ws3).set H3.length _)[H3.length + 0]? = _
            rw [Nat.add_zero, List.getElem?_set_self (by simp; omega)]; rfl)
          _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
      (fun ps w s4 H' ⟨e, hr2, hw⟩ => ?_)
    subst H'; subst hw
    have hok3 := ctxOK_H hok H3
    have hiL : PIN_LIST < (ctxH C H3).pins.names.size := by rw [hok3.pinsRel.1]; decide
    refine specR_pinAtI (C := ctxH C H3) hok3 PIN_LIST (by decide) lsS (by decide) ?_
    refine Knot.specR_tagIteV lsT t 6 (by decide) (by decide) (by simp +decide [Env.get, lpParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (t.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ 0 rfl (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (t.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv lsT) (Enc.idxW t) (by decide) (by simp +decide [Env.get, lpParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H3) t (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
    refine specR_congr (view_bind_eq t vw _ s4 hv) ?_
    have h6 : vw.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨d, b, rfl⟩ : ∃ d b, vw = .forallE d b := by cases vw <;> simp [ENodeView.tagN] at h6 ⊢
    refine specR_loadI' lsD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW d) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW d) [Enc.idxW b] []) ?_
    refine specR_loadI' lsF _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW d) (Enc.idxW b) [] []) ?_
    dsimp only
    refine specR_ifI _ (boolW (d != srt)) (by simp +decide [sev, Env.get]; exact neIdx_w d srt) (fun h => ?_) (fun h => ?_)
    · have he : (d != srt) = true := by cases e : (d != srt) <;> simp_all [boolW]
      rw [if_pos he]
      exact specR_returnI _ 0 rfl (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have he : (d != srt) = false := by cases e : (d != srt) <;> simp_all [boolW]
    rw [if_neg (by simp [he])]
    refine specR_dropM ?_
    refine specR_assignI lDh (vv lsF) (Enc.idxW b) (by decide) (by simp +decide [Env.get]) ?_
    refine specR_viewP (C := ctxH C H3) b (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v2 P2 hv2 htn2 _ => ?_)
    rcases v2 with i | ⟨idx, ty⟩ | u | ⟨cn, cus⟩ | ⟨f, a⟩ | ⟨ty, bd⟩ | ⟨ty, bd⟩ | ⟨ty, vl, bd⟩ | l | ⟨pn, pi, sub⟩
    rotate_left 4
    · have htg : (b.tag == ETag.app) = true := by
        have : b.tag.toNat = 4 := by simpa [ENodeView.tagN] using htn2.symm
        simp only [beq_iff_eq]; apply UInt32.toNat_inj.mp; simpa [ETag.app] using this
      rw [if_pos htg]
      refine specR_congr (view_bind_eq b _ _ s4 hv2) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' lsF (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P2 (Enc.idxW f) [Enc.idxW a] []) ?_
      refine specR_loadI' lsX _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P2 (Enc.idxW f) (Enc.idxW a) [] []) ?_
      dsimp only
      refine specR_dropM ?_
      refine specR_assignI lDh (vv lsF) (Enc.idxW f) (by decide) (by simp +decide [Env.get]) ?_
      refine specR_viewP (C := ctxH C H3) f (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v3 P3 hv3 htn3 _ => ?_)
      rcases v3 with i | ⟨idx, ty⟩ | u | ⟨cn, cus⟩ | ⟨f', a'⟩ | ⟨ty, bd⟩ | ⟨ty, bd⟩ | ⟨ty, vl, bd⟩ | l | ⟨pn, pi, sub⟩
      rotate_left 3
      · have htg : (f.tag == ETag.const) = true := by
          have : f.tag.toNat = 3 := by simpa [ENodeView.tagN] using htn3.symm
          simp only [beq_iff_eq]; apply UInt32.toNat_inj.mp; simpa [ETag.const] using this
        rw [if_pos htg]
        refine specR_congr (view_bind_eq f _ _ s4 hv3) ?_
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_loadI' lsL (vv lRp) P3 (P3 + BitVec.ofNat 64 0) (Enc.idxW cn) (by decide) (by simp) (by simp)
          (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P3 (Enc.idxW cn) [Enc.idxW cus] []) ?_
        refine specR_loadI' lsU _ (P3 + 8) (P3 + BitVec.ofNat 64 8) (Enc.idxW cus) (by decide) (by simp +decide [sev]) rfl
          (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P3 (Enc.idxW cn) (Enc.idxW cus) [] []) ?_
        dsimp only
        refine specR_dropM ?_
        refine specR_assignI lDh (vv lsX) (Enc.idxW a) (by decide) (by simp +decide [Env.get]) ?_
        refine specR_viewP (C := ctxH C H3) a (by simp) (by simp +decide [Env.get] <;> rfl)
          (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v4 P4 hv4 htn4 _ => ?_)
        rcases v4 with i | ⟨idx, ty⟩ | u | ⟨cn', cus'⟩ | ⟨f', a'⟩ | ⟨ty, bd⟩ | ⟨ty, bd⟩ | ⟨ty, vl, bd⟩ | l | ⟨pn, pi, sub⟩
        · have htg : (a.tag == ETag.bvar) = true := by
            have : a.tag.toNat = 0 := by simpa [ENodeView.tagN] using htn4.symm
            simp only [beq_iff_eq]; apply UInt32.toNat_inj.mp; simpa [ETag.bvar] using this
          rw [if_pos htg]
          refine specR_congr (view_bind_eq a _ _ s4 hv4) ?_
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
          rcases i with _ | i
          · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, encEView, Enc.encBVar, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun h => absurd rfl h) (fun _ => ?_)
            exact specR_returnI _ (boolW (cn == (ctxH C H3).pins.names[PIN_LIST]'hiL && cus == ps))
              (by simp +decide [sev, Env.get]; rw [eqIdx_w', eqIdx_w']; exact and_w _ _)
              (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
          · have hl61 := ‹(encEView (ENodeView.bvar (i + 1))).length < 2 ^ 61›
            simp only [encEView, Enc.encBVar] at hl61
            have hne : (Enc.limbs (i + 1)).length ≠ 0 := fun e => absurd ((limbs_len0 _).mp e) (by omega)
            refine specR_ifI _ 1 (by
                simp +decide [sev, Env.get, encEView, Enc.encBVar, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
                intro e; have := congrArg BitVec.toNat e; simp at this; omega) (fun _ => ?_) (fun h => absurd h (by decide))
            exact specR_returnI _ 0 rfl (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        all_goals (
          rw [if_neg (by intro e; simp only [beq_iff_eq] at e; rw [e] at htn4; simp [ENodeView.tagN, ETag.bvar] at htn4)]
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          exact specR_returnI _ 0 rfl (fun t' ht => ⟨_, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩))
      all_goals (
        rw [if_neg (by intro e; simp only [beq_iff_eq] at e; rw [e] at htn3; simp [ENodeView.tagN, ETag.const] at htn3)]
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_returnI _ 0 rfl (fun t' ht => ⟨_, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩))
    all_goals (
      rw [if_neg (by intro e; simp only [beq_iff_eq] at e; rw [e] at htn2; simp [ENodeView.tagN, ETag.app] at htn2)]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t' ht => ⟨_, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩))

structure LcCodes (C : Ctx) : Prop where
  ll : LlCodes C
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  bv : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  ia : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)

/-- **`List.cons` shape**. -/
theorem llc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : LcCodes C)
    (s : AState) (lps : List NIdx) (o : Nat) (hb : BlkAt C.H o (lps.map Enc.idxW)) (hl : lps.length < 2 ^ 62)
    (t : EIdx) :
    SpecR (σ := σ) (Pre C s (lpParams.zip [BitVec.ofNat 64 lps.length, cellA C o, Enc.idxW t])) (lcBody C) s
      (match lps with
        | [p] => do
          let pl ← internLNode (.param p)
          let sp ← internLNode (.succ pl)
          let sort ← internE (.sort sp)
          let ps ← internLsNode [pl]
          let li ← pinList
          let b0 ← internE (.bvar 0)
          let b1 ← internE (.bvar 1)
          let b2 ← internE (.bvar 2)
          let l1 ← internE (.const li ps)
          let dom3 ← internE (.app l1 b1)
          let cod3 ← internE (.app l1 b2)
          if t.tag == ETag.forallE then
            match ← view t with
            | .forallE d1 r1 => do
              if d1 != sort then pure false else
              if r1.tag == ETag.forallE then
                match ← view r1 with
                | .forallE d2 r2 => do
                  if d2 != b0 then pure false else
                  arrT r2 dom3 cod3
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C lnLocals lpParams _ (by decide) (by decide)) ?_
  refine specR_ifI _ (boolW (decide (lps.length ≠ 1)))
    (by simp +decide [sev, Env.get, lpParams, ctxEnv]; exact len1_w lps hl) (fun h => ?_) (fun h => ?_)
  · have h1 : lps.length ≠ 1 := by intro e; simp [e, boolW] at h
    match lps, h1 with
    | [], _ => exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | [_], h1 => exact absurd rfl h1
    | _ :: _ :: _, _ => exact specR_returnI _ 0 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      hc.ll.lp ⟨by simp, trivial⟩ (.param p) (internLParam_body_spec ra C hok s p) (fun pl s1 _ => ?_)
    refine callLN lsD fInternLSucc [lEu] [vv lsC] internLSuccBody [Enc.idxW pl] (by decide) rfl (by decide)
      hc.ll.lsu ⟨by simp +decide [Env.get], trivial⟩ (.succ pl) (internLSucc_body_spec ra C hok s1 pl) (fun sp s2 _ => ?_)
    refine ILP.callE_spec lsB fInternSort [lEu] [vv lsD] sortBody [Enc.idxW sp] (by decide) rfl (by decide) hc.ll.so
      ⟨by simp +decide [Env.get], trivial⟩ (by exact sort_body_spec ra C hok s2 sp) (fun srt s3 => ?_)
    refine specR_allocI (C := C) lsK (.const 8) 1 (by norm_num) (by decide) (fun _ => by simp [sev])
      (fun H3 ws3 hpre hwl hcap => ?_)
    have hpl := hpre.length_le
    have hj : H3.length < (ctxH (ctxH C C.H) (H3 ++ ws3)).H.length := by show _ < (H3 ++ ws3).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv lsK) (vv lsC) _ hj (Enc.idxW pl)
      (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get] <;> rfl) ?_
    let H4 := (H3 ++ ws3).set H3.length (Enc.idxW pl)
    have hp34 : H3 <+: H4 := prefix_set_ge (List.prefix_append _ _) _ (le_refl _) _
    have hp13 : C.H <+: H3 := hpre
    refine specR_callNIA (C := ctxH C H4) lsZ fInternLs [pKey, lEc] [vv lsK, .const 1] internLsBody
      [cellA C H3.length, BitVec.ofNat 64 1] (by decide) rfl (by decide) hc.ls
      ⟨by simp +decide [Env.get] <;> rfl, rfl, trivial⟩
      (fun a w s' st => internLsNode [pl] s3 = .ok (a, s') ∧ PostLs (ctxH (ctxH C H4) H3) a w s' st)
      (fun a w s' H' => H' = H3 ∧ internLsNode [pl] s3 = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H3, ⟨rfl, hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact internLs_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s3 [pl] H3.length H3 hp34
          (le_refl _) (by show H3.length + 1 ≤ H4.length; simp [H4]; omega) (by norm_num)
          (fun j hj => by
            have : j = 0 := by simpa using hj
            subst this
            show ((H3 ++ ws3).set H3.length _)[H3.length + 0]? = _
            rw [Nat.add_zero, List.getElem?_set_self (by simp; omega)]; rfl)
          _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
      (fun ps w s4 H' ⟨e, hr2, hw⟩ => ?_)
    subst H'; subst hw
    have hok3 := ctxOK_H hok H3
    have hiL : PIN_LIST < (ctxH C H3).pins.names.size := by rw [hok3.pinsRel.1]; decide
    refine specR_pinAtI (C := ctxH C H3) hok3 PIN_LIST (by decide) lsS (by decide) ?_
    refine specR_internBVarI (C := ctxH C H3) ra hok3 hc.bv lsE (.const 0) 0 (by decide) (by decide) rfl (fun b0 s5 => ?_)
    refine specR_internBVarI (C := ctxH C H3) ra hok3 hc.bv lsF (.const 1) 1 (by decide) (by decide) rfl (fun b1 s6 => ?_)
    refine specR_internBVarI (C := ctxH C H3) ra hok3 hc.bv lsX (.const 2) 2 (by decide) (by decide) rfl (fun b2 s7 => ?_)
    refine ILP.callE_spec (C := ctxH C H3) lsL fInternConst [lEn, lEus] [vv lsS, vv lsZ] constBody
      [_, Enc.idxW ps] (by decide) rfl (by decide) hc.ic
      ⟨by first | (simp +decide [Env.get] <;> rfl) | rfl, by first | (simp +decide [Env.get] <;> rfl) | rfl, trivial⟩
      (by exact const_body_spec ra (ctxH C H3) hok3 s7 _ _) (fun l1 s8 => ?_)
    refine specR_internAppI (C := ctxH C H3) ra hok3 hc.ia lsU (vv lsL) (vv lsF) l1 b1
      (by decide) (by simp) (by simp +decide [Env.get]) (fun dom3 s9 => ?_)
    refine specR_internAppI (C := ctxH C H3) ra hok3 hc.ia lsL (vv lsL) (vv lsX) l1 b2
      (by decide) (by simp +decide [Env.get]) (by simp +decide [Env.get]) (fun cod3 s10 => ?_)
    refine Knot.specR_tagIteV lsT t 6 (by decide) (by decide) (by simp +decide [Env.get, lpParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (t.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ 0 rfl (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (t.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv lsT) (Enc.idxW t) (by decide) (by simp +decide [Env.get, lpParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H3) t (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
    refine specR_congr (view_bind_eq t vw _ s10 hv) ?_
    have h6 : vw.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨d1, r1, rfl⟩ : ∃ d b, vw = .forallE d b := by cases vw <;> simp [ENodeView.tagN] at h6 ⊢
    refine specR_loadI' lsD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW d1) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW d1) [Enc.idxW r1] []) ?_
    refine specR_loadI' lsF _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW r1) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW d1) (Enc.idxW r1) [] []) ?_
    dsimp only
    refine specR_ifI _ (boolW (d1 != srt)) (by simp +decide [sev, Env.get]; exact neIdx_w d1 srt) (fun h => ?_) (fun h => ?_)
    · have he : (d1 != srt) = true := by cases e : (d1 != srt) <;> simp_all [boolW]
      rw [if_pos he]
      exact specR_returnI _ 0 rfl (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have he : (d1 != srt) = false := by cases e : (d1 != srt) <;> simp_all [boolW]
    rw [if_neg (by simp [he])]
    refine Knot.specR_tagIteV lsF r1 6 (by decide) (by decide) (by simp +decide [Env.get]) (fun htg1 => ?_) (fun htg1 => ?_)
    swap
    · rw [if_neg (show ¬ (r1.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg1)]
      exact specR_returnI _ 0 rfl (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (r1.tag == ETag.forallE) = true by simp [htg1, ETag.forallE])]
    refine specR_dropM ?_
    refine specR_assignI lDh (vv lsF) (Enc.idxW r1) (by decide) (by simp +decide [Env.get]) ?_
    refine specR_viewP (C := ctxH C H3) r1 (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw2 P2 hv2 htn2 _ => ?_)
    refine specR_congr (view_bind_eq r1 vw2 _ s10 hv2) ?_
    have h62 : vw2.tagN = 6 := by rw [htn2, htg1]; rfl
    obtain ⟨d2, r2, rfl⟩ : ∃ d b, vw2 = .forallE d b := by cases vw2 <;> simp [ENodeView.tagN] at h62 ⊢
    refine specR_loadI' lsD (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW d2) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P2 (Enc.idxW d2) [Enc.idxW r2] []) ?_
    refine specR_loadI' lsF _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (Enc.idxW r2) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P2 (Enc.idxW d2) (Enc.idxW r2) [] []) ?_
    dsimp only
    refine specR_ifI _ (boolW (d2 != b0)) (by simp +decide [sev, Env.get]; exact neIdx_w d2 b0) (fun h => ?_) (fun h => ?_)
    · have he : (d2 != b0) = true := by cases e : (d2 != b0) <;> simp_all [boolW]
      rw [if_pos he]
      exact specR_returnI _ 0 rfl (fun t' ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have he2 : (d2 != b0) = false := by cases e : (d2 != b0) <;> simp_all [boolW]
    rw [if_neg (by simp [he2])]
    refine specR_dropM ?_
    refine specR_congr (m' := arrT r2 dom3 cod3 >>= fun b => pure b) (by simp) ?_
    refine specR_arrI (C := ctxH C H3) hc.ll.ar lsR (vv lsF) (vv lsU) (vv lsL) r2 dom3 cod3 (by decide)
      (by simp +decide [Env.get]) (by simp +decide [Env.get]) (by simp +decide [Env.get]) (fun b H' s' hp => ?_)
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp13.trans hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)



theorem specR_bindPure {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : SpecR P c s (m >>= fun b => pure b) R) : SpecR P c s m R :=
  specR_congr (by simp) h

structure LsoCodes (C : Ctx) : Prop where
  ss : C.code.lookup fLss = some (lsParams.map (fun p => (p, ShapeHOL.one)), lssBody C, .one)
  sz : C.code.lookup fLsz = some (lsParams.map (fun p => (p, ShapeHOL.one)), lszBody C, .one)
  su : C.code.lookup fLsu = some (lsParams.map (fun p => (p, ShapeHOL.one)), lsuBody C, .one)
  sl : C.code.lookup fLsl = some (lsParams.map (fun p => (p, ShapeHOL.one)), lslBody C, .one)
  co : C.code.lookup fLco = some (lsParams.map (fun p => (p, ShapeHOL.one)), lscBody C, .one)
  li : C.code.lookup fLli = some (lpParams.map (fun p => (p, ShapeHOL.one)), lliBody, .one)
  ln : C.code.lookup fLln = some (lpParams.map (fun p => (p, ShapeHOL.one)), lnBody C, .one)
  lc : C.code.lookup fLlc = some (lpParams.map (fun p => (p, ShapeHOL.one)), lcBody C, .one)
  lsc : LsCodes C
  lcc : LcCodes C

/-- **`litShapeOk`** at a record's constant value (a `CVE` block at `q` in the value heap). -/
theorem lso_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : LsoCodes C)
    (s : AState) (cv : IConstantVal) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 62) :
    SpecR (σ := σ) (Pre C s [(lsQ, cellA C q)]) (lsoBody C) s (litShapeOk (.axiomInfo cv)) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [lsA, lsP, lsT, lsN, lsX, lsR] [lsQ] [cellA C q] (by decide) (by decide)) ?_
  unfold litShapeOk
  dsimp only
  simp only [show (IConstantInfo.axiomInfo cv).name = cv.name from rfl, pinNat, pinNatZero, pinNatSucc, pinString, pinStringOfList, pinList, pinListNil, pinListCons, pinChar,
    pinCharOfNat]
  refine UD.specR_heapLoadI' (C := C) lsA _ q _ hn (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) lsP _ (q + 1) _ hl (by decide)
    (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add8 C q) ?_
  refine UD.specR_heapLoadI' (C := C) lsT _ (q + 2) _ ht (by decide)
    (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add_ofNat C q 2) ?_
  refine UD.specR_heapLoadI' (C := C) lsN _ o _ (by simpa using hb.1) (by decide) (by simp +decide [Env.get]) ?_
  refine specR_pinAtI hok PIN_NAT (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLss lsParams [vv lsN, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, Enc.idxW cv.type] (by decide) rfl (by decide) hc.ss ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lsParams _ rfl hlk) (by exact lss_spec C hok s cv.levelParams hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_NAT_ZERO (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLsz lsParams [vv lsN, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, Enc.idxW cv.type] (by decide) rfl (by decide) hc.sz ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lsParams _ rfl hlk) (by exact lsz_spec ra C hok hc.lsc.ic s cv.levelParams hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_NAT_SUCC (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLsu lsParams [vv lsN, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, Enc.idxW cv.type] (by decide) rfl (by decide) hc.su ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lsParams _ rfl hlk) (by exact lsu_spec ra C hok hc.lsc.ic hc.lsc.ar s cv.levelParams hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_STRING (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLss lsParams [vv lsN, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, Enc.idxW cv.type] (by decide) rfl (by decide) hc.ss ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lsParams _ rfl hlk) (by exact lss_spec C hok s cv.levelParams hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_STRING_OF_LIST (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLsl lsParams [vv lsN, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, Enc.idxW cv.type] (by decide) rfl (by decide) hc.sl ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lsParams _ rfl hlk) (by exact lsl_spec ra C hok hc.lsc s cv.levelParams hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_LIST (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLli lpParams [vv lsN, vv lsP, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, cellA C o, Enc.idxW cv.type] (by decide) rfl (by decide) hc.li ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lpParams _ rfl hlk) (by exact lli_spec ra C hok hc.lcc.ll s cv.levelParams o hb hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_LIST_NIL (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLln lpParams [vv lsN, vv lsP, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, cellA C o, Enc.idxW cv.type] (by decide) rfl (by decide) hc.ln ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lpParams _ rfl hlk) (by exact lln_spec ra C hok ⟨hc.lcc.ll, hc.lcc.ls⟩ s cv.levelParams o hb hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_LIST_CONS (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLlc lpParams [vv lsN, vv lsP, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, cellA C o, Enc.idxW cv.type] (by decide) rfl (by decide) hc.lc ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lpParams _ rfl hlk) (by exact llc_spec ra C hok hc.lcc s cv.levelParams o hb hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_CHAR (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLss lsParams [vv lsN, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, Enc.idxW cv.type] (by decide) rfl (by decide) hc.ss ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lsParams _ rfl hlk) (by exact lss_spec C hok s cv.levelParams hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  refine specR_pinAtI hok PIN_CHAR_OF_NAT (by decide) lsX (by decide) ?_
  refine specR_ifI _ (boolW (cv.name == _)) (by simp +decide [sev, Env.get]; exact eqIdx_w' _ _) (fun h => ?_) (fun h => ?_)
  · rw [if_pos (show (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
    refine specR_bindPure ?_
    refine specR_callNIH lsR fLco lsParams [vv lsN, vv lsT] _ [BitVec.ofNat 64 cv.levelParams.length, Enc.idxW cv.type] (by decide) rfl (by decide) hc.co ⟨(by simp +decide [Env.get]), (by simp +decide [Env.get]), trivial⟩
      (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lsParams _ rfl hlk) (by exact lsc_spec ra C hok hc.lsc.ic hc.lsc.ar s cv.levelParams hlen cv.type))
      (fun b w s' H' hp hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp) (fun t' ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg (show ¬ (cv.name == _) = true by cases e : (cv.name == _) <;> simp_all [boolW])]
  exact specR_returnI _ 1 rfl (fun t' ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


theorem get_prefix {H H' : List (BitVec 64)} {i : Nat} {v : BitVec 64} (h : H[i]? = some v) (hp : H <+: H') :
    H'[i]? = some v := by
  obtain ⟨r, rfl⟩ := hp
  rw [List.getElem?_append_left (by
    rcases Nat.lt_or_ge i H.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h; simp at h)]
  exact h

/-- **`checkConstantVal`**, `litShapeOk` discharged. -/
theorem ccv_full (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hpr : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hpim : C.code.lookup fPim = some (pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one))
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false) (hk : KCodes C Comp.kBodies)
    (hac : Comp.AllCodes mode C)
    (hcl : C.code.lookup fLso = some ([lsQ].map (fun p => (p, ShapeHOL.one)), lsoBody C, .one)) (hlso : LsoCodes C)
    (hndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one))
    (hndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one))
    (hlbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one))
    (hcB : ExB.CodesB C (ExB.bodyB C))
    (hbvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one))
    (hhf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one))
    (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (hat : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)) (hal : AlCodes C)
    (hcrff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)) (hcrf : CrfCodes C)
    (hens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one))
    (fe : IFEnv) (hfe : fe = C.fe) (cv : IConstantVal) (aO aR aS : Bool) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (ccvParams.zip [cellA C q, boolW aO, boolW aR, boolW aS])) (ccvBody C) s
      (checkConstantVal mode fe cv aO aR aS) (PostU C) :=
  ccv_spec mode C hok hg hpr hpim ra hs hk hac (lsoBody C) hcl hndh hndg hlbb hcB hbvb hhf hcF hfvb hat hal hcrff hcrf
    hens fe hfe cv aO aR aS q o hn hl ht hb hlen ks hkl hks
    (fun H s1 hp => lso_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hlso) s1 cv q o (get_prefix hn hp) (get_prefix hl hp)
      (get_prefix ht hp) (blkAt_mono hb hp) hlen) s

end

end ConPanqueque.T.Decl
