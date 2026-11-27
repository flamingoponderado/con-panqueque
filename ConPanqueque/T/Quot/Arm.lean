import ConPanqueque.T.Quot.Block
import ConPanqueque.T.Quot.Install
import ConPanqueque.T.Decl.Axiom
import ConPanqueque.T.Decl.OffCheck
import ConPanqueque.T.InstLPFast
import ConPanqueque.T.Ind.ParamLevels

/-!
# `checkDecl` at a quotient record (the type former and the constructor)

`kqBody`: the record's kind (`1` the type former, `2` the constructor; the recursors hang); then the twin's
`checkQuotRecord`: the pinned block interned (scratch tier off, else a hang), the record compared with its
slot's pin at its own level-parameter names (`quotPinHit`: a mismatch hangs), the slots it needs stored
(`quotPredsOk`: a miss hangs), the block interned again and the pin at the record's names (`quotAt`), its name
fresh (else a hang), the install, the literal flags, the flush.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Decl
open ConPanqueque.T.Lit ConPanqueque.Logic.PlainIntern
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)
open ConPanqueque.T.Ind (fParamLevels plParams plBody pl_spec PostLsH fPlFill pfParams pfBody)

def kqRL := ofString "kq_rl"
def kqLn := ofString "kq_ln"
def kqPl := ofString "kq_pl"
def kqUs := ofString "kq_us"
def kqTy := ofString "kq_ty"
def kqT2 := ofString "kq_t2"
def kqR := ofString "kq_r"
def kqF := ofString "kq_f"
def kqE := ofString "kq_e"
def fKq := ofString "checkQuot"

def kqLocals : List MlS := [kdN, kdX, kdL, kdLn, lJ0, kqRL, kqLn, kqPl, kqUs, kqTy, kqT2, kqR, kqF, kqE,
  ocA, ocB, ocC, ocD, qN, qL, qT, qU, qX, ConPanqueque.Start.vPn, ConPanqueque.Start.vKa] ++ genLocals

/-- Pin `i`'s constant stored, else a hang. -/
def predGuard (C : Ctx) (i : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local kqF (.load .one (.const (ecell C (C.PO + i)))))
    (envFindP C kqF (vv kqF) (.ite (.cmp .equal (vv kqF) (.const 0)) hang rest))

/-- `quotPredsOk` at slot `j`: the constants its type mentions stored, else a hang. -/
def predsP (C : Ctx) : Nat → ProgHOL 64 → ProgHOL 64
  | 0, rest => predGuard C PIN_EQ rest
  | 1, rest => predGuard C PIN_QUOT rest
  | 3, rest => predGuard C PIN_QUOT (predGuard C PIN_QUOT_MK rest)
  | _, rest => predGuard C PIN_EQ (predGuard C PIN_QUOT (predGuard C PIN_QUOT_MK rest))

/-- `IConstantVal.atLps` of the pin (`qL`, `qT`) at the record's level parameters (`kqRL`): the type in `kqTy`. -/
def atLpsP (rest : ProgHOL 64) : ProgHOL 64 :=
  callR kqUs fParamLevels [vv kqRL]
    (callR kqTy fInstLPF [.const (BitVec.ofNat 64 coreWalkFuel), vv qT, vv qL, vv kqUs] rest)

/-- `quotPinHit`: as many level parameters as the pin's, distinct, then name and type the pin's at them. -/
def hitP (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local kqRL (.load .one (.op .add [vv kdQ, .const 8])))
  (.seq (.assign .local kqLn (.load .one (vv kqRL)))
  (.seq (.assign .local kqPl (.load .one (vv qL)))
  (.ite (.cmp .notEqual (vv kqLn) (vv kqPl)) hang
  (callR kdX fNdg [vv kqRL, .const 0, vv kqLn]
  (.ite (.cmp .equal (vv kdX) (.const 0)) hang
  (atLpsP
  (.seq (.assign .local kdN (.load .one (vv kdQ)))
  (.ite (.cmp .notEqual (vv kdN) (vv qN)) hang
  (.seq (.assign .local kqT2 (.load .one (.op .add [vv kdQ, .const 16])))
  (.ite (.cmp .notEqual (vv kqT2) (vv kqTy)) hang rest))))))))))

/-- The literal flags, the flush, success. -/
def tailP (C : Ctx) : ProgHOL 64 :=
  callR kdX fFlags [] (flushCode C (flushRegions false) (.return (.const 0)))

/-- The install at slot `j`. -/
def instP (C : Ctx) : Nat → ProgHOL 64
  | 0 => envAllocP C kqE (.const 8) (.seq (.store (vv kqE) (.const 0))
      (callR kdX fInstQ [.const 3, vv kqR, .const 0, vv kqE, .const 0, .const 0, vv kqE, .const 0] (tailP C)))
  | _ => callR kdX fInstQ [.const 4, vv kqR, .const 2, .const 1, vv qX, .const 0, .const 0, .const 0] (tailP C)

/-- The record at slot `j`. -/
def armP (C : Ctx) (j : Nat) : ProgHOL 64 :=
  offCheckP C (quotSlotP C j (hitP (predsP C j
  (offCheckP C (quotSlotP C j (atLpsP
  (alloc3 C kqR (vv qN) (vv kqRL) (vv kqTy)
  (envFindP C kqF (vv qN) (.ite (.cmp .notEqual (vv kqF) (.const 0)) hang (instP C j))))))))))

/-- `checkDecl` at a quotient record (its constant value at `kdQ`, its kind's number in `kdV`). -/
def kqBody (C : Ctx) : ProgHOL 64 := prologue kqLocals
  (.ite (.cmp .equal (vv kdV) (.const 1)) (armP C 0)
  (.ite (.cmp .equal (vv kdV) (.const 2)) (armP C 1) hang))

/-- A quotient kind's number. -/
def qkN : ConLeche.QuotKind → Nat
  | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4 | .sound => 5

section
variable {σ : Type}

theorem specR_okImp {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m m' : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (e : ∀ a s', m' s = .ok (a, s') → m s = .ok (a, s'))
    (h : SpecR P c s m' R) : SpecR P c s m R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a, s', hm, hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', e a s' hm, hq⟩

theorem denoteNList_of_get {ns : NStore} : ∀ (hs : List NIdx) (ks : List ConLeche.Name)
    (hkl : ks.length = hs.length), (∀ j (hj : j < hs.length), denoteN ns hs[j] = some (ks[j]'(by omega))) →
    Frontend.denoteNList ns hs = some ks
  | [], [], _, _ => rfl
  | [], _ :: _, hkl, _ => by simp at hkl
  | _ :: _, [], hkl, _ => by simp at hkl
  | h :: hs, k :: ks, hkl, hg => by
    have h0 := hg 0 (by simp)
    have ih := denoteNList_of_get hs ks (by simpa using hkl) (fun j hj => by have := hg (j + 1) (by simpa using hj); simpa only [List.getElem_cons_succ] using this)
    simp only [List.getElem_cons_zero] at h0
    simp [Frontend.denoteNList, h0, ih]

theorem checkDecl_quot (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) (k : ConLeche.QuotKind)
    (cv : IConstantVal) :
    checkDecl mode pins fe (.quotDecl k cv) = (checkQuotRecord fe k cv >>= fun fe₂ => flushCaches >>= fun _ => pure fe₂) := by
  simp [checkDecl, checkDeclKind, basisNamesOk]

theorem kq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kqLocals → (ctxEnv C ++ kdParams.zip vals).get x = none :=
  Knot.params_none C kqLocals kdParams vals (by decide) (by decide)

end

end ConPanqueque.T.Quot
