import ConPanqueque.T.Core.LamBody
import ConPanqueque.T.Core.ConstVal
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `ruleBodyAt`: a recursor rule's body for its ι step

Memoized on `(recursor, constructor, levels)` in the fixed rule-body cache: on a miss, `lamBody k rhs`, the level
parameters copied to the heap, `instLPFast`, then the detach-insert write.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody)
open ConRon.Bridge

/-- The twin's detach-then-insert write of the rule-body cache. -/
def rbSetOp (key : NIdx × NIdx × LsIdx) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.ruleBodyC
  let s := { s with caches := { s.caches with ruleBodyC := ∅ } }
  set { s with caches := { s.caches with ruleBodyC := mp.insert key r } }

def rbSetS (s : AState) (key : NIdx × NIdx × LsIdx) (r : EIdx) : AState :=
  { s with caches := { s.caches with ruleBodyC := s.caches.ruleBodyC.insert key r } }

theorem rbSetOp_run (key : NIdx × NIdx × LsIdx) (r : EIdx) (s : AState) :
    rbSetOp key r s = .ok ((), rbSetS s key r) := rfl

theorem ruleBodyAt_eq (recName ctor : NIdx) (lps : List NIdx) (rhs : EIdx) (k : Nat) (us : LsIdx) (s : AState) :
    ruleBodyAt recName ctor lps rhs k us s =
      ((fun s => .ok (s.caches.ruleBodyC[(recName, ctor, us)]?, s) : AM (Option EIdx)) >>= fun r =>
        match r with
        | some x => pure x
        | none => lamBody k rhs >>= fun body => instLPFast coreWalkFuel lps us body >>= fun x =>
            rbSetOp (recName, ctor, us) x >>= fun _ => pure x) s := by
  rfl

theorem encRB_inj : ∀ x y, encRB x = encRB y → x = y := by
  intro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  simp only [encRB, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [Enc.idxW_inj h1, Enc.idxW_inj h2, Enc.idxW_inj h3]


def rbX := ofString "rbx"
def rbLen := ofString "rblen"
def rbP := ofString "rbp"
def rbY := ofString "rby"
def rbZ := ofString "rbz"
def rbB := ofString "rbb"

@[simp] theorem rb_rbX_ne_rbLen : rbX ≠ rbLen := by decide
@[simp] theorem rb_rbX_ne_rbP : rbX ≠ rbP := by decide
@[simp] theorem rb_rbX_ne_rbY : rbX ≠ rbY := by decide
@[simp] theorem rb_rbX_ne_rbZ : rbX ≠ rbZ := by decide
@[simp] theorem rb_rbX_ne_rbB : rbX ≠ rbB := by decide
@[simp] theorem rb_rbX_ne_pmC : rbX ≠ pmC := by decide
@[simp] theorem rb_pmC_ne_rbX : pmC ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_pmK : rbX ≠ pmK := by decide
@[simp] theorem rb_pmK_ne_rbX : pmK ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_pmR : rbX ≠ pmR := by decide
@[simp] theorem rb_pmR_ne_rbX : pmR ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_pmM : rbX ≠ pmM := by decide
@[simp] theorem rb_pmM_ne_rbX : pmM ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_ioRp : rbX ≠ ioRp := by decide
@[simp] theorem rb_ioRp_ne_rbX : ioRp ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_ioUj : rbX ≠ ioUj := by decide
@[simp] theorem rb_ioUj_ne_rbX : ioUj ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_lCn : rbX ≠ lCn := by decide
@[simp] theorem rb_lCn_ne_rbX : lCn ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_lSrc : rbX ≠ lSrc := by decide
@[simp] theorem rb_lSrc_ne_rbX : lSrc ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_lDst : rbX ≠ lDst := by decide
@[simp] theorem rb_lDst_ne_rbX : lDst ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_lCi : rbX ≠ lCi := by decide
@[simp] theorem rb_lCi_ne_rbX : lCi ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_lCz : rbX ≠ lCz := by decide
@[simp] theorem rb_lCz_ne_rbX : lCz ≠ rbX := by decide
@[simp] theorem rb_rbX_ne_lKb : rbX ≠ lKb := by decide
@[simp] theorem rb_lKb_ne_rbX : lKb ≠ rbX := by decide
@[simp] theorem rb_rbLen_ne_rbX : rbLen ≠ rbX := by decide
@[simp] theorem rb_rbLen_ne_rbP : rbLen ≠ rbP := by decide
@[simp] theorem rb_rbLen_ne_rbY : rbLen ≠ rbY := by decide
@[simp] theorem rb_rbLen_ne_rbZ : rbLen ≠ rbZ := by decide
@[simp] theorem rb_rbLen_ne_rbB : rbLen ≠ rbB := by decide
@[simp] theorem rb_rbLen_ne_pmC : rbLen ≠ pmC := by decide
@[simp] theorem rb_pmC_ne_rbLen : pmC ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_pmK : rbLen ≠ pmK := by decide
@[simp] theorem rb_pmK_ne_rbLen : pmK ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_pmR : rbLen ≠ pmR := by decide
@[simp] theorem rb_pmR_ne_rbLen : pmR ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_pmM : rbLen ≠ pmM := by decide
@[simp] theorem rb_pmM_ne_rbLen : pmM ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_ioRp : rbLen ≠ ioRp := by decide
@[simp] theorem rb_ioRp_ne_rbLen : ioRp ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_ioUj : rbLen ≠ ioUj := by decide
@[simp] theorem rb_ioUj_ne_rbLen : ioUj ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_lCn : rbLen ≠ lCn := by decide
@[simp] theorem rb_lCn_ne_rbLen : lCn ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_lSrc : rbLen ≠ lSrc := by decide
@[simp] theorem rb_lSrc_ne_rbLen : lSrc ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_lDst : rbLen ≠ lDst := by decide
@[simp] theorem rb_lDst_ne_rbLen : lDst ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_lCi : rbLen ≠ lCi := by decide
@[simp] theorem rb_lCi_ne_rbLen : lCi ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_lCz : rbLen ≠ lCz := by decide
@[simp] theorem rb_lCz_ne_rbLen : lCz ≠ rbLen := by decide
@[simp] theorem rb_rbLen_ne_lKb : rbLen ≠ lKb := by decide
@[simp] theorem rb_lKb_ne_rbLen : lKb ≠ rbLen := by decide
@[simp] theorem rb_rbP_ne_rbX : rbP ≠ rbX := by decide
@[simp] theorem rb_rbP_ne_rbLen : rbP ≠ rbLen := by decide
@[simp] theorem rb_rbP_ne_rbY : rbP ≠ rbY := by decide
@[simp] theorem rb_rbP_ne_rbZ : rbP ≠ rbZ := by decide
@[simp] theorem rb_rbP_ne_rbB : rbP ≠ rbB := by decide
@[simp] theorem rb_rbP_ne_pmC : rbP ≠ pmC := by decide
@[simp] theorem rb_pmC_ne_rbP : pmC ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_pmK : rbP ≠ pmK := by decide
@[simp] theorem rb_pmK_ne_rbP : pmK ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_pmR : rbP ≠ pmR := by decide
@[simp] theorem rb_pmR_ne_rbP : pmR ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_pmM : rbP ≠ pmM := by decide
@[simp] theorem rb_pmM_ne_rbP : pmM ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_ioRp : rbP ≠ ioRp := by decide
@[simp] theorem rb_ioRp_ne_rbP : ioRp ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_ioUj : rbP ≠ ioUj := by decide
@[simp] theorem rb_ioUj_ne_rbP : ioUj ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_lCn : rbP ≠ lCn := by decide
@[simp] theorem rb_lCn_ne_rbP : lCn ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_lSrc : rbP ≠ lSrc := by decide
@[simp] theorem rb_lSrc_ne_rbP : lSrc ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_lDst : rbP ≠ lDst := by decide
@[simp] theorem rb_lDst_ne_rbP : lDst ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_lCi : rbP ≠ lCi := by decide
@[simp] theorem rb_lCi_ne_rbP : lCi ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_lCz : rbP ≠ lCz := by decide
@[simp] theorem rb_lCz_ne_rbP : lCz ≠ rbP := by decide
@[simp] theorem rb_rbP_ne_lKb : rbP ≠ lKb := by decide
@[simp] theorem rb_lKb_ne_rbP : lKb ≠ rbP := by decide
@[simp] theorem rb_rbY_ne_rbX : rbY ≠ rbX := by decide
@[simp] theorem rb_rbY_ne_rbLen : rbY ≠ rbLen := by decide
@[simp] theorem rb_rbY_ne_rbP : rbY ≠ rbP := by decide
@[simp] theorem rb_rbY_ne_rbZ : rbY ≠ rbZ := by decide
@[simp] theorem rb_rbY_ne_rbB : rbY ≠ rbB := by decide
@[simp] theorem rb_rbY_ne_pmC : rbY ≠ pmC := by decide
@[simp] theorem rb_pmC_ne_rbY : pmC ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_pmK : rbY ≠ pmK := by decide
@[simp] theorem rb_pmK_ne_rbY : pmK ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_pmR : rbY ≠ pmR := by decide
@[simp] theorem rb_pmR_ne_rbY : pmR ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_pmM : rbY ≠ pmM := by decide
@[simp] theorem rb_pmM_ne_rbY : pmM ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_ioRp : rbY ≠ ioRp := by decide
@[simp] theorem rb_ioRp_ne_rbY : ioRp ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_ioUj : rbY ≠ ioUj := by decide
@[simp] theorem rb_ioUj_ne_rbY : ioUj ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_lCn : rbY ≠ lCn := by decide
@[simp] theorem rb_lCn_ne_rbY : lCn ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_lSrc : rbY ≠ lSrc := by decide
@[simp] theorem rb_lSrc_ne_rbY : lSrc ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_lDst : rbY ≠ lDst := by decide
@[simp] theorem rb_lDst_ne_rbY : lDst ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_lCi : rbY ≠ lCi := by decide
@[simp] theorem rb_lCi_ne_rbY : lCi ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_lCz : rbY ≠ lCz := by decide
@[simp] theorem rb_lCz_ne_rbY : lCz ≠ rbY := by decide
@[simp] theorem rb_rbY_ne_lKb : rbY ≠ lKb := by decide
@[simp] theorem rb_lKb_ne_rbY : lKb ≠ rbY := by decide
@[simp] theorem rb_rbZ_ne_rbX : rbZ ≠ rbX := by decide
@[simp] theorem rb_rbZ_ne_rbLen : rbZ ≠ rbLen := by decide
@[simp] theorem rb_rbZ_ne_rbP : rbZ ≠ rbP := by decide
@[simp] theorem rb_rbZ_ne_rbY : rbZ ≠ rbY := by decide
@[simp] theorem rb_rbZ_ne_rbB : rbZ ≠ rbB := by decide
@[simp] theorem rb_rbZ_ne_pmC : rbZ ≠ pmC := by decide
@[simp] theorem rb_pmC_ne_rbZ : pmC ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_pmK : rbZ ≠ pmK := by decide
@[simp] theorem rb_pmK_ne_rbZ : pmK ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_pmR : rbZ ≠ pmR := by decide
@[simp] theorem rb_pmR_ne_rbZ : pmR ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_pmM : rbZ ≠ pmM := by decide
@[simp] theorem rb_pmM_ne_rbZ : pmM ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_ioRp : rbZ ≠ ioRp := by decide
@[simp] theorem rb_ioRp_ne_rbZ : ioRp ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_ioUj : rbZ ≠ ioUj := by decide
@[simp] theorem rb_ioUj_ne_rbZ : ioUj ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_lCn : rbZ ≠ lCn := by decide
@[simp] theorem rb_lCn_ne_rbZ : lCn ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_lSrc : rbZ ≠ lSrc := by decide
@[simp] theorem rb_lSrc_ne_rbZ : lSrc ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_lDst : rbZ ≠ lDst := by decide
@[simp] theorem rb_lDst_ne_rbZ : lDst ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_lCi : rbZ ≠ lCi := by decide
@[simp] theorem rb_lCi_ne_rbZ : lCi ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_lCz : rbZ ≠ lCz := by decide
@[simp] theorem rb_lCz_ne_rbZ : lCz ≠ rbZ := by decide
@[simp] theorem rb_rbZ_ne_lKb : rbZ ≠ lKb := by decide
@[simp] theorem rb_lKb_ne_rbZ : lKb ≠ rbZ := by decide
@[simp] theorem rb_rbB_ne_rbX : rbB ≠ rbX := by decide
@[simp] theorem rb_rbB_ne_rbLen : rbB ≠ rbLen := by decide
@[simp] theorem rb_rbB_ne_rbP : rbB ≠ rbP := by decide
@[simp] theorem rb_rbB_ne_rbY : rbB ≠ rbY := by decide
@[simp] theorem rb_rbB_ne_rbZ : rbB ≠ rbZ := by decide
@[simp] theorem rb_rbB_ne_pmC : rbB ≠ pmC := by decide
@[simp] theorem rb_pmC_ne_rbB : pmC ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_pmK : rbB ≠ pmK := by decide
@[simp] theorem rb_pmK_ne_rbB : pmK ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_pmR : rbB ≠ pmR := by decide
@[simp] theorem rb_pmR_ne_rbB : pmR ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_pmM : rbB ≠ pmM := by decide
@[simp] theorem rb_pmM_ne_rbB : pmM ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_ioRp : rbB ≠ ioRp := by decide
@[simp] theorem rb_ioRp_ne_rbB : ioRp ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_ioUj : rbB ≠ ioUj := by decide
@[simp] theorem rb_ioUj_ne_rbB : ioUj ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_lCn : rbB ≠ lCn := by decide
@[simp] theorem rb_lCn_ne_rbB : lCn ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_lSrc : rbB ≠ lSrc := by decide
@[simp] theorem rb_lSrc_ne_rbB : lSrc ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_lDst : rbB ≠ lDst := by decide
@[simp] theorem rb_lDst_ne_rbB : lDst ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_lCi : rbB ≠ lCi := by decide
@[simp] theorem rb_lCi_ne_rbB : lCi ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_lCz : rbB ≠ lCz := by decide
@[simp] theorem rb_lCz_ne_rbB : lCz ≠ rbB := by decide
@[simp] theorem rb_rbB_ne_lKb : rbB ≠ lKb := by decide
@[simp] theorem rb_lKb_ne_rbB : lKb ≠ rbB := by decide

/-- `KB[0..2] := (rec, ctor, us); x := memoGet(rule-body cache, 3); rest`. -/
def rbGetP (C : Ctx) (x : MlS) (e0 e1 e2 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) e0)
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) e1)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 2))]) e2)
        (.seq (.call (some (some (.local, x), none)) fMemoGet [.const (C.mG (.c .ruleBody)), .const 3]) rest)))

def rbSetP (C : Ctx) (x : MlS) (e0 e1 e2 ev : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) e0)
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) e1)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 2))]) e2)
        (.seq (.call (some (some (.local, x), none)) fMemoSet [.const (C.mG (.c .ruleBody)), .const 3, ev]) rest)))

def rbLocals : List MlS := [rbX, rbLen, rbP, rbY, rbZ, rbB, lCn, lSrc, lDst, lCi, lCz]

def rbMiss (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, rbB), none)) fLb [vv ioRp, vv pmM])
  (.seq (.assign .local rbLen (.load .one (vv pmR)))
  (.seq (.assign .local lCn (.op .add [vv rbLen, .const 1]))
  (allocP C rbP (.panop .mul [vv lCn, .const 8])
  (.seq (.assign .local lSrc (vv pmR)) (.seq (.assign .local lDst (vv rbP)) (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop
  (.seq (.call (some (some (.local, rbY), none)) fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv rbB, vv rbP, vv ioUj])
  (rbSetP C rbZ (vv pmC) (vv pmK) (vv ioUj) (vv rbY) (.return (vv rbY)))))))))))

def rbBody (C : Ctx) : ProgHOL 64 :=
  prologue rbLocals (rbGetP C rbX (vv pmC) (vv pmK) (vv ioUj)
    (.ite (.cmp .notEqual (vv rbX) (.const 0)) (.return (.op .sub [vv rbX, .const 1])) (rbMiss C)))

section
variable {σ : Type}

theorem words_kbRB {C : Ctx} {u : PState σ} {a b : NIdx} {c : LsIdx}
    (hM : ∀ x v, (x, v) ∈ [(C.KB + BitVec.ofNat 64 (8 * 0), Enc.idxW a), (C.KB + BitVec.ofNat 64 (8 * 1), Enc.idxW b),
      (C.KB + BitVec.ofNat 64 (8 * 2), Enc.idxW c)] → u.memaddrs x ∧ u.memory x = .word v) :
    Words u C.KB (encRB (a, b, c)) := by
  intro j hj
  have : j < 3 := by simpa [encRB] using hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact hM _ (Enc.idxW a) (by simp)
  · exact hM _ (Enc.idxW b) (by simp)
  · exact hM _ (Enc.idxW c) (by simp)

theorem specR_rbGetI {β : Type} {C : Ctx} (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k' : Option EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (e0 e1 e2 : ExpHOL 64) (a b : NIdx) (c : LsIdx) (hx : x ∈ D)
    (he0 : sev Γ e0 = some (Enc.idxW a)) (he1 : sev Γ e1 = some (Enc.idxW b)) (he2 : sev Γ e2 = some (Enc.idxW c))
    (hkb : Γ.get lKb = some C.KB)
    (hk : SpecR (Inv C s ((x, optW s.caches.ruleBodyC[(a, b, c)]?) :: Γ) [] D) rest s
      (k' s.caches.ruleBodyC[(a, b, c)]?) R) :
    SpecR (Inv C s Γ M D) (rbGetP C x e0 e1 e2 rest) s
      ((fun s => .ok (s.caches.ruleBodyC[(a, b, c)]?, s) : AM (Option EIdx)) >>= k') R := by
  refine specR_storeKB3I hok e0 e1 e2 (Enc.idxW a) (Enc.idxW b) (Enc.idxW c) he0 he1 he2 hkb ?_
  exact specR_memoGetGI encRB_inj (C.mG (.c .ruleBody)) (C.mg (.c .ruleBody)) s.caches.ruleBodyC (a, b, c) _ rfl
    (fun u hu => hu.cache .ruleBody) hcodeG hcodeP x
    (.const (C.mG (.c .ruleBody))) (.const 3) hx rfl rfl (by simp [encRB]) (fun u hM => words_kbRB hM) hk

theorem specR_rbSetI {β : Type} {C : Ctx} (hok : CtxOK C)
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k' : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (e0 e1 e2 ev : ExpHOL 64) (a b : NIdx) (c : LsIdx) (r : EIdx) (hx : x ∈ D)
    (he0 : sev Γ e0 = some (Enc.idxW a)) (he1 : sev Γ e1 = some (Enc.idxW b)) (he2 : sev Γ e2 = some (Enc.idxW c))
    (hev : sev Γ ev = some (Enc.idxW r)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv C (rbSetS s (a, b, c) r) ((x, w) :: Γ) [] D) rest (rbSetS s (a, b, c) r) (k' ()) R) :
    SpecR (Inv C s Γ M D) (rbSetP C x e0 e1 e2 ev rest) s (rbSetOp (a, b, c) r >>= k') R := by
  refine specR_storeKB3I hok e0 e1 e2 (Enc.idxW a) (Enc.idxW b) (Enc.idxW c) he0 he1 he2 hkb ?_
  refine specR_memoSetGI encRB_inj (C.mG (.c .ruleBody)) (C.mg (.c .ruleBody)) s.caches.ruleBodyC (a, b, c) r _
    (rbSetOp_run (a, b, c) r s) (fun u hu => hu.cache .ruleBody)
    (fun i hi => hok.kbMemo _ i (by simp [encRB] at hi; omega)) (fun j hj => hok.mdescMemo _ _ j hj)
    (fun u u' hsr hmem hfr hd hg hc => ?_) hcodeS hcodeI x (.const (C.mG (.c .ruleBody))) (.const 3) ev hx rfl rfl hev
    (by simp [encRB]) (fun u hM => words_kbRB hM) hk
  exact sr_upd_fix hok .ruleBody hsr hfr hd hg hc rfl rfl rfl hmem
    (fun k'' hk'' => by cases k'' <;> first | rfl | exact absurd rfl hk'') ⟨rfl, rfl⟩

end

section
variable {σ : Type}

theorem RO.viewBind (h : EIdx) : RO (ConRon.Arena.viewBind h) := RO.bind RO.get (fun _ => RO.pure _)

theorem RO.lamBody : ∀ (k : Nat) (h : EIdx), RO (ConRon.Arena.lamBody k h)
  | 0, h => by rw [ConRon.Arena.lamBody]; exact RO.pure _
  | k + 1, h => by
    rw [ConRon.Arena.lamBody]
    refine RO.ite _ (RO.bind (RO.viewBind h) (fun o => ?_)) (RO.pure _)
    rcases o with _ | ⟨_, b⟩
    · exact RO.failDanglingE
    · exact RO.lamBody k b

theorem rb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rbLocals → (ctxEnv C ++ rbParams.zip vals).get x = none :=
  Knot.params_none C rbLocals rbParams vals (by decide) (by decide)

theorem rb_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesILP C (ilpBody C))
    (hcf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one))
    (hcl : C.code.lookup fLb = some (lbParams.map (fun p => (p, ShapeHOL.one)), lbBody, .one))
    (s : AState) (recN ctor : NIdx) (lps : List NIdx) (ks : List ConLeche.Name) (rhs : EIdx) (k : Nat) (us : LsIdx)
    (vsL : List ConLeche.Level) (o : Nat) (hlp : EBlk C.EH o (lps.map Enc.idxW)) (hlen : lps.length + 1 < 2 ^ 60)
    (hk : k < 2 ^ 64)
    (hks : Frontend.denoteNList s.store.ns lps = some ks) (hus : denoteLs s.store.lss us = some vsL)
    (hst : StateOK s) (hcn : ReadNCacheOK s.caches.readNC s.store) (hcl' : ReadLCacheOK s.caches.readLC s.store)
    (hcls : ReadLsCacheOK s.caches.readLsC s.store)
    (hden : ∀ b, lamBody k rhs s = .ok (b, s) → (denoteE s.store b).isSome = true) :
    SpecR (σ := σ) (Pre C s (rbParams.zip [Enc.idxW recN, Enc.idxW ctor, ecell C o, Enc.idxW rhs, BitVec.ofNat 64 k,
      Enc.idxW us])) (rbBody C) s (ruleBodyAt recN ctor lps rhs k us) (PostK C) := by
  refine specR_prologue (postK_locals C) (rb_none C _) ?_
  refine specR_congr (ruleBodyAt_eq recN ctor lps rhs k us s) ?_
  refine specR_rbGetI hok hc.memoGet hc.memoProbe rbX (vv pmC) (vv pmK) (vv ioUj) recN ctor us (by decide)
    (by simp +decide [Env.get, rbParams, ctxEnv]) (by simp +decide [Env.get, rbParams, ctxEnv])
    (by simp +decide [Env.get, rbParams, ctxEnv]) (by simp +decide [Env.get, rbParams, ctxEnv]) ?_
  rcases hr : s.caches.ruleBodyC[(recN, ctor, us)]? with _ | x
  · -- miss
    refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optW, optWG])
      (fun h => absurd rfl h) (fun _ => ?_)
    unfold rbMiss
    refine specR_callNIH rbB fLb lbParams [vv ioRp, vv pmM] lbBody [BitVec.ofNat 64 k, Enc.idxW rhs] (by decide) rfl
      (by decide) hcl ⟨by simp +decide [Env.get, rbParams, ctxEnv], by simp +decide [Env.get, rbParams, ctxEnv], trivial⟩
      (fun b w s' st => lamBody k rhs s = .ok (b, s') ∧ PostK C b w s' st)
      (fun b w s' _ => lamBody k rhs s = .ok (b, s') ∧ w = Enc.idxW b)
      (fun b w s' st ⟨hrun, H', hp, hw, hsr⟩ => ⟨H', hp, ⟨hrun, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu lbParams _ rfl hlk)
        (lb_spec C hok hcl k rhs s hk)))
      (fun body w s1 H1 hp1 ⟨hrun, hw⟩ => ?_)
    subst hw
    have hs1 : s1 = s := RO.lamBody k rhs s body s1 hrun
    subst s1
    have hbden := hden body hrun
    have hok1 := ctxOK_H hok H1
    have hl0 : C.EH[o]? = some (BitVec.ofNat 64 lps.length) := by have := hlp.1; simpa using this
    refine specR_envLoadI (C := ctxH C H1) rbLen (vv pmR) o _ (by decide)
      (by simp +decide [Env.get, rbParams, ctxEnv]; rfl) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (lps.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI (C := ctxH C H1) rbP (.panop .mul [vv lCn, .const 8]) (lps.length + 1) (by omega) (by decide)
      (fun v => by simp +decide [sev, Env.get]; exact CV.mul8_eq _) (fun H' wsN hpre hwl hcap => ?_)
    refine specR_assignI lSrc (vv pmR) (ecell C o) (by decide)
      (by simp +decide [sev, Env.get, rbParams, ctxEnv]) ?_
    refine specR_assignI lDst (vv rbP) (cellA C H'.length) (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = lps.length + 1 := by simp
    refine specR_copyEI (C := ctxH C H1) hok1 (H' ++ wsN) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) o
      H'.length (by decide) (fun j hj => ?_) (by simp [hwl]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, rbParams, ctxEnv]) ?_
    · rcases j with _ | j
      · exact hl0
      · have := hlp.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show o + (j + 1) = o + 1 + j by omega]; exact this
    have hblk := CV.blk_of_fillI (H' ++ wsN) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H'.length
      (lps.map Enc.idxW) (by simp) (by simp [hwl])
    refine specR_callNIH rbY fInstLPF ilpParams [.const (BitVec.ofNat 64 coreWalkFuel), vv rbB, vv rbP, vv ioUj]
      (ilpfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body, cellA C H'.length, Enc.idxW us] (by decide) rfl
      (by decide) hcf
      ⟨rfl, by simp +decide [sev, Env.get, rbParams, ctxEnv], by simp +decide [sev, Env.get]; rfl,
        by simp +decide [sev, Env.get, rbParams, ctxEnv], trivial⟩
      (ILP.PostILP (ctxH C _)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H'', hp, hw, hsr⟩ => ⟨H'', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc coreWalkFuel CV.coreWalkFuel_lt H'.length lps ks us vsL _ s body hks hus hst hcn hcl'
          hcls hbden hblk))
      (fun a w s' H'' hp hw => ?_)
    subst hw
    refine specR_rbSetI (C := ctxH C H'') (ctxOK_H hok H'') hc.memoSet hc.memoIns rbZ (vv pmC) (vv pmK) (vv ioUj)
      (vv rbY) recN ctor us a (by decide) (by simp +decide [sev, Env.get, rbParams, ctxEnv])
      (by simp +decide [sev, Env.get, rbParams, ctxEnv]) (by simp +decide [sev, Env.get, rbParams, ctxEnv])
      (by simp +decide [sev, Env.get]) (by simp +decide [Env.get, rbParams, ctxEnv]; rfl) (fun w => ?_)
    refine specR_returnI _ (Enc.idxW a) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
    refine ⟨H'', ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
    have hp1' : C.H <+: fillI (H' ++ wsN) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H'.length
        (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length :=
      CV.prefix_fillI _ _ _ C.H (hp1.length_le.trans hpre.length_le)
        ((hp1.trans hpre).trans (List.prefix_append _ _)) _
    exact hp1'.trans hp
  · -- hit
    refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact Knot.optW_some_ne x)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_returnI _ (Enc.idxW x) (by simp [sev, Env.get, optW, optWG]; exact BitVec.add_sub_cancel _ _)
      (fun t ht => ?_)
    exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.WC
