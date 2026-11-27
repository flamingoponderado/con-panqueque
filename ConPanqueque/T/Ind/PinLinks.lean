import ConPanqueque.T.Ind.PinCopy
import ConPanqueque.T.Ind.LpsEq

/-!
# A block's links against its pin (`blockLinksOk`)

The twin's `blockLinksOk`: a constructor carries its former's level parameters (`lpsEq`), and each of the pinned
recursor's rules reads its constructor's parameters at the stream recursor's names as the pin's does
(`pinLinkOk`). Over handles that is `C == Cp.map (goH Rp R)`: the stream constructor's names are the pin
constructor's, each renamed by the first matching pin recursor name to the stream recursor's (`goH`), which
`pinLink_val` shows is the twin's comparison of the read-back names.

* `fndBody`: the first record of a pointer block whose name is `x` (index plus one, `0` for none);
* `sgoBody`: `goH` from index `j`; `lgoBody`: the comparison from index `i`;
* `rllBody`: the pinned recursor's rules from `j`; `bllBody`: the block's pairs from `i` (hang unless they link).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl
open ConPanqueque.T.Quot (specR_guardNe specR_guardZ specR_guardNZ specR_readNamesI)

/-! ## The handle-level renaming -/

/-- `Level.subst.go` over handles: the first `k = n` gives its `v`, else `n`. -/
def goH : List NIdx → List NIdx → NIdx → NIdx
  | k :: ks, v :: vs, n => if k == n then v else goH ks vs n
  | _, _, n => n

/-- `Level.subst.go` over names, returning the name. -/
def goN : List ConLeche.Name → List ConLeche.Name → ConLeche.Name → ConLeche.Name
  | k :: ks, v :: vs, n => if k = n then v else goN ks vs n
  | _, _, n => n

theorem subst_go_param : ∀ (ks vs : List ConLeche.Name) (n : ConLeche.Name),
    ConLeche.Level.subst.go ks (vs.map ConLeche.Level.param) n = .param (goN ks vs n)
  | k :: ks, v :: vs, n => by
    simp only [List.map_cons, ConLeche.Level.subst.go, goN]
    split
    · rfl
    · exact subst_go_param ks vs n
  | [], _, n => by simp [ConLeche.Level.subst.go, goN]
  | _ :: _, [], n => by simp [ConLeche.Level.subst.go, goN]

theorem goH_denote {st : EStore} (hwf : StoreWF st) : ∀ (ks vs : List NIdx) (kn vn : List ConLeche.Name)
    (x : NIdx) (xn : ConLeche.Name), Frontend.denoteNList st.ns ks = some kn →
    Frontend.denoteNList st.ns vs = some vn → denoteN st.ns x = some xn →
    denoteN st.ns (goH ks vs x) = some (goN kn vn xn)
  | k :: ks, v :: vs, kn, vn, x, xn, hk, hv, hx => by
    obtain ⟨k', kn', hk1, hk2, rfl⟩ := denoteNList_cons_inv hk
    obtain ⟨v', vn', hv1, hv2, rfl⟩ := denoteNList_cons_inv hv
    simp only [goH, goN]
    rw [denoteN_beqS hwf hk1 hx]
    by_cases e : k' = xn
    · simp [e, hv1]
    · simp only [e, beq_iff_eq, if_false]; exact goH_denote hwf ks vs kn' vn' x xn hk2 hv2 hx
  | [], vs, kn, vn, x, xn, hk, hv, hx => by
    simp only [Frontend.denoteNList, Option.some.injEq] at hk; subst hk; simpa [goH, goN] using hx
  | _ :: _, [], kn, vn, x, xn, hk, hv, hx => by
    simp only [Frontend.denoteNList, Option.some.injEq] at hv; subst hv
    obtain ⟨k', kn', -, -, rfl⟩ := denoteNList_cons_inv hk
    simpa [goH, goN] using hx

theorem denoteNList_map_goH {st : EStore} (hwf : StoreWF st) (ks vs : List NIdx) (kn vn : List ConLeche.Name)
    (hk : Frontend.denoteNList st.ns ks = some kn) (hv : Frontend.denoteNList st.ns vs = some vn) :
    ∀ (xs : List NIdx) (xn : List ConLeche.Name), Frontend.denoteNList st.ns xs = some xn →
      Frontend.denoteNList st.ns (xs.map (goH ks vs)) = some (xn.map (goN kn vn))
  | [], xn, h => by simp only [Frontend.denoteNList, Option.some.injEq] at h; subst h; rfl
  | x :: xs, xn, h => by
    obtain ⟨x', xn', h1, h2, rfl⟩ := denoteNList_cons_inv h
    simp only [List.map_cons, Frontend.denoteNList, goH_denote hwf ks vs kn vn x x' hk hv h1,
      denoteNList_map_goH hwf ks vs kn vn hk hv xs xn' h2, List.map_cons]

theorem denoteNList_beq {st : EStore} (hwf : StoreWF st) {as bs : List NIdx} {xs ys : List ConLeche.Name}
    (ha : Frontend.denoteNList st.ns as = some xs) (hb : Frontend.denoteNList st.ns bs = some ys) :
    (as == bs) = (xs == ys) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact denoteNList_inj hwf as bs xs ha hb

theorem map_param_beq (xs ys : List ConLeche.Name) :
    (xs.map ConLeche.Level.param == ys.map ConLeche.Level.param) = (xs == ys) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h; exact (List.map_inj_right (fun a b e => ConLeche.Level.param.inj e)).mp h
  · rintro rfl; rfl

/-- **The twin's link comparison is the handles'.** -/
theorem pinLink_val {st : EStore} (hwf : StoreWF st) {R Rp Cl Cpl : List NIdx}
    {rT rpT cT cpT : List ConLeche.Name}
    (hR : Frontend.denoteNList st.ns R = some rT) (hRp : Frontend.denoteNList st.ns Rp = some rpT)
    (hC : Frontend.denoteNList st.ns Cl = some cT) (hCp : Frontend.denoteNList st.ns Cpl = some cpT) :
    (cT.map ConLeche.Level.param == cpT.map fun p => ConLeche.Level.subst rpT (rT.map ConLeche.Level.param) (.param p))
      = (Cl == Cpl.map (goH Rp R)) := by
  have e1 : (fun p => ConLeche.Level.subst rpT (rT.map ConLeche.Level.param) (.param p)) =
      ConLeche.Level.param ∘ goN rpT rT := by
    funext p; simp only [ConLeche.Level.subst, Function.comp, subst_go_param]
  rw [e1, ← List.map_map, map_param_beq,
    denoteNList_beq hwf hC (denoteNList_map_goH hwf Rp R rpT rT hRp hR Cpl cpT hCp)]

/-! ## Finding a record by name -/

/-- Record names in a pointer block: entry `i`'s record has name `xs[i]`. -/
def NamesAt (C : Ctx) (H : List (BitVec 64)) (ob : Nat) (xs : List NIdx) : Prop :=
  H[ob]? = some (BitVec.ofNat 64 xs.length) ∧
    ∀ i (hi : i < xs.length), ∃ o, H[ob + 1 + i]? = some (cellA C o) ∧ H[o + 1]? = some (Enc.idxW xs[i])

theorem namesAt_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {ob : Nat} {xs : List NIdx}
    (h : NamesAt C H ob xs) : NamesAt C H' ob xs :=
  ⟨get_prefix h.1 hp, fun i hi => let ⟨o, h1, h2⟩ := h.2 i hi; ⟨o, get_prefix h1 hp, get_prefix h2 hp⟩⟩

theorem namesAt_ind {C : Ctx} {H : List (BitVec 64)} {ob : Nat} {blk : List IConstantInfo}
    (h : IndBlk C H ob blk) : NamesAt C H ob (blk.map (·.name)) := by
  obtain ⟨os, hl, hb, hc⟩ := h
  refine ⟨by rw [List.length_map, ← hl]; simpa using hb.1, fun i hi => ?_⟩
  simp only [List.length_map] at hi
  refine ⟨os[i]'(by omega), by have := hb.2 i (by simp; omega); rw [List.getElem_map] at this; exact this, ?_⟩
  simp only [List.getElem_map]
  rw [ci_name_eq]; exact (hc i hi (by omega)).1.1

theorem namesAt_pin {C : Ctx} {H : List (BitVec 64)} {ob : Nat} {blk : List IConstantInfo}
    (h : PinBlk C H ob blk) : NamesAt C H ob (blk.map (·.name)) := by
  obtain ⟨os, hl, hb, hc⟩ := h
  refine ⟨by rw [List.length_map, ← hl]; simpa using hb.1, fun i hi => ?_⟩
  simp only [List.length_map] at hi
  refine ⟨os[i]'(by omega), by have := hb.2 i (by simp; omega); rw [List.getElem_map] at this; exact this, ?_⟩
  simp only [List.getElem_map]
  rw [ci_name_eq]; exact (hc i hi (by omega)).1.1

/-- The first index from `k` on in `ys` whose name is `x`, plus one; `0` for none. -/
def fndGo (x : NIdx) : List NIdx → Nat → Nat
  | [], _ => 0
  | y :: ys, k => if y == x then k + 1 else fndGo x ys (k + 1)

/-- The first index from `i` whose name is `x`, plus one; `0` for none. -/
def fndV (xs : List NIdx) (x : NIdx) (i : Nat) : Nat := fndGo x (xs.drop i) i

theorem fndV_stop (xs : List NIdx) (x : NIdx) : fndV xs x xs.length = 0 := by simp [fndV, fndGo]

theorem fndV_step (xs : List NIdx) (x : NIdx) (i : Nat) (hi : i < xs.length) :
    fndV xs x i = if xs[i] == x then i + 1 else fndV xs x (i + 1) := by
  unfold fndV
  rw [List.drop_eq_getElem_cons hi]; rfl

/-- **The twin's `constNamed?` by `fndV`.** -/
theorem constNamed_fnd (cs : List IConstantInfo) (x : NIdx) :
    ∀ f i, cs.length - i = f → i ≤ cs.length →
      (fndV (cs.map (·.name)) x i = 0 → (cs.drop i).find? (fun c => c.name == x) = none) ∧
      (∀ j, fndV (cs.map (·.name)) x i = j + 1 → ∃ h : j < cs.length, (cs.drop i).find? (fun c => c.name == x) = some cs[j]) := by
  intro f
  induction f with
  | zero =>
    intro i hf hi
    have hil : i = cs.length := by omega
    subst hil
    refine ⟨fun _ => by simp, fun j hj => ?_⟩
    rw [show cs.length = (cs.map (·.name)).length by simp, fndV_stop] at hj
    omega
  | succ f ih =>
    intro i hf hi
    have hil : i < cs.length := by omega
    have hil' : i < (cs.map (·.name)).length := by simpa using hil
    rw [fndV_step _ x i hil', List.drop_eq_getElem_cons hil, List.find?_cons]
    simp only [List.getElem_map]
    by_cases e : cs[i].name == x
    · simp only [e, if_true]
      refine ⟨fun h => by omega, fun j hj => ?_⟩
      have e : j = i := by omega
      subst e
      exact ⟨hil, rfl⟩
    · simp only [e, Bool.false_eq_true, if_false]
      exact ih (i + 1) (by omega) (by omega)

theorem constNamed_none {cs : List IConstantInfo} {x : NIdx} (h : fndV (cs.map (·.name)) x 0 = 0) :
    constNamed? cs x = none := by
  have := (constNamed_fnd cs x cs.length 0 (by omega) (Nat.zero_le _)).1 h
  simpa [constNamed?] using this

theorem constNamed_some {cs : List IConstantInfo} {x : NIdx} {j : Nat} (h : fndV (cs.map (·.name)) x 0 = j + 1) :
    ∃ hj : j < cs.length, constNamed? cs x = some cs[j] := by
  obtain ⟨hj, e⟩ := (constNamed_fnd cs x cs.length 0 (by omega) (Nat.zero_le _)).2 j h
  exact ⟨hj, by simpa [constNamed?] using e⟩

def fdB := ofString "fd_b"
def fdI := ofString "fd_i"
def fdN := ofString "fd_n"
def fdX := ofString "fd_x"
def fdP := ofString "fd_p"
def fdY := ofString "fd_y"
def fdR := ofString "fd_r"
def fFnd := ofString "nameFind"

def fndParams : List MlS := [fdB, fdI, fdN, fdX]
def fndLocals : List MlS := [fdP, fdY, fdR]

def fndBody : ProgHOL 64 := prologue fndLocals
  (.ite (.cmp .lower (vv fdI) (vv fdN))
    (.seq (.assign .local fdP (.load .one (.op .add [vv fdB, .op .add [.panop .mul [vv fdI, .const 8], .const 8]])))
    (.seq (.assign .local fdY (.load .one (.op .add [vv fdP, .const 8])))
    (.ite (.cmp .equal (vv fdY) (vv fdX)) (.return (.op .add [vv fdI, .const 1]))
      (.seq (.call (some (some (.local, fdR), none)) fFnd [vv fdB, .op .add [vv fdI, .const 1], vv fdN, vv fdX])
        (.return (vv fdR))))))
    (.return (.const 0)))

/-! ## The renaming and the comparison -/

def sgK := ofString "sg_k"
def sgV := ofString "sg_v"
def sgJ := ofString "sg_j"
def sgM := ofString "sg_m"
def sgX := ofString "sg_x"
def sgY := ofString "sg_y"
def sgR := ofString "sg_r"
def fSgo := ofString "substGoH"

def sgoParams : List MlS := [sgK, sgV, sgJ, sgM, sgX]
def sgoLocals : List MlS := [sgY, sgR]

def sgoBody : ProgHOL 64 := prologue sgoLocals
  (.ite (.cmp .lower (vv sgJ) (vv sgM))
    (.seq (.assign .local sgY (.load .one (.op .add [vv sgK, .op .add [.panop .mul [vv sgJ, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv sgY) (vv sgX))
      (.seq (.assign .local sgY (.load .one (.op .add [vv sgV, .op .add [.panop .mul [vv sgJ, .const 8], .const 8]])))
        (.return (vv sgY)))
      (.seq (.call (some (some (.local, sgR), none)) fSgo [vv sgK, vv sgV, .op .add [vv sgJ, .const 1], vv sgM, vv sgX])
        (.return (vv sgR)))))
    (.return (vv sgX)))

def lnC := ofString "lg_c"
def lnD := ofString "lg_d"
def lnR := ofString "lg_r"
def lnS := ofString "lg_s"
def lnI := ofString "lg_i"
def lnN := ofString "lg_n"
def lnY := ofString "lg_y"
def lnZ := ofString "lg_z"
def lnW := ofString "lg_w"
def fLgo := ofString "pinLinkGo"

def lgoParams : List MlS := [lnC, lnD, lnR, lnS, lnI, lnN]
def lgoLocals : List MlS := [lnY, lnZ, lnW]

/-- `C[i..] == Cp[i..].map (goH Rp R)` (lists at `c`, `d`, `r`, `s`; `n` the common length). -/
def lgoBody : ProgHOL 64 := prologue lgoLocals
  (.ite (.cmp .lower (vv lnI) (vv lnN))
    (.seq (.assign .local lnY (.load .one (.op .add [vv lnD, .op .add [.panop .mul [vv lnI, .const 8], .const 8]])))
    (.seq (.assign .local lnW (.load .one (vv lnS)))
    (.seq (.call (some (some (.local, lnZ), none)) fSgo [vv lnS, vv lnR, .const 0, vv lnW, vv lnY])
    (.seq (.assign .local lnW (.load .one (.op .add [vv lnC, .op .add [.panop .mul [vv lnI, .const 8], .const 8]])))
    (.ite (.cmp .notEqual (vv lnW) (vv lnZ)) (.return (.const 0))
      (.seq (.call (some (some (.local, lnZ), none)) fLgo
          [vv lnC, vv lnD, vv lnR, vv lnS, .op .add [vv lnI, .const 1], vv lnN])
        (.return (vv lnZ))))))))
    (.return (.const 1)))


def rlP := ofString "rl_p"
def rlJ := ofString "rl_j"
def rlM := ofString "rl_m"
def rlR := ofString "rl_r"
def rlS := ofString "rl_s"
def rlB := ofString "rl_b"
def rlQ := ofString "rl_q"
def rlN := ofString "rl_n"
def rlA := ofString "rl_a"
def rlX := ofString "rl_x"
def rlC := ofString "rl_c"
def rlD := ofString "rl_d"
def rlE := ofString "rl_e"
def rlF := ofString "rl_f"
def rlY := ofString "rl_y"
def fRll := ofString "pinRulesLink"

def rllParams : List MlS := [rlP, rlJ, rlM, rlR, rlS, rlB, rlQ, rlN]
def rllLocals : List MlS := [rlA, rlX, rlC, rlD, rlE, rlF, rlY]

/-- The pinned recursor's rules from `j` (block at `p`): each rule's constructor found in the stream block (`b`)
and the pin (`q`), its level parameters linked through the recursors' (`r`, `s`); a miss or mismatch hangs. -/
def rllBody : ProgHOL 64 := prologue rllLocals
  (.ite (.cmp .lower (vv rlJ) (vv rlM))
    (.seq (.assign .local rlA (.load .one (.op .add [vv rlP, .op .add [.panop .mul [vv rlJ, .const 8], .const 8]])))
    (.seq (.assign .local rlX (.load .one (vv rlA)))
    (.seq (.call (some (some (.local, rlA), none)) fFnd [vv rlB, .const 0, vv rlN, vv rlX])
    (.ite (.cmp .equal (vv rlA) (.const 0)) hang
    (.seq (.call (some (some (.local, rlC), none)) fFnd [vv rlQ, .const 0, vv rlN, vv rlX])
    (.ite (.cmp .equal (vv rlC) (.const 0)) hang
    (.seq (.assign .local rlD (.load .one (.op .add [vv rlB, .panop .mul [vv rlA, .const 8]])))
    (.seq (.assign .local rlD (.load .one (.op .add [vv rlD, .const 16])))
    (.seq (.assign .local rlE (.load .one (.op .add [vv rlQ, .panop .mul [vv rlC, .const 8]])))
    (.seq (.assign .local rlE (.load .one (.op .add [vv rlE, .const 16])))
    (.seq (.assign .local rlF (.load .one (vv rlD)))
    (.seq (.assign .local rlY (.load .one (vv rlE)))
    (.ite (.cmp .notEqual (vv rlF) (vv rlY)) hang
    (.seq (.call (some (some (.local, rlY), none)) fLgo [vv rlD, vv rlE, vv rlR, vv rlS, .const 0, vv rlF])
    (.ite (.cmp .equal (vv rlY) (.const 0)) hang
    (.seq (.call (some (some (.local, rlY), none)) fRll
        [vv rlP, .op .add [vv rlJ, .const 1], vv rlM, vv rlR, vv rlS, vv rlB, vv rlQ, vv rlN])
      (.return (.const 1))))))))))))))))))
    (.return (.const 1)))

def blB := ofString "bl_b"
def blQ := ofString "bl_q"
def blI := ofString "bl_i"
def blN := ofString "bl_n"
def blF := ofString "bl_f"
def blC := ofString "bl_c"
def blP := ofString "bl_p"
def blT := ofString "bl_t"
def blX := ofString "bl_x"
def blY := ofString "bl_y"
def blR := ofString "bl_r"
def blS := ofString "bl_s"
def fBll := ofString "pinBlockLinks"

def bllParams : List MlS := [blB, blQ, blI, blN, blF]
def bllLocals : List MlS := [blC, blP, blT, blX, blY, blR, blS]

/-- The rest of the pairs. -/
def bllTail : ProgHOL 64 :=
  .seq (.call (some (some (.local, blX), none)) fBll [vv blB, vv blQ, .op .add [vv blI, .const 1], vv blN, vv blF])
    (.return (.const 1))

/-- A constructor's pair: its level parameters are the former's (else hang). -/
def bllCtor : ProgHOL 64 :=
  .seq (.assign .local blX (.load .one (.op .add [vv blC, .const 16])))
    (.seq (.call (some (some (.local, blY), none)) fLpsEq [vv blX, vv blF])
      (.ite (.cmp .equal (vv blY) (.const 0)) hang bllTail))

/-- A recursor pair: as many level parameters (else hang), then the pinned rules' links. -/
def bllRec : ProgHOL 64 :=
  .seq (.assign .local blR (.load .one (.op .add [vv blC, .const 16])))
  (.seq (.assign .local blS (.load .one (.op .add [vv blP, .const 16])))
  (.seq (.assign .local blX (.load .one (vv blR)))
  (.seq (.assign .local blY (.load .one (vv blS)))
  (.ite (.cmp .notEqual (vv blX) (vv blY)) hang
  (.seq (.assign .local blX (.load .one (.op .add [vv blP, .const 56])))
  (.seq (.assign .local blY (.load .one (vv blX)))
  (.seq (.call (some (some (.local, blX), none)) fRll
      [vv blX, .const 0, vv blY, vv blR, vv blS, vv blB, vv blQ, vv blN])
    bllTail)))))))

/-- The block's pairs from `i` (stream block at `b`, pin at `q`, the former's level parameters at `f`). -/
def bllBody : ProgHOL 64 := prologue bllLocals
  (.ite (.cmp .lower (vv blI) (vv blN))
    (.seq (.assign .local blC (.load .one (.op .add [vv blB, .op .add [.panop .mul [vv blI, .const 8], .const 8]])))
    (.seq (.assign .local blP (.load .one (.op .add [vv blQ, .op .add [.panop .mul [vv blI, .const 8], .const 8]])))
    (.seq (.assign .local blT (.load .one (vv blC)))
    (.ite (.cmp .equal (vv blT) (.const 4)) bllCtor
      (.ite (.cmp .equal (vv blT) (.const 5))
        (.seq (.assign .local blT (.load .one (vv blP)))
          (.ite (.cmp .equal (vv blT) (.const 5)) bllRec bllTail))
        bllTail)))))
    (.return (.const 1)))

/-- The links' code. -/
structure PLCodes (C : Ctx) : Prop where
  fnd : C.code.lookup fFnd = some (fndParams.map (fun p => (p, ShapeHOL.one)), fndBody, .one)
  sgo : C.code.lookup fSgo = some (sgoParams.map (fun p => (p, ShapeHOL.one)), sgoBody, .one)
  lgo : C.code.lookup fLgo = some (lgoParams.map (fun p => (p, ShapeHOL.one)), lgoBody, .one)
  rll : C.code.lookup fRll = some (rllParams.map (fun p => (p, ShapeHOL.one)), rllBody, .one)
  bll : C.code.lookup fBll = some (bllParams.map (fun p => (p, ShapeHOL.one)), bllBody, .one)
  leg : C.code.lookup fLpsEqGo = some (legParams.map (fun p => (p, ShapeHOL.one)), legBody, .one)
  le : C.code.lookup fLpsEq = some (leParams.map (fun p => (p, ShapeHOL.one)), leBody, .one)

section
variable {σ : Type}

/-- A word-returning procedure's post at a `Nat` answer. -/
def PostNv (C : Ctx) (n : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = BitVec.ofNat 64 n ∧ SR (ctxH C H') s' st

theorem postNv_locals (C : Ctx) : ∀ (a : Nat) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNv C a w s' st → PostNv C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hs⟩ => ⟨H', hp, hw, sr_of_eq hs rfl rfl rfl rfl⟩

/-- A handle-returning procedure's post. -/
def PostNI (C : Ctx) (n : NIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW n ∧ SR (ctxH C H') s' st

theorem postNI_locals (C : Ctx) : ∀ (a : NIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNI C a w s' st → PostNI C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hs⟩ => ⟨H', hp, hw, sr_of_eq hs rfl rfl rfl rfl⟩

theorem fnd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fndLocals → (ctxEnv C ++ fndParams.zip vals).get x = none :=
  Knot.params_none C fndLocals fndParams vals (by decide) (by decide)

theorem sgo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ sgoLocals → (ctxEnv C ++ sgoParams.zip vals).get x = none :=
  Knot.params_none C sgoLocals sgoParams vals (by decide) (by decide)

theorem lgo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lgoLocals → (ctxEnv C ++ lgoParams.zip vals).get x = none :=
  Knot.params_none C lgoLocals lgoParams vals (by decide) (by decide)

/-- **`nameFind`**: the first record from `i` named `x`. -/
theorem fnd_spec (C : Ctx) (hc : C.code.lookup fFnd = some (fndParams.map (fun p => (p, ShapeHOL.one)), fndBody, .one))
    (xs : List NIdx) (ob : Nat) (x : NIdx) (hl : xs.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → NamesAt C H ob xs → xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (fndParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length,
          Enc.idxW x])) fndBody s (pure (fndV xs x i)) (PostNv (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hpH hn hf hi
    have hil : i = xs.length := by omega
    subst hil
    refine specR_prologue (postNv_locals _) (fnd_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, fndParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [fndV_stop]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hpH hn hf hi
    have hil : i < xs.length := by omega
    refine specR_prologue (postNv_locals _) (fnd_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, fndParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨o, ho, hnm⟩ := hn.2 i hil
    refine UD.specR_heapLoadI' (C := ctxH C H) fdP _ (ob + 1 + i) _ ho (by decide)
      (by simp +decide [sev, Env.get, fndParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) fdY _ (o + 1) _ hnm (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C o) ?_
    simp only [fndV_step xs x i hil]
    by_cases e : xs[i] = x
    · subst e
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, fndParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, if_true]
      exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons, Env.get, fndParams, ctxEnv]; exact e_succ i)
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get_cons, Env.get, fndParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact fun h => e (Enc.idxW_inj h)) (fun h => absurd rfl h) (fun _ => ?_)
      have : (xs[i] == x) = false := by simpa using e
      simp only [this, Bool.false_eq_true, if_false]
      refine specR_congr (m' := (pure (fndV xs x (i + 1)) : AM Nat) >>= fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) fdR fFnd fndParams
        [vv fdB, .op .add [vv fdI, .const 1], vv fdN, vv fdX] fndBody
        [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length, Enc.idxW x]
        (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, fndParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, fndParams, ctxEnv]; exact e_succ i,
          by simp +decide [sev, Env.get_cons, Env.get, fndParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, fndParams, ctxEnv], trivial⟩
        (PostNv (ctxH C H)) (fun b w _ _ => w = BitVec.ofNat 64 b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fndParams _ rfl hlk)
          (ih (i + 1) H s hpH hn (by omega) (by omega)))
        (fun b w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem goH_stop (ks vs : List NIdx) (x : NIdx) (j : Nat) (hj : ks.length ≤ j) :
    goH (ks.drop j) (vs.drop j) x = x := by
  rw [List.drop_eq_nil_of_le hj]; cases vs.drop j <;> rfl

theorem goH_step (ks vs : List NIdx) (x : NIdx) (j : Nat) (hj : j < ks.length) (hv : j < vs.length) :
    goH (ks.drop j) (vs.drop j) x = if ks[j] == x then vs[j] else goH (ks.drop (j + 1)) (vs.drop (j + 1)) x := by
  rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons hv]; rfl

/-- **`substGoH`**: `goH` from index `j`. -/
theorem sgo_spec (C : Ctx) (hc : C.code.lookup fSgo = some (sgoParams.map (fun p => (p, ShapeHOL.one)), sgoBody, .one))
    (ks vs : List NIdx) (ok ov : Nat) (x : NIdx) (hl : ks.length < 2 ^ 59) (hkv : ks.length ≤ vs.length) :
    ∀ f j (H : List (BitVec 64)) (s : AState), C.H <+: H → EBlk H ok (ks.map Enc.idxW) → EBlk H ov (vs.map Enc.idxW) →
      ks.length - j = f → j ≤ ks.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (sgoParams.zip [cellA C ok, cellA C ov, BitVec.ofNat 64 j,
          BitVec.ofNat 64 ks.length, Enc.idxW x])) sgoBody s (pure (goH (ks.drop j) (vs.drop j) x))
        (PostNI (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j H s hpH hk hv hf hj
    have hjl : j = ks.length := by omega
    subst hjl
    refine specR_prologue (postNI_locals _) (sgo_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ks.length ks.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, sgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [goH_stop ks vs x _ (le_refl _)]
    exact specR_returnI _ _ (by simp +decide [sev, Env.get, sgoParams, ctxEnv])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hpH hk hv hf hj
    have hjl : j < ks.length := by omega
    have hjv : j < vs.length := by omega
    refine specR_prologue (postNI_locals _) (sgo_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j ks.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, sgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hkj := hk.2 j (by simpa using hjl)
    simp only [List.getElem_map] at hkj
    refine UD.specR_heapLoadI' (C := ctxH C H) sgY _ (ok + 1 + j) _ hkj (by decide)
      (by simp +decide [sev, Env.get, sgoParams, ctxEnv]; exact cellA_mulIdx C ok j (by omega)) ?_
    simp only [goH_step ks vs x j hjl hjv]
    by_cases e : ks[j] = x
    · subst e
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, if_true]
      have hvj := hv.2 j (by simpa using hjv)
      simp only [List.getElem_map] at hvj
      refine UD.specR_heapLoadI' (C := ctxH C H) sgY _ (ov + 1 + j) _ hvj (by decide)
        (by simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv]; exact cellA_mulIdx C ov j (by omega)) ?_
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact fun h => e (Enc.idxW_inj h)) (fun h => absurd rfl h) (fun _ => ?_)
      have : (ks[j] == x) = false := by simpa using e
      simp only [this, Bool.false_eq_true, if_false]
      refine specR_congr (m' := (pure (goH (ks.drop (j + 1)) (vs.drop (j + 1)) x) : AM NIdx) >>= fun b => pure b)
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H) sgR fSgo sgoParams
        [vv sgK, vv sgV, .op .add [vv sgJ, .const 1], vv sgM, vv sgX] sgoBody
        [cellA C ok, cellA C ov, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 ks.length, Enc.idxW x]
        (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv]; exact e_succ j,
          by simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, sgoParams, ctxEnv], trivial⟩
        (PostNI (ctxH C H)) (fun b w _ _ => w = Enc.idxW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sgoParams _ rfl hlk)
          (ih (j + 1) H s hpH hk hv (by omega) (by omega)))
        (fun b w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


theorem list_beq_cons (a b : NIdx) (as bs : List NIdx) : ((a :: as) == (b :: bs)) = (a == b && as == bs) := rfl

/-- **`pinLinkGo`**: `C[i..] == Cp[i..].map (goH Rp R)`. -/
theorem lgo_spec (C : Ctx) (hcs : C.code.lookup fSgo = some (sgoParams.map (fun p => (p, ShapeHOL.one)), sgoBody, .one))
    (hc : C.code.lookup fLgo = some (lgoParams.map (fun p => (p, ShapeHOL.one)), lgoBody, .one))
    (cs cps rs rps : List NIdx) (oc od orr ors : Nat) (hlen : cs.length = cps.length) (hl : cs.length < 2 ^ 59)
    (hrl : rps.length ≤ rs.length) (hrl2 : rps.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → EBlk H oc (cs.map Enc.idxW) →
      EBlk H od (cps.map Enc.idxW) → EBlk H orr (rs.map Enc.idxW) → EBlk H ors (rps.map Enc.idxW) →
      cs.length - i = f → i ≤ cs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (lgoParams.zip [cellA C oc, cellA C od, cellA C orr, cellA C ors,
          BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length])) lgoBody s
        (pure ((cs.drop i) == (cps.drop i).map (goH rps rs))) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hpH hc1 hc2 hc3 hc4 hf hi
    have hil : i = cs.length := by omega
    subst hil
    refine specR_prologue (postB_locals _) (lgo_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff cs.length cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, lgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    have e : ((cs.drop cs.length) == (cps.drop cs.length).map (goH rps rs)) = true := by
      rw [List.drop_length, hlen, List.drop_length]; rfl
    rw [e]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hpH hc1 hc2 hc3 hc4 hf hi
    have hil : i < cs.length := by omega
    have hil' : i < cps.length := by omega
    refine specR_prologue (postB_locals _) (lgo_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, lgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h2 := hc2.2 i (by simpa using hil')
    simp only [List.getElem_map] at h2
    refine UD.specR_heapLoadI' (C := ctxH C H) lnY _ (od + 1 + i) _ h2 (by decide)
      (by simp +decide [sev, Env.get, lgoParams, ctxEnv]; exact cellA_mulIdx C od i (by omega)) ?_
    have h4 : H[ors]? = some (BitVec.ofNat 64 rps.length) := by simpa using hc4.1
    refine UD.specR_heapLoadI' (C := ctxH C H) lnW _ ors _ h4 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv] <;> rfl) ?_
    refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H) lnZ fSgo sgoParams
      [vv lnS, vv lnR, .const 0, vv lnW, vv lnY] sgoBody
      [cellA C ors, cellA C orr, BitVec.ofNat 64 0, BitVec.ofNat 64 rps.length, Enc.idxW cps[i]]
      (goH (rps.drop 0) (rs.drop 0) cps[i]) (by decide) rfl (by decide) hcs
      ⟨by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostNI (ctxH C H)) (fun b w _ _ => w = Enc.idxW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sgoParams _ rfl hlk)
        (sgo_spec C hcs rps rs ors orr cps[i] hrl2 hrl _ 0 H s hpH hc4 hc3 rfl (Nat.zero_le _)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    have hp1' : C.H <+: H1 := hpH.trans hp1
    have h1 := hc1.2 i (by simpa using hil)
    simp only [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H1) lnW _ (oc + 1 + i) _ (get_prefix h1 hp1) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv]; exact cellA_mulIdx C oc i (by omega)) ?_
    simp only [List.drop_zero]
    rw [List.drop_eq_getElem_cons hil, List.drop_eq_getElem_cons hil', List.map_cons, list_beq_cons]
    by_cases e : cs[i] = goH rps rs cps[i]
    · refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [e, beq_self_eq_true, Bool.true_and]
      refine specR_congr (m' := (pure ((cs.drop (i + 1)) == (cps.drop (i + 1)).map (goH rps rs)) : AM Bool) >>=
        fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) lnZ fLgo lgoParams
        [vv lnC, vv lnD, vv lnR, vv lnS, .op .add [vv lnI, .const 1], vv lnN] lgoBody
        [cellA C oc, cellA C od, cellA C orr, cellA C ors, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length]
        (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv]; exact e_succ i,
          by simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv], trivial⟩
        (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lgoParams _ rfl hlk)
          (ih (i + 1) H1 s hp1' (eblk_mono hc1 hp1) (eblk_mono hc2 hp1) (eblk_mono hc3 hp1) (eblk_mono hc4 hp1)
            (by omega) (by omega)))
        (fun b w s1 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get_cons, Env.get, lgoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact fun h => e (Enc.idxW_inj h)) (fun _ => ?_) (fun h => absurd h (by decide))
      have : (cs[i] == goH rps rs cps[i]) = false := by simpa using e
      rw [this, Bool.false_and]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- The post of a procedure that hangs unless its verdict holds and moves only the caches. -/
def PostPinS {α : Type} (C : Ctx) (s0 : AState) (P : α → Prop) (a : α) (_ : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  P a ∧ s'.store = s0.store ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postPinS_locals {α : Type} (C : Ctx) (s0 : AState) (P : α → Prop) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostPinS C s0 P a w s' st → PostPinS C s0 P a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, h1, H', h2, h3⟩ => ⟨h0, h1, H', h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem pin_cellA_mul8 (C : Ctx) (o i : Nat) (hi : i < 2 ^ 61) :
    cellA C o + BitVec.ofNat 64 i * 8#64 = cellA C (o + i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem rll_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rllLocals → (ctxEnv C ++ rllParams.zip vals).get x = none :=
  Knot.params_none C rllLocals rllParams vals (by decide) (by decide)

theorem bll_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bllLocals → (ctxEnv C ++ bllParams.zip vals).get x = none :=
  Knot.params_none C bllLocals bllParams vals (by decide) (by decide)

theorem ne_zero_of_ofNat {n : Nat} (h : BitVec.ofNat 64 n ≠ 0) : n ≠ 0 := fun e => h (by rw [e]; rfl)

/-- A block constant's level parameters denote. -/
theorem lps_den_get {st : EStore} {blk : List IConstantInfo} {B : List ConLeche.ConstantInfo}
    (hB : Frontend.denoteCIList st blk = some B) (j : Nat) (hj : j < blk.length) :
    ∃ xs, Frontend.denoteNList st.ns blk[j].toConstantVal.levelParams = some xs := by
  obtain ⟨x, -, hx⟩ := denoteCIList_get blk B j blk[j] hB (List.getElem?_eq_getElem hj)
  exact ⟨_, (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hx)).2.1⟩

/-- A stream record's level-parameter block. -/
theorem cie_lps {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) :
    ∃ ol, H[o + 2]? = some (EB + BitVec.ofNat 64 (8 * ol)) ∧ EBlk H ol (ci.toConstantVal.levelParams.map Enc.idxW) := by
  obtain ⟨-, ⟨w, hw, ol, rfl, he⟩, -⟩ := h.1
  exact ⟨ol, by rw [show o + 2 = o + 1 + 1 by omega]; exact hw, he⟩

theorem pinRec_lps {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : PinRec EB H o ci) :
    ∃ ol, H[o + 2]? = some (EB + BitVec.ofNat 64 (8 * ol)) ∧ EBlk H ol (ci.toConstantVal.levelParams.map Enc.idxW) := by
  obtain ⟨-, ⟨w, hw, ol, rfl, he⟩, -⟩ := h.1
  exact ⟨ol, by rw [show o + 2 = o + 1 + 1 by omega]; exact hw, he⟩

set_option maxHeartbeats 16000000 in
/-- **The pinned recursor's rules from `j` link** (else hang): the twin's `rulesLinkOk`. -/
theorem rll_spec (C : Ctx) (hok : CtxOK C) (hc : PLCodes C) (blk pins : List IConstantInfo) (ob opb : Nat)
    (prs : List IRecRule) (orp : Nat) (R Rp : List NIdx) (orr ors : Nat)
    (hlen : blk.length = pins.length) (hbl : blk.length < 2 ^ 59) (hRR : R.length = Rp.length)
    (hRb : Rp.length < 2 ^ 59) (hprl : prs.length < 2 ^ 61)
    (hlb : ∀ c ∈ blk, c.toConstantVal.levelParams.length < 2 ^ 59)
    (hlpn : ∀ c ∈ pins, c.toConstantVal.levelParams.length < 2 ^ 59)
    (B P : List ConLeche.ConstantInfo) (rT rpT : List ConLeche.Name) :
    ∀ f j (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → PinBlk C H opb pins →
      PinRulesAt C H orp prs → EBlk H orr (R.map Enc.idxW) → EBlk H ors (Rp.map Enc.idxW) →
      Frontend.denoteCIList s.store blk = some B → Frontend.denoteCIList s.store pins = some P →
      Frontend.denoteNList s.store.ns R = some rT → Frontend.denoteNList s.store.ns Rp = some rpT →
      prs.length - j = f → j ≤ prs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (rllParams.zip [cellA C orp, BitVec.ofNat 64 j, BitVec.ofNat 64 prs.length,
          cellA C orr, cellA C ors, cellA C ob, cellA C opb, BitVec.ofNat 64 blk.length])) rllBody s
        (rulesLinkOk blk pins R Rp (prs.drop j)) (PostPinS (ctxH C H) s (fun b => b = true)) := by
  intro f
  induction f with
  | zero =>
    intro j H s hpH hblk hpb hpr hR hRp hB hP hrT hrpT hf hj
    have hjl : j = prs.length := by omega
    subst hjl
    refine specR_prologue (postPinS_locals _ _ _) (rll_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff prs.length prs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, rllParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, rulesLinkOk]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hpH hblk hpb hpr hR hRp hB hP hrT hrpT hf hj
    have hjl : j < prs.length := by omega
    refine specR_prologue (postPinS_locals _ _ _) (rll_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j prs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, rllParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨q, hq, hRq⟩ := hpr.2 j hjl
    refine UD.specR_heapLoadI' (C := ctxH C H) rlA _ (orp + 1 + j) _ hq (by decide)
      (by simp +decide [sev, Env.get, rllParams, ctxEnv]; exact cellA_mulIdx C orp j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rlX _ q _ hRq.1 (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    set x := prs[j].ctor with hx
    -- the constructor in the stream block
    refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H) rlA fFnd fndParams [vv rlB, .const 0, vv rlN, vv rlX]
      fndBody [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 (blk.map (·.name)).length, Enc.idxW x]
      (fndV (blk.map (·.name)) x 0) (by decide) rfl (by decide) hc.fnd
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostNv (ctxH C H)) (fun b w _ _ => w = BitVec.ofNat 64 b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fndParams _ rfl hlk)
        (fnd_spec C hc.fnd (blk.map (·.name)) ob x (by simp; omega) _ 0 H s hpH (namesAt_ind hblk) rfl
          (Nat.zero_le _)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    refine specR_guardZ rlA (BitVec.ofNat 64 (fndV (blk.map (·.name)) x 0)) (by simp +decide [Env.get_cons])
      (fun hz1 => ?_)
    obtain ⟨jc, hjc⟩ := Nat.exists_eq_succ_of_ne_zero (ne_zero_of_ofNat hz1)
    obtain ⟨hjcl, hcn1⟩ := constNamed_some hjc
    -- the constructor in the pin
    refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H1) rlC fFnd fndParams [vv rlQ, .const 0, vv rlN, vv rlX]
      fndBody [cellA C opb, BitVec.ofNat 64 0, BitVec.ofNat 64 (pins.map (·.name)).length, Enc.idxW x]
      (fndV (pins.map (·.name)) x 0) (by decide) rfl (by decide) hc.fnd
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv, hlen], by simp +decide [sev, Env.get_cons],
        trivial⟩
      (PostNv (ctxH C H1)) (fun b w _ _ => w = BitVec.ofNat 64 b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fndParams _ rfl hlk)
        (fnd_spec C hc.fnd (pins.map (·.name)) opb x (by simp; omega) _ 0 H1 s (hpH.trans hp1)
          (namesAt_pin (pinBlk_mono hpb hp1)) rfl (Nat.zero_le _)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    refine specR_guardZ rlC (BitVec.ofNat 64 (fndV (pins.map (·.name)) x 0)) (by simp +decide [Env.get_cons])
      (fun hz2 => ?_)
    obtain ⟨jp, hjp⟩ := Nat.exists_eq_succ_of_ne_zero (ne_zero_of_ofNat hz2)
    obtain ⟨hjpl, hcn2⟩ := constNamed_some hjp
    have hp02 : H <+: H2 := hp1.trans hp2
    -- the two constructors' level-parameter blocks
    obtain ⟨os, hosl, hosb, hosr⟩ := hblk
    obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hpb
    have hb1 := hosb.2 jc (by simp; omega)
    simp only [List.getElem_map] at hb1
    have hjc61 : jc + 1 < 2 ^ 61 := by omega
    have hjp61 : jp + 1 < 2 ^ 61 := by omega
    refine UD.specR_heapLoadI' (C := ctxH C H2) rlD _ (ob + 1 + jc) _ (get_prefix hb1 hp02) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv, hjc]
          rw [pin_cellA_mul8 C ob (jc + 1) hjc61, show ob + (jc + 1) = ob + 1 + jc by omega]; rfl) ?_
    obtain ⟨ocl, hocl, hecl⟩ := cie_lps (hosr jc hjcl (by rw [hosl]; exact hjcl))
    refine UD.specR_heapLoadI' (C := ctxH C H2) rlD _ (os[jc] + 2) _ (get_prefix hocl hp02) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C os[jc] 2) ?_
    have hb2 := hpsb.2 jp (by simp; omega)
    simp only [List.getElem_map] at hb2
    refine UD.specR_heapLoadI' (C := ctxH C H2) rlE _ (opb + 1 + jp) _ (get_prefix hb2 hp02) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv, hjp]
          rw [pin_cellA_mul8 C opb (jp + 1) hjp61, show opb + (jp + 1) = opb + 1 + jp by omega]; rfl) ?_
    obtain ⟨opl, hopl, hepl⟩ := pinRec_lps (hpsr jp hjpl (by rw [hpsl]; exact hjpl))
    refine UD.specR_heapLoadI' (C := ctxH C H2) rlE _ (ps[jp] + 2) _ (get_prefix hopl hp02) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ps[jp] 2) ?_
    set Cl := blk[jc].toConstantVal.levelParams with hCl
    set Cpl := pins[jp].toConstantVal.levelParams with hCpl
    have hcl59 : Cl.length < 2 ^ 59 := hlb _ (List.getElem_mem hjcl)
    have hcpl59 : Cpl.length < 2 ^ 59 := hlpn _ (List.getElem_mem hjpl)
    refine UD.specR_heapLoadI' (C := ctxH C H2) rlF _ ocl _ (by simpa [ctxH] using get_prefix hecl.1 hp02) (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) rlY _ opl _ (by simpa [ctxH] using get_prefix hepl.1 hp02) (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    refine specR_guardNe rlF rlY (BitVec.ofNat 64 Cl.length) (BitVec.ofNat 64 Cpl.length)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun ecl => ?_)
    have ecl' : Cl.length = Cpl.length := natW_inj (by omega) (by omega) ecl
    -- the comparison
    refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H2) rlY fLgo lgoParams
      [vv rlD, vv rlE, vv rlR, vv rlS, .const 0, vv rlF] lgoBody
      [cellA C ocl, cellA C opl, cellA C orr, cellA C ors, BitVec.ofNat 64 0, BitVec.ofNat 64 Cl.length]
      ((Cl.drop 0) == (Cpl.drop 0).map (goH Rp R)) (by decide) rfl (by decide) hc.lgo
      ⟨by simp +decide [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons]; rfl,
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lgoParams _ rfl hlk)
        (lgo_spec C hc.sgo hc.lgo Cl Cpl R Rp ocl opl orr ors ecl' hcl59 (by omega) hRb _ 0 H2 s (hpH.trans hp02)
          (eblk_mono hecl hp02) (eblk_mono hepl hp02) (eblk_mono hR hp02) (eblk_mono hRp hp02) rfl (Nat.zero_le _)))
      (fun w H3 hp3 hw => ?_)
    subst hw
    refine specR_guardZ rlY (boolW ((Cl.drop 0) == (Cpl.drop 0).map (goH Rp R))) (by simp +decide [Env.get_cons])
      (fun hz3 => ?_)
    have hv : (Cl == Cpl.map (goH Rp R)) = true := by
      simp only [List.drop_zero] at hz3
      cases e : (Cl == Cpl.map (goH Rp R))
      · rw [e] at hz3; exact absurd rfl hz3
      · rfl
    -- the twin: the rule's links, read off the names
    rw [List.drop_eq_getElem_cons hjl]
    simp only [rulesLinkOk, ← hx, hcn1, hcn2]
    unfold pinLinkOk
    simp only [bind_assoc]
    obtain ⟨cT, hcT⟩ := lps_den_get hB jc hjcl
    obtain ⟨cpT, hcpT⟩ := lps_den_get hP jp hjpl
    refine specR_atEntry fun t0 ht0 => ?_
    have hwf : StoreWF s.store := (sr_stateOK ht0.sr).wf
    refine specR_readNamesI _ _ hrT (fun c1 => ?_)
    refine specR_readNamesI _ _ hrpT (fun c2 => ?_)
    refine specR_readNamesI _ _ hcT (fun c3 => ?_)
    refine specR_readNamesI _ _ hcpT (fun c4 => ?_)
    rw [pure_bind, pinLink_val hwf hrT hrpT hcT hcpT, hv, if_pos rfl]
    have hp03 : H <+: H3 := hp02.trans hp3
    refine specR_congr (m' := rulesLinkOk blk pins R Rp (prs.drop (j + 1)) >>= fun b => pure b) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) rlY fRll rllParams
      [vv rlP, .op .add [vv rlJ, .const 1], vv rlM, vv rlR, vv rlS, vv rlB, vv rlQ, vv rlN] rllBody
      [cellA C orp, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 prs.length, cellA C orr, cellA C ors, cellA C ob,
        cellA C opb, BitVec.ofNat 64 blk.length] (by decide) rfl (by decide) hc.rll
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv]; exact e_succ j,
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rllParams, ctxEnv], trivial⟩
      (PostPinS (ctxH C H3) (withC (withC (withC (withC s c1) c2) c3) c4) (fun b => b = true))
      (fun b _ s' _ => b = true ∧ s'.store = s.store)
      (fun a w s' st ⟨h0, h1, H', hp', hsr⟩ => ⟨H', hp', ⟨h0, h1⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rllParams _ rfl hlk)
        (ih (j + 1) H3 _ (hpH.trans hp03) ⟨os, hosl, blkAt_mono hosb hp03, fun i hi ho => cie_mono hp03 (hosr i hi ho)⟩
          (pinBlk_mono ⟨ps, hpsl, hpsb, hpsr⟩ hp03) (pinRulesAt_mono hp03 hpr) (eblk_mono hR hp03)
          (eblk_mono hRp hp03) hB hP hrT hrpT (by omega) (by omega)))
      (fun b w s5 H5 hp5 ⟨hb5, hs5⟩ => ?_)
    subst hb5
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, hs5, H5, hp03.trans hp5, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


set_option maxHeartbeats 16000000 in
/-- **The block's pairs from `i` link** (else hang): the twin's `blockLinksOkGo`. -/
theorem bll_spec (C : Ctx) (hok : CtxOK C) (hc : PLCodes C) (blk pins : List IConstantInfo) (ob opb ofm : Nat)
    (former : List NIdx) (hlen : blk.length = pins.length) (hbl : blk.length < 2 ^ 59)
    (hfm : former.length < 2 ^ 59)
    (hlb : ∀ c ∈ blk, c.toConstantVal.levelParams.length < 2 ^ 59)
    (hlpn : ∀ c ∈ pins, c.toConstantVal.levelParams.length < 2 ^ 59)
    (B P : List ConLeche.ConstantInfo) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → PinBlk C H opb pins →
      EBlk H ofm (former.map Enc.idxW) →
      Frontend.denoteCIList s.store blk = some B → Frontend.denoteCIList s.store pins = some P →
      blk.length - i = f → i ≤ blk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (bllParams.zip [cellA C ob, cellA C opb, BitVec.ofNat 64 i,
          BitVec.ofNat 64 blk.length, cellA C ofm])) bllBody s
        (blockLinksOkGo blk pins former (blk.drop i) (pins.drop i)) (PostPinS (ctxH C H) s (fun b => b = true)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hpH hblk hpb hfmb hB hP hf hi
    have hil : i = blk.length := by omega
    subst hil
    refine specR_prologue (postPinS_locals _ _ _) (bll_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff blk.length blk.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, bllParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, blockLinksOkGo]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hpH hblk hpb hfmb hB hP hf hi
    have hil : i < blk.length := by omega
    have hilp : i < pins.length := by omega
    refine specR_prologue (postPinS_locals _ _ _) (bll_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i blk.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, bllParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    -- the tail, from any branch
    have htail : ∀ (Γ' : Env) (H' : List (BitVec 64)) (s' : AState), H <+: H' → s'.store = s.store →
        Γ'.get blB = some (cellA C ob) → Γ'.get blQ = some (cellA C opb) → Γ'.get blI = some (BitVec.ofNat 64 i) →
        Γ'.get blN = some (BitVec.ofNat 64 blk.length) → Γ'.get blF = some (cellA C ofm) →
        SpecR (σ := σ) (Inv (ctxH C H') s' Γ' [] (ctxLocals ++ bllLocals)) bllTail s'
          (blockLinksOkGo blk pins former (blk.drop (i + 1)) (pins.drop (i + 1)))
          (PostPinS (ctxH C H) s (fun b => b = true)) := by
      intro Γ' H' s' hp' hs' g1 g2 g3 g4 g5
      unfold bllTail
      refine specR_congr (m' := blockLinksOkGo blk pins former (blk.drop (i + 1)) (pins.drop (i + 1)) >>=
        fun b => pure b) (by simp) ?_
      refine specR_callNIH (C := ctxH C H') blX fBll bllParams
        [vv blB, vv blQ, .op .add [vv blI, .const 1], vv blN, vv blF] bllBody
        [cellA C ob, cellA C opb, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 blk.length, cellA C ofm]
        (by decide) rfl (by decide) hc.bll
        ⟨by simp [sev, g1], by simp [sev, g2], by simp [sev, g3]; exact e_succ i, by simp [sev, g4],
          by simp [sev, g5], trivial⟩
        (PostPinS (ctxH C H') s' (fun b => b = true)) (fun b _ s2 _ => b = true ∧ s2.store = s'.store)
        (fun a w s2 st ⟨h0, h1, H2, hp2, hsr⟩ => ⟨H2, hp2, ⟨h0, h1⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bllParams _ rfl hlk)
          (ih (i + 1) H' s' (hpH.trans hp') (indBlk_mono hblk hp') (pinBlk_mono hpb hp') (eblk_mono hfmb hp')
            (by rw [hs']; exact hB) (by rw [hs']; exact hP) (by omega) (by omega)))
        (fun b w s2 H2 hp2 ⟨hb2, hs2⟩ => ?_)
      subst hb2
      exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, hs2.trans hs', H2, hp'.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    obtain ⟨os, hosl, hosb, hosr⟩ := hblk
    obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hpb
    have hb1 := hosb.2 i (by simp; omega)
    simp only [List.getElem_map] at hb1
    have hb2 := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hb2
    refine UD.specR_heapLoadI' (C := ctxH C H) blC _ (ob + 1 + i) _ hb1 (by decide)
      (by simp +decide [sev, Env.get, bllParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) blP _ (opb + 1 + i) _ hb2 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, bllParams, ctxEnv]; exact cellA_mulIdx C opb i (by omega)) ?_
    have hci := hosr i hil (by omega)
    have hpi := hpsr i hilp (by omega)
    refine UD.specR_heapLoadI' (C := ctxH C H) blT _ os[i] _ (cie_tag hci) (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    rw [List.drop_eq_getElem_cons hil, List.drop_eq_getElem_cons hilp]
    simp only [blockLinksOkGo]
    have hblkH : IndBlk C H ob blk := ⟨os, hosl, hosb, hosr⟩
    have hpbH : PinBlk C H opb pins := ⟨ps, hpsl, hpsb, hpsr⟩
    obtain ⟨ocl, hocl, hecl⟩ := cie_lps hci
    have hcl59 : blk[i].toConstantVal.levelParams.length < 2 ^ 59 := hlb _ (List.getElem_mem hil)
    generalize hci' : blk[i] = ci at hci hocl hecl hcl59
    generalize hpi' : pins[i] = pi at hpi
    cases ci with
    | ctorInfo cv nP nF T =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      unfold bllCtor
      refine UD.specR_heapLoadI' (C := ctxH C H) blX _ (os[i] + 2) _ hocl (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C os[i] 2) ?_
      refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H) blY fLpsEq leParams [vv blX, vv blF] leBody
        [cellA C ocl, cellA C ofm] (cv.levelParams == former) (by decide) rfl (by decide) hc.le
        ⟨by simp +decide [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons, Env.get, bllParams, ctxEnv],
          trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu leParams _ rfl hlk)
          (le_spec C hc.leg hc.le cv.levelParams former ocl ofm hcl59 hfm H s hpH hecl hfmb))
        (fun w H1 hp1 hw => ?_)
      subst hw
      refine specR_guardZ blY (boolW (cv.levelParams == former)) (by simp +decide [Env.get_cons]) (fun hz => ?_)
      have hv : (cv.levelParams == former) = true := by
        cases e : (cv.levelParams == former)
        · rw [e] at hz; exact absurd rfl hz
        · rfl
      simp only [blockLinkOkAt, hv, pure_bind, if_true]
      exact htail _ H1 s hp1 rfl (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
    | recInfo cv mI rP isK crs =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) blT _ ps[i] _ (pinRec_tag hpi) (by decide)
        (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
      cases pi with
      | recInfo cvp pmI prP pK prs =>
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        unfold bllRec
        obtain ⟨opl, hopl, hepl⟩ := pinRec_lps hpi
        have hpl59 : cvp.levelParams.length < 2 ^ 59 := by
          have := hlpn _ (List.getElem_mem hilp); rw [hpi'] at this; exact this
        refine UD.specR_heapLoadI' (C := ctxH C H) blR _ (os[i] + 2) _ hocl (by decide)
          (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C os[i] 2) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H) blS _ (ps[i] + 2) _ hopl (by decide)
          (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ps[i] 2) ?_
        have hcl59' : cv.levelParams.length < 2 ^ 59 := hcl59
        have hecl' : EBlk H ocl (cv.levelParams.map Enc.idxW) := hecl
        have hepl' : EBlk H opl (cvp.levelParams.map Enc.idxW) := hepl
        refine UD.specR_heapLoadI' (C := ctxH C H) blX _ ocl _ (by simpa [ctxH] using hecl'.1) (by decide)
          (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H) blY _ opl _ (by simpa [ctxH] using hepl'.1) (by decide)
          (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
        refine specR_guardNe blX blY (BitVec.ofNat 64 cv.levelParams.length) (BitVec.ofNat 64 cvp.levelParams.length)
          (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun ell => ?_)
        have ell' : cv.levelParams.length = cvp.levelParams.length := natW_inj (by omega) (by omega) ell
        obtain ⟨-, -, -, -, ⟨wpr, hwpr, hpr⟩⟩ := hpi.2
        obtain ⟨orp, rfl, hpr'⟩ := pinRulesAt_of hpr
        refine UD.specR_heapLoadI' (C := ctxH C H) blX _ (ps[i] + 7) _ hwpr (by decide)
          (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ps[i] 7) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H) blY _ orp _ hpr'.1 (by decide)
          (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
        refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
        have hprl := pinRulesAt_len hok hHN hpr'
        obtain ⟨rT, hrT⟩ : ∃ xs, Frontend.denoteNList s.store.ns cv.levelParams = some xs := by
          have := lps_den_get hB i hil; rw [hci'] at this; exact this
        obtain ⟨rpT, hrpT⟩ : ∃ xs, Frontend.denoteNList s.store.ns cvp.levelParams = some xs := by
          have := lps_den_get hP i hilp; rw [hpi'] at this; exact this
        simp only [blockLinkOkAt, bind_assoc]
        refine specR_callNIH (C := ctxH C H) blX fRll rllParams
          [vv blX, .const 0, vv blY, vv blR, vv blS, vv blB, vv blQ, vv blN] rllBody
          [cellA C orp, BitVec.ofNat 64 0, BitVec.ofNat 64 prs.length, cellA C ocl, cellA C opl, cellA C ob,
            cellA C opb, BitVec.ofNat 64 blk.length] (by decide) rfl (by decide) hc.rll
          ⟨by simp +decide [sev, Env.get_cons] <;> rfl, rfl, by simp +decide [sev, Env.get_cons],
            by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
            by simp +decide [sev, Env.get_cons, Env.get, bllParams, ctxEnv],
            by simp +decide [sev, Env.get_cons, Env.get, bllParams, ctxEnv],
            by simp +decide [sev, Env.get_cons, Env.get, bllParams, ctxEnv], trivial⟩
          (PostPinS (ctxH C H) s (fun b => b = true)) (fun b _ s2 _ => b = true ∧ s2.store = s.store)
          (fun a w s2 st ⟨h0, h1, H2, hp2, hsr⟩ => ⟨H2, hp2, ⟨h0, h1⟩, hsr⟩)
          (fun u hu _ hlk => by
            have := rll_spec (σ := σ) C hok hc blk pins ob opb prs orp cv.levelParams cvp.levelParams ocl opl hlen hbl
              ell' (by omega) (by omega) hlb hlpn B P rT rpT _ 0 H s hpH hblkH hpbH hpr' hecl' hepl' hB hP hrT hrpT rfl
              (Nat.zero_le _)
            rw [List.drop_zero] at this
            exact Knot.specR_of_pre u (pre_of_lookups hu rllParams _ rfl hlk) this)
          (fun b w s2 H2 hp2 ⟨hb2, hs2⟩ => ?_)
        subst hb2
        simp only [if_true]
        exact htail _ H2 s2 hp2 hs2 (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
      | _ =>
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        simp only [blockLinkOkAt, pure_bind, if_true]
        exact htail _ H s (List.prefix_refl _) rfl (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
    | _ =>
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [blockLinkOkAt, pure_bind, if_true]
      exact htail _ H s (List.prefix_refl _) rfl (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, bllParams, ctxEnv])

end

end ConPanqueque.T.Ind
