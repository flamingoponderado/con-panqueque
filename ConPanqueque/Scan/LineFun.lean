import ConPanqueque.Scan.RecEnds
import ConPanqueque.Scan.Line

/-! # The line loop in Pancake

Compiled from `lineTblP`: `lineTbl` with, per payload, a tag, the index kind it requires and, for a
record payload, the Pancake function that reads the record's end.  A record payload is kept as its
start position (`s0`); interning reads its fields again. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-- A payload key's action, Pancake side. -/
inductive LActP where
  | idxP (kind : UInt8)
  | natP (tag grp : Nat) (mk : Nat → LinePayload)
  | strP (tag grp : Nat) (mk : String → LinePayload)
  | objP (tag grp : Nat) (fn : MlS) (scan : ByteArray → USize → ScanRes LinePayload)

def LActP.toLAct : LActP → LAct
  | .idxP k => .idx k
  | .natP _ _ f => .natPl f
  | .strP _ _ f => .strPl f
  | .objP _ _ _ scan => .objPl scan

def fRecStr := ofString "recStrName"
def fRecNum := ofString "recNumName"
def fRecApp := ofString "recApp"
def fRecLam := ofString "recLam"
def fRecForall := ofString "recForall"
def fRecLet := ofString "recLet"
def fRecConst := ofString "recConst"
def fRecProj := ofString "recProj"
def fRecDef := ofString "recDef"
def fRecThm := ofString "recThm"
def fRecOpaque := ofString "recOpaque"

/-- The port's line table, Pancake side.  Groups: 1 names, 2 levels, 3 expressions, 0 declarations. -/
def lineTblP : List (Key × LActP) :=
  [(.kIn, .idxP 1), (.kIl, .idxP 2), (.kIe, .idxP 3),
   (.kBvar, .natP 1 3 (fun n => .expr (.bvar n))), (.kSort, .natP 2 3 (fun n => .expr (.sort n))),
   (.kSucc, .natP 3 2 (fun n => .level (.succ n))), (.kParam, .natP 4 2 (fun n => .level (.param n))),
   (.kStr, .objP 5 1 fRecStr nameStr), (.kNum, .objP 6 1 fRecNum nameNum),
   (.kApp, .objP 7 3 fRecApp exprApp), (.kLam, .objP 8 3 fRecLam exprLam),
   (.kForallE, .objP 9 3 fRecForall exprForall), (.kLetE, .objP 10 3 fRecLet exprLet),
   (.kConst, .objP 11 3 fRecConst exprConst), (.kProj, .objP 12 3 fRecProj exprProj),
   (.kStrVal, .strP 13 3 (fun s => .expr (.strVal s))),
   (.kDef, .objP 14 0 fRecDef declDef), (.kThm, .objP 15 0 fRecThm declThm), (.kOpaque, .objP 16 0 fRecOpaque declOpaque)]

theorem lineTblP_toLAct : lineTblP.map (fun e => (e.1, e.2.toLAct)) = lineTbl := rfl

def sIK := ofString "ik"
def sIdx := ofString "idx"
def sPl := ofString "pl"

/-- The payload actions' common ending: the payload's tag, then past the value. -/
def plAdvance (tag : Nat) : ProgHOL 64 :=
  .seq (.assign .local sPl (.const (BitVec.ofNat 64 tag)))
    (.seq (.assign .local sW (.const 0)) (.assign .local sI (vv sE2)))

def notAbsent : ExpHOL 64 := .cmp .notEqual (vv sPl) (.const 0)

def lineAct : LActP → ProgHOL 64
  | .idxP kind => .ite (.cmp .notEqual (vv sIK) (.const 0)) hang
      (.seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sV])
        (.ite (.cmp .equal (vv sE2) (vv sV)) hang
          (.ite (.cmp .lower (vv sI) (vv sE2))
            (.seq (callTo sIdx fReadNat [vv sB, vv sV, vv sE2])
              (.seq (.assign .local sIK (.const (BitVec.ofNat 64 kind.toNat)))
                (.seq (.assign .local sW (.const 0)) (.assign .local sI (vv sE2)))))
            hang)))
  | .natP tag _ _ => .ite notAbsent hang
      (.seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sV])
        (.ite (.cmp .equal (vv sE2) (vv sV)) hang
          (.ite (.cmp .lower (vv sI) (vv sE2))
            (.seq (callTo (slotName 0) fReadNat [vv sB, vv sV, vv sE2]) (plAdvance tag))
            hang)))
  | .strP tag _ _ => .ite notAbsent hang
      (.seq (callTo sE2 fStr [vv sB, vv sN, vv sV])
        (.seq (.assign .local sE2 (.op .add [vv sE2, .const 1]))
          (.ite (.cmp .lower (vv sI) (vv sE2))
            (.seq (.assign .local (slotName 0) (vv sV)) (plAdvance tag)) hang)))
  | .objP tag _ fn _ => .ite notAbsent hang
      (.seq (callTo sE2 fn [vv sB, vv sN, vv sV])
        (.ite (.cmp .lower (vv sI) (vv sE2))
          (.seq (.assign .local (slotName 0) (vv sV)) (plAdvance tag)) hang))

def lineDispatch : List (Key × LActP) → ProgHOL 64
  | [] => hang
  | (k, a) :: r => .ite (.cmp .equal (vv sKK) (.const (BitVec.ofNat 64 k.ctorIdx))) (lineAct a) (lineDispatch r)

def lineKeyPart : ProgHOL 64 :=
  .seq (callTo sK fKeyEnd [vv sB, vv sN, .op .add [vv sI, .const 1]])
    (.ite (.cmp .equal (vv sK) (.const 0)) hang
      (.seq (callTo sV fValueAt [vv sB, vv sN, vv sI, vv sK])
        (.ite (.cmp .equal (vv sV) (vv sI)) hang
          (.seq (callTo sKK fKeyAt [vv sB, vv sN, vv sI, .op .sub [vv sK, .op .add [vv sI, .const 1]]])
            (lineDispatch lineTblP)))))

/-- The tag's required index kind, for the closing brace. -/
def tagGroups : List (Nat × Nat) :=
  lineTblP.filterMap (fun e => match e.2 with
    | .idxP _ => none
    | .natP t g _ => some (t, g)
    | .strP t g _ => some (t, g)
    | .objP t g _ _ => some (t, g))

def endCheck : List (Nat × Nat) → ProgHOL 64
  | [] => hang
  | (t, g) :: r => .ite (.cmp .equal (vv sPl) (.const (BitVec.ofNat 64 t)))
      (.ite (.cmp .equal (vv sIK) (.const (BitVec.ofNat 64 g))) (.seq incI (.assign .local sG (.const 0))) hang)
      (endCheck r)

def lineBody : ProgHOL 64 :=
  .ite (.cmp .lower (vv sI) (vv sN))
    (.seq (.assign .local sC (.loadByte (.op .add [vv sB, vv sI])))
      (.ite wsTest incI
        (.ite (.cmp .equal (vv sC) (.const 125))
          (.ite (.op .and [vv sW, .op .or [.cmp .notEqual (vv sIK) (.const 0), notAbsent]]) hang
            (endCheck tagGroups))
          (.ite (.cmp .equal (vv sC) (.const 44))
            (.ite (vv sW) hang (.seq (.assign .local sW (.const 1)) incI))
            (.ite (.cmp .equal (vv sC) (.const 34)) (.ite (vv sW) lineKeyPart hang) hang)))))
    hang

def lineLoopP : ProgHOL 64 := .while (vv sG) lineBody

/-! ## The invariant -/

/-- How the payload's tag and `s0` stand for con-leche's payload. -/
def PlEntry (b : ByteArray) (wpl ws0 : BitVec 64) (pl : LinePayload) : LActP → Prop
  | .idxP _ => False
  | .natP t _ f => wpl = BitVec.ofNat 64 t ∧ ∃ n, pl = f n ∧ ws0 = BitVec.ofNat 64 (min n natCap)
  | .strP t _ f => wpl = BitVec.ofNat 64 t ∧ ∃ (v e : USize) (str : String), pl = f str ∧
      ws0 = BitVec.ofNat 64 v.toNat ∧ scanString b v = .ok str e
  | .objP t _ _ scan => wpl = BitVec.ofNat 64 t ∧ ∃ (v e : USize), scan b v = .ok pl e ∧
      ws0 = BitVec.ofNat 64 v.toNat

def PlOK (b : ByteArray) (wpl ws0 : BitVec 64) (pl : LinePayload) : Prop :=
  (pl = .absent ∧ wpl = 0) ∨ ∃ k a, (k, a) ∈ lineTblP ∧ PlEntry b wpl ws0 pl a

section
variable {σ : Type}

/-- A record function at its name, with its proved spec. -/
def RecCode (t : PanSemStateFiniteExact 64 σ) (fn : MlS) (scan : ByteArray → USize → ScanRes LinePayload) : Prop :=
  ∃ body, t.code.lookup fn = some ([(sB, .one), (sN, .one), (sI, .one)], body, .one) ∧
    ∀ (u : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (v : USize), Plat b →
      BytesAt u A b.data.toList → u.code = t.code → v.toNat ≤ b.size →
      u.locals.lookup sB = some (.val (.word A)) →
      u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))) →
      RetP u body (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧ ∃ r, scan b v = .ok r j)

/-- The code table the line scanner needs. -/
def LineCodes (t : PanSemStateFiniteExact 64 σ) : Prop :=
  ScanCodes t ∧ ∀ k tag g fn scan, (k, LActP.objP tag g fn scan) ∈ lineTblP → RecCode t fn scan

def LnI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (R : ScanRes LineRec)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) ∧
  (∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w))) ∧
  ∃ (j : USize) (wm : Bool) (ik : UInt8) (idx : Nat) (pl : LinePayload) (wpl ws0 : BitVec 64),
    j.toNat ≤ b.size + 64 ∧
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
    u.locals.lookup sW = some (.val (.word (bw (wm = true)))) ∧
    u.locals.lookup sIK = some (.val (.word (BitVec.ofNat 64 ik.toNat))) ∧
    u.locals.lookup sIdx = some (.val (.word (BitVec.ofNat 64 (min idx natCap)))) ∧
    u.locals.lookup sPl = some (.val (.word wpl)) ∧
    u.locals.lookup (slotName 0) = some (.val (.word ws0)) ∧
    PlOK b wpl ws0 pl ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ lineLoopI lineTbl b j wm ik idx pl = R) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ ∃ j0 rec, lineEnd j0 ik idx pl = .ok rec j ∧ R = .ok rec j))

end

end ConPanqueque.Scan
