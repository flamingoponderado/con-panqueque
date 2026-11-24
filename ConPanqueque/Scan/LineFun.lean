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
      RetP u body (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧ j.toNat ≤ b.size + 64 ∧
        ∃ r, scan b v = .ok r j)

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
     (u.locals.lookup sG = some (.val (.word 0)) ∧ j.toNat ≤ b.size ∧
       ∃ j0 rec, lineEnd j0 ik idx pl = .ok rec j ∧ R = .ok rec j))

end

/-! ## One key's value -/

/-- The fixed locals of the line loop. -/
def lineLocals : List MlS := [sB, sN, sI, sG, sW, sIK, sIdx, sPl, slotName 0, sC, sK, sV, sKK, sE2]

theorem lineLocals_nodup : lineLocals.Nodup := by decide

section
variable {σ : Type}

/-- The state the key dispatch hands to a value's code. -/
structure LCtx (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (j v : USize) (ik : UInt8)
    (idx : Nat) (pl : LinePayload) (u : PanSemStateFiniteExact 64 σ) : Prop where
  mem : u.memory = t.memory
  dom : u.memaddrs = t.memaddrs
  code : u.code = t.code
  glob : u.globals = t.globals
  be : u.be = t.be
  lb : u.locals.lookup sB = some (.val (.word A))
  ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size)))
  li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat)))
  lv : u.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat)))
  lik : u.locals.lookup sIK = some (.val (.word (BitVec.ofNat 64 ik.toNat)))
  lidx : u.locals.lookup sIdx = some (.val (.word (BitVec.ofNat 64 (min idx natCap))))
  pl0 : ∃ wpl ws0, u.locals.lookup sPl = some (.val (.word wpl)) ∧
    u.locals.lookup (slotName 0) = some (.val (.word ws0)) ∧ PlOK b wpl ws0 pl
  lg : u.locals.lookup sG = some (.val (.word 1))
  lw : ∃ w, u.locals.lookup sW = some (.val (.word w))
  scratch : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w))
  hj : j.toNat < b.size
  hv : v.toNat ≤ b.size

/-- The tag word of a present payload is nonzero; of an absent one, zero. -/
theorem plOK_tag {b : ByteArray} {wpl ws0 : BitVec 64} {pl : LinePayload} (h : PlOK b wpl ws0 pl) :
    (wpl = 0 ↔ pl.isAbsent = true) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨k, a, hm, he⟩
  · simp [LinePayload.isAbsent]
  · simp only [lineTblP, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [PlEntry] at he
    all_goals first
      | exact he.elim
      | (obtain ⟨rfl, n, rfl, -⟩ := he; simp [LinePayload.isAbsent]; done)
      | (obtain ⟨rfl, v, e, hsc, -⟩ := he
         simp only [nameStr, nameNum, exprApp, exprLam, exprForall, exprLet, exprConst, exprProj, declDef,
           declThm, declOpaque] at hsc
         obtain ⟨r, -, rfl⟩ := srMap_ok hsc
         simp [LinePayload.isAbsent]; done)
      | (obtain ⟨rfl, v, e, str, rfl, -, -⟩ := he; simp [LinePayload.isAbsent]; done)

end

/-- con-leche's line loop after one payload key's action (the key branch of `lineLoopI`). -/
def lineCont (tbl : List (Key × LAct)) (b : ByteArray) (j v : USize) (ik : UInt8) (idx : Nat) (pl : LinePayload) :
    LAct → ScanRes LineRec
  | .idx kind =>
    if ik != 0 then .err ⟨j.toNat, .duplicateKey⟩
    else
      let e := numEnd b v
      if e == v then .err ⟨v.toNat, .expectedNat⟩
      else if _hj : j < e then lineLoopI tbl b e false kind (readNatAt b v e) pl
      else .err ⟨j.toNat, .noProgress⟩
  | .natPl f =>
    if !pl.isAbsent then .err ⟨j.toNat, .duplicateKey⟩
    else
      let e := numEnd b v
      if e == v then .err ⟨v.toNat, .expectedNat⟩
      else if _hj : j < e then lineLoopI tbl b e false ik idx (f (readNatAt b v e))
      else .err ⟨j.toNat, .noProgress⟩
  | .strPl f =>
    if !pl.isAbsent then .err ⟨j.toNat, .duplicateKey⟩
    else
      match scanString b v with
      | .err err => .err err
      | .ok s e =>
        if _hj : j < e then lineLoopI tbl b e false ik idx (f s)
        else .err ⟨j.toNat, .noProgress⟩
  | .objPl scan =>
    if !pl.isAbsent then .err ⟨j.toNat, .duplicateKey⟩
    else
      match scan b v with
      | .err err => .err err
      | .ok r e =>
        if _hj : j < e then lineLoopI tbl b e false ik idx r
        else .err ⟨j.toNat, .noProgress⟩
  | .reject => .err ⟨j.toNat, .unknownKey⟩

section
variable {σ : Type}

theorem lact_idx (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (R : ScanRes LineRec) (j v : USize) (ik : UInt8)
    (idx : Nat) (pl : LinePayload) (kind : UInt8) (u : PanSemStateFiniteExact 64 σ) (hk : LCtx t A b j v ik idx pl u)
    (hR : lineCont lineTbl b j v ik idx pl (.idx kind) = R) :
    Stop (evaluateHOLFiniteState u (lineAct (.idxP kind))).1 ∨
      ((evaluateHOLFiniteState u (lineAct (.idxP kind))).1 = none ∧ LnI t A b R (evaluateHOLFiniteState u (lineAct (.idxP kind))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.1.congr hk.code
  simp only [lineAct, callTo]
  rw [ite_word u _ _ _ _ (ConsLoop.eval_cmp_of u .notEqual (vv sIK) (.const 0) (BitVec.ofNat 64 ik.toNat) 0
    (eval_vv u sIK _ hk.lik) (by simp [evalHOLExact]))]
  by_cases hik : ik = 0
  · subst hik
    simp only [UInt8.toNat_zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [show (BitVec.ofNat 64 0 == 0) = true from rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false]
    obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
    have hcall := call3_ret u sE2 fNumEnd sB sN sI neFun (vv sB) (vv sN) (vv sV) A
      (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 (ConLeche.Frontend.numEnd b v).toNat) e0
      (by decide) (by decide) (by decide) hcu.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
      (eval_vv u sV _ hk.lv) le0
      (fun callee h1 h2 h3 => numEnd_refines (callEntryStateHOLFinite u callee) A b hp
        (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
        ((hcu.entry rfl callee).2.1) h1 h2 h3)
    rcases hcall with hs | ⟨u1, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
    · exact Or.inl (seq_stop u _ _ hs)
    rw [seq_normal _ hu1]
    obtain ⟨E, hE⟩ : ∃ E, E = ConLeche.Frontend.numEnd b v := ⟨_, rfl⟩
    rw [← hE] at le1
    have hne := numEnd_eq hp v hk.hv
    rw [← hE] at hne
    have hEl : E.toNat ≤ b.size := by
      have := numEndL_le b.data.toList v.toNat (by simp; exact hk.hv); rw [hne]; simpa using this
    have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
      rw [lo1 sV (by decide)]; exact hk.lv
    rw [ite_word u1 _ _ _ _ (ConsLoop.eval_cmp_of u1 .equal (vv sE2) (vv sV) _ _ (eval_vv u1 sE2 _ le1)
      (eval_vv u1 sV _ lv1)), bw_eq _ _ (by omega) (by omega)]
    by_cases hEv : E.toNat = v.toNat
    · simp only [bw, hEv, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact Or.inl (stop_hang u1)
    simp only [bw, hEv, ↓reduceIte, ne_eq, not_true_eq_false]
    have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      rw [lo1 sI (by decide)]; exact hk.li
    rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
      (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
    by_cases hjE0 : ¬ j.toNat < E.toNat
    · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
    have hjE : j.toNat < E.toNat := by omega
    simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hskip : E.toNat = skipDigitsL b.data.toList v.toNat := by
      rw [hne]; exact numEndL_skip _ _ (by rw [← hne]; exact hEv)
    have hcall2 := call3_ret u1 sIdx fReadNat sB sI sE rnFun (vv sB) (vv sV) (vv sE2) A
      (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 E.toNat)
      (BitVec.ofNat 64 (min (ConLeche.Frontend.readNatAt b v E) natCap)) _
      (by decide) (by decide) (by decide) (by rw [k1]; exact hcu.2.2.2.2.2.1)
      (eval_vv u1 sB _ (by rw [lo1 sB (by decide)]; exact hk.lb)) (eval_vv u1 sV _ lv1) (eval_vv u1 sE2 _ le1)
      (by rw [lo1 sIdx (by decide)]; exact hk.lidx)
      (fun callee h1 h2 h3 => rnFun_refines (callEntryStateHOLFinite u1 callee) A b hp
        (bytesAt_congr hb (by exact m1.trans hk.mem) (by exact d1.trans hk.dom) (by exact b1.trans hk.be))
        v E hk.hv hskip h1 h3 h2)
    rcases hcall2 with hs | ⟨u2, hu2, m2, d2, g2, k2, b2, lx2, lo2⟩
    · exact Or.inl (seq_stop u1 _ _ hs)
    rw [seq_normal _ hu2]
    obtain ⟨wik, lik2⟩ : ∃ w, u2.locals.lookup sIK = some (.val (.word w)) :=
      ⟨_, by rw [lo2 sIK (by decide), lo1 sIK (by decide)]; exact hk.lik⟩
    rw [seq_normal _ (ConsLoop.assign_local u2 sIK _ (BitVec.ofNat 64 kind.toNat) wik (by simp [evalHOLExact]) lik2)]
    let u3 := setVarHOLFinite sIK (.val (.word (BitVec.ofNat 64 kind.toNat))) u2
    obtain ⟨ww, lw⟩ := hk.lw
    have lw3 : u3.locals.lookup sW = some (.val (.word ww)) := by
      lk [u3]; rw [lo2 sW (by decide), lo1 sW (by decide)]; exact lw
    rw [seq_normal _ (ConsLoop.assign_local u3 sW (.const 0) 0 ww (by simp [evalHOLExact]) lw3)]
    let u4 := setVarHOLFinite sW (.val (.word 0)) u3
    have li4 : u4.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      lk [u4, u3]; rw [lo2 sI (by decide)]; exact li1
    rw [ConsLoop.assign_local u4 sI (vv sE2) (BitVec.ofNat 64 E.toNat) _
      (eval_vv u4 sE2 _ (by lk [u4, u3]; rw [lo2 sE2 (by decide)]; exact le1)) li4]
    let u5 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 E.toNat))) u4
    have lo : ∀ y, y ≠ sI → y ≠ sW → y ≠ sIK → y ≠ sIdx → y ≠ sE2 → u5.locals.lookup y = u.locals.lookup y :=
      fun y h1 h2 h3 h4 h5 => by
        show (setVarHOLFinite _ _ (setVarHOLFinite _ _ (setVarHOLFinite _ _ u2))).locals.lookup y = _
        rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h3, lo2 y h4, lo1 y h5]
    have hR' : lineLoopI lineTbl b E false kind (ConLeche.Frontend.readNatAt b v E) pl = R := by
      rw [← hR]; unfold lineCont; simp only [show ik = 0 from rfl] at *
      simp only [show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, ← hE]
      have : (E == v) = false := beq_eq_false_iff_ne.mpr (fun h => hEv (by rw [h]))
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [dif_pos (USize.lt_iff_toNat_lt.mpr hjE)]
    obtain ⟨wpl, ws0, lpl, ls0, hpl⟩ := hk.pl0
    refine Or.inr ⟨rfl, m2.trans (m1.trans hk.mem), d2.trans (d1.trans hk.dom), k2.trans (k1.trans hk.code),
      g2.trans (g1.trans hk.glob), b2.trans (b1.trans hk.be),
      by rw [lo sB (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lb,
      by rw [lo sN (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.ln, ?_,
      E, false, kind, ConLeche.Frontend.readNatAt b v E, pl, wpl, ws0, by omega, by lk [u5], by lk [u5, u4]; rfl,
      by lk [u5, u4, u3], by lk [u5, u4, u3]; exact lx2,
      by rw [lo sPl (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lpl,
      by rw [lo _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ls0, hpl,
      Or.inl ⟨by rw [lo sG (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lg, hR'⟩⟩
    intro x hx
    by_cases hxe : x = sE2
    · subst hxe; exact ⟨_, by lk [u5, u4, u3]; rw [lo2 sE2 (by decide)]; exact le1⟩
    · obtain ⟨w, hw⟩ := hk.scratch x hx
      refine ⟨w, ?_⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (rw [lo _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw)
        | exact absurd rfl hxe
  · have hne : (BitVec.ofNat 64 ik.toNat == 0) = false := by
      apply beq_eq_false_iff_ne.mpr; intro e
      apply hik
      have h1 := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat] at h1
      have h2 : ik.toNat < 256 := ik.toNat_lt
      have h3 : ik.toNat = 0 := by
        rw [Nat.mod_eq_of_lt (by omega)] at h1; simpa using h1
      exact UInt8.toNat_inj.mp (by simpa using h3)
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne, Bool.not_false, ↓reduceIte, ne_eq,
      show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u)


theorem lact_nat (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (R : ScanRes LineRec) (j v : USize) (ik : UInt8)
    (idx : Nat) (pl : LinePayload) (k : Key) (tag g : Nat) (f : Nat → LinePayload) (hmem : (k, .natP tag g f) ∈ lineTblP)
    (u : PanSemStateFiniteExact 64 σ) (hk : LCtx t A b j v ik idx pl u)
    (hR : lineCont lineTbl b j v ik idx pl (.natPl f) = R) :
    Stop (evaluateHOLFiniteState u (lineAct (.natP tag g f))).1 ∨
      ((evaluateHOLFiniteState u (lineAct (.natP tag g f))).1 = none ∧ LnI t A b R (evaluateHOLFiniteState u (lineAct (.natP tag g f))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.1.congr hk.code
  simp only [lineAct, callTo, notAbsent]
  obtain ⟨wpl, ws0, lpl, ls0, hpl⟩ := hk.pl0
  rw [ite_word u _ _ _ _ (ConsLoop.eval_cmp_of u .notEqual (vv sPl) (.const 0) wpl 0
    (eval_vv u sPl _ lpl) (by simp [evalHOLExact]))]
  by_cases hab : pl.isAbsent = true
  · have hw0 : wpl = 0 := (plOK_tag hpl).mpr hab
    subst hw0
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [show ((0 : BitVec 64) == 0) = true from rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false]
    obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
    have hcall := call3_ret u sE2 fNumEnd sB sN sI neFun (vv sB) (vv sN) (vv sV) A
      (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 (ConLeche.Frontend.numEnd b v).toNat) e0
      (by decide) (by decide) (by decide) hcu.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
      (eval_vv u sV _ hk.lv) le0
      (fun callee h1 h2 h3 => numEnd_refines (callEntryStateHOLFinite u callee) A b hp
        (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
        ((hcu.entry rfl callee).2.1) h1 h2 h3)
    rcases hcall with hs | ⟨u1, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
    · exact Or.inl (seq_stop u _ _ hs)
    rw [seq_normal _ hu1]
    obtain ⟨E, hE⟩ : ∃ E, E = ConLeche.Frontend.numEnd b v := ⟨_, rfl⟩
    rw [← hE] at le1
    have hne := numEnd_eq hp v hk.hv
    rw [← hE] at hne
    have hEl : E.toNat ≤ b.size := by
      have := numEndL_le b.data.toList v.toNat (by simp; exact hk.hv); rw [hne]; simpa using this
    have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
      rw [lo1 sV (by decide)]; exact hk.lv
    rw [ite_word u1 _ _ _ _ (ConsLoop.eval_cmp_of u1 .equal (vv sE2) (vv sV) _ _ (eval_vv u1 sE2 _ le1)
      (eval_vv u1 sV _ lv1)), bw_eq _ _ (by omega) (by omega)]
    by_cases hEv : E.toNat = v.toNat
    · simp only [bw, hEv, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact Or.inl (stop_hang u1)
    simp only [bw, hEv, ↓reduceIte, ne_eq, not_true_eq_false]
    have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      rw [lo1 sI (by decide)]; exact hk.li
    rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
      (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
    by_cases hjE0 : ¬ j.toNat < E.toNat
    · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
    have hjE : j.toNat < E.toNat := by omega
    simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hskip : E.toNat = skipDigitsL b.data.toList v.toNat := by
      rw [hne]; exact numEndL_skip _ _ (by rw [← hne]; exact hEv)
    have hcall2 := call3_ret u1 (slotName 0) fReadNat sB sI sE rnFun (vv sB) (vv sV) (vv sE2) A
      (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 E.toNat)
      (BitVec.ofNat 64 (min (ConLeche.Frontend.readNatAt b v E) natCap)) _
      (by decide) (by decide) (by decide) (by rw [k1]; exact hcu.2.2.2.2.2.1)
      (eval_vv u1 sB _ (by rw [lo1 sB (by decide)]; exact hk.lb)) (eval_vv u1 sV _ lv1) (eval_vv u1 sE2 _ le1)
      (by rw [lo1 _ (by decide)]; exact ls0)
      (fun callee h1 h2 h3 => rnFun_refines (callEntryStateHOLFinite u1 callee) A b hp
        (bytesAt_congr hb (by exact m1.trans hk.mem) (by exact d1.trans hk.dom) (by exact b1.trans hk.be))
        v E hk.hv hskip h1 h3 h2)
    rcases hcall2 with hs | ⟨u2, hu2, m2, d2, g2, k2, b2, lx2, lo2⟩
    · exact Or.inl (seq_stop u1 _ _ hs)
    rw [seq_normal _ hu2]
    simp only [plAdvance]
    rw [seq_normal _ (ConsLoop.assign_local u2 sPl _ (BitVec.ofNat 64 tag) 0 (by simp [evalHOLExact])
      (by rw [lo2 sPl (by decide), lo1 sPl (by decide)]; exact lpl))]
    let u3 := setVarHOLFinite sPl (.val (.word (BitVec.ofNat 64 tag))) u2
    obtain ⟨ww, lw⟩ := hk.lw
    have lw3 : u3.locals.lookup sW = some (.val (.word ww)) := by
      lk [u3]; rw [lo2 sW (by decide), lo1 sW (by decide)]; exact lw
    rw [seq_normal _ (ConsLoop.assign_local u3 sW (.const 0) 0 ww (by simp [evalHOLExact]) lw3)]
    let u4 := setVarHOLFinite sW (.val (.word 0)) u3
    have li4 : u4.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      lk [u4, u3]; rw [lo2 sI (by decide)]; exact li1
    rw [ConsLoop.assign_local u4 sI (vv sE2) (BitVec.ofNat 64 E.toNat) _
      (eval_vv u4 sE2 _ (by lk [u4, u3]; rw [lo2 sE2 (by decide)]; exact le1)) li4]
    let u5 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 E.toNat))) u4
    have lo : ∀ y, y ≠ sI → y ≠ sW → y ≠ sPl → y ≠ slotName 0 → y ≠ sE2 → u5.locals.lookup y = u.locals.lookup y :=
      fun y h1 h2 h3 h4 h5 => by
        show (setVarHOLFinite _ _ (setVarHOLFinite _ _ (setVarHOLFinite _ _ u2))).locals.lookup y = _
        rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h3, lo2 y h4, lo1 y h5]
    have hR' : lineLoopI lineTbl b E false ik idx (f (ConLeche.Frontend.readNatAt b v E)) = R := by
      rw [← hR]; unfold lineCont
      simp only [hab, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ← hE]
      have : (E == v) = false := beq_eq_false_iff_ne.mpr (fun h => hEv (by rw [h]))
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [dif_pos (USize.lt_iff_toNat_lt.mpr hjE)]
    refine Or.inr ⟨rfl, m2.trans (m1.trans hk.mem), d2.trans (d1.trans hk.dom), k2.trans (k1.trans hk.code),
      g2.trans (g1.trans hk.glob), b2.trans (b1.trans hk.be),
      by rw [lo sB (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lb,
      by rw [lo sN (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.ln, ?_,
      E, false, ik, idx, f (ConLeche.Frontend.readNatAt b v E), BitVec.ofNat 64 tag,
      BitVec.ofNat 64 (min (ConLeche.Frontend.readNatAt b v E) natCap), by omega, by lk [u5], by lk [u5, u4]; rfl,
      by rw [lo sIK (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lik,
      by rw [lo sIdx (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lidx,
      by lk [u5, u4, u3], by lk [u5, u4, u3]; exact lx2,
      Or.inr ⟨k, _, hmem, rfl, _, rfl, rfl⟩,
      Or.inl ⟨by rw [lo sG (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lg, hR'⟩⟩
    intro x hx
    by_cases hxe : x = sE2
    · subst hxe; exact ⟨_, by lk [u5, u4, u3]; rw [lo2 sE2 (by decide)]; exact le1⟩
    · obtain ⟨w, hw⟩ := hk.scratch x hx
      refine ⟨w, ?_⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (rw [lo _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw)
        | exact absurd rfl hxe
  · have hne : (wpl == 0) = false := beq_eq_false_iff_ne.mpr (fun h => hab ((plOK_tag hpl).mp h))
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne, Bool.not_false, ↓reduceIte, ne_eq,
      show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u)

theorem lact_obj (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (R : ScanRes LineRec) (j v : USize) (ik : UInt8)
    (idx : Nat) (pl : LinePayload) (k : Key) (tag g : Nat) (fn : MlS) (scan : ByteArray → USize → ScanRes LinePayload)
    (hmem : (k, .objP tag g fn scan) ∈ lineTblP)
    (u : PanSemStateFiniteExact 64 σ) (hk : LCtx t A b j v ik idx pl u)
    (hR : lineCont lineTbl b j v ik idx pl (.objPl scan) = R) :
    Stop (evaluateHOLFiniteState u (lineAct (.objP tag g fn scan))).1 ∨
      ((evaluateHOLFiniteState u (lineAct (.objP tag g fn scan))).1 = none ∧ LnI t A b R (evaluateHOLFiniteState u (lineAct (.objP tag g fn scan))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.1.congr hk.code
  simp only [lineAct, callTo, notAbsent]
  obtain ⟨wpl, ws0, lpl, ls0, hpl⟩ := hk.pl0
  rw [ite_word u _ _ _ _ (ConsLoop.eval_cmp_of u .notEqual (vv sPl) (.const 0) wpl 0
    (eval_vv u sPl _ lpl) (by simp [evalHOLExact]))]
  by_cases hab : pl.isAbsent = true
  · have hw0 : wpl = 0 := (plOK_tag hpl).mpr hab
    subst hw0
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [show ((0 : BitVec 64) == 0) = true from rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false]
    obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
    obtain ⟨fbody, hfc, hfs⟩ := hc.2 k tag g fn scan hmem
    have hcall := call3_retP u sE2 fn sB sN sI fbody (vv sB) (vv sN) (vv sV) A
      (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
      (by decide) (by decide) (by decide) (by rw [hk.code]; exact hfc) (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
      (eval_vv u sV _ hk.lv) le0
      (fun callee h1 h2 h3 => hfs (callEntryStateHOLFinite u callee) A b v hp
        (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) (by exact hk.code) hk.hv h1 h2 h3)
    rcases hcall with hs | ⟨w, u1, ⟨E, rfl, hEb, r, hsc⟩, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
    · exact Or.inl (seq_stop u _ _ hs)
    rw [seq_normal _ hu1]
    have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      rw [lo1 sI (by decide)]; exact hk.li
    rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
      (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
    by_cases hjE0 : ¬ j.toNat < E.toNat
    · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
    have hjE : j.toNat < E.toNat := by omega
    simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
      rw [lo1 sV (by decide)]; exact hk.lv
    rw [seq_normal _ (ConsLoop.assign_local u1 (slotName 0) (vv sV) _ ws0 (eval_vv u1 sV _ lv1)
      (by rw [lo1 _ (by decide)]; exact ls0))]
    let u2 := setVarHOLFinite (slotName 0) (.val (.word (BitVec.ofNat 64 v.toNat))) u1
    have lo2 : ∀ y, y ≠ slotName 0 → u2.locals.lookup y = u1.locals.lookup y := fun y h => lookup_setVar_other _ _ h
    have lx2 : u2.locals.lookup (slotName 0) = some (.val (.word (BitVec.ofNat 64 v.toNat))) := lookup_setVar_same _ _ _
    have m2 : u2.memory = u1.memory := rfl
    have d2 : u2.memaddrs = u1.memaddrs := rfl
    have k2 : u2.code = u1.code := rfl
    have g2 : u2.globals = u1.globals := rfl
    have b2 : u2.be = u1.be := rfl
    simp only [plAdvance]
    rw [seq_normal _ (ConsLoop.assign_local u2 sPl _ (BitVec.ofNat 64 tag) 0 (by simp [evalHOLExact])
      (by rw [lo2 sPl (by decide), lo1 sPl (by decide)]; exact lpl))]
    let u3 := setVarHOLFinite sPl (.val (.word (BitVec.ofNat 64 tag))) u2
    obtain ⟨ww, lw⟩ := hk.lw
    have lw3 : u3.locals.lookup sW = some (.val (.word ww)) := by
      lk [u3]; rw [lo2 sW (by decide), lo1 sW (by decide)]; exact lw
    rw [seq_normal _ (ConsLoop.assign_local u3 sW (.const 0) 0 ww (by simp [evalHOLExact]) lw3)]
    let u4 := setVarHOLFinite sW (.val (.word 0)) u3
    have li4 : u4.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      lk [u4, u3]; rw [lo2 sI (by decide)]; exact li1
    rw [ConsLoop.assign_local u4 sI (vv sE2) (BitVec.ofNat 64 E.toNat) _
      (eval_vv u4 sE2 _ (by lk [u4, u3]; rw [lo2 sE2 (by decide)]; exact le1)) li4]
    let u5 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 E.toNat))) u4
    have lo : ∀ y, y ≠ sI → y ≠ sW → y ≠ sPl → y ≠ slotName 0 → y ≠ sE2 → u5.locals.lookup y = u.locals.lookup y :=
      fun y h1 h2 h3 h4 h5 => by
        show (setVarHOLFinite _ _ (setVarHOLFinite _ _ (setVarHOLFinite _ _ u2))).locals.lookup y = _
        rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h3, lo2 y h4, lo1 y h5]
    have hR' : lineLoopI lineTbl b E false ik idx r = R := by
      rw [← hR]; unfold lineCont
      simp only [hab, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsc]
      rw [dif_pos (USize.lt_iff_toNat_lt.mpr hjE)]
    refine Or.inr ⟨rfl, m2.trans (m1.trans hk.mem), d2.trans (d1.trans hk.dom), k2.trans (k1.trans hk.code),
      g2.trans (g1.trans hk.glob), b2.trans (b1.trans hk.be),
      by rw [lo sB (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lb,
      by rw [lo sN (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.ln, ?_,
      E, false, ik, idx, r, BitVec.ofNat 64 tag, BitVec.ofNat 64 v.toNat, by omega, by lk [u5], by lk [u5, u4]; rfl,
      by rw [lo sIK (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lik,
      by rw [lo sIdx (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lidx,
      by lk [u5, u4, u3], by lk [u5, u4, u3]; exact lx2,
      Or.inr ⟨k, _, hmem, rfl, v, E, hsc, rfl⟩,
      Or.inl ⟨by rw [lo sG (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lg, hR'⟩⟩
    intro x hx
    by_cases hxe : x = sE2
    · subst hxe; exact ⟨_, by lk [u5, u4, u3]; rw [lo2 sE2 (by decide)]; exact le1⟩
    · obtain ⟨w, hw⟩ := hk.scratch x hx
      refine ⟨w, ?_⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (rw [lo _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw)
        | exact absurd rfl hxe
  · have hne : (wpl == 0) = false := beq_eq_false_iff_ne.mpr (fun h => hab ((plOK_tag hpl).mp h))
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne, Bool.not_false, ↓reduceIte, ne_eq,
      show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u)

theorem lact_str (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (R : ScanRes LineRec) (j v : USize) (ik : UInt8)
    (idx : Nat) (pl : LinePayload) (k : Key) (tag g : Nat) (f : String → LinePayload)
    (hmem : (k, .strP tag g f) ∈ lineTblP)
    (u : PanSemStateFiniteExact 64 σ) (hk : LCtx t A b j v ik idx pl u)
    (hR : lineCont lineTbl b j v ik idx pl (.strPl f) = R) :
    Stop (evaluateHOLFiniteState u (lineAct (.strP tag g f))).1 ∨
      ((evaluateHOLFiniteState u (lineAct (.strP tag g f))).1 = none ∧ LnI t A b R (evaluateHOLFiniteState u (lineAct (.strP tag g f))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.1.congr hk.code
  simp only [lineAct, callTo, notAbsent]
  obtain ⟨wpl, ws0, lpl, ls0, hpl⟩ := hk.pl0
  rw [ite_word u _ _ _ _ (ConsLoop.eval_cmp_of u .notEqual (vv sPl) (.const 0) wpl 0
    (eval_vv u sPl _ lpl) (by simp [evalHOLExact]))]
  by_cases hab : pl.isAbsent = true
  · have hw0 : wpl = 0 := (plOK_tag hpl).mpr hab
    subst hw0
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [show ((0 : BitVec 64) == 0) = true from rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false]
    obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
    have hcall := call3_retP u sE2 fStr sB sN sI ssFun (vv sB) (vv sN) (vv sV) A
      (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
      (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
      (eval_vv u sV _ hk.lv) le0
      (fun callee h1 h2 h3 => ssFun_sound (callEntryStateHOLFinite u callee) A b hp
        (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
        (hcu.entry rfl callee).2.2.2.1 h1 h2 h3)
    rcases hcall with hs | ⟨w, u0, ⟨e, rfl, hel, str, hss, -⟩, hu0, m0', d0', g0', k0', b0', le0', lo0⟩
    · exact Or.inl (seq_stop u _ _ hs)
    rw [seq_normal _ hu0]
    have he1 : (e + 1).toNat = e.toNat + 1 := ConLeche.Frontend.usizeStep b e ((hp.lt_iff e).mpr hel)
    obtain ⟨E, hE⟩ : ∃ E, E = e + 1 := ⟨_, rfl⟩
    rw [seq_normal _ (ConsLoop.assign_local u0 sE2 _ (BitVec.ofNat 64 E.toNat) _ (by
      rw [eval_add_c u0 sE2 _ _ le0', hE, he1]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) le0')]
    let u1 := setVarHOLFinite sE2 (.val (.word (BitVec.ofNat 64 E.toNat))) u0
    have le1 : u1.locals.lookup sE2 = some (.val (.word (BitVec.ofNat 64 E.toNat))) := lookup_setVar_same _ _ _
    have lo1 : ∀ y, y ≠ sE2 → u1.locals.lookup y = u.locals.lookup y := fun y hy => by
      show (setVarHOLFinite _ _ u0).locals.lookup y = _; rw [lookup_setVar_other _ _ hy, lo0 y hy]
    have m1 : u1.memory = u.memory := m0'
    have d1 : u1.memaddrs = u.memaddrs := d0'
    have k1 : u1.code = u.code := k0'
    have g1 : u1.globals = u.globals := g0'
    have b1 : u1.be = u.be := b0'
    have hEb : E.toNat ≤ b.size + 64 := by rw [hE, he1]; omega
    have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      rw [lo1 sI (by decide)]; exact hk.li
    rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
      (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
    by_cases hjE0 : ¬ j.toNat < E.toNat
    · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
    have hjE : j.toNat < E.toNat := by omega
    simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
      rw [lo1 sV (by decide)]; exact hk.lv
    rw [seq_normal _ (ConsLoop.assign_local u1 (slotName 0) (vv sV) _ ws0 (eval_vv u1 sV _ lv1)
      (by rw [lo1 _ (by decide)]; exact ls0))]
    let u2 := setVarHOLFinite (slotName 0) (.val (.word (BitVec.ofNat 64 v.toNat))) u1
    have lo2 : ∀ y, y ≠ slotName 0 → u2.locals.lookup y = u1.locals.lookup y := fun y h => lookup_setVar_other _ _ h
    have lx2 : u2.locals.lookup (slotName 0) = some (.val (.word (BitVec.ofNat 64 v.toNat))) := lookup_setVar_same _ _ _
    have m2 : u2.memory = u1.memory := rfl
    have d2 : u2.memaddrs = u1.memaddrs := rfl
    have k2 : u2.code = u1.code := rfl
    have g2 : u2.globals = u1.globals := rfl
    have b2 : u2.be = u1.be := rfl
    simp only [plAdvance]
    rw [seq_normal _ (ConsLoop.assign_local u2 sPl _ (BitVec.ofNat 64 tag) 0 (by simp [evalHOLExact])
      (by rw [lo2 sPl (by decide), lo1 sPl (by decide)]; exact lpl))]
    let u3 := setVarHOLFinite sPl (.val (.word (BitVec.ofNat 64 tag))) u2
    obtain ⟨ww, lw⟩ := hk.lw
    have lw3 : u3.locals.lookup sW = some (.val (.word ww)) := by
      lk [u3]; rw [lo2 sW (by decide), lo1 sW (by decide)]; exact lw
    rw [seq_normal _ (ConsLoop.assign_local u3 sW (.const 0) 0 ww (by simp [evalHOLExact]) lw3)]
    let u4 := setVarHOLFinite sW (.val (.word 0)) u3
    have li4 : u4.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      lk [u4, u3]; rw [lo2 sI (by decide)]; exact li1
    rw [ConsLoop.assign_local u4 sI (vv sE2) (BitVec.ofNat 64 E.toNat) _
      (eval_vv u4 sE2 _ (by lk [u4, u3]; rw [lo2 sE2 (by decide)]; exact le1)) li4]
    let u5 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 E.toNat))) u4
    have lo : ∀ y, y ≠ sI → y ≠ sW → y ≠ sPl → y ≠ slotName 0 → y ≠ sE2 → u5.locals.lookup y = u.locals.lookup y :=
      fun y h1 h2 h3 h4 h5 => by
        show (setVarHOLFinite _ _ (setVarHOLFinite _ _ (setVarHOLFinite _ _ u2))).locals.lookup y = _
        rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h3, lo2 y h4, lo1 y h5]
    have hR' : lineLoopI lineTbl b E false ik idx (f str) = R := by
      rw [← hR]; unfold lineCont
      simp only [hab, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hss, ← hE]
      rw [dif_pos (USize.lt_iff_toNat_lt.mpr hjE)]
    refine Or.inr ⟨rfl, m2.trans (m1.trans hk.mem), d2.trans (d1.trans hk.dom), k2.trans (k1.trans hk.code),
      g2.trans (g1.trans hk.glob), b2.trans (b1.trans hk.be),
      by rw [lo sB (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lb,
      by rw [lo sN (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.ln, ?_,
      E, false, ik, idx, f str, BitVec.ofNat 64 tag, BitVec.ofNat 64 v.toNat, by omega, by lk [u5], by lk [u5, u4]; rfl,
      by rw [lo sIK (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lik,
      by rw [lo sIdx (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lidx,
      by lk [u5, u4, u3], by lk [u5, u4, u3]; exact lx2,
      Or.inr ⟨k, _, hmem, rfl, v, e + 1, str, rfl, rfl, hss⟩,
      Or.inl ⟨by rw [lo sG (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk.lg, hR'⟩⟩
    intro x hx
    by_cases hxe : x = sE2
    · subst hxe; exact ⟨_, by lk [u5, u4, u3]; rw [lo2 sE2 (by decide)]; exact le1⟩
    · obtain ⟨w, hw⟩ := hk.scratch x hx
      refine ⟨w, ?_⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (rw [lo _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw)
        | exact absurd rfl hxe
  · have hne : (wpl == 0) = false := beq_eq_false_iff_ne.mpr (fun h => hab ((plOK_tag hpl).mp h))
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne, Bool.not_false, ↓reduceIte, ne_eq,
      show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u)
end

section
variable {σ : Type}

theorem lineDispatch_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (R : ScanRes LineRec) (j v : USize) (ik : UInt8)
    (idx : Nat) (pl : LinePayload) (K : Key) :
    ∀ (ks : List (Key × LActP)) (u : PanSemStateFiniteExact 64 σ), (∀ e ∈ ks, e ∈ lineTblP) →
      LCtx t A b j v ik idx pl u →
      u.locals.lookup sKK = some (.val (.word (BitVec.ofNat 64 K.ctorIdx))) →
      lineCont lineTbl b j v ik idx pl (lookupL K (ks.map (fun e => (e.1, e.2.toLAct)))) = R →
      Stop (evaluateHOLFiniteState u (lineDispatch ks)).1 ∨
        ((evaluateHOLFiniteState u (lineDispatch ks)).1 = none ∧
          LnI t A b R (evaluateHOLFiniteState u (lineDispatch ks)).2) := by
  intro ks
  induction ks with
  | nil => intro u _ _ _ _; exact Or.inl (stop_hang u)
  | cons e r ih =>
    intro u hks hk lkk hR
    obtain ⟨k, a⟩ := e
    unfold lineDispatch
    have hcmp := eval_eq_c u sKK K.ctorIdx k.ctorIdx (by have := key_ctorIdx_lt K; omega)
      (by have := key_ctorIdx_lt k; omega) lkk
    rw [ite_word u _ _ _ _ hcmp]
    by_cases hK : K.ctorIdx = k.ctorIdx
    · simp only [bw, hK, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      have hKk : K = k := key_ctorIdx_inj hK
      subst hKk
      simp only [List.map_cons, lookupL, ↓reduceIte] at hR
      have hmem := hks _ (List.mem_cons_self ..)
      cases a with
      | idxP kind => exact lact_idx t A b hp hb hc R j v ik idx pl kind u hk hR
      | natP tag g f => exact lact_nat t A b hp hb hc R j v ik idx pl K tag g f hmem u hk hR
      | strP tag g f => exact lact_str t A b hp hb hc R j v ik idx pl K tag g f hmem u hk hR
      | objP tag g fn scan => exact lact_obj t A b hp hb hc R j v ik idx pl K tag g fn scan hmem u hk hR
    · simp only [bw, hK, ↓reduceIte, ne_eq, not_true_eq_false]
      have hKk : K ≠ k := fun h => hK (by rw [h])
      simp only [List.map_cons, lookupL, hKk, ↓reduceIte] at hR
      exact ih u (fun e he => hks e (List.mem_cons_of_mem _ he)) hk lkk hR

end

/-! ## The closing brace -/

def tagLookup (t : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (t', g) :: r => if t = t' then some g else tagLookup t r

section
variable {σ : Type}

/-- `endCheck` at a tag: the tag's group must be the index kind, then the loop ends past the brace. -/
theorem endCheck_spec (u : PanSemStateFiniteExact 64 σ) (t : Nat) (ht : t < 2 ^ 32) (ik : UInt8) (j : USize)
    (lpl : u.locals.lookup sPl = some (.val (.word (BitVec.ofNat 64 t))))
    (lik : u.locals.lookup sIK = some (.val (.word (BitVec.ofNat 64 ik.toNat))))
    (li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))))
    (lg : ∃ w, u.locals.lookup sG = some (.val (.word w))) (hj1 : j.toNat + 1 < 2 ^ 64) :
    ∀ (L : List (Nat × Nat)), (∀ e ∈ L, e.1 < 2 ^ 32 ∧ e.2 < 4) →
      Stop (evaluateHOLFiniteState u (endCheck L)).1 ∨
        ∃ g, tagLookup t L = some g ∧ g = ik.toNat ∧
          evaluateHOLFiniteState u (endCheck L) =
            (none, setVarHOLFinite sG (.val (.word 0))
              (setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j.toNat + 1)))) u)) := by
  intro L
  induction L with
  | nil => intro _; exact Or.inl (stop_hang u)
  | cons e r ih =>
    intro hL
    obtain ⟨t', g⟩ := e
    have h1 := hL (t', g) (List.mem_cons_self ..)
    simp only at h1
    unfold endCheck
    rw [ite_word u _ _ _ _ (eval_eq_c u sPl t t' (by omega) (by omega) lpl)]
    by_cases htt : t = t'
    · subst htt
      simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      have hikl : ik.toNat < 2 ^ 64 := by have := ik.toNat_lt; omega
      rw [ite_word u _ _ _ _ (eval_eq_c u sIK ik.toNat g hikl (by omega) lik)]
      by_cases hg : ik.toNat = g
      · simp only [bw, hg, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
        right
        refine ⟨g, by simp [tagLookup], by first | rfl | exact hg.symm, ?_⟩
        unfold incI
        rw [seq_normal _ (ConsLoop.assign_local u sI _ (BitVec.ofNat 64 (j.toNat + 1)) _ (by
          rw [eval_add_c u sI _ _ li]; congr 3; apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]; try omega) li)]
        obtain ⟨wg, lg⟩ := lg
        rw [ConsLoop.assign_local _ sG (.const 0) 0 wg (by simp [evalHOLExact]) (by lk; exact lg)]
      · simp only [bw, hg, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u)
    · simp only [bw, htt, ↓reduceIte, ne_eq, not_true_eq_false]
      rcases ih (fun e he => hL e (List.mem_cons_of_mem _ he)) with hs | ⟨g', hl, hg', he⟩
      · exact Or.inl hs
      · exact Or.inr ⟨g', by simp [tagLookup, htt, hl], hg', he⟩

end

theorem tagGroups_bounds : ∀ e ∈ tagGroups, e.1 < 2 ^ 32 ∧ e.2 < 4 := by decide

/-- A present payload: its tag's group, and con-leche's line end at that index kind. -/
theorem plOK_end {b : ByteArray} {wpl ws0 : BitVec 64} {pl : LinePayload} (h : PlOK b wpl ws0 pl)
    (hab : pl.isAbsent = false) (j : USize) (ik : UInt8) (idx : Nat) :
    ∃ t g, wpl = BitVec.ofNat 64 t ∧ t < 2 ^ 32 ∧ tagLookup t tagGroups = some g ∧
      (ik.toNat = g → ∃ rec, lineEnd j ik idx pl = .ok rec (j + 1)) := by
  rcases h with ⟨rfl, -⟩ | ⟨k, a, hm, he⟩
  · simp [LinePayload.isAbsent] at hab
  simp only [lineTblP, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  have hik : ∀ n : Nat, n < 4 → ik.toNat = n → ik = UInt8.ofNat n := fun n hn h => by
    apply UInt8.toNat_inj.mp; rw [h, UInt8.toNat_ofNat']; omega
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [PlEntry] at he
  all_goals first
    | exact he.elim
    | (obtain ⟨rfl, n, rfl, -⟩ := he
       exact ⟨_, _, rfl, by decide, rfl, fun hg => by rw [hik _ (by decide) hg]; simp [lineEnd]⟩)
    | (obtain ⟨rfl, v, e, hsc, -⟩ := he
       simp only [nameStr, nameNum, exprApp, exprLam, exprForall, exprLet, exprConst, exprProj, declDef,
         declThm, declOpaque] at hsc
       obtain ⟨r, -, rfl⟩ := srMap_ok hsc
       exact ⟨_, _, rfl, by decide, rfl, fun hg => by rw [hik _ (by decide) hg]; simp [lineEnd]⟩)
    | (obtain ⟨rfl, v, e, str, rfl, -, -⟩ := he
       exact ⟨_, _, rfl, by decide, rfl, fun hg => by rw [hik _ (by decide) hg]; simp [lineEnd]⟩)

/-- The key branch of `lineLoopI` is `lineCont` at the looked-up action. -/
theorem lineBranch_eq (tbl : List (Key × LAct)) (b : ByteArray) (j v : USize) (ik : UInt8) (idx : Nat)
    (pl : LinePayload) (a : LAct) :
    (match a with
      | .idx kind =>
        if ik != 0 then .err ⟨j.toNat, .duplicateKey⟩
        else
          let e := numEnd b v
          if e == v then .err ⟨v.toNat, .expectedNat⟩
          else if _hj : j < e then lineLoopI tbl b e false kind (readNatAt b v e) pl
          else .err ⟨j.toNat, .noProgress⟩
      | .natPl f =>
        if !pl.isAbsent then .err ⟨j.toNat, .duplicateKey⟩
        else
          let e := numEnd b v
          if e == v then .err ⟨v.toNat, .expectedNat⟩
          else if _hj : j < e then lineLoopI tbl b e false ik idx (f (readNatAt b v e))
          else .err ⟨j.toNat, .noProgress⟩
      | .strPl f =>
        if !pl.isAbsent then .err ⟨j.toNat, .duplicateKey⟩
        else
          match scanString b v with
          | .err err => .err err
          | .ok s e =>
            if _hj : j < e then lineLoopI tbl b e false ik idx (f s)
            else .err ⟨j.toNat, .noProgress⟩
      | .objPl scan =>
        if !pl.isAbsent then .err ⟨j.toNat, .duplicateKey⟩
        else
          match scan b v with
          | .err err => .err err
          | .ok r e =>
            if _hj : j < e then lineLoopI tbl b e false ik idx r
            else .err ⟨j.toNat, .noProgress⟩
      | .reject => .err ⟨j.toNat, .unknownKey⟩ : ScanRes LineRec) = lineCont tbl b j v ik idx pl a := by
  cases a <;> rfl

section
variable {σ : Type}

theorem bw_or (p q : Prop) [Decidable p] [Decidable q] :
    wordOpHOL .or [bw p, bw q] = some (bw (p ∨ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, bw, wordOpHOL, wordOp] <;> decide

theorem eval_ne0 (u : PanSemStateFiniteExact 64 σ) (x : MlS) (w : BitVec 64)
    (h : u.locals.lookup x = some (.val (.word w))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
      (.cmp .notEqual (vv x) (.const 0)) = some (.val (.word (bw (w ≠ 0)))) := by
  rw [ConsLoop.eval_cmp_of u .notEqual _ _ w 0 (eval_vv u x _ h) (by simp [evalHOLExact])]
  by_cases h0 : w = 0 <;> simp [h0, bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem line_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc0 : LineCodes t) (R : ScanRes LineRec)
    (u : PanSemStateFiniteExact 64 σ) (hu : LnI t A b R u)
    (hg : u.locals.lookup sG = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState (decClockHOLFinite u) lineBody).1 ∨
      ((evaluateHOLFiniteState (decClockHOLFinite u) lineBody).1 = none ∧
        LnI t A b R (evaluateHOLFiniteState (decClockHOLFinite u) lineBody).2) := by
  have hc : ScanCodes t := hc0.1
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, scr, j, wm, ik, idx, pl, wpl, ws0, hj, li, lw, lik, lidx, lpl, ls0, hpl, br⟩ := hu
  obtain ⟨_, hR⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  let v0 := decClockHOLFinite u
  have hlt := eval_lower v0 (vv sI) (vv sN) j.toNat b.size (by omega) hL
    (eval_vv v0 sI _ (by lk [v0]; exact li)) (eval_vv v0 sN _ (by lk [v0]; exact ln))
  unfold lineBody
  rw [ite_word v0 _ _ _ _ hlt]
  by_cases hjl0 : ¬ j.toNat < b.size
  · simp only [bw, hjl0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v0)
  have hjl : j.toNat < b.size := by omega
  simp only [bw, hjl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hjl' : j.toNat < b.data.toList.length := by simpa using hjl
  have hju : j < b.usize := (hp.lt_iff j).mpr hjl
  have hj1 : (j + 1).toNat = j.toNat + 1 := ConLeche.Frontend.usizeStep b j hju
  have hbv : BytesAt v0 A b.data.toList := bytesAt_congr hb m0 d0 b0
  have haddr : @evalHOLExact 64 σ _ v0.toExact (fun a => Classical.propDecidable (v0.memaddrs a))
      (.op .add [vv sB, vv sI]) = some (.val (.word (A + BitVec.ofNat 64 j.toNat))) := by
    have lb' : v0.locals.lookup sB = some (.val (.word A)) := by lk [v0]; exact lb
    have li' : v0.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v0]; exact li
    simp [vv, evalHOLExact, evalListHOLExact, lb', li', wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨wc, lc⟩ := scr sC (by simp)
  obtain ⟨c, hcx⟩ : ∃ c, c = b.data.toList[j.toNat] := ⟨_, rfl⟩
  rw [seq_normal _ (ConsLoop.assign_local v0 sC _ (BitVec.ofNat 64 c.toNat) wc
    (by rw [hcx]; exact eval_loadByte_bytes v0 _ A b.data.toList j.toNat hbv hjl' haddr) (by lk [v0]; exact lc))]
  let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 c.toNat))) v0
  have lc1 : v1.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 c.toNat))) := by lk [v1]
  -- every line local other than `c` is as it was
  have lo1 : ∀ y, y ≠ sC → v1.locals.lookup y = u.locals.lookup y := fun y h => by
    show (setVarHOLFinite _ _ v0).locals.lookup y = _; rw [lookup_setVar_other _ _ h]; lk [v0]
  have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by rw [lo1 sI (by decide)]; exact li
  have lw1 : v1.locals.lookup sW = some (.val (.word (bw (wm = true)))) := by rw [lo1 sW (by decide)]; exact lw
  have lik1 : v1.locals.lookup sIK = some (.val (.word (BitVec.ofNat 64 ik.toNat))) := by
    rw [lo1 sIK (by decide)]; exact lik
  have lpl1 : v1.locals.lookup sPl = some (.val (.word wpl)) := by rw [lo1 sPl (by decide)]; exact lpl
  have lg1 : v1.locals.lookup sG = some (.val (.word 1)) := by rw [lo1 sG (by decide)]; exact hg
  have hct : c.toNat < 256 := UInt8.toNat_lt c
  have hstep := lineLoopI.eq_1 lineTbl b j wm ik idx pl
  rw [dif_pos hju, uget_eq b j hjl hju, ← hcx] at hstep
  simp only at hstep
  -- the new state's invariant, once the changed locals are known
  have mk : ∀ (w : PanSemStateFiniteExact 64 σ) (j' : USize) (wm' : Bool),
      w.memory = v1.memory → w.memaddrs = v1.memaddrs → w.code = v1.code → w.globals = v1.globals →
      w.be = v1.be → (∀ y, y ∉ [sI, sW, sG] → w.locals.lookup y = v1.locals.lookup y) →
      j'.toNat ≤ b.size + 64 →
      w.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j'.toNat))) →
      w.locals.lookup sW = some (.val (.word (bw (wm' = true)))) →
      ((w.locals.lookup sG = some (.val (.word 1)) ∧ lineLoopI lineTbl b j' wm' ik idx pl = R) ∨
       (w.locals.lookup sG = some (.val (.word 0)) ∧ j'.toNat ≤ b.size ∧
         ∃ j0 rec, lineEnd j0 ik idx pl = .ok rec j' ∧ R = .ok rec j')) →
      LnI t A b R w := by
    intro w j' wm' a1 a2 a3 a4 a5 hlo hj' li' lw' hg'
    have q : ∀ y, y ∉ [sI, sW, sG] → y ≠ sC → w.locals.lookup y = u.locals.lookup y := fun y h1 h2 => by
      rw [hlo y h1, lo1 y h2]
    refine ⟨a1.trans m0, a2.trans d0, a3.trans c0, a4.trans g0, a5.trans b0,
      by rw [q sB (by decide) (by decide)]; exact lb, by rw [q sN (by decide) (by decide)]; exact ln, ?_,
      j', wm', ik, idx, pl, wpl, ws0, hj', li', lw', by rw [q sIK (by decide) (by decide)]; exact lik,
      by rw [q sIdx (by decide) (by decide)]; exact lidx, by rw [q sPl (by decide) (by decide)]; exact lpl,
      by rw [q _ (by decide) (by decide)]; exact ls0, hpl, hg'⟩
    intro x hx
    by_cases hxc : x = sC
    · subst hxc; exact ⟨_, by rw [hlo sC (by decide)]; exact lc1⟩
    · obtain ⟨wx, hwx⟩ := scr x hx
      refine ⟨wx, ?_⟩
      have : x ∉ [sI, sW, sG] := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [q x this hxc]; exact hwx
  rw [ite_word v1 _ _ _ _ (wsTest_ok v1 c.toNat hct lc1)]
  by_cases hws : isWsN c.toNat = true
  · simp only [bw, hws, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [incI, ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
      rw [eval_add_c v1 sI _ _ li1, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li1]
    rw [isWs_eq, hws] at hstep; simp only [↓reduceIte] at hstep
    refine Or.inr ⟨rfl, mk _ (j + 1) wm rfl rfl rfl rfl rfl (fun y hy => ?_) (by omega) (by lk) (by lk; exact lw1)
      (Or.inl ⟨by lk; exact lg1, by rw [← hR, hstep]⟩)⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
    exact lookup_setVar_other _ _ hy.1
  simp only [bw, hws, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [isWs_eq] at hstep; simp only [hws, Bool.false_eq_true, ↓reduceIte] at hstep
  have hc125 := eval_eq_c v1 sC c.toNat 125 (by omega) (by decide) lc1
  simp only [show (125 : BitVec 64) = BitVec.ofNat 64 125 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc125]
  by_cases h125 : c.toNat = 125
  · simp only [bw, h125, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hc' : (c == 125) = true := by
      rw [show (125 : UInt8) = UInt8.ofNat 125 from rfl, beq_ofNat c 125 (by decide)]; simp [h125]
    rw [hc'] at hstep; simp only [↓reduceIte] at hstep
    have hikw : (BitVec.ofNat 64 ik.toNat ≠ 0) ↔ ik ≠ 0 := by
      constructor
      · intro h e; apply h; rw [e]; rfl
      · intro h e; apply h
        have h1 := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := ik.toNat_lt; omega)] at h1
        exact UInt8.toNat_inj.mp (by simpa using h1)
    have hor : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.op .or [.cmp .notEqual (vv sIK) (.const 0), notAbsent]) =
        some (.val (.word (bw (BitVec.ofNat 64 ik.toNat ≠ 0 ∨ wpl ≠ 0)))) := by
      rw [evalHOLExact]; simp only [evalListHOLExact, eval_ne0 v1 sIK _ lik1, notAbsent, eval_ne0 v1 sPl _ lpl1]
      simp [valueIsWord, valueWord, bw_or]
    have hand : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.op .and [vv sW, .op .or [.cmp .notEqual (vv sIK) (.const 0), notAbsent]]) =
        some (.val (.word (bw (wm = true ∧ (BitVec.ofNat 64 ik.toNat ≠ 0 ∨ wpl ≠ 0))))) := by
      rw [evalHOLExact]; simp only [evalListHOLExact, eval_vv v1 sW _ lw1, hor]
      simp [valueIsWord, valueWord, bw_and]
    rw [ite_word v1 _ _ _ _ hand]
    by_cases hbad : wm = true ∧ (BitVec.ofNat 64 ik.toNat ≠ 0 ∨ wpl ≠ 0)
    · simp only [bw, hbad, ne_eq, not_false_eq_true, and_self, ↓reduceIte, show ¬ (1 : BitVec 64) = 0 from by decide]
      exact Or.inl (stop_hang v1)
    simp only [bw, hbad, ↓reduceIte, ne_eq, not_true_eq_false]
    have hok1 : (wm && (ik != 0 || !pl.isAbsent)) = false := by
      have ht := plOK_tag hpl
      cases wm
      · rfl
      · simp only [Bool.true_and, Bool.or_eq_false_iff, bne_eq_false_iff_eq, Bool.not_eq_false']
        simp only [true_and, not_or, hikw] at hbad
        exact ⟨Classical.byContradiction hbad.1, ht.mp (Classical.byContradiction hbad.2)⟩
    rw [hok1] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
    by_cases hab : pl.isAbsent = true
    · have hw0 : wpl = 0 := (plOK_tag hpl).mpr hab
      rw [hw0] at lpl1
      rcases endCheck_spec v1 0 (by decide) ik j lpl1 lik1 li1 ⟨_, lg1⟩ (by omega) tagGroups tagGroups_bounds with
        hs | ⟨g, hl, -, -⟩
      · exact Or.inl hs
      · simp [tagLookup, tagGroups, lineTblP] at hl
    obtain ⟨tg, g, hwt, htg, hlk, hend⟩ := plOK_end hpl (by simpa using hab) j ik idx
    rw [hwt] at lpl1
    rcases endCheck_spec v1 tg htg ik j lpl1 lik1 li1 ⟨_, lg1⟩ (by omega) tagGroups tagGroups_bounds with
      hs | ⟨g', hl, hg', he⟩
    · exact Or.inl hs
    rw [hlk] at hl; simp only [Option.some.injEq] at hl; subst hl
    obtain ⟨rec, hrec⟩ := hend hg'.symm
    rw [he]
    refine Or.inr ⟨rfl, mk _ (j + 1) wm rfl rfl rfl rfl rfl (fun y hy => ?_) (by omega) (by lk; rw [hj1])
      (by lk; exact lw1) (Or.inr ⟨by lk, by omega, j, rec, hrec, by rw [← hR, hstep, hrec]⟩)⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
    show (setVarHOLFinite _ _ (setVarHOLFinite _ _ v1)).locals.lookup y = _
    rw [lookup_setVar_other _ _ hy.2.2, lookup_setVar_other _ _ hy.1]
  simp only [bw, h125, ↓reduceIte, ne_eq, not_true_eq_false]
  have hc' : (c == 125) = false := by
    rw [show (125 : UInt8) = UInt8.ofNat 125 from rfl, beq_ofNat c 125 (by decide)]; simp [h125]
  rw [hc'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  have hc44 := eval_eq_c v1 sC c.toNat 44 (by omega) (by decide) lc1
  simp only [show (44 : BitVec 64) = BitVec.ofNat 64 44 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc44]
  by_cases h44 : c.toNat = 44
  · simp only [bw, h44, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hc44' : (c == 44) = true := by
      rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [h44]
    rw [hc44'] at hstep; simp only [↓reduceIte] at hstep
    rw [ite_word v1 _ _ _ _ (eval_vv v1 sW _ lw1)]
    cases wm
    · simp only [bw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at hstep ⊢
      rw [seq_normal _ (ConsLoop.assign_local v1 sW (.const 1) 1 0 (by simp [evalHOLExact]) lw1)]
      let w1 := setVarHOLFinite sW (.val (.word 1)) v1
      have li2 : w1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [w1]; exact li1
      rw [incI, ConsLoop.assign_local w1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
        rw [eval_add_c w1 sI _ _ li2, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) li2]
      refine Or.inr ⟨rfl, mk _ (j + 1) true rfl rfl rfl rfl rfl (fun y hy => ?_) (by omega) (by lk)
        (by lk [w1]; rfl) (Or.inl ⟨by lk [w1]; exact lg1, by rw [← hR, hstep]⟩)⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
      show (setVarHOLFinite _ _ (setVarHOLFinite _ _ v1)).locals.lookup y = _
      rw [lookup_setVar_other _ _ hy.1, lookup_setVar_other _ _ hy.2.1]
    · simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact Or.inl (stop_hang v1)
  simp only [bw, h44, ↓reduceIte, ne_eq, not_true_eq_false]
  have hc44' : (c == 44) = false := by
    rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [h44]
  rw [hc44'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  have lov : ∀ y, y ≠ sC → v1.locals.lookup y = u.locals.lookup y := lo1
  have hscr1 : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, v1.locals.lookup x = some (.val (.word w)) := by
    intro x hx
    by_cases hxc : x = sC
    · subst hxc; exact ⟨_, lc1⟩
    · obtain ⟨w, hw⟩ := scr x hx
      exact ⟨w, by rw [lo1 x hxc]; exact hw⟩
  have hfx : ∀ k, k < 1 → ∀ x ∈ fixedLocals, slotName k ≠ x := fun k hk => slotName_fixed k (by omega)
  have hc34 := eval_eq_c v1 sC c.toNat 34 (by omega) (by decide) lc1
  simp only [show (34 : BitVec 64) = BitVec.ofNat 64 34 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc34]
  by_cases h34 : ¬ c.toNat = 34
  · simp only [bw, h34, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v1)
  have h34' : c.toNat = 34 := by omega
  simp only [bw, h34', ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hc34' : (c == 34) = true := by
    rw [show (34 : UInt8) = UInt8.ofNat 34 from rfl, beq_ofNat c 34 (by decide)]; simp [h34']
  rw [hc34'] at hstep; simp only [↓reduceIte] at hstep
  rw [ite_word v1 _ _ _ _ (eval_vv v1 sW _ lw1)]
  cases wm
  · simp only [bw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v1)
  simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstep
  have hcu : ScanCodes v1 := hc.congr (by show u.code = t.code; exact c0)
  simp only [lineKeyPart, callTo]
  -- keyEnd
  obtain ⟨wk, lk0⟩ := hscr1 sK (by simp)
  have hcall1 := call3_ret v1 sK fKeyEnd sB sN sI keFun (vv sB) (vv sN) (.op .add [vv sI, .const 1]) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 (j + 1).toNat) (BitVec.ofNat 64 (ConLeche.Frontend.keyEnd b (j + 1)).toNat) wk
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.2.2.2.1
    (eval_vv v1 sB _ (by lk [v1, v0]; exact lb)) (eval_vv v1 sN _ (by lk [v1, v0]; exact ln))
    (by rw [eval_add_c v1 sI _ _ li1, hj1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega)
    lk0
    (fun callee h1 h2 h3 => keyEnd_refines (callEntryStateHOLFinite v1 callee) A b hp
      (bytesAt_congr hb (by exact m0) (by exact d0) (by exact b0)) (j + 1) (by omega)
      (hcu.entry rfl callee).2.2.1 h1 h2 h3)
  rcases hcall1 with hs | ⟨u1, hu1, m1, d1, g1, k1, b1, lke, lo1⟩
  · exact Or.inl (seq_stop v1 _ _ hs)
  rw [seq_normal _ hu1]
  obtain ⟨ke, hke⟩ : ∃ ke, ke = ConLeche.Frontend.keyEnd b (j + 1) := ⟨_, rfl⟩
  rw [← hke] at lke hstep
  have hkeL := keyEnd_eq hp _ (j + 1) rfl
  rw [← hke, hj1] at hkeL
  have hz := eval_eq_c u1 sK ke.toNat 0 (usz_lt ke) (by decide) lke
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl] at hz
  rw [ite_word u1 _ _ _ _ hz]
  by_cases hk0 : ke.toNat = 0
  · simp only [bw, hk0, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u1)
  simp only [bw, hk0, ↓reduceIte, ne_eq, not_true_eq_false]
  have hk0' : (ke == 0) = false := beq_eq_false_iff_ne.mpr (fun h => hk0 (by rw [h]; rfl))
  rw [hk0'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  obtain ⟨hkel, hjke⟩ := keyEndL_lt b.data.toList (j.toNat + 1) (by rw [← hkeL]; exact hk0)
  rw [← hkeL] at hkel hjke
  replace hkel : ke.toNat < b.size := by simpa using hkel
  have lof : ∀ y, y ≠ sK → u1.locals.lookup y = v1.locals.lookup y := lo1
  -- valueAt
  obtain ⟨wv, lv0⟩ := hscr1 sV (by simp)
  have hcall2 := call4_ret u1 sV fValueAt sB sN sI sK vaFun (vv sB) (vv sN) (vv sI) (vv sK) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 j.toNat) (BitVec.ofNat 64 ke.toNat)
    (BitVec.ofNat 64 (ConLeche.Frontend.valueAt b j ke).toNat) wv (by decide)
    (by rw [k1]; exact hcu.2.2.2.2.2.2.2.2.2.2.2.1)
    (eval_vv u1 sB _ (by rw [lof sB (by decide)]; lk [v1, v0]; exact lb))
    (eval_vv u1 sN _ (by rw [lof sN (by decide)]; lk [v1, v0]; exact ln))
    (eval_vv u1 sI _ (by rw [lof sI (by decide)]; exact li1)) (eval_vv u1 sK _ lke)
    (by rw [lof sV (by decide)]; exact lv0)
    (fun callee h1 h2 h3 h4 => valueAt_refines (callEntryStateHOLFinite u1 callee) A b hp
      (bytesAt_congr hb (by exact m1.trans m0) (by exact d1.trans d0) (by exact b1.trans b0)) j ke hkel
      ((hcu.congr k1).entry rfl callee).1 h1 h2 h3 h4)
  rcases hcall2 with hs | ⟨u2, hu2, m2, d2, g2, k2, b2, lv2, lo2⟩
  · exact Or.inl (seq_stop u1 _ _ hs)
  rw [seq_normal _ hu2]
  obtain ⟨v, hv⟩ : ∃ v, v = ConLeche.Frontend.valueAt b j ke := ⟨_, rfl⟩
  rw [← hv] at lv2 hstep
  have hvL := valueAt_eq hp j ke hkel
  rw [← hv] at hvL
  have hvb : v.toNat ≤ b.size := by
    have := valueAtL_le b.data.toList j.toNat ke.toNat (by simp; omega) (by simpa using hkel)
    rw [hvL]; simpa using this
  have li2 : u2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo2 sI (by decide), lof sI (by decide)]; exact li1
  rw [ite_word u2 _ _ _ _ (ConsLoop.eval_cmp_of u2 .equal (vv sV) (vv sI) _ _ (eval_vv u2 sV _ lv2)
    (eval_vv u2 sI _ li2)), bw_eq _ _ (by omega) (by omega)]
  by_cases hvj : v.toNat = j.toNat
  · simp only [bw, hvj, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u2)
  simp only [bw, hvj, ↓reduceIte, ne_eq, not_true_eq_false]
  have hvj' : (v == j) = false := beq_eq_false_iff_ne.mpr (fun h => hvj (by rw [h]))
  rw [hvj'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  -- keyAt
  obtain ⟨wq, lq0⟩ := hscr1 sKK (by simp)
  have hkl : (ke - (j + 1)).toNat = ke.toNat - (j.toNat + 1) := by
    rw [USize.toNat_sub_of_le, hj1]; rw [USize.le_iff_toNat_le, hj1]; omega
  have hcall3 := call4_ret u2 sKK fKeyAt sB sN sI sL kaFun (vv sB) (vv sN) (vv sI)
    (.op .sub [vv sK, .op .add [vv sI, .const 1]]) A (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 j.toNat)
    (BitVec.ofNat 64 (ke - (j + 1)).toNat)
    (BitVec.ofNat 64 (ConLeche.Frontend.keyAt b j (ke - (j + 1))).ctorIdx) wq (by decide)
    (by rw [k2, k1]; exact hcu.2.2.2.2.2.2.2.2.2.2.2.2)
    (eval_vv u2 sB _ (by rw [lo2 sB (by decide), lof sB (by decide)]; lk [v1, v0]; exact lb))
    (eval_vv u2 sN _ (by rw [lo2 sN (by decide), lof sN (by decide)]; lk [v1, v0]; exact ln))
    (eval_vv u2 sI _ li2)
    (by
      have lk2 : u2.locals.lookup sK = some (.val (.word (BitVec.ofNat 64 ke.toNat))) := by
        rw [lo2 sK (by decide)]; exact lke
      simp [vv, evalHOLExact, evalListHOLExact, lk2, li2, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [hkl]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega)
    (by rw [lo2 sKK (by decide), lof sKK (by decide)]; exact lq0)
    (fun callee h1 h2 h3 h4 => keyAt_refines (callEntryStateHOLFinite u2 callee) A b hp
      (bytesAt_congr hb (by exact m2.trans (m1.trans m0)) (by exact d2.trans (d1.trans d0))
        (by exact b2.trans (b1.trans b0))) j (ke - (j + 1)) (by omega) h1 h2 h3 h4)
  rcases hcall3 with hs | ⟨u3, hu3, m3, d3, g3, k3, b3, lq3, lo3⟩
  · exact Or.inl (seq_stop u2 _ _ hs)
  rw [seq_normal _ hu3]
  -- the dispatch, at the key context
  have lo : ∀ y, y ≠ sKK → y ≠ sV → y ≠ sK → u3.locals.lookup y = v1.locals.lookup y := fun y h1 h2 h3 => by
    rw [lo3 y h1, lo2 y h2, lof y h3]
  have hlc : LCtx t A b j v ik idx pl u3 :=
    { mem := m3.trans (m2.trans (m1.trans m0)), dom := d3.trans (d2.trans (d1.trans d0)),
      code := k3.trans (k2.trans (k1.trans c0)), glob := g3.trans (g2.trans (g1.trans g0)),
      be := b3.trans (b2.trans (b1.trans b0)),
      lb := by rw [lo sB (by decide) (by decide) (by decide), lov sB (by decide)]; exact lb,
      ln := by rw [lo sN (by decide) (by decide) (by decide), lov sN (by decide)]; exact ln,
      li := by rw [lo3 sI (by decide)]; exact li2,
      lv := by rw [lo3 sV (by decide)]; exact lv2,
      lik := by rw [lo sIK (by decide) (by decide) (by decide)]; exact lik1,
      lidx := by rw [lo sIdx (by decide) (by decide) (by decide), lov sIdx (by decide)]; exact lidx,
      pl0 := ⟨wpl, ws0, by rw [lo sPl (by decide) (by decide) (by decide)]; exact lpl1,
        by rw [lo _ (by decide) (by decide) (by decide), lov _ (by decide)]; exact ls0, hpl⟩,
      lg := by rw [lo sG (by decide) (by decide) (by decide)]; exact lg1,
      lw := ⟨_, by rw [lo sW (by decide) (by decide) (by decide)]; exact lw1⟩,
      scratch := by
        intro x hx
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, by rw [lo sC (by decide) (by decide) (by decide)]; exact lc1⟩
        · exact ⟨_, by rw [lo3 sK (by decide), lo2 sK (by decide)]; exact lke⟩
        · exact ⟨_, by rw [lo3 sV (by decide)]; exact lv2⟩
        · exact ⟨_, lq3⟩
        · obtain ⟨we, le⟩ := hscr1 sE2 (by simp)
          exact ⟨we, by rw [lo sE2 (by decide) (by decide) (by decide)]; exact le⟩,
      hj := hjl, hv := hvb }
  exact lineDispatch_spec t A b hp hb hc0 R j v ik idx pl _ lineTblP u3 (fun e he => he) hlc lq3
    (by rw [lineTblP_toLAct, ← hR, hstep]; exact (lineBranch_eq _ _ _ _ _ _ _ _).symm)

end

section
variable {σ : Type}

/-- **The Pancake line loop refines the table's**: from the invariant it stops, or exits with `go = 0`
where con-leche's line end has accepted the line. -/
theorem lineLoopP_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (R : ScanRes LineRec)
    (u : PanSemStateFiniteExact 64 σ) (hu : LnI t A b R u) :
    Stop (evaluateHOLFiniteState u lineLoopP).1 ∨ ((evaluateHOLFiniteState u lineLoopP).1 = none ∧
      LnI t A b R (evaluateHOLFiniteState u lineLoopP).2 ∧
      (evaluateHOLFiniteState u lineLoopP).2.locals.lookup sG = some (.val (.word 0))) := by
  have := while_stop (vv sG) lineBody (LnI t A b R)
    (fun u => LnI t A b R u ∧ u.locals.lookup sG = some (.val (.word 0)))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, j, wm, ik, idx, pl, wpl, ws0, _, _, _, _, _, _, _, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, _⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        exact line_step t A b hp hb hc R u hu hg
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, hg⟩, fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

end

end ConPanqueque.Scan

/-! # `scanLineFwd` -/

namespace ConPanqueque.Scan

open ConLeche.Frontend
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

/-- The line's kind word: `0` a blank line or an incomplete tail, `1` a record. -/
def sLK := ofString "lk"

/-- One line from `i`: whitespace, then a newline (blank), the end of the buffer (incomplete: next
position `0`), or a record and whitespace to the newline.  The next position is left in `i`. -/
def lineStmt : ProgHOL 64 :=
  .seq (callTo sE2 fSkipWs [vv sB, vv sN, vv sI])
    (.seq (bAt sC (vv sE2))
      (.ite (.cmp .equal (vv sC) (.const 10))
        (.seq (.assign .local sLK (.const 0)) (.assign .local sI (.op .add [vv sE2, .const 1])))
        (.ite (.cmp .lower (vv sE2) (vv sN))
          (.ite (.cmp .equal (vv sC) (.const 123))
            (.seq (.assign .local sI (.op .add [vv sE2, .const 1]))
              (.seq lineLoopP
                (.seq (callTo sE2 fSkipWs [vv sB, vv sN, vv sI])
                  (.seq (bAt sC (vv sE2))
                    (.ite (.cmp .equal (vv sC) (.const 10))
                      (.seq (.assign .local sLK (.const 1)) (.assign .local sI (.op .add [vv sE2, .const 1])))
                      (.ite (.cmp .lower (vv sE2) (vv sN)) hang
                        (.seq (.assign .local sLK (.const 1)) (.assign .local sI (.const 0)))))))))
            hang)
          (.seq (.assign .local sLK (.const 0)) (.assign .local sI (.const 0))))))

section
variable {σ : Type}

/-- What a scanned line leaves: con-leche's `scanLineFwd` accepted it; a record's locals. -/
def LineOut (b : ByteArray) (i : USize) (u : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ (rec : LineRec) (next : USize), scanLineFwd b i = .ok rec next ∧
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 next.toNat))) ∧
    ((rec = .blank ∧ u.locals.lookup sLK = some (.val (.word 0))) ∨
     (u.locals.lookup sLK = some (.val (.word 1)) ∧
      ∃ (ik : UInt8) (idx : Nat) (pl : LinePayload) (wpl ws0 : BitVec 64) (j0 j' : USize),
        u.locals.lookup sIK = some (.val (.word (BitVec.ofNat 64 ik.toNat))) ∧
        u.locals.lookup sIdx = some (.val (.word (BitVec.ofNat 64 (min idx natCap)))) ∧
        u.locals.lookup sPl = some (.val (.word wpl)) ∧
        u.locals.lookup (slotName 0) = some (.val (.word ws0)) ∧ PlOK b wpl ws0 pl ∧
        lineEnd j0 ik idx pl = .ok rec j'))

theorem lineStmt_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (u : PanSemStateFiniteExact 64 σ)
    (m0 : u.memory = t.memory) (d0 : u.memaddrs = t.memaddrs) (c0 : u.code = t.code) (g0 : u.globals = t.globals)
    (b0 : u.be = t.be)
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (lg : u.locals.lookup sG = some (.val (.word 1)))
    (lw : u.locals.lookup sW = some (.val (.word 1)))
    (lik : u.locals.lookup sIK = some (.val (.word 0)))
    (lidx : u.locals.lookup sIdx = some (.val (.word 0)))
    (lpl : u.locals.lookup sPl = some (.val (.word 0)))
    (ls0 : ∃ w, u.locals.lookup (slotName 0) = some (.val (.word w)))
    (llk : ∃ w, u.locals.lookup sLK = some (.val (.word w)))
    (scr : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState u lineStmt).1 ∨ ((evaluateHOLFiniteState u lineStmt).1 = none ∧
      LineOut b i (evaluateHOLFiniteState u lineStmt).2 ∧
      (evaluateHOLFiniteState u lineStmt).2.memory = t.memory ∧
      (evaluateHOLFiniteState u lineStmt).2.memaddrs = t.memaddrs ∧
      (evaluateHOLFiniteState u lineStmt).2.globals = t.globals ∧
      (evaluateHOLFiniteState u lineStmt).2.code = t.code ∧
      (evaluateHOLFiniteState u lineStmt).2.be = t.be) := by
  sorry

end

end ConPanqueque.Scan
