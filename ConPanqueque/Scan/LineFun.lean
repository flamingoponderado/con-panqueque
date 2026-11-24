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
end

end ConPanqueque.Scan
