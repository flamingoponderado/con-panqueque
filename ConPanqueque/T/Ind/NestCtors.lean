import ConPanqueque.T.Ind.CtorChecks

/-!
# `nestCtors` at the root frame: every constructor of one member through the positivity walk

The state's constructor records (`ns.ctorNfs`) and the outputs (`(kinds, closed)` pairs) are pointer blocks, appended
to; `ns.keys`/`ns.active` stay empty (no container frame).  Checks that fail in the twin hang here.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

section
variable {σ : Type}

/-- **`whnf` at the checker's fuel, by the port**. -/
theorem whnfTop (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) {C : Ctx}
    (hok : CtxOK C) (hc : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hs : C.side = false) (s : AState)
    (d : Nat) (hd : d < 2 ^ 63) (e : EIdx) :
    Callee (σ := σ) C kParams [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s
      (whnf mode C.fe checkFuel d e) (PostK C) := by
  have : whnf mode C.fe checkFuel d e = (knot mode C checkFuel).whnf d e := by unfold knot whnf; rw [hs]; rfl
  rw [this]
  exact (Comp.knot_closed (σ := σ) ra mode checkFuel Comp.checkFuel_le C hok hc s hac).2.1 d e hd

end

def nctCs := ofString "nct_cs"
def nctJ := ofString "nct_j"
def nctNs := ofString "nct_ns"
def nctOuts := ofString "nct_outs"
def nctMs := ofString "nct_ms"
def nctNP := ofString "nct_np"
def nctHi := ofString "nct_hi"
def nctUs := ofString "nct_us"
def nctDH := ofString "nct_dh"
def nctDn := ofString "nct_dn"
def nctPs := ofString "nct_ps"
def nctL := ofString "nct_l"
def nctQ := ofString "nct_q"
def nctNF := ofString "nct_nf"
def nctLp := ofString "nct_lp"
def nctLn := ofString "nct_ln"
def nctNd := ofString "nct_nd"
def nctTp := ofString "nct_tp"
def nctCty := ofString "nct_cty"
def nctCr := ofString "nct_cr"
def nctTy := ofString "nct_ty"
def nctU := ofString "nct_u"
def nctFu := ofString "nct_fu"
def nctK0 := ofString "nct_k0"
def nctN0 := ofString "nct_n0"
def nctR3 := ofString "nct_r3"
def nctKs := ofString "nct_ks"
def nctNds := ofString "nct_nds"
def nctCur := ofString "nct_cur"
def nctCl := ofString "nct_cl"
def nctU4 := ofString "nct_u4"
def nctRh := ofString "nct_rh"
def nctG := ofString "nct_g"
def nctOcc := ofString "nct_occ"
def nctNm := ofString "nct_nm"
def nctNnf := ofString "nct_nnf"
def nctNs2 := ofString "nct_ns2"
def nctOp := ofString "nct_op"
def nctOuts2 := ofString "nct_outs2"
def nctR := ofString "nct_r"
def fNct := ofString "nestCtors"

def nctParams : List MlS := [nctCs, nctJ, nctNs, nctOuts, nctMs, nctNP, nctHi, nctUs, nctDH, nctDn, nctPs]
def nctLocals : List MlS := [nctL, nctQ, nctNF, nctLp, nctLn, nctNd, nctTp, nctCty, nctCr, nctTy, nctU, nctFu, nctK0,
  nctN0, nctR3, nctKs, nctNds, nctCur, nctCl, nctU4, nctRh, nctG, nctOcc, nctNm, nctNnf, nctNs2, nctOp, nctOuts2, nctR]

/-- The tail of one constructor's walk: the result head and indices, the record, the outputs, the next. -/
def nctTail (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, nctRh), none)) fNrh [vv nctCur])
  (.ite (.cmp .equal (vv nctRh) (.const 0)) hang
  (.seq (.call (some (some (.local, nctG), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv nctCur])
  (.seq (.call (some (some (.local, nctOcc), none)) fAnyNoc [vv nctG, .const 0, vv nctMs, vv nctNP, vv nctHi])
  (.ite (.cmp .equal (vv nctOcc) (.const 0))
    (.seq (.assign .local nctNm (.load .one (vv nctQ)))
    (.seq (.call (some (some (.local, nctNnf), none)) fNnf
        [vv nctNm, vv nctUs, vv nctPs, vv nctCl, vv nctMs, vv nctNP, vv nctPs])
    (.seq (.call (some (some (.local, nctNs2), none)) ExPre.fAppend [vv nctNs, vv nctNnf])
    (alloc2 C nctOp (vv nctKs) (vv nctCl)
    (.seq (.call (some (some (.local, nctOuts2), none)) ExPre.fAppend [vv nctOuts, vv nctOp])
    (.seq (.call (some (some (.local, nctR), none)) fNct
        [vv nctCs, .op .add [vv nctJ, .const 1], vv nctNs2, vv nctOuts2, vv nctMs, vv nctNP, vv nctHi, vv nctUs, vv nctDH,
          vv nctDn, vv nctPs])
      (.return (vv nctR))))))))
    hang))))

/-- One constructor's walk up to U4. -/
def nctStep (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local nctQ (.load .one (.op .add [.op .add [vv nctCs, .const 8], .shift .lsl (vv nctJ) (.const 4)])))
  (.seq (.assign .local nctNF (.load .one (.op .add [.op .add [vv nctCs, .const 16], .shift .lsl (vv nctJ) (.const 4)])))
  (.seq (.assign .local nctLp (.load .one (.op .add [vv nctQ, .const 8])))
  (.seq (.assign .local nctLn (.load .one (vv nctLp)))
  (.seq (.call (some (some (.local, nctNd), none)) fNdg [vv nctLp, .const 0, vv nctLn])
  (.ite (.cmp .equal (vv nctNd) (.const 0)) hang
  (.seq (.assign .local nctTp (.load .one (.op .add [vv nctQ, .const 16])))
  (.seq (.call (some (some (.local, nctCty), none)) ILP.fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv nctTp, vv nctLp, vv nctUs])
  (.seq (.call (some (some (.local, nctCr), none)) fNcr [vv nctMs, vv nctUs, vv nctDn, vv nctDH, vv nctCty])
  (.seq (.call (some (some (.local, nctTy), none)) fI [.const (BitVec.ofNat 64 checkFuel), vv nctHi, vv nctCr])
  (.seq (.call (some (some (.local, nctU), none)) fEns [.const (BitVec.ofNat 64 checkFuel), vv nctHi, vv nctTy])
  (.seq (.call (some (some (.local, nctFu), none)) fWwf [vv nctCr])
  (.ite (.cmp .notLower (vv nctFu) (.const (BitVec.ofNat 64 (2 ^ 58)))) hang
  (alloc1 C nctK0 (.const 0) (alloc1 C nctN0 (.const 0)
  (.seq (.call (some (some (.local, nctR3), none)) fNestFields
      [vv nctFu, vv nctHi, vv nctNF, .const 0, vv nctCr, vv nctK0, vv nctN0, vv nctMs, vv nctNP, vv nctHi])
  (.seq (.assign .local nctKs (.load .one (vv nctR3)))
  (.seq (.assign .local nctNds (.load .one (.op .add [vv nctR3, .const 8])))
  (.seq (.assign .local nctCur (.load .one (.op .add [vv nctR3, .const 16])))
  (.seq (.call (some (some (.local, nctCl), none)) fCtg [vv nctHi, .const 0, vv nctNds, .const 0, vv nctCur])
  (.seq (.call (some (some (.local, nctU4), none)) fU4 [vv nctKs, .const 0, vv nctNF, vv nctCl])
  (.ite (.cmp .equal (vv nctU4) (.const 0)) (nctTail C) hang)))))))))))))))))))))

def nctBody (C : Ctx) : ProgHOL 64 := prologue nctLocals
  (.seq (.assign .local nctL (.load .one (vv nctCs)))
  (.ite (.cmp .lower (vv nctJ) (vv nctL)) (nctStep C)
    (alloc2 C nctR (vv nctOuts) (vv nctNs) (.return (vv nctR)))))

structure NCTCodes (C : Ctx) : Prop where
  nf : NFCodes C
  nt : NTCodes C
  crest : CrestCodes C
  nnf : NNFCodes C
  cc : CCCodes C
  ctg : CTGCodes C
  ndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  ndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
  ilp : ILP.CodesILP C (ILP.ilpBody C)
  ilpf : C.code.lookup ILP.fInstLPF = some (ILP.ilpParams.map (fun p => (p, ShapeHOL.one)), ILP.ilpfBody C, .one)
  ens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one)
  self : C.code.lookup fNct = some (nctParams.map (fun p => (p, ShapeHOL.one)), nctBody C, .one)

end ConPanqueque.T.Ind
