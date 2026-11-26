import ConPanqueque.T.Ind.BlockTables2
import ConPanqueque.T.Decl.TblIns

/-!
# A projection table installed (`IFEnv.pushTable`)

`twBody`: the table's level parameters and bodies copied into environment blocks, its six-word record written,
its structure's name inserted into the table memo.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

def twT := ofString "tw_t"
def twNm := ofString "tw_nm"
def twLp := ofString "tw_lp"
def twLn := ofString "tw_ln"
def twNp := ofString "tw_np"
def twCt := ofString "tw_ct"
def twNf := ofString "tw_nf"
def twBp := ofString "tw_bp"
def twBn := ofString "tw_bn"
def twLb := ofString "tw_lb"
def twBb := ofString "tw_bb"
def twR1 := ofString "tw_r1"
def twR2 := ofString "tw_r2"
def twX := ofString "tw_x"
def twRi := ofString "tw_ri"
def fTw := ofString "pushTable"

def twParams : List MlS := [twT]
def twLocals : List MlS := [twNm, twLp, twLn, twNp, twCt, twNf, twBp, twBn, twLb, twBb, twR1, twR2, twX, twRi]

def twBody (C : Ctx) : ProgHOL 64 := prologue twLocals
  (.seq (.assign .local twNm (.load .one (vv twT)))
  (.seq (.assign .local twLp (.load .one (.op .add [vv twT, .const 8])))
  (.seq (.assign .local twLn (.load .one (vv twLp)))
  (.seq (.assign .local twNp (.load .one (.op .add [vv twT, .const 16])))
  (.seq (.assign .local twCt (.load .one (.op .add [vv twT, .const 24])))
  (.seq (.assign .local twNf (.load .one (.op .add [vv twT, .const 32])))
  (.seq (.assign .local twBp (.load .one (.op .add [vv twT, .const 40])))
  (.seq (.assign .local twBn (.load .one (vv twBp)))
  (envBlkP C twLb twLp twLn twR1
  (envBlkP C twBb twBp twBn twR2
  (envRecP C twX [vv twNm, vv twLb, vv twNp, vv twCt, vv twNf, vv twBb]
  (tbInsP C (vv twNm) (vv twX) twRi
  (.return (.const 0))))))))))))))

section
variable {σ : Type}

theorem tw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ twLocals → (ctxEnv C ++ twParams.zip vals).get x = none :=
  Knot.params_none C twLocals twParams vals (by decide) (by decide)

/-- The table installed: the next context. -/
def PostTW (C : Ctx) (t : IProjTable) (s : AState) (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ EH tblM, C.EH <+: EH ∧ CtxOK (ctxTb C (C.fe.pushTable t) EH tblM) ∧ SR (ctxTb C (C.fe.pushTable t) EH tblM) s' st

theorem postTW_locals (C : Ctx) (t : IProjTable) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostTW C t s a w s' st → PostTW C t s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, EH, M, h1, h2, h3⟩ => ⟨h0, EH, M, h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

set_option maxHeartbeats 32000000 in
/-- **A projection table installed.** -/
theorem tw_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (t : IProjTable) (o : Nat) (htv : TblVRep C C.H o t) (hs : (C.fe.find? t.structName).isSome = true)
    (hden : NewTblDen t C.St) (hll : t.levelParams.length < 2 ^ 60) (hbl : t.bodies.size < 2 ^ 60)
    (hnp : t.numParams < 2 ^ 63) (hnf : t.numFields < 2 ^ 63) (s : AState) :
    SpecR (σ := σ) (Pre C s (twParams.zip [cellA C o])) (twBody C) s (pure ()) (PostTW C t s) := by
  refine specR_prologue (postTW_locals C t s) (tw_none C _) ?_
  obtain ⟨h0, ⟨ol, h1, hlb⟩, h2, h3, h4, ⟨ob, h5, hbb⟩⟩ := htv
  refine UD.specR_heapLoadI' (C := C) twNm _ o _ h0 (by decide) (by simp +decide [sev, Env.get, twParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) twLp _ (o + 1) _ h1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, twParams, ctxEnv]; exact cellA_add8 C o) ?_
  have hll0 : C.H[ol]? = some (BitVec.ofNat 64 (t.levelParams.map Enc.idxW).length) := hlb.1
  refine UD.specR_heapLoadI' (C := C) twLn (vv twLp) ol _ hll0 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) twNp _ (o + 2) _ h2 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, twParams, ctxEnv]; exact cellA_add_ofNat C o 2) ?_
  refine UD.specR_heapLoadI' (C := C) twCt _ (o + 3) _ h3 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, twParams, ctxEnv]; exact cellA_add_ofNat C o 3) ?_
  refine UD.specR_heapLoadI' (C := C) twNf _ (o + 4) _ h4 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, twParams, ctxEnv]; exact cellA_add_ofNat C o 4) ?_
  refine UD.specR_heapLoadI' (C := C) twBp _ (o + 5) _ h5 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, twParams, ctxEnv]; exact cellA_add_ofNat C o 5) ?_
  have hbn0 : C.H[ob]? = some (BitVec.ofNat 64 (t.bodies.toList.map Enc.idxW).length) := hbb.1
  refine UD.specR_heapLoadI' (C := C) twBn (vv twBp) ob _ hbn0 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_envBlkI hok hcp twLb twLp twLn twR1 ol _ hlb (by simpa using hll) (by decide) (by decide)
    (by decide) (by decide) (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
    (fun EH1 w1 hp1 heb1 => ?_)
  have hok1 := ctxOK_E hok hp1
  refine specR_envBlkI hok1 hcp twBb twBp twBn twR2 ob _ hbb (by simpa using hbl) (by decide) (by decide)
    (by decide) (by decide) (by simp +decide [Env.get_cons]; rfl) (by simp +decide [Env.get_cons])
    (fun EH2 w2 hp2 heb2 => ?_)
  have hok2 := ctxOK_E hok1 hp2
  refine specR_envRecI hok2 twX [vv twNm, vv twLb, vv twNp, vv twCt, vv twNf, vv twBb]
    [Enc.idxW t.structName, ecell C C.EH.length, BitVec.ofNat 64 t.numParams, Enc.idxW t.ctor,
      BitVec.ofNat 64 t.numFields, ecell C EH1.length] (by decide) rfl (by decide)
    (fun w j hj hj' => by
      rcases j with _ | _ | _ | _ | _ | _ | j <;>
        first | (simp +decide [sev, Env.get_cons]; done) | (simp +decide [sev, Env.get_cons]; rfl) | (simp at hj; omega))
    (fun EH3 hp3 hl3 hv3 => ?_)
  have hpE : C.EH <+: EH3 := hp1.trans (hp2.trans hp3)
  have g : ∀ j (hj : j < 6), EH3[EH2.length + j]? = some ([Enc.idxW t.structName, ecell C C.EH.length,
      BitVec.ofNat 64 t.numParams, Enc.idxW t.ctor, BitVec.ofNat 64 t.numFields, ecell C EH1.length] : List (BitVec 64))[j] :=
    fun j hj => hv3 j (by simpa using hj)
  have htbE : TblE C.EB EH3 EH2.length t :=
    ⟨g 0 (by decide), ⟨ecell C C.EH.length, g 1 (by decide), C.EH.length, rfl,
        eblk_mono heb1 (hp2.trans hp3)⟩,
      ⟨g 2 (by decide), hnp⟩, g 3 (by decide), ⟨g 4 (by decide), hnf⟩,
      ⟨ecell C EH1.length, g 5 (by decide), EH1.length, rfl, eblk_mono heb2 hp3⟩⟩
  refine specR_atEntry fun t3 ht3 => ?_
  have hden3 : NewTblDen t s.store := ⟨fun n hn => denoteN_isSome_ext ht3.sr.floor (hden.1 n hn),
    fun b hb => denoteE_isSome_ext ht3.sr.floor (hden.2.1 b hb), hden.2.2⟩
  refine specR_tbInsI (C := C) hok hcS hcI t hs EH3 EH2.length hpE hden3 (vv twNm) (vv twX) twRi (by decide)
    (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons]; rfl)
    (by simp +decide [Env.get_cons, Env.get, twParams, ctxEnv]) (fun wr => ?_)
  have hokT := ctxOK_tb hok hpE htbE (find?_pushTable C.fe t) (findTable?_pushTable C.fe t hs)
  exact specR_returnI _ 0 rfl (fun t4 ht4 => ⟨rfl, EH3, _, hpE, hokT, sr_of_eq ht4.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
