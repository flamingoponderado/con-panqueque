import ConPanqueque.T.Ind.GenRecCheck
import ConPanqueque.T.Ind.LargeElim

/-!
# `classStreamRecs` over any number of recursors

`csrBody(or, i, n)`: recursor `i`'s record (the pointer-block cell `or + 8 (i + 1)`), its constant checked
(`checkConstantVal … false false false`, `ccv`), then itself at `i + 1`, until `i` reaches `n`. `csr_spec` refines
`classStreamRecs mode fe (rcs.drop i)`, whose answer is the recursors' constants (`PostCSR`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def csrO := ofString "csr_o"
def csrI := ofString "csr_i"
def csrN := ofString "csr_n"
def csrR := ofString "csr_r"
def csrQ := ofString "csr_q"
def csrX := ofString "csr_x"
def csrY := ofString "csr_y"
def fCsr := ofString "classStreamRecs"

def csrParams : List MlS := [csrO, csrI, csrN]
def csrLocals : List MlS := [csrR, csrQ, csrX, csrY]

def csrBody (C : Ctx) : ProgHOL 64 := prologue csrLocals
  (.ite (.cmp .lower (vv csrI) (vv csrN))
    (.seq (.assign .local csrR (.load .one (.op .add [vv csrO, .op .add [.panop .mul [vv csrI, .const 8], .const 8]])))
    (.seq (.assign .local csrQ (.load .one (vv csrR)))
    (.seq (.call (some (some (.local, csrX), none)) fCcv [vv csrQ, .const 0, .const 0, .const 0])
    (.seq (.call (some (some (.local, csrY), none)) fCsr [vv csrO, .op .add [vv csrI, .const 1], vv csrN])
      (.return (.const 0))))))
    (.return (.const 0)))

structure CSRCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  gcc : GCCCodes C
  pim : C.code.lookup fPim = some (Decl.pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one)
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  ccv : C.code.lookup fCcv = some (ccvParams.map (fun p => (p, ShapeHOL.one)), ccvBody C, .one)
  self : C.code.lookup fCsr = some (csrParams.map (fun p => (p, ShapeHOL.one)), csrBody C, .one)

section
variable {σ : Type}

theorem csr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ csrLocals → (ctxEnv C ++ csrParams.zip vals).get x = none :=
  Knot.params_none C csrLocals csrParams vals (by decide) (by decide)

/-- The answer: the recursors' constants, the heap grown, the state related. -/
def PostCSR (C : Ctx) (cvs : List IConstantVal) (r : List IConstantVal) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  r = cvs ∧ Decl.PostU C () w s' st

theorem postCSR_locals (C : Ctx) (cvs : List IConstantVal) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostCSR C cvs a w s' st → PostCSR C cvs a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, H', hp, hsr⟩ => ⟨h0, H', hp, sr_of_eq hsr rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **`classStreamRecs`** over the recursors from `i` on. -/
theorem csr_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CSRCodes mode C)
    (rcs : List RecShape) (or_ : Nat) (hR : PtrsRep C C.H or_ (RecRep C C.H) rcs) (hrl : rcs.length < 2 ^ 58)
    (hlr : ∀ rc ∈ rcs, rc.cvR.levelParams.length < 2 ^ 59)
    (hks : ∀ rc ∈ rcs, ∃ ks : List ConLeche.Name, ∃ hkl : ks.length = rc.cvR.levelParams.length,
      ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (ks[j]'(by omega))) :
    ∀ f i (H : List (BitVec 64)) (s : AState), rcs.length - i = f → i ≤ rcs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (csrParams.zip [cellA C or_, BitVec.ofNat 64 i, BitVec.ofNat 64 rcs.length]))
        (csrBody C) s (classStreamRecs mode C.fe (rcs.drop i))
        (PostCSR (ctxH C H) ((rcs.drop i).map (·.cvR))) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = rcs.length := by omega
    subst hin
    refine specR_prologue (postCSR_locals _ _) (csr_none _ _) ?_
    have hlw := nd_lt_iff rcs.length rcs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, csrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < rcs.length := by omega
    refine specR_prologue (postCSR_locals _ _) (csr_none _ _) ?_
    have hlw := nd_lt_iff i rcs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, csrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oi, hoi, hrep⟩ := hR.2 i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) csrR _ (or_ + 1 + i) _ (get_prefix hoi hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, csrParams, ctxEnv]; exact cellA_mulIdx C or_ i (by omega)) ?_
    obtain ⟨⟨ocv, hocv, hcvr⟩, -, -, -, -, -⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxH C H) csrQ (vv csrR) oi _ (get_prefix hocv hp) (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin]
    simp only [classStreamRecs, List.map_cons]
    obtain ⟨hn0, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcvr
    subst hwlo
    have hmem : rcs[i] ∈ rcs := List.getElem_mem _
    obtain ⟨ks, hkl, hksd⟩ := hks _ hmem
    have hok1 := ctxOK_H hok H
    refine specR_callNIH (C := ctxH C H) csrX fCcv ccvParams [vv csrQ, .const 0, .const 0, .const 0] (ccvBody C)
      [cellA C ocv, boolW false, boolW false, boolW false] (by decide) rfl (by decide) (by ctx_tr hc.ccv)
      ⟨by simp +decide [sev, Env.get_cons], rfl, rfl, rfl, trivial⟩
      (Decl.PostU (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccvParams _ rfl hlk)
        (ccv_full mode (ctxH C H) hok1 (by ctx_tr hc.gcc.hg) (by ctx_tr hc.gcc.hpr) (by ctx_tr hc.pim) ra hs
          (kcodes_H hc.k H) (allCodes_H hc.ac H)
          (by ctx_tr hc.gcc.hcl) (by ctx_tr hc.gcc.hlso) (by ctx_tr hc.gcc.hndh) (by ctx_tr hc.gcc.hndg)
          (by ctx_tr hc.gcc.hlbb) (by ctx_tr hc.gcc.hcB) (by ctx_tr hc.gcc.hbvb) (by ctx_tr hc.gcc.hhf)
          (by ctx_tr hc.gcc.hcF) (by ctx_tr hc.gcc.hfvb) (by ctx_tr hc.gcc.hat) (by ctx_tr hc.gcc.hal)
          (by ctx_tr hc.gcc.hcrff) (by ctx_tr hc.gcc.hcrf) (by ctx_tr hc.gcc.hens) C.fe rfl rcs[i].cvR false false false
          ocv ol (get_prefix hn0 hp) (get_prefix hwl hp) (get_prefix hty hp) (blkAt_mono hebl hp)
          (by have := hlr _ hmem; omega) ks hkl hksd s))
      (fun _ w s2 H2 hp2 _ => ?_)
    have hp2' : H <+: H2 := hp2
    refine specR_callNIH (C := ctxH C H2) csrY fCsr csrParams
      [vv csrO, .op .add [vv csrI, .const 1], vv csrN] (csrBody C)
      [cellA C or_, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rcs.length] (by decide) rfl (by decide) (by ctx_tr hc.self)
      ⟨by simp +decide [sev, Env.get_cons, Env.get, csrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, csrParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, csrParams, ctxEnv], trivial⟩
      (PostCSR (ctxH C H2) ((rcs.drop (i + 1)).map (·.cvR)))
      (fun r _ _ _ => r = (rcs.drop (i + 1)).map (·.cvR))
      (fun a w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu csrParams _ rfl hlk)
        (ih (i + 1) H2 s2 (by omega) (by omega) (hp.trans hp2')))
      (fun r w s3 H3 hp3 hr => ?_)
    subst hr
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, H3, hp2'.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
