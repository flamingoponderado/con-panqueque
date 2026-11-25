import ConPanqueque.T.Ind.IotaRecOf
import ConPanqueque.T.Ex.InstLift

/-!
# A rule's parts, read off the recursor's type (`iotaPartsOfAt`)

`liftFieldDoms amt fd j`: each field domain lifted by `amt` above its own position; `liftIdxArgs amt nT nF as`:
each index argument with the induction hypotheses dropped, then lifted above the fields.  Both build their
lists as blocks (`prependP`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA

def lfA := ofString "lf_a"
def lfI := ofString "lf_i"
def lfM := ofString "lf_m"
def lfT := ofString "lf_t"
def lfX := ofString "lf_x"
def fLiftFields := ofString "liftFieldDoms"

def lfParams : List MlS := [lfA, lfI, lfM, lfT]
def lfLocals : List MlS := gaaLocals ++ [lfX]

/-- Fields `i … m - 1` of the block at `a`, field `j` lifted by `amt` above `j`. -/
def lfBody (C : Ctx) : ProgHOL 64 := prologue lfLocals
  (.ite (.cmp .lower (vv lfI) (vv lfM))
    (.seq (.assign .local lfX (.load .one (.op .add [vv lfA, .op .add [.panop .mul [vv lfI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, lA1), none)) ExL.fLiftF [.const (BitVec.ofNat 64 coreWalkFuel), vv lfT, vv lfI, vv lfX])
    (.seq (.call (some (some (.local, ExS.lY), none)) fLiftFields [vv lfA, .op .add [vv lfI, .const 1], vv lfM, vv lfT])
      (prependP C lA1))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem lf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lfLocals → (ctxEnv C ++ lfParams.zip vals).get x = none :=
  Knot.params_none C lfLocals lfParams vals (by decide) (by decide)

theorem liftFieldDoms_cons (amt : Nat) (d : EIdx) (ds : List EIdx) (j : Nat) :
    liftFieldDoms amt (d :: ds) j = (do
      let d' ← liftLooseBVarsFast coreWalkFuel amt j d
      let rest ← liftFieldDoms amt ds (j + 1)
      pure (d' :: rest)) := rfl

theorem liftFieldDoms_nil (amt j : Nat) : liftFieldDoms amt [] j = pure [] := rfl

/-- **`liftFieldDoms`** from field `i`. -/
theorem lf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fLiftFields = some (lfParams.map (fun p => (p, ShapeHOL.one)), lfBody C, .one))
    (hcF : C.code.lookup ExL.fLiftF = some ([(pFu, .one), (ExL.pA, .one), (pD, .one), (pH, .one)], ExL.fastBodyL C, .one))
    (hcl : ExL.CodesL C (ExL.bodyL C)) (xs : List EIdx) (oa amt : Nat) (hl : xs.length < 2 ^ 61) (hamt : amt < 2 ^ 63) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → EElems H oa xs → xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (lfParams.zip [cellA C oa, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length,
        BitVec.ofNat 64 amt])) (lfBody C) s (liftFieldDoms amt (xs.drop i) i) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hp hb hf hi
    have him : i = xs.length := by omega
    subst him
    refine specR_prologue (postA_locals _) (lf_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, liftFieldDoms_nil]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by simp +decide [ctxLocals, lfLocals, gaaLocals, inst1Locals])
      (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    exact specR_returnI _ _ (by simp [sev] <;> rfl) (fun t ht => ⟨_, H2.length, hp2.trans (img1_prefix _ _ _ hws), rfl,
      ⟨by simpa using img1_get H2 ws (0 : BitVec 64) hws, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hp hb hf hi
    have him : i < xs.length := by omega
    refine specR_prologue (postA_locals _) (lf_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, lfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr him])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons him, liftFieldDoms_cons]
    have hx : (ctxH C H).H[oa + 1 + i]? = some (Enc.idxW xs[i]) := hb i him
    refine UD.specR_heapLoadI' (C := ctxH C H) lfX _ (oa + 1 + i) _ hx (by simp +decide [ctxLocals, lfLocals, gaaLocals, inst1Locals])
      (by simp +decide [sev, Env.get, lfParams, ctxEnv]; exact cellA_mulIdx C oa i (by omega)) ?_
    refine ILP.callE_spec (C := ctxH C H) lA1 ExL.fLiftF [pFu, ExL.pA, pD, pH]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv lfT, vv lfI, vv lfX] (ExL.fastBodyL C)
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 amt, BitVec.ofNat 64 i, Enc.idxW xs[i]]
      (by decide) rfl (by simp +decide [ctxLocals, lfLocals, gaaLocals, inst1Locals]) hcF
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, lfParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, lfParams, ctxEnv],
        by simp [sev, Env.get_cons], trivial⟩
      (ExL.fastL_spec ra (ctxH C H) (ctxOK_H hok H) ⟨hcl.lift, hcl.memoGet, hcl.memoProbe, hcl.memoSet, hcl.memoIns,
        hcl.internApp, hcl.internLam, hcl.internForallE, hcl.internLet, hcl.internBVar, hcl.internProj⟩ s coreWalkFuel amt i xs[i]
        (by decide) hamt (by omega)) (fun y s1 => ?_)
    refine specR_congr (m' := liftFieldDoms amt (xs.drop (i + 1)) (i + 1) >>= fun ys => pure (y :: ys)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fLiftFields lfParams [vv lfA, .op .add [vv lfI, .const 1], vv lfM, vv lfT]
      (lfBody C) [cellA C oa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length, BitVec.ofNat 64 amt] (by decide) rfl
      (by simp +decide [ctxLocals, lfLocals, gaaLocals, inst1Locals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, lfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, lfParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, lfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, lfParams, ctxEnv], trivial⟩
      (PostA (ctxH C H)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lfParams _ rfl hlk)
        (ih (i + 1) H s1 hp hb (by omega) (by omega)))
      (fun ys wr s2 H2 hp2 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    exact prepend_spec C hok lA1 (Enc.idxW y) oy _ (by simp +decide [ctxLocals, lfLocals, gaaLocals, inst1Locals])
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hblk (by decide)
      (by simp +decide [Env.get_cons, Env.get, lfParams, ctxEnv]) (by decide)
      (fun H' o t hpH hbk hsr => ⟨H', o, hp2.trans hpH, rfl, by simpa using hbk, hsr⟩)

end

def liA := ofString "li_a"
def liI := ofString "li_i"
def liM := ofString "li_m"
def liT := ofString "li_t"
def liNT := ofString "li_nt"
def liNF := ofString "li_nf"
def liX := ofString "li_x"
def fLiftIdx := ofString "liftIdxArgs"

def liParams : List MlS := [liA, liI, liM, liT, liNT, liNF]
def liLocals : List MlS := gaaLocals ++ [liX]

def liBody (C : Ctx) : ProgHOL 64 := prologue liLocals
  (.ite (.cmp .lower (vv liI) (vv liM))
    (.seq (.assign .local liX (.load .one (.op .add [vv liA, .op .add [.panop .mul [vv liI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, liX), none)) fDropVars [vv liNT, vv liX])
    (.seq (.call (some (some (.local, lA1), none)) ExL.fLiftF [.const (BitVec.ofNat 64 coreWalkFuel), vv liT, vv liNF, vv liX])
    (.seq (.call (some (some (.local, ExS.lY), none)) fLiftIdx
        [vv liA, .op .add [vv liI, .const 1], vv liM, vv liT, vv liNT, vv liNF])
      (prependP C lA1)))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem li_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ liLocals → (ctxEnv C ++ liParams.zip vals).get x = none :=
  Knot.params_none C liLocals liParams vals (by decide) (by decide)

theorem liftIdxArgs_cons (amt nT nF : Nat) (a : EIdx) (as : List EIdx) :
    liftIdxArgs amt nT nF (a :: as) = (do
      let b ← exprDropVars nT a
      let c ← liftLooseBVarsFast coreWalkFuel amt nF b
      let rest ← liftIdxArgs amt nT nF as
      pure (c :: rest)) := rfl

/-- **`liftIdxArgs`** over arguments `i … m - 1`. -/
theorem li_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fLiftIdx = some (liParams.map (fun p => (p, ShapeHOL.one)), liBody C, .one))
    (hcF : C.code.lookup ExL.fLiftF = some ([(pFu, .one), (ExL.pA, .one), (pD, .one), (pH, .one)], ExL.fastBodyL C, .one))
    (hcl : ExL.CodesL C (ExL.bodyL C))
    (hcd : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one))
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (hcI : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcc : Codes C (body C))
    (xs : List EIdx) (oa m amt nT nF : Nat) (hm : m ≤ xs.length) (hl : xs.length < 2 ^ 61) (hamt : amt < 2 ^ 63)
    (hnT : nT < 2 ^ 63) (hnF : nF < 2 ^ 63) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → EElems H oa xs → m - i = f → i ≤ m →
      SpecR (σ := σ) (Pre (ctxH C H) s (liParams.zip [cellA C oa, BitVec.ofNat 64 i, BitVec.ofNat 64 m,
        BitVec.ofNat 64 amt, BitVec.ofNat 64 nT, BitVec.ofNat 64 nF])) (liBody C) s
        (liftIdxArgs amt nT nF ((xs.take m).drop i)) (PostA (ctxH C H)) := by
  have hcl' : ∀ H, ExL.CodesL (ctxH C H) (ExL.bodyL (ctxH C H)) := fun H => ⟨hcl.lift, hcl.memoGet, hcl.memoProbe,
    hcl.memoSet, hcl.memoIns, hcl.internApp, hcl.internLam, hcl.internForallE, hcl.internLet, hcl.internBVar, hcl.internProj⟩
  have hcc' : ∀ H, Codes (ctxH C H) (body (ctxH C H)) := fun H => ⟨hcc.inst1, hcc.memoGet, hcc.memoProbe, hcc.memoSet,
    hcc.memoIns, hcc.internApp, hcc.internLam, hcc.internForallE, hcc.internLet, hcc.internBVar, hcc.internProj⟩
  intro f
  induction f with
  | zero =>
    intro i H s hp hb hf hi
    have him : i = m := by omega
    subst him
    refine specR_prologue (postA_locals _) (li_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, liParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_eq_nil_of_le (by simp)]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by simp +decide [ctxLocals, liLocals, gaaLocals, inst1Locals])
      (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    exact specR_returnI _ _ (by simp [sev] <;> rfl) (fun t ht => ⟨_, H2.length, hp2.trans (img1_prefix _ _ _ hws), rfl,
      ⟨by simpa using img1_get H2 ws (0 : BitVec 64) hws, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hp hb hf hi
    have him : i < m := by omega
    refine specR_prologue (postA_locals _) (li_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i m (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, liParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr him])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [take_drop_cons' xs i m him hm, liftIdxArgs_cons]
    have hx : (ctxH C H).H[oa + 1 + i]? = some (Enc.idxW xs[i]) := hb i (by omega)
    refine UD.specR_heapLoadI' (C := ctxH C H) liX _ (oa + 1 + i) _ hx (by simp +decide [ctxLocals, liLocals, gaaLocals, inst1Locals])
      (by simp +decide [sev, Env.get, liParams, ctxEnv]; exact cellA_mulIdx C oa i (by omega)) ?_
    refine ILP.callE_spec (C := ctxH C H) liX fDropVars dvParams [vv liNT, vv liX] (dvBody C)
      [BitVec.ofNat 64 nT, Enc.idxW xs[i]] (by decide) rfl (by simp +decide [ctxLocals, liLocals, gaaLocals, inst1Locals]) hcd
      ⟨by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv], by simp [sev, Env.get_cons], trivial⟩
      (dv_spec ra (ctxH C H) (ctxOK_H hok H) hcd hcS hcI (hcc' H) nT (by omega) s xs[i]) (fun b s1 => ?_)
    refine ILP.callE_spec (C := ctxH C H) lA1 ExL.fLiftF [pFu, ExL.pA, pD, pH]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv liT, vv liNF, vv liX] (ExL.fastBodyL C)
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 amt, BitVec.ofNat 64 nF, Enc.idxW b]
      (by decide) rfl (by simp +decide [ctxLocals, liLocals, gaaLocals, inst1Locals]) hcF
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv],
        by simp [sev, Env.get_cons], trivial⟩
      (ExL.fastL_spec ra (ctxH C H) (ctxOK_H hok H) (hcl' H) s1 coreWalkFuel amt nF b (by decide) hamt hnF) (fun c s2 => ?_)
    refine specR_congr (m' := liftIdxArgs amt nT nF ((xs.take m).drop (i + 1)) >>= fun ys => pure (c :: ys)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fLiftIdx liParams
      [vv liA, .op .add [vv liI, .const 1], vv liM, vv liT, vv liNT, vv liNF]
      (liBody C) [cellA C oa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 m, BitVec.ofNat 64 amt, BitVec.ofNat 64 nT,
        BitVec.ofNat 64 nF] (by decide) rfl
      (by simp +decide [ctxLocals, liLocals, gaaLocals, inst1Locals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, liParams, ctxEnv], trivial⟩
      (PostA (ctxH C H)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu liParams _ rfl hlk)
        (ih (i + 1) H s2 hp hb (by omega) (by omega)))
      (fun ys wr s3 H2 hp2 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    exact prepend_spec C hok lA1 (Enc.idxW c) oy _ (by simp +decide [ctxLocals, liLocals, gaaLocals, inst1Locals])
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hblk (by decide)
      (by simp +decide [Env.get_cons, Env.get, liParams, ctxEnv]) (by decide)
      (fun H' o t hpH hbk hsr => ⟨H', o, hp2.trans hpH, rfl, by simpa using hbk, hsr⟩)

end

end ConPanqueque.T.Ind
