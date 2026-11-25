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

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.Decl
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.ExSP

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

section
variable {σ : Type}

/-- A rule's parts at `o`: `[fieldDoms, indices, us, params]`, the lists as blocks. -/
def PartsRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (ip : IIotaParts) : Prop :=
  (∃ o1, H[o]? = some (cellA C o1) ∧ BlkAt H o1 (ip.fieldDoms.map Enc.idxW)) ∧
  (∃ o2, H[o + 1]? = some (cellA C o2) ∧ BlkAt H o2 (ip.idx.map Enc.idxW)) ∧
  H[o + 2]? = some (Enc.idxW ip.us) ∧
  (∃ o3, H[o + 3]? = some (cellA C o3) ∧ BlkAt H o3 (ip.params.map Enc.idxW))

theorem partsRep_mono {C : Ctx} {H H' : List (BitVec 64)} {o : Nat} {ip : IIotaParts} (h : PartsRep C H o ip)
    (hp : H <+: H') : PartsRep C H' o ip := by
  obtain ⟨⟨o1, a1, a2⟩, ⟨o2, b1, b2⟩, c, ⟨o3, d1, d2⟩⟩ := h
  exact ⟨⟨o1, get_prefix a1 hp, blkAt_mono a2 hp⟩, ⟨o2, get_prefix b1 hp, blkAt_mono b2 hp⟩, get_prefix c hp,
    ⟨o3, get_prefix d1 hp, blkAt_mono d2 hp⟩⟩

/-- An optional `IIotaParts`: `0` for none. -/
def PostIP (C : Ctx) (o : Option IIotaParts) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ ip, o = some ip → ∃ ob, w = cellA C ob ∧ PartsRep C H' ob ip

theorem postIP_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostIP C a w s' st → PostIP C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

def iqR := ofString "iq_rr"
def iqRP := ofString "iq_rp"
def iqN := ofString "iq_n"
def iqI := ofString "iq_i"
def iqF := ofString "iq_f"
def iqMb := ofString "iq_mb"
def iqMc := ofString "iq_mc"
def iqQ := ofString "iq_q"
def iqPb := ofString "iq_pb"
def iqPl := ofString "iq_pl"
def iqD := ofString "iq_d"
def iqS := ofString "iq_s"
def iqSc := ofString "iq_sc"
def iqIn := ofString "iq_in"
def iqAm := ofString "iq_am"
def iqFd := ofString "iq_fd"
def iqT := ofString "iq_t"
def iqTn := ofString "iq_tn"
def iqTb := ofString "iq_tb"
def iqA := ofString "iq_a"
def iqAl := ofString "iq_al"
def iqM1 := ofString "iq_m1"
def iqM := ofString "iq_m"
def iqIx := ofString "iq_ix"
def iqU := ofString "iq_u"
def iqPs := ofString "iq_ps"
def iqO := ofString "iq_o"
def fIotaPartsOf := ofString "iotaPartsOfAt"

def iqoParams : List MlS := [iqR, iqRP, iqN, iqI, iqF]
def iqoLocals : List MlS := [iqMb, iqMc, iqQ, iqPb, iqPl, iqD, iqS, iqSc, iqIn, iqAm, iqFd, iqT, iqTn, iqTb, iqA, iqAl,
  iqM1, iqM, iqIx, iqU, iqPs, iqO]

def iqoBody (C : Ctx) : ProgHOL 64 := prologue iqoLocals
  (.seq (.assign .local iqMb (.load .one (.op .add [vv iqR, .const 8])))
  (.seq (.assign .local iqMc (.load .one (vv iqMb)))
  (.ite (.cmp .lower (vv iqI) (vv iqMc))
    (.seq (.assign .local iqQ (.load .one (.op .add [vv iqMb, .op .add [.panop .mul [vv iqI, .const 8], .const 8]])))
    (.seq (.assign .local iqPb (.load .one (vv iqR)))
    (.seq (.assign .local iqPl (.load .one (vv iqPb)))
    (.ite (.cmp .lower (vv iqQ) (.op .sub [vv iqPl, .const 1]))
      (.seq (.assign .local iqD (.load .one (.op .add [vv iqPb, .op .add [.panop .mul [vv iqQ, .const 8], .const 8]])))
      (.seq (.call (some (some (.local, iqS), none)) fStripPis [vv iqF, vv iqD])
      (.ite (.cmp .equal (vv iqS) (.const 0)) (.return (.const 0))
      (.seq (.assign .local iqSc (.load .one (vv iqS)))
      (.seq (.assign .local iqIn (.load .one (.op .add [vv iqS, .shift .lsl (vv iqSc) (.const 3)])))
      (.seq (.call (some (some (.local, iqAm), none)) fTSub [vv iqRP, vv iqQ])
      (.seq (.call (some (some (.local, iqFd), none)) fLiftFields [vv iqS, .const 0, .op .sub [vv iqSc, .const 1], vv iqAm])
      (.seq (.call (some (some (.local, iqT), none)) fPiTele [.const (BitVec.ofNat 64 coreWalkFuel), vv iqIn])
      (.seq (.assign .local iqTn (.load .one (vv iqT)))
      (.seq (.assign .local iqTb (.load .one (.op .add [vv iqT, .const 8])))
      (.seq (.call (some (some (.local, iqA), none)) fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv iqTb])
      (.seq (.assign .local iqAl (.load .one (vv iqA)))
      (.seq (.call (some (some (.local, iqM1), none)) fTSub [vv iqN, vv iqAl])
      (.seq (.call (some (some (.local, iqM), none)) fTSub [vv iqN, vv iqM1])
      (.seq (.call (some (some (.local, iqIx), none)) fLiftIdx [vv iqA, .const 0, vv iqM, vv iqAm, vv iqTn, vv iqF])
      (.seq (.assign .local iqU (.load .one (.op .add [vv iqR, .const 16])))
      (.seq (.assign .local iqPs (.load .one (.op .add [vv iqR, .const 24])))
        (alloc4 C iqO (vv iqFd) (vv iqIx) (vv iqU) (vv iqPs) (.return (vv iqO))))))))))))))))))))
      hang))))
    (.return (.const 0)))))

end

section
variable {σ : Type}

theorem iqo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ iqoLocals → (ctxEnv C ++ iqoParams.zip vals).get x = none :=
  Knot.params_none C iqoLocals iqoParams vals (by decide) (by decide)

theorem eelems_of_blk {H : List (BitVec 64)} {o : Nat} {xs : List EIdx} (h : BlkAt H o (xs.map Enc.idxW)) :
    EElems H o xs := fun j hj => by have := h.2 j (by simp; omega); simpa using this

theorem take_min_eq {α : Type} (l : List α) (n : Nat) : l.take (n - (n - l.length)) = l.take n := by
  by_cases h : n ≤ l.length
  · rw [show n - l.length = 0 by omega, Nat.sub_zero]
  · rw [show n - (n - l.length) = l.length by omega, List.take_length, List.take_of_length_le (by omega)]

/-- The functions `iotaPartsOfAt` calls, and theirs. -/
structure IQCodes (C : Ctx) : Prop where
  iqo : C.code.lookup fIotaPartsOf = some (iqoParams.map (fun p => (p, ShapeHOL.one)), iqoBody C, .one)
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  ts : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one)
  lf : C.code.lookup fLiftFields = some (lfParams.map (fun p => (p, ShapeHOL.one)), lfBody C, .one)
  li : C.code.lookup fLiftIdx = some (liParams.map (fun p => (p, ShapeHOL.one)), liBody C, .one)
  liftF : C.code.lookup ExL.fLiftF = some ([(pFu, .one), (ExL.pA, .one), (pD, .one), (pH, .one)], ExL.fastBodyL C, .one)
  cl : ExL.CodesL C (ExL.bodyL C)
  pt : C.code.lookup fPiTele = some ([(pFu, .one), (pH, .one)], ptBody C fPiTele, .one)
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)
  dv : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ifa : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  ic : Codes C (body C)

/-- **`iotaPartsOfAt`**, at a rule with `nf` fields. -/
theorem iqo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : IQCodes C)
    (rr : IotaRec) (orr rP nIdx i : Nat) (rl : IRecRule) (hrP : rP < 2 ^ 62) (hN : nIdx < 2 ^ 62) (hi : i < 2 ^ 62)
    (hnf : rl.nfields < 2 ^ 62) (H : List (BitVec 64)) (hp : C.H <+: H) (hrr : IotaRecRep C H orr rr) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (iqoParams.zip [cellA C orr, BitVec.ofNat 64 rP, BitVec.ofNat 64 nIdx,
      BitVec.ofNat 64 i, BitVec.ofNat 64 rl.nfields])) (iqoBody C) s (iotaPartsOfAt rr rP nIdx i rl) (PostIP (ctxH C H)) := by
  refine specR_prologue (postIP_locals _) (iqo_none _ _) ?_
  unfold iotaPartsOfAt
  obtain ⟨⟨op, hop, hpc, hpre⟩, ⟨om, hom, hmb⟩, hus, ⟨opp, hopp, hpsb⟩, hmlt⟩ := hrr
  let Γ0 : Env := ctxEnv (ctxH C H) ++ iqoParams.zip [cellA C orr, BitVec.ofNat 64 rP, BitVec.ofNat 64 nIdx,
    BitVec.ofNat 64 i, BitVec.ofNat 64 rl.nfields]
  have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ iqoLocals → z ∉ iqoLocals →
      Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
    have hne : z ≠ x := fun e => hz (e ▸ hx)
    simp only [Env.get_cons, hne, ite_false]
  have pk : ∀ (Γ : Env), (∀ z, z ∉ iqoLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ iqoParams → ∀ v,
      Γ0.get y = some v → sev Γ (vv y) = some v := fun Γ hΓ y hy v h => by
    have hyl : y ∉ iqoLocals := by
      simp only [iqoParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl <;> decide
    simp only [sev, sev_vv, hΓ y hyl, h]
  have vR : Γ0.get iqR = some (cellA C orr) := by simp +decide [Γ0, Env.get, iqoParams, ctxEnv]
  have vRP : Γ0.get iqRP = some (BitVec.ofNat 64 rP) := by simp +decide [Γ0, Env.get, iqoParams, ctxEnv]
  have vN : Γ0.get iqN = some (BitVec.ofNat 64 nIdx) := by simp +decide [Γ0, Env.get, iqoParams, ctxEnv]
  have vI : Γ0.get iqI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, iqoParams, ctxEnv]
  have vF : Γ0.get iqF = some (BitVec.ofNat 64 rl.nfields) := by simp +decide [Γ0, Env.get, iqoParams, ctxEnv]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hml := blkAt_len hmb
  simp only [List.length_map] at hml
  -- the minors
  refine UD.specR_heapLoadI' (C := ctxH C H) iqMb _ (orr + 1) _ hom (by simp +decide [ctxLocals, iqoLocals])
    (by have e : sev Γ0 (.op .add [vv iqR, .const 8]) = some (cellA C (orr + 1)) := by
          simp only [sev, sev_vv, vR]; simp; exact cellA_add8 C orr
        exact e) ?_
  have hmc : (ctxH C H).H[om]? = some (BitVec.ofNat 64 rr.minors.length) := by
    show H[om]? = _; rw [hmb.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) iqMc (vv iqMb) om _ hmc (by simp +decide [ctxLocals, iqoLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  let Γ1 : Env := (iqMc, BitVec.ofNat 64 rr.minors.length) :: (iqMb, cellA C om) :: Γ0
  have hΓ1 : ∀ z, z ∉ iqoLocals → Γ1.get z = Γ0.get z := fun z hz => by
    simp only [Γ1]; rw [cnl (by decide) hz, cnl (by decide) hz]
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ1 (vv iqI) (vv iqMc) i rr.minors.length
    (pk Γ1 hΓ1 iqI (by decide) _ vI) (by simp [Γ1, sev, Env.get_cons]) (by omega) (by omega)) (fun hlt => ?_) (fun hlt => ?_)
  swap
  · have c : ¬ i < rr.minors.length := by intro c; simp [bw, c] at hlt
    rw [if_neg c]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl,
      fun _ e => by simp at e⟩)
  have c : i < rr.minors.length := by by_cases c : i < rr.minors.length; exact c; simp [bw, c] at hlt
  rw [if_pos c]
  let q := rr.minors[i]
  have hgd : rr.minors.getD i 0 = q := by simp [q, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem c]
  rw [hgd]
  dsimp only
  have hq : (ctxH C H).H[om + 1 + i]? = some (BitVec.ofNat 64 q) := by
    show H[om + 1 + i]? = _; have := hmb.2 i (by simp; omega); simpa using this
  refine UD.specR_heapLoadI' (C := ctxH C H) iqQ _ (om + 1 + i) _ hq (by simp +decide [ctxLocals, iqoLocals])
    (by
      have gI := pk Γ1 hΓ1 iqI (by decide) _ vI
      have e : sev Γ1 (.op .add [vv iqMb, .op .add [.panop .mul [vv iqI, .const 8], .const 8]]) =
          some (cellA C (om + 1 + i)) := by
        simp only [sev] at gI ⊢; rw [gI]; simp +decide [Γ1, Env.get_cons]; exact cellA_mulIdx C om i (by omega)
      exact e) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) iqPb (vv iqR) orr _ hop (by simp +decide [ctxLocals, iqoLocals])
    (by have := pk ((iqQ, BitVec.ofNat 64 q) :: Γ1) (fun z hz => by rw [cnl (by decide) hz]; exact hΓ1 z hz) iqR
          (by decide) _ vR
        exact this) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) iqPl (vv iqPb) op _ hpc (by simp +decide [ctxLocals, iqoLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  let Γ2 : Env := (iqPl, BitVec.ofNat 64 (rr.pre.length + 1)) :: (iqPb, cellA C op) :: (iqQ, BitVec.ofNat 64 q) :: Γ1
  have hΓ2 : ∀ z, z ∉ iqoLocals → Γ2.get z = Γ0.get z := fun z hz => by
    simp only [Γ2]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ1 z hz
  have hpl : rr.pre.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos rr.pre.length with h0 | h0
    · omega
    · have h1 := hpre (rr.pre.length - 1) (by omega)
      rcases Nat.lt_or_ge (op + 1 + (rr.pre.length - 1)) H.length with h2 | h2
      · omega
      · rw [List.getElem?_eq_none h2] at h1; cases h1
  have hqb : q < 2 ^ 63 := hmlt i c
  have hsubl : sev Γ2 (.op .sub [vv iqPl, .const 1]) = some (BitVec.ofNat 64 rr.pre.length) := by
    simp [Γ2, sev, Env.get_cons]; exact ofNat_succ_sub_one _
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ2 (vv iqQ) _ q rr.pre.length (by simp +decide [Γ2, sev, Env.get_cons])
    hsubl (by omega) (by omega)) (fun hlt2 => ?_) (fun _ => specR_hangI)
  have c2 : q < rr.pre.length := by by_cases c2 : q < rr.pre.length; exact c2; simp [bw, c2] at hlt2
  have hget : exprGetD rr.pre q = pure rr.pre[q] := by simp [exprGetD, List.getElem?_eq_getElem c2]
  rw [hget, pure_bind]
  have hd : (ctxH C H).H[op + 1 + q]? = some (Enc.idxW rr.pre[q]) := hpre q c2
  refine UD.specR_heapLoadI' (C := ctxH C H) iqD _ (op + 1 + q) _ hd (by simp +decide [ctxLocals, iqoLocals])
    (by simp +decide [Γ2, sev, Env.get_cons]; exact cellA_mulIdx C op q (by omega)) ?_
  let Γ3 : Env := (iqD, Enc.idxW rr.pre[q]) :: Γ2
  have hΓ3 : ∀ z, z ∉ iqoLocals → Γ3.get z = Γ0.get z := fun z hz => by
    simp only [Γ3]; rw [cnl (by decide) hz]; exact hΓ2 z hz
  -- the fields
  refine ro_strip C hok hc.sp rl.nfields (by omega) rr.pre[q] H s iqS (vv iqF) (vv iqD)
    (by simp +decide [ctxLocals, iqoLocals]) (pk Γ3 hΓ3 iqF (by decide) _ vF) (by simp [Γ3, sev, Env.get_cons])
    (fun o ws s1 H1 hp1 hr1 hn1 hs1 => ?_)
  have hpH1 : H <+: H1 := hp1
  rcases o with _ | ⟨fd, inner⟩
  · have e0 := hn1 rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hpH1, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl,
      fun _ e => by simp at e⟩)
  obtain ⟨osb, rfl, hsb⟩ := hs1 fd inner rfl
  have hfl := stripPis_length _ _ _ _ _ _ hr1
  obtain ⟨hs0, hsL, hfd⟩ := strip_last hsb
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
  have hol := blkAt_lt hsb
  have hHN1' : H1.length ≤ C.HN := hHN1
  have hsbl := blkAt_len hsb
  simp only [List.length_append, List.length_map, List.length_singleton] at hsbl
  have hne : cellA C osb ≠ 0 := cellA_ne0 C hok osb (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H1) iqSc (vv iqS) osb _ hs0 (by simp +decide [ctxLocals, iqoLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) iqIn _ (osb + 1 + fd.length) _ hsL (by simp +decide [ctxLocals, iqoLocals])
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C osb + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  let Γ4 : Env := (iqIn, Enc.idxW inner) :: (iqSc, BitVec.ofNat 64 (fd.length + 1)) :: (iqS, cellA C osb) :: Γ3
  have hΓ4 : ∀ z, z ∉ iqoLocals → Γ4.get z = Γ0.get z := fun z hz => by
    simp only [Γ4]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ3 z hz
  -- the lift amount
  let amt := rP - q
  refine specR_pureBind amt ?_
  refine rb_tsub (D := ctxLocals ++ iqoLocals) C hc.ts rP q (by omega) (by omega) H1 s1 iqAm (vv iqRP) (vv iqQ)
    (by simp +decide [ctxLocals, iqoLocals]) (pk Γ4 hΓ4 iqRP (by decide) _ vRP) (by simp +decide [Γ4, Γ3, Γ2, sev, Env.get_cons])
    (fun H2 hp2 => ?_)
  let Γ5 : Env := (iqAm, BitVec.ofNat 64 amt) :: Γ4
  have hΓ5 : ∀ z, z ∉ iqoLocals → Γ5.get z = Γ0.get z := fun z hz => by
    simp only [Γ5]; rw [cnl (by decide) hz]; exact hΓ4 z hz
  have hp02 : C.H <+: H2 := (hp.trans hpH1).trans hp2
  -- the fields lifted
  refine specR_congr (m' := liftFieldDoms amt (fd.drop 0) 0 >>= fun fds => do
      let t ← piTele coreWalkFuel inner
      let args ← getAppArgs coreWalkFuel t.2
      let idx ← liftIdxArgs amt t.1 rl.nfields (args.take nIdx)
      pure (some ({ fieldDoms := fds, idx := idx, us := rr.us, params := rr.params } : IIotaParts))) (by simp [amt]) ?_
  refine specR_callNIH (C := ctxH C H2) iqFd fLiftFields lfParams [vv iqS, .const 0, .op .sub [vv iqSc, .const 1], vv iqAm]
    (lfBody C) [cellA C osb, BitVec.ofNat 64 0, BitVec.ofNat 64 fd.length, BitVec.ofNat 64 amt] (by decide) rfl
    (by simp +decide [ctxLocals, iqoLocals]) hc.lf
    ⟨by simp +decide [Γ5, Γ4, sev, Env.get_cons], rfl,
      by simp +decide [Γ5, Γ4, sev, Env.get_cons]; exact ofNat_succ_sub_one _, by simp [Γ5, sev, Env.get_cons] <;> rfl, trivial⟩
    (PostA (ctxH C H2)) (fun fds w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (fds.map Enc.idxW))
    (fun fds w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lfParams _ rfl hlk)
      (lf_spec ra C hok hc.lf hc.liftF hc.cl fd osb amt (by omega) (by omega) fd.length 0 H2 s1 hp02
        (fun j hj => get_prefix (hfd j hj) hp2) (by omega) (by omega)))
    (fun fds wf s3 H3 hp3 ⟨ofd, hwf, hfdb⟩ => ?_)
  subst hwf
  have hp23 : H2 <+: H3 := hp3
  let Γ6 : Env := (iqFd, cellA C ofd) :: Γ5
  have hΓ6 : ∀ z, z ∉ iqoLocals → Γ6.get z = Γ0.get z := fun z hz => by
    simp only [Γ6]; rw [cnl (by decide) hz]; exact hΓ5 z hz
  -- the conclusion
  refine specR_callNIH (C := ctxH C H3) iqT fPiTele [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv iqIn]
    (ptBody C fPiTele) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW inner] (by decide) rfl
    (by simp +decide [ctxLocals, iqoLocals]) hc.pt ⟨rfl, by simp +decide [Γ6, Γ5, Γ4, sev, Env.get_cons], trivial⟩
    (PostPT (ctxH C H3) coreWalkFuel) (fun r w _ H' => r.1 < coreWalkFuel ∧
      ∃ ob, w = cellA C ob ∧ H'[ob]? = some (BitVec.ofNat 64 r.1) ∧ H'[ob + 1]? = some (Enc.idxW r.2))
    (fun r w s' st ⟨H', hp', hs, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw; exact pt_spec C hok hc.pt coreWalkFuel (by decide) H3 s3 inner _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun t wt s4 H4 hp4 ⟨htf, otb, hwt, ht0, ht1⟩ => ?_)
  subst hwt
  have hp34 : H3 <+: H4 := hp4
  have hcw : coreWalkFuel < 2 ^ 62 := by decide
  refine UD.specR_heapLoadI' (C := ctxH C H4) iqTn (vv iqT) otb _ ht0 (by simp +decide [ctxLocals, iqoLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H4) iqTb _ (otb + 1) _ ht1 (by simp +decide [ctxLocals, iqoLocals])
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C otb) ?_
  let Γ7 : Env := (iqTb, Enc.idxW t.2) :: (iqTn, BitVec.ofNat 64 t.1) :: (iqT, cellA C otb) :: Γ6
  have hΓ7 : ∀ z, z ∉ iqoLocals → Γ7.get z = Γ0.get z := fun z hz => by
    simp only [Γ7]; rw [cnl (by decide) hz, cnl (by decide) hz, cnl (by decide) hz]; exact hΓ6 z hz
  refine specR_callNIH (C := ctxH C H4) iqA fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv iqTb] (gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW t.2] (by decide) rfl (by simp +decide [ctxLocals, iqoLocals]) hc.gaa
    ⟨rfl, by simp [Γ7, sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H4)) (fun args w _ H' => ∃ oa, w = cellA C oa ∧ BlkAt H' oa (args.map Enc.idxW))
    (fun args w s' st ⟨H', oa, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨oa, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ConPanqueque.T.ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H4 t.2 s4))
    (fun args wa s5 H5 hp5 ⟨oa, hwa, hab⟩ => ?_)
  subst hwa
  have hp45 : H4 <+: H5 := hp5
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN5 => ?_)
  have hHN5' : H5.length ≤ C.HN := hHN5
  have hal := blkAt_len hab
  simp only [List.length_map] at hal
  have hc0 : (ctxH C H5).H[oa]? = some (BitVec.ofNat 64 args.length) := by show H5[oa]? = _; rw [hab.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H5) iqAl (vv iqA) oa _ hc0 (by simp +decide [ctxLocals, iqoLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  let Γ8 : Env := (iqAl, BitVec.ofNat 64 args.length) :: (iqA, cellA C oa) :: Γ7
  have hΓ8 : ∀ z, z ∉ iqoLocals → Γ8.get z = Γ0.get z := fun z hz => by
    simp only [Γ8]; rw [cnl (by decide) hz, cnl (by decide) hz]; exact hΓ7 z hz
  -- `min nIdx args.length`
  rw [← take_min_eq args nIdx]
  let m1 := nIdx - args.length
  refine specR_pureBind m1 ?_
  refine rb_tsub (D := ctxLocals ++ iqoLocals) C hc.ts nIdx args.length (by omega) (by omega) H5 s5 iqM1 (vv iqN) (vv iqAl)
    (by simp +decide [ctxLocals, iqoLocals]) (pk Γ8 hΓ8 iqN (by decide) _ vN) (by simp [Γ8, sev, Env.get_cons])
    (fun H6 hp6 => ?_)
  let Γ9 : Env := (iqM1, BitVec.ofNat 64 m1) :: Γ8
  have hΓ9 : ∀ z, z ∉ iqoLocals → Γ9.get z = Γ0.get z := fun z hz => by
    simp only [Γ9]; rw [cnl (by decide) hz]; exact hΓ8 z hz
  let m := nIdx - m1
  refine specR_pureBind m ?_
  refine rb_tsub (D := ctxLocals ++ iqoLocals) C hc.ts nIdx m1 (by omega) (by omega) H6 s5 iqM (vv iqN) (vv iqM1)
    (by simp +decide [ctxLocals, iqoLocals]) (pk Γ9 hΓ9 iqN (by decide) _ vN) (by simp [Γ9, sev, Env.get_cons] <;> rfl)
    (fun H7 hp7 => ?_)
  let Γ10 : Env := (iqM, BitVec.ofNat 64 m) :: Γ9
  have hΓ10 : ∀ z, z ∉ iqoLocals → Γ10.get z = Γ0.get z := fun z hz => by
    simp only [Γ10]; rw [cnl (by decide) hz]; exact hΓ9 z hz
  have hp57 : H5 <+: H7 := hp6.trans hp7
  have hp07 : C.H <+: H7 := ((((hp02.trans hp23).trans hp34).trans hp45).trans hp57)
  -- the indices
  refine specR_congr (m' := liftIdxArgs amt t.1 rl.nfields ((args.take m).drop 0) >>= fun idx =>
      pure (some ({ fieldDoms := fds, idx := idx, us := rr.us, params := rr.params } : IIotaParts))) (by simp [m, m1]) ?_
  refine specR_callNIH (C := ctxH C H7) iqIx fLiftIdx liParams [vv iqA, .const 0, vv iqM, vv iqAm, vv iqTn, vv iqF]
    (liBody C) [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 m, BitVec.ofNat 64 amt, BitVec.ofNat 64 t.1,
      BitVec.ofNat 64 rl.nfields] (by decide) rfl (by simp +decide [ctxLocals, iqoLocals]) hc.li
    ⟨by simp +decide [Γ10, Γ9, Γ8, sev, Env.get_cons], rfl, by simp [Γ10, sev, Env.get_cons] <;> rfl,
      by simp +decide [Γ10, Γ9, Γ8, Γ7, Γ6, Γ5, sev, Env.get_cons] <;> rfl,
      by simp +decide [Γ10, Γ9, Γ8, Γ7, sev, Env.get_cons], pk Γ10 hΓ10 iqF (by decide) _ vF, trivial⟩
    (PostA (ctxH C H7)) (fun idx w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (idx.map Enc.idxW))
    (fun idx w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu liParams _ rfl hlk)
      (li_spec ra C hok hc.li hc.liftF hc.cl hc.dv hc.srt hc.ifa hc.ic args oa m amt t.1 rl.nfields (by omega) (by omega)
        (by omega) (by omega) (by omega) (m - 0) 0 H7 s5 hp07 (fun j hj => get_prefix (eelems_of_blk hab j hj) hp57)
        rfl (by omega)))
    (fun idx wi s6 H8 hp8 ⟨oix, hwi, hixb⟩ => ?_)
  subst hwi
  have hp78 : H7 <+: H8 := hp8
  have hHH8 : H <+: H8 := (((((((hpH1.trans hp2).trans hp23).trans hp34).trans hp45).trans hp57).trans hp78))
  have hus8 : (ctxH C H8).H[orr + 2]? = some (Enc.idxW rr.us) := get_prefix hus hHH8
  have hps8 : (ctxH C H8).H[orr + 3]? = some (cellA C opp) := get_prefix hopp hHH8
  let Γ11 : Env := (iqIx, cellA C oix) :: Γ10
  have hΓ11 : ∀ z, z ∉ iqoLocals → Γ11.get z = Γ0.get z := fun z hz => by
    simp only [Γ11]; rw [cnl (by decide) hz]; exact hΓ10 z hz
  have gR11 := pk Γ11 hΓ11 iqR (by decide) _ vR
  refine UD.specR_heapLoadI' (C := ctxH C H8) iqU _ (orr + 2) _ hus8 (by simp +decide [ctxLocals, iqoLocals])
    (by simp only [sev] at gR11 ⊢; rw [gR11]; simp; exact cellA_plus C orr 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H8) iqPs _ (orr + 3) _ hps8 (by simp +decide [ctxLocals, iqoLocals])
    (by
      have g : sev ((iqU, Enc.idxW rr.us) :: Γ11) (vv iqR) = some (cellA C orr) := by
        simp only [sev, sev_vv, Env.get_cons, show iqR ≠ iqU by decide, ite_false] at gR11 ⊢; exact gR11
      simp only [sev] at g ⊢; rw [g]; simp; exact cellA_plus C orr 3) ?_
  refine specR_alloc4I (C := ctxH C H8) (ctxOK_H hok H8) iqO _ _ _ _ (cellA C ofd) (cellA C oix) (Enc.idxW rr.us)
    (cellA C opp) (by simp +decide [ctxLocals, iqoLocals])
    (fun v => by simp +decide [Γ11, Γ10, Γ9, Γ8, Γ7, Γ6, sev, Env.get_cons])
    (fun v => by simp +decide [Γ11, sev, Env.get_cons])
    (fun v => by simp +decide [sev, Env.get_cons])
    (fun v => by simp +decide [sev, Env.get_cons]) (fun H9 ws hp9 hws hroom9 => ?_)
  have hp89 : H8 <+: H9 := hp9
  obtain ⟨g0, g1, g2, g3⟩ := img4_get H9 ws (cellA C ofd) (cellA C oix) (Enc.idxW rr.us) (cellA C opp) hws
  have hI := img4_prefix H9 ws (cellA C ofd) (cellA C oix) (Enc.idxW rr.us) (cellA C opp) hws
  have hHI := (hHH8.trans hp89).trans hI
  exact specR_returnI _ (cellA C H9.length) (by simp [sev, Env.get_cons]; rfl) (fun tt ht => ⟨_, hHI,
    sr_of_eq ht.sr rfl rfl rfl rfl, fun e => by simp at e, fun ip e => by
      simp only [Option.some.injEq] at e; subst e
      exact ⟨H9.length, rfl, ⟨ofd, g0, blkAt_mono hfdb ((((((hp34.trans hp45).trans hp57).trans hp78).trans hp89).trans hI))⟩,
        ⟨oix, g1, blkAt_mono hixb ((hp89).trans hI)⟩, g2,
        ⟨opp, g3, blkAt_mono hpsb (hHH8.trans hp89 |>.trans hI)⟩⟩⟩)

end

end ConPanqueque.T.Ind
