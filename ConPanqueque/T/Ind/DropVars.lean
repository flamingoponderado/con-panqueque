import ConPanqueque.T.Ind.IotaMinors
import ConPanqueque.T.Ex.Inst1Fast
import ConPanqueque.T.EIntern2

/-!
# `exprDropVars`: drop the `n` innermost variables

Each step instantiates the innermost variable with `Sort 0` (`internSortE`, `instantiate1Fast`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA

def dvN := ofString "dv_n"
def dvE := ofString "dv_e"
def dvZ := ofString "dv_z"
def dvS := ofString "dv_s"
def dvX := ofString "dv_x"
def fDropVars := ofString "dropVars"

def dvParams : List MlS := [dvN, dvE]
def dvLocals : List MlS := [dvZ, dvS, dvX]

def dvBody (C : Ctx) : ProgHOL 64 := prologue dvLocals
  (.ite (.cmp .equal (vv dvN) (.const 0)) (.return (vv dvE))
    (.seq (.assign .local dvZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, dvS), none)) fInternSort [vv dvZ])
    (.seq (.call (some (some (.local, dvX), none)) fInst1F [.const (BitVec.ofNat 64 coreWalkFuel), vv dvE, vv dvS, .const 0])
    (.seq (.call (some (some (.local, dvX), none)) fDropVars [.op .sub [vv dvN, .const 1], vv dvX])
      (.return (vv dvX)))))))

section
variable {σ : Type}

theorem dv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dvLocals → (ctxEnv C ++ dvParams.zip vals).get x = none :=
  Knot.params_none C dvLocals dvParams vals (by decide) (by decide)

theorem dv_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one))
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (hcF : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcI : Codes C (body C)) :
    ∀ n, n < 2 ^ 64 → ∀ (s : AState) (e : EIdx),
      SpecR (σ := σ) (Pre C s (dvParams.zip [BitVec.ofNat 64 n, Enc.idxW e])) (dvBody C) s (exprDropVars n e)
        (PostE C) := by
  intro n
  induction n with
  | zero =>
    intro _ s e
    refine specR_prologue (postE_locals C) (dv_none _ _) ?_
    rw [exprDropVars]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ _ (by simp +decide [sev, Env.get, dvParams, ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ n ih =>
    intro hn s e
    refine specR_prologue (postE_locals C) (dv_none _ _) ?_
    rw [exprDropVars]
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hn
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Env.get, dvParams, ctxEnv] at hw; exact absurd hw this
    simp only [zeroLevel, bind_assoc]
    refine specR_pinXI hok pinZeroLevel 1 C.pins.zeroLevel _ (fun s hp => pinZeroLevel_run hok hp)
      (pin_zeroLevel_cell hok) dvZ (by simp +decide [ctxLocals, dvLocals]) ?_
    refine ILP.callE_spec dvS fInternSort [lEu] [vv dvZ] sortBody [Enc.idxW C.pins.zeroLevel] (by decide) rfl
      (by simp +decide [ctxLocals, dvLocals]) hcS ⟨by simp [sev, Env.get_cons], trivial⟩
      (sort_body_spec ra C hok s C.pins.zeroLevel) (fun s0 s1 => ?_)
    refine ILP.callE_spec dvX fInst1F [pFu, pH, pV, pD] [.const (BitVec.ofNat 64 coreWalkFuel), vv dvE, vv dvS, .const 0]
      (fastBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, Enc.idxW s0, BitVec.ofNat 64 0] (by decide) rfl
      (by simp +decide [ctxLocals, dvLocals]) hcF
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, dvParams, ctxEnv], by simp [sev, Env.get_cons], rfl, trivial⟩
      (fast_spec ra C hok hcI s1 coreWalkFuel e s0 0 (by decide) (by decide)) (fun e1 s2 => ?_)
    refine specR_congr (m' := exprDropVars n e1 >>= fun r => pure r) (by simp) ?_
    refine ILP.callE_spec dvX fDropVars dvParams [.op .sub [vv dvN, .const 1], vv dvX] (dvBody C)
      [BitVec.ofNat 64 n, Enc.idxW e1] (by decide) rfl (by simp +decide [ctxLocals, dvLocals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, dvParams, ctxEnv]; exact ofNat_succ_sub_one n,
        by simp [sev, Env.get_cons], trivial⟩
      (ih (by omega) s2 e1) (fun r s3 => ?_)
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def dmA := ofString "dm_a"
def dmI := ofString "dm_i"
def dmM := ofString "dm_m"
def dmN := ofString "dm_n"
def dmX := ofString "dm_x"
def fDropMap := ofString "dropMap"

def dmParams : List MlS := [dmA, dmI, dmM, dmN]
def dmLocals : List MlS := gaaLocals ++ [dmX]

/-- `(xs.take m).drop i` each with its `n` innermost variables dropped, as a block. -/
def dmBody (C : Ctx) : ProgHOL 64 := prologue dmLocals
  (.ite (.cmp .lower (vv dmI) (vv dmM))
    (.seq (.assign .local dmX (.load .one (.op .add [vv dmA, .op .add [.panop .mul [vv dmI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, lA1), none)) fDropVars [vv dmN, vv dmX])
    (.seq (.call (some (some (.local, ExS.lY), none)) fDropMap [vv dmA, .op .add [vv dmI, .const 1], vv dmM, vv dmN])
      (prependP C lA1))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem dm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dmLocals → (ctxEnv C ++ dmParams.zip vals).get x = none :=
  Knot.params_none C dmLocals dmParams vals (by decide) (by decide)

theorem take_drop_cons' {α : Type} (l : List α) (i m : Nat) (hi : i < m) (hm : m ≤ l.length) :
    (l.take m).drop i = l[i]'(by omega) :: (l.take m).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]; simp

theorem dm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fDropMap = some (dmParams.map (fun p => (p, ShapeHOL.one)), dmBody C, .one))
    (hcd : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one))
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (hcF : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcI : Codes C (body C)) (xs : List EIdx) (oa m n : Nat) (hm : m ≤ xs.length) (hl : xs.length < 2 ^ 59)
    (hn : n < 2 ^ 64) :
    ∀ f i (H : List (BitVec 64)) (s : AState), C.H <+: H → BlkAt H oa (xs.map Enc.idxW) → m - i = f → i ≤ m →
      SpecR (σ := σ) (Pre (ctxH C H) s (dmParams.zip [cellA C oa, BitVec.ofNat 64 i, BitVec.ofNat 64 m,
        BitVec.ofNat 64 n])) (dmBody C) s (((xs.take m).drop i).mapM (exprDropVars n)) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hp hb hf hi
    have him : i = m := by omega
    subst him
    refine specR_prologue (postA_locals _) (dm_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_eq_nil_of_le (by simp), List.mapM_nil]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by simp +decide [ctxLocals, dmLocals, gaaLocals, inst1Locals])
      (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    exact specR_returnI _ _ (by simp [sev] <;> rfl) (fun t ht => ⟨_, H2.length, hp2.trans (img1_prefix _ _ _ hws), rfl,
      ⟨by simpa using img1_get H2 ws (0 : BitVec 64) hws, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hp hb hf hi
    have him : i < m := by omega
    refine specR_prologue (postA_locals _) (dm_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i m (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr him])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [take_drop_cons' xs i m him hm, List.mapM_cons]
    have hx : (ctxH C H).H[oa + 1 + i]? = some (Enc.idxW xs[i]) := by
      show H[oa + 1 + i]? = _; have := hb.2 i (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) dmX _ (oa + 1 + i) _ hx (by simp +decide [ctxLocals, dmLocals, gaaLocals, inst1Locals])
      (by simp +decide [sev, Env.get, dmParams, ctxEnv]; exact cellA_mulIdx C oa i (by omega)) ?_
    refine ILP.callE_spec (C := ctxH C H) lA1 fDropVars dvParams [vv dmN, vv dmX] (dvBody C) [BitVec.ofNat 64 n, Enc.idxW xs[i]]
      (by decide) rfl (by simp +decide [ctxLocals, dmLocals, gaaLocals, inst1Locals]) hcd
      ⟨by simp +decide [sev, Env.get_cons, Env.get, dmParams, ctxEnv], by simp [sev, Env.get_cons], trivial⟩
      (dv_spec ra (ctxH C H) (ctxOK_H hok H) hcd hcS hcF ⟨hcI.inst1, hcI.memoGet, hcI.memoProbe, hcI.memoSet, hcI.memoIns,
        hcI.internApp, hcI.internLam, hcI.internForallE, hcI.internLet, hcI.internBVar, hcI.internProj⟩ n hn s xs[i]) (fun y s1 => ?_)
    refine specR_congr (m' := ((xs.take m).drop (i + 1)).mapM (exprDropVars n) >>= fun ys => pure (y :: ys))
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fDropMap dmParams [vv dmA, .op .add [vv dmI, .const 1], vv dmM, vv dmN]
      (dmBody C) [cellA C oa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 m, BitVec.ofNat 64 n] (by decide) rfl
      (by simp +decide [ctxLocals, dmLocals, gaaLocals, inst1Locals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, dmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, dmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, dmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, dmParams, ctxEnv], trivial⟩
      (PostA (ctxH C H)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dmParams _ rfl hlk)
        (ih (i + 1) H s1 hp hb (by omega) (by omega)))
      (fun ys wr s2 H2 hp2 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    exact prepend_spec C hok lA1 (Enc.idxW y) oy _ (by simp +decide [ctxLocals, dmLocals, gaaLocals, inst1Locals])
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hblk (by decide)
      (by simp +decide [Env.get_cons, Env.get, dmParams, ctxEnv]) (by decide)
      (fun H' o t hpH hbk hsr => ⟨H', o, hp2.trans hpH, rfl, by simpa using hbk, hsr⟩)

end

end ConPanqueque.T.Ind
