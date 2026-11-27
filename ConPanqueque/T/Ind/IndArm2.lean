import ConPanqueque.T.SameLay
import ConPanqueque.T.Ind.IndArm
import ConPanqueque.T.Ind.CheckBlockAny
import ConPanqueque.T.Ind.ReadBlock
import ConPanqueque.T.Ind.BlockReadsSpec
import ConPanqueque.Bridge.SeqFold
import ConPanqueque.T.Ind.NodeCount

/-!
# The record of an inductive block (`checkDeclStep` at `.indDecl`)

`kiBody`: the record `[4, nP, block]`; the block's names free (else hang), the full flush, `indParamsOk` (false
hangs), `readBlock`, `blockReadsAt`, `checkBlock`, the reads' verdict (false hangs), the flush, the scratch tier
off (else hang), and the block none of the pinned basis blocks (a reserved slice matching hangs).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def kiQ := ofString "ki_q"
def kiNp := ofString "ki_np"
def kiOb := ofString "ki_ob"
def kiN := ofString "ki_n"
def kiR := ofString "ki_r"
def kiRl := ofString "ki_rl"
def kiX := ofString "ki_x"
def kiOk := ofString "ki_ok"
def kiSh := ofString "ki_sh"
def kiRd := ofString "ki_rd"
def kiFe := ofString "ki_fe"
def fKi := ofString "checkInductive"

def kiParams : List MlS := [kiQ]
def kiLocals : List MlS := [kiNp, kiOb, kiN, kiR, kiRl, kiX, kiOk, kiSh, kiRd, kiFe, ocA, ocB, ocC, ocD, lJ0]

/-- One pinned block's test: the block's length is the slice's and its names match it — hang. -/
def kiHit (m a : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv kiN) (.const (BitVec.ofNat 64 m)))
    (.seq (.call (some (some (.local, kiX), none)) fBsq [vv kiOb, .const 0, vv kiN, vv kiR, .const (BitVec.ofNat 64 a)])
      (.ite (vv kiX) hang rest))
    rest

def kiBody (C : Ctx) : ProgHOL 64 := prologue kiLocals
  (.seq (.assign .local kiNp (.load .one (.op .add [vv kiQ, .const 8])))
  (.seq (.assign .local kiOb (.load .one (.op .add [vv kiQ, .const 16])))
  (.seq (.assign .local kiN (.load .one (vv kiOb)))
  (.seq (.assign .local kiR (.load .one (.const (ecell C (C.PO + pinCount + 4)))))
  (.seq (.assign .local kiRl (.load .one (vv kiR)))
  (.seq (.call (some (some (.local, kiX), none)) fIbn [vv kiOb, .const 0, vv kiN, vv kiR, vv kiRl])
  (flushCode C (flushRegions true)
  (.seq (.call (some (some (.local, kiOk), none)) fIpo [vv kiOb, .const 0, vv kiN, vv kiNp])
  (.ite (.cmp .equal (vv kiOk) (.const 0)) hang
  (.seq (.call (some (some (.local, kiSh), none)) fReadBlock [vv kiOb, vv kiNp])
  (.seq (.call (some (some (.local, kiRd), none)) fBlockReadsAt [vv kiSh])
  (.seq (.call (some (some (.local, kiFe), none)) fCbk [vv kiSh])
  (.ite (.cmp .equal (vv kiRd) (.const 0)) hang
  (flushCode C (flushRegions false)
  (offCheckP C
  (kiHit 3 0 (kiHit 4 3 (kiHit 2 7 (kiHit 2 9 (.return (.const 0)))))))))))))))))))))

structure KICodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  ibn : IBNCodes C
  ipo : C.code.lookup fIpo = some (ipoParams.map (fun p => (p, ShapeHOL.one)), ipoBody, .one)
  pst : C.code.lookup fPiSortTele = some ([(pFu, .one), (pH, .one)], pstBody fPiSortTele, .one)
  rb : RBCodes C
  br : BRCodes C
  brS : C.code.lookup fBlockReadsAt = some (brParams.map (fun p => (p, ShapeHOL.one)), brBody C, .one)
  cbk : CBKCodes mode C
  bsq : BSQCodes C
  self : C.code.lookup fKi = some (kiParams.map (fun p => (p, ShapeHOL.one)), kiBody C, .one)

/-- `blockReadsAt`'s facts of a read block, at a store. -/
def BRFacts (p : BlockShape) (st : EStore) : Prop :=
  (∀ ms ∈ p.members, ms.nIdx < 2 ^ 63) ∧ (∀ ms ∈ p.members, p.nP + ms.nIdx < 2 ^ 63) ∧
  (∀ ms ∈ p.members, ms.declared.levelParams.length < 2 ^ 60) ∧
  (∀ ms ∈ p.members, ∀ c ∈ ms.ctors, c.1.levelParams.length < 2 ^ 60) ∧
  (∀ rc ∈ p.recs, rc.cvR.levelParams.length < 2 ^ 60) ∧ ((p.members.map (·.ctors.length)).sum < 2 ^ 58) ∧
  ((∀ ms ∈ p.members, CVDen ms.declared st ∧ (CVDen ms.cvT st) ∧ ∀ c ∈ ms.ctors, CVDen c.1 st) ∧
    ∀ rc ∈ p.recs, CVDen rc.cvR st) ∧
  (∀ sa sb fs, StateOK sa → PinsOK sa → Ext st sa.store → p.recs.mapM (recFire p) sa = .ok (fs, sb) →
    ∀ f ∈ fs, FireDen f sb.store)

/-- **The twin-run facts the inductive record relies on**: of the block `readBlock` answers, at the store it
answers in — when it is run at a checking state (con-ron's `FoldOK`, the bridge's invariant with the caches
flushed) at which the block denotes. -/
def IndRun (C : Ctx) (block : List IConstantInfo) (nP : Nat) : Prop :=
  ∀ (env : ConLeche.Env) (fe : IFEnv) (b : List ConLeche.ConstantInfo) (s : AState) (p : BlockShape) (s' : AState),
    FoldOK env fe s → Ext C.St s.store → s.store.nodeCount < 2 ^ 55 → Frontend.denoteCIList s.store block = some b →
    readBlock nP block s = .ok (.ok p, s') →
    BRFacts p s'.store ∧ ∀ C' : Ctx, C'.St = s'.store → C'.code = C.code →
      ∀ ms0 rc, p.members = [ms0] → p.recs = [rc] → CBKFacts .verified C' block p ms0 rc

/-- The bridge's invariant between records, at a flushed state: con-ron's `FoldOK`. -/
theorem seqOK_flushed {env : ConLeche.Env} {fe : IFEnv} {s : AState} (h : ConPanqueque.Bridge.SeqOK env fe s)
    (mem : Bool) : FoldOK env fe (Decl.flushedS mem s) :=
  ConPanqueque.Bridge.SeqOK.fold ⟨⟨h.state.wf⟩, h.pins.mono (Ext.refl _) rfl, h.ienv.mono (Ext.refl _), h.envWF,
    h.tblShape, h.persPins.mono rfl, h.coh, h.gate⟩ rfl

theorem ki_fail_bind {α β : Type} (e : CheckError) (k : α → AM β) : (fail e : AM α) >>= k = fail e := by
  funext s; simp [fail, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind, Except.bind]

theorem match_unwrap {β γ : Type} (x : AM (Except CheckError BlockShape)) (K : BlockShape → AM β) (k : β → AM γ) :
    ((x >>= fun r => match r with | .ok p => K p | .error e => fail e) >>= k) = (unwrapE x >>= fun p => K p >>= k) := by
  simp only [unwrapE, bind_assoc]
  congr 1; funext r
  cases r with
  | ok p => simp
  | error e => simp [ki_fail_bind]

theorem unwrapE_ok {α : Type} {x : AM (Except CheckError α)} {s s' : AState} {a : α}
    (h : unwrapE x s = .ok (a, s')) : x s = .ok (.ok a, s') := by
  unfold unwrapE at h
  obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok h
  cases r with
  | ok v => obtain ⟨rfl, rfl⟩ := AM.pure_ok h2; exact h1
  | error e => exact (AM.fail_ok h2).elim

theorem bsqVal_of_eq (blk : List IConstantInfo) (rs : List NIdx) (a : Nat) (hle : a + blk.length ≤ rs.length)
    (he : (rs.drop a).take blk.length = blk.map (·.name)) : bsqVal blk rs a 0 = true := by
  unfold bsqVal
  simp only [List.drop_zero, Nat.add_zero, Nat.sub_zero, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun p hp => ?_, by omega⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  simp only [List.getElem_zip, beq_iff_eq]
  have hi1 : i < blk.length := by simp at hi; omega
  have := congrArg (fun l => l[i]?) he
  simp only [List.getElem?_take, hi1, ↓reduceIte, List.getElem?_drop, List.getElem?_map] at this
  rw [List.getElem?_eq_getElem (by simp at hi; omega), List.getElem?_eq_getElem hi1] at this
  simpa using this.symm

section
variable {σ : Type}

/-- A spec of `unwrapE x` is one of `x`, its answer `.ok`. -/
theorem specR_of_unwrap {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState}
    {x : AM (Except CheckError α)} {R : α → BitVec 64 → AState → PState σ → Prop}
    (h : SpecR P c s (unwrapE x) R) :
    SpecR P c s x (fun r w s' t => ∃ a, r = .ok a ∧ unwrapE x s = .ok (a, s') ∧ R a w s' t) := by
  intro t ht
  rcases h t ht with hs | ⟨w, hw, a, s', hm, hr⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hw, .ok a, s', unwrapE_ok hm, a, rfl, hm, hr⟩

/-- **One pinned block's test**: a match hangs; past it the slice is not the block's names. -/
theorem specR_kiHitI {α : Type} {Cx : Ctx} (hok : CtxOK Cx) (hc : BSQCodes Cx) {s : AState} {Γ : Env}
    {D : List MlS} {rest : ProgHOL 64} {mm : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (blk : List IConstantInfo) (ob : Nat) (hblk : IndBlk Cx Cx.H ob blk) (rs : List NIdx) (oR : Nat)
    (hR : EBlk Cx.EH oR (rs.map Enc.idxW)) (hRl : rs.length < 2 ^ 59) (m a : Nat) (hle : a + m ≤ rs.length)
    (hblen : blk.length < 2 ^ 61) (hn : Γ.get kiN = some (BitVec.ofNat 64 blk.length))
    (hob : Γ.get kiOb = some (cellA Cx ob)) (hr : Γ.get kiR = some (ecell Cx oR)) (hD : kiX ∈ D)
    (hk : ∀ (Γ' : Env) (H' : List (BitVec 64)), Cx.H <+: H' → (∀ x, x ≠ kiX → Γ'.get x = Γ.get x) →
      (rs.drop a).take m ≠ blk.map (·.name) → SpecR (Inv (ctxH Cx H') s Γ' [] D) rest s mm R) :
    SpecR (Inv Cx s Γ [] D) (kiHit m a rest) s mm R := by
  unfold kiHit
  by_cases hlm : blk.length = m
  swap
  · refine specR_ifI _ 0 (by
      simp only [sev, sev_vv, hn]
      simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hlm
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact this) (fun h => absurd rfl h) (fun _ => ?_)
    refine hk Γ Cx.H (List.prefix_refl _) (fun _ _ => rfl) (fun he => hlm ?_)
    have := congrArg List.length he
    simp only [List.length_take, List.length_drop, List.length_map] at this
    omega
  subst hlm
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, hn]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_callPure (C := Cx) kiX fBsq bsqParams [vv kiOb, .const 0, vv kiN, vv kiR, .const (BitVec.ofNat 64 a)]
    bsqBody [cellA Cx ob, BitVec.ofNat 64 0, BitVec.ofNat 64 blk.length, ecell Cx oR, BitVec.ofNat 64 a]
    (bsqVal blk rs a 0) (by decide) rfl hD hc.self
    ⟨by simp [sev, hob], by simp [sev], by simp [sev, hn], by simp [sev, hr], by simp [sev], trivial⟩
    (PostB Cx) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bsqParams _ rfl hlk)
      (bsq_spec Cx hok hc blk ob hblk rs oR hR a hle hRl _ 0 Cx.H s rfl (Nat.zero_le _) (List.prefix_refl _)))
    (fun w H' hp' hw => ?_)
  subst hw
  cases hv : bsqVal blk rs a 0
  · refine specR_ifI _ 0 (by simp [sev, Env.get_cons, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    refine hk _ H' hp' (fun x hx => by simp [Env.get_cons, hx]) (fun he => ?_)
    rw [bsqVal_of_eq blk rs a hle he] at hv; cases hv
  · exact specR_ifI _ 1 (by simp [sev, Env.get_cons, boolW]) (fun _ => specR_hangI) (fun h => absurd h (by decide))

theorem ki_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kiLocals → (ctxEnv C ++ kiParams.zip vals).get x = none :=
  Knot.params_none C kiLocals kiParams vals (by decide) (by decide)

set_option maxHeartbeats 64000000 in
/-- **The record of an inductive block.** -/
theorem ki_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (C : Ctx) (hok : CtxOK C) (hs : C.side = false) (hpl : C.saved = none) (hc : KICodes mode C)
    (hf : ConPanqueque.Front.FrontOK C) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (heqS : ∀ (C' : Ctx), SameLay C C' → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
      (lu lv : ConLeche.Level), denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C' H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C' H) o w s' st))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H)))
    (hA : denoteN C.St.ns anonH = some .anonymous) (hb : BasisInv C)
    (block : List IConstantInfo) (nP : Nat) (o ob : Nat) (hq1 : C.H[o + 1]? = some (BitVec.ofNat 64 nP))
    (hq2 : C.H[o + 2]? = some (cellA C ob)) (hblk : IndBlk C C.H ob block)
    (hlen : block.length < 2 ^ 59) (hnP : nP < 2 ^ 59)
    (hlp : ∀ i (hi : i < block.length), block[i].toConstantVal.levelParams.length < 2 ^ 59)
    (hrun : IndRun C block nP) (s : AState) (hmode : mode = .verified) (env : ConLeche.Env)
    (hseq : ConPanqueque.Bridge.SeqOK env C.fe s) (bP : List ConLeche.ConstantInfo)
    (hbP : Frontend.denoteCIList s.store block = some bP) :
    SpecR (σ := σ) (Pre C s (kiParams.zip [cellA C o])) (kiBody C) s
      (checkDeclStep mode pins C.fe (.indDecl block nP)) (PostBlk C) := by
  subst hmode
  refine specR_prologue (postBlk_locals C) (ki_none C _) ?_
  refine UD.specR_heapLoadI' (C := C) kiNp _ (o + 1) _ hq1 (by decide)
    (by simp +decide [sev, Env.get, kiParams, ctxEnv]; exact cellA_add8 C o) ?_
  refine UD.specR_heapLoadI' (C := C) kiOb _ (o + 2) _ hq2 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, kiParams, ctxEnv]; exact cellA_add_ofNat C o 2) ?_
  have hblk0 := hblk
  obtain ⟨os, hosl, hosb, hosr⟩ := hblk0
  have hn0 : C.H[ob]? = some (BitVec.ofNat 64 block.length) := by simpa [hosl] using hosb.1
  refine UD.specR_heapLoadI' (C := C) kiN (vv kiOb) ob _ hn0 (by decide) (by simp [sev, Env.get_cons]) ?_
  obtain ⟨wR, hwR, oR, hwoR, hblkR⟩ := hok.pinsRel.2.2.2.2.2.2
  have hblkR' : EBlk C.EH oR (C.pins.reserved.map Enc.idxW) := hblkR
  refine specR_envLoadI kiR _ (C.PO + pinCount + 4) wR (by decide) rfl hwR ?_
  have hlR : C.EH[oR]? = some (BitVec.ofNat 64 C.pins.reserved.length) := by
    have h := hblkR'.1; simp only [List.length_map] at h; exact h
  refine specR_envLoadI kiRl (vv kiR) oR _ (by decide) (by simp [Env.get_cons, hwoR]; rfl) hlR ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hlenR : C.pins.reserved.length < 2 ^ 61 := by
    have hl2 : C.EH.length ≤ C.EN := ht0.sr.env.1.len
    have hlay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64 := hok.envLay
    rcases Nat.eq_zero_or_pos C.pins.reserved.length with h0 | hpos
    · omega
    · have h1 := hblkR'.2 (C.pins.reserved.length - 1) (by simp; omega)
      have hlt : oR + 1 + (C.pins.reserved.length - 1) < C.EH.length := (List.getElem?_eq_some_iff.mp h1).1
      omega
  rw [hwoR]
  refine specR_callPure (C := C) kiX fIbn ibnParams [vv kiOb, .const 0, vv kiN, vv kiR, vv kiRl] ibnBody
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 block.length, ecell C oR, BitVec.ofNat 64 C.pins.reserved.length]
    () (by decide) rfl (by decide) hc.ibn.self
    ⟨by simp +decide [sev, Env.get_cons], by simp [sev], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (PostKFH C s (∀ c ∈ block.drop 0, NameFree C c.name))
    (fun _ _ s' H' => s' = s ∧ ∀ c ∈ block, NameFree C c.name)
    (fun a w s' st ⟨hs', hP, H', hp', hsr⟩ => ⟨H', hp', ⟨hs', fun c hc' => hP c (by simpa using hc')⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibnParams _ rfl hlk)
      (ibn_spec C hok hc.ibn block ob hblk oR hblkR' (by omega) _ 0 C.H s rfl (Nat.zero_le _) (List.prefix_refl _)))
    (fun w H1 hp1 ⟨_, hfree⟩ => ?_)
  have hp1' : C.H <+: H1 := hp1
  have hok1 := ctxOK_H hok H1
  unfold checkDeclStep
  refine specR_runBind (andPinOk_ind hok ht0.sr.pins block nP hfree) ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
  refine specR_congr (m' := ((flushCaches >>= fun _ => (get : AM AState) >>= fun s' =>
      set { s' with memos := Memos.empty }) >>= fun _ => checkDecl .verified pins C.fe (IDeclaration.indDecl block nP)))
    (by simp only [bind_assoc]) ?_
  refine specR_flushTopI (C := ctxH C H1) (D := ctxLocals ++ kiLocals) hok1 hpl true _ (stepFlush_run s) (by decide) ?_
  have hF1 : FoldOK env C.fe (flushedS true s) := seqOK_flushed hseq true
  have hbP1 : Frontend.denoteCIList (flushedS true s).store block = some bP := hbP
  generalize hsF : flushedS true s = s1 at hF1 hbP1
  simp only [checkDecl, checkDeclKind, bind_assoc]
  refine specR_callNIH (C := ctxH C H1) kiOk fIpo ipoParams [vv kiOb, .const 0, vv kiN, vv kiNp] ipoBody
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 block.length, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc.ipo
    ⟨by simp +decide [sev, Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl, by simp [sev],
      by simp +decide [sev, Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem],
      by simp +decide [sev, Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem], trivial⟩
    (fun b w s' st => indParamsOk nP block s1 = .ok (b, s') ∧ PostB (ctxH C H1) b w s' st)
    (fun b w s' _ => indParamsOk nP block s1 = .ok (b, s') ∧ w = boolW b)
    (fun b w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ipoParams _ rfl hlk)
      (ipo_spec C hc.ipo hc.pst block ob nP (by omega) hlen _ 0 H1 s1 hp1' (indBlk_mono hblk hp1') rfl (Nat.zero_le _))))
    (fun okb w s2 H2 hp2 ⟨hipr, hw⟩ => ?_)
  subst hw
  obtain ⟨hps2, -⟩ := ConRon.Bridge.Inductives.indParamsOk_spec nP block bP s1 s2 okb hF1.check.state hbP1 hipr
  have hF2 : FoldOK env C.fe s2 := hF1.ofCore (hps2.toCore hF1.check)
  have hbP2 : Frontend.denoteCIList s2.store block = some bP := denoteCIList_mono hps2.ext _ _ hbP1
  have hp2' : C.H <+: H2 := hp1'.trans hp2
  cases okb
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine specR_atEntry fun t2 ht2 => ?_
  have hx2 : Ext C.St s2.store := ht2.sr.floor
  simp only [bind_assoc]
  refine specR_callNIH (C := ctxH C H2) kiSh fReadBlock rbParams [vv kiOb, vv kiNp] (rbBody C)
    [cellA C ob, BitVec.ofNat 64 nP] (by decide) rfl (by decide) hc.rb.rb
    ⟨by simp +decide [sev, Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem], trivial⟩
    (fun r w s' st => ∃ a, r = .ok a ∧ unwrapE (readBlock nP block) s2 = .ok (a, s') ∧ PostRB (ctxH C H2) a w s' st)
    (fun r w s' H' => ∃ p, r = .ok p ∧ unwrapE (readBlock nP block) s2 = .ok (p, s') ∧
      ∃ osh, w = cellA C osh ∧ ShapeRep C H' osh p)
    (fun r w s' st ⟨a, hra, hr, H', hp', hsr, osh, hw, hsh⟩ => ⟨H', hp', ⟨a, hra, hr, osh, hw, hsh⟩, hsr⟩)
    (fun u hu _ hlk => specR_of_unwrap (Knot.specR_of_pre u (pre_of_lookups hu rbParams _ rfl hlk)
      (rb_spec ra C hok hc.rb block ob nP hlen hnP hlp hA hLE H2 s2 hp2' (indBlk_mono hblk hp2'))))
    (fun r w s3 H3 hp3 ⟨p, hrp, hrb, osh, hw, hsh⟩ => ?_)
  subst hw hrp
  simp only
  have hp3' : C.H <+: H3 := hp2'.trans hp3
  obtain ⟨hbrf, hcbkf⟩ := hrun env C.fe bP s2 p s3 hF2 hx2 (sr_nodeCount ht2.sr) hbP2 (unwrapE_ok hrb)
  obtain ⟨hps3, hrb3⟩ := ConRon.Bridge.Inductives.readBlock_run nP block bP s2 s3 (.ok p) hF2.check hbP2 (unwrapE_ok hrb)
  obtain ⟨pP, -, hdsh3⟩ := hrb3
  have hF3 : FoldOK env C.fe s3 := hF2.ofCore (hps3.toCore hF2.check)
  refine specR_atEntry fun t3 ht3 => ?_
  have hx3 : Ext C.St s3.store := ht3.sr.floor
  have hpin3 : s3.pins = C.pins := ht3.sr.pins
  refine specR_invRaise (R' := PostBlk (ctxSt C s3.store)) ?_ (fun a w s' t hx h => postBlk_lower (C := C) hx a w s' t h)
  let C3 : Ctx := { C with H := H3, St := s3.store }
  have hok3 : CtxOK C3 := ctxOK_St (ctxOK_H hok H3) _
  have hA3 : denoteN C3.St.ns anonH = some .anonymous := hx3.lss.ls.ns _ _ hA
  have hcBR : BRCodes C3 := by ctx_tr hc.br
  have hcBRS : C3.code.lookup fBlockReadsAt = some (brParams.map (fun p => (p, ShapeHOL.one)), brBody C3, .one) := by
    ctx_tr hc.brS
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hbrf
  simp only [bind_assoc]
  refine specR_callNC (C := C3) kiRd fBlockReadsAt brParams [vv kiSh] (brBody C3) [cellA C osh]
    (by decide) rfl (by decide) hcBRS ⟨by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (fun r w s' st => blockReadsAt C.fe p s3 = .ok (r, s') ∧ PostBR C3 r w s' st)
    (fun r w s' C' => blockReadsAt C.fe p s3 = .ok (r, s') ∧ w = boolW r.1 ∧ ConRon.Bridge.Inductives.GR.FEq r.2 C.fe ∧
      r.2.natLit = C.fe.natLit ∧
      r.2.strLit = C.fe.strLit ∧ ∃ H' EH', C' = ctxE (ctxH C3 H') EH' ∧ H3 <+: H' ∧ C.EH <+: EH')
    (fun r w s' st ⟨h0, h1, h2, h3, h4, H', EH', h5, h6, h7⟩ => ⟨_, ⟨h0, h1, h2, h3, h4, H', EH', rfl, h5, h6⟩, h7⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu brParams _ rfl hlk)
      (br_spec ra C3 hok3 (by obtain ⟨⟩ := hf; constructor <;> assumption) hcBR hA3
        (fun sa hpa hxa => hF3.check.pins.mono hxa (by rw [hpa, hpin3]))
        p osh hsh b1 b2 b3 b4 b5 b6 b7 b8 s3)))
    (fun d w s4 C4 ⟨hbrr, ew, hfeq, hn4, hs4, H4, EH4, eC, hp4, hpE4⟩ => ?_)
  subst eC ew
  obtain ⟨c4, hrel4, -, -, -⟩ := ConRon.Bridge.Inductives.blockReadsAt_bridge hF3.check
    (ConRon.Bridge.Inductives.EnvRel.ofCheck hF3.check hF3.gate hF3.envWF) hdsh3 hbrr
  obtain ⟨reads, fe₀⟩ := d
  simp only at hfeq hn4 hs4 c4 hrel4 ⊢
  have hp4' : H3 <+: H4 := hp4
  have hfT : ∀ n, fe₀.findTable? n = C.fe.findTable? n := fun n => by
    unfold IFEnv.findTable?; rw [hfeq.find?, hfeq.rawTable?]
  refine specR_atEntry fun t4 ht4 => ?_
  refine specR_feI (fe := fe₀) (by unfold litW; rw [hn4, hs4]; rfl)
    (Decl.envDen_congr hfeq.find? hfT ht4.sr.envd) ?_
  let C5 : Ctx := { C with H := H4, St := s3.store, EH := EH4, fe := fe₀ }
  have hok5 : CtxOK C5 := ctxOK_fe (ctxOK_E (ctxOK_H hok3 H4) hpE4) (fun n => hfeq.find? n) hfT
  have hcK : CBKCodes .verified C5 := by ctx_tr hc.cbk
  have hg5 : TblGate fe₀ := hfeq.gate hg
  have hF5 : FlagsOK fe₀ := FlagsOK.of_same hF (by rw [hfeq.2.2.1]) hfeq.find? hn4 hs4
  have hL5 : LitsPinned fe₀ C.pins := by unfold LitsPinned; rw [hfeq.2.2.1]; exact hL
  refine specR_callNC (C := C5) kiFe fCbk cbkParams [vv kiSh] (cbkBody C5) [cellA C osh]
    (by decide) rfl (by decide) hcK.self ⟨by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (PostBlk C5)
    (fun fe' w s' C' => ∃ EH envM tblM H, C' = ctxNT C5 fe' EH envM tblM H ∧ EH4 <+: EH ∧ H4 <+: H ∧
      CtxOK (ctxNT C5 fe' EH envM tblM H) ∧ TblGate fe' ∧ FlagsOK fe' ∧ LitsPinned fe' C.pins)
    (fun a w s' st ⟨EH, envM, tblM, H, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, tblM, H, rfl, h1, h2, h3, h5⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cbkParams _ rfl hlk)
      (cbk_spec_any .verified ra C5 hok5 hs hpl hcK (by obtain ⟨⟩ := hf; constructor <;> assumption) hg5 hF5 hL5
        (fun C' hcode => heqS C' hcode) block p osh (shapeRep_mono hp4' hsh)
        (fun ms0 rc hm hr => hcbkf C5 rfl rfl ms0 rc hm hr) s4 ⟨env, c4, hF3.envWF, hrel4⟩))
    (fun fe' w s5 C6 ⟨EH6, envM6, tblM6, H6, eC, hpE6, hp6, hok6, hg6, hF6, hL6⟩ => ?_)
  subst eC
  cases reads
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [↓reduceIte, pure_bind]
  refine specR_flushTopI hok6 hpl false flushCaches rfl (by decide) ?_
  generalize hsF6 : flushedS false s5 = s6
  refine specR_offCheckI (by decide) (fun hoff => ?_)
  obtain ⟨st0, hwf0, hx0, hres0, hrun0⟩ := hb
  have hrs16 : C.pins.reserved.length = 16 := by
    have hl : ∀ (xs : List NIdx) (ns : List ConLeche.Name), denoteNL st0 xs ns → xs.length = ns.length := by
      intro xs; induction xs with
      | nil => intro ns h; cases ns with
        | nil => rfl
        | cons => exact h.elim
      | cons x xs ih =>
        intro ns h
        cases ns with
        | nil => simp [denoteNL] at h
        | cons n ns => simp only [List.length_cons]; exact congrArg (· + 1) (ih ns h.2)
    rw [hl _ _ hres0]; rfl
  have hpH6 : C.H <+: H6 := hp1'.trans (hp2.trans (hp3.trans (hp4'.trans hp6)))
  have hpE6 : C.EH <+: EH6 := hpE4.trans hpE6
  let C6 := ctxNT C5 fe' EH6 envM6 tblM6 H6
  have hok6' : CtxOK C6 := hok6
  have hblk6 : IndBlk C6 C6.H ob block := indBlk_mono hblk hpH6
  have hR6 : EBlk C6.EH oR (C.pins.reserved.map Enc.idxW) := eblk_mono hblkR' hpE6
  have hcB : BSQCodes C6 := by ctx_tr hc.bsq
  have hbl : block.length < 2 ^ 61 := by omega
  refine specR_kiHitI hok6' hcB block ob hblk6 C.pins.reserved oR hR6 (by omega) 3 0 (by omega) hbl
    (by simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
    (by simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl)
    (by simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl) (by decide)
    (fun Γ1 H7 hp7 hΓ1 hne1 => ?_)
  refine specR_kiHitI (ctxOK_H hok6' H7) (by ctx_tr hcB) block ob (indBlk_mono hblk6 hp7) C.pins.reserved oR hR6
    (by omega) 4 3 (by omega) hbl
    (by rw [hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
    (by rw [hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl)
    (by rw [hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl)
    (by decide) (fun Γ2 H8 hp8 hΓ2 hne2 => ?_)
  have hp78 : H6 <+: H8 := hp7.trans hp8
  refine specR_kiHitI (ctxOK_H hok6' H8) (by ctx_tr hcB) block ob (indBlk_mono hblk6 hp78) C.pins.reserved oR hR6
    (by omega) 2 7 (by omega) hbl
    (by rw [hΓ2 _ (by decide), hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
    (by rw [hΓ2 _ (by decide), hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl)
    (by rw [hΓ2 _ (by decide), hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl)
    (by decide) (fun Γ3 H9 hp9 hΓ3 hne3 => ?_)
  have hp79 : H6 <+: H9 := hp78.trans hp9
  refine specR_kiHitI (ctxOK_H hok6' H9) (by ctx_tr hcB) block ob (indBlk_mono hblk6 hp79) C.pins.reserved oR hR6
    (by omega) 2 9 (by omega) hbl
    (by rw [hΓ3 _ (by decide), hΓ2 _ (by decide), hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
    (by rw [hΓ3 _ (by decide), hΓ2 _ (by decide), hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl)
    (by rw [hΓ3 _ (by decide), hΓ2 _ (by decide), hΓ1 _ (by decide)]; simp +decide [Env.get_cons, Env.kill, ConPanqueque.T.ExP.Env.get_kill_of_not_mem] <;> rfl)
    (by decide) (fun Γ4 H10 hp10 hΓ4 hne4 => ?_)
  have hp6t : H6 <+: H10 := hp79.trans hp10
  have hnh : NoHit (ctxH C6 H10) block := by
    intro k hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hne1
    · exact hne2
    · exact hne3
    · exact hne4
  have hbC : BasisInv (ctxH C6 H10) := ⟨st0, hwf0, hx0.trans hx3, hres0, hrun0⟩
  refine specR_atEntry fun t10 ht10 => ?_
  refine specR_runBind (basisNamesOk_ind (ctxOK_H hok6' H10) hbC ht10.sr hoff block nP hfree hnh) ?_
  simp only [↓reduceIte]
  exact specR_returnI _ 0 rfl (fun t ht => ⟨EH6, envM6, tblM6, H10, hpE6, hpH6.trans hp6t, ctxOK_H hok6' H10,
    sr_of_eq ht.sr rfl rfl rfl rfl, hg6, hF6, hL6⟩)

end

end ConPanqueque.T.Ind
