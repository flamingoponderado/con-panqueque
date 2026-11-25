import ConPanqueque.T.Ind.MentionsAny
import ConPanqueque.T.Ind.RecFire

/-!
# `blockIsRec`: does some member occur in some binder domain of some constructor type

`piDomsMentionAny names fuel e` walks the syntactic telescope of `e`, asking `mentionsAnyConst names` of each
domain (`mentionsAnyGo` at an empty memo); `blockIsRec` asks it of every constructor type of every member, the names
the members' own (a value-heap block of the names, filled from the member records).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG

def pzF := ofString "pz_f"
def pzNs := ofString "pz_ns"
def pzNn := ofString "pz_nn"
def pzE := ofString "pz_e"
def pzTy := ofString "pz_ty"
def pzB := ofString "pz_b"
def pzK := ofString "pz_k"
def pzR := ofString "pz_r"
def pzX := ofString "pz_x"
def fPiDomsMA := ofString "piDomsMentionAny"

def pzParams : List MlS := [pzF, pzNs, pzNn, pzE]
def pzLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, pzTy, pzB, pzK, pzR, pzX]

def pzBody : ProgHOL 64 := prologue pzLocals
  (.ite (.cmp .equal (vv pzF) (.const 0)) hang
  (viewOf pzE
    (.ite (veEqC lDg 6)
      (.seq (.assign .local pzTy (.load .one (vv lRp)))
      (.seq (.assign .local pzB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, pzK), none)) WC.fMx
        [.const (BitVec.ofNat 64 coreWalkFuel), vv pzNs, vv pzNn, vv pzTy, .const 0])
      (.seq (.assign .local pzR (.load .one (vv pzK)))
      (.ite (.cmp .notEqual (vv pzR) (.const 0)) (.return (.const 1))
        (.seq (.call (some (some (.local, pzX), none)) fPiDomsMA [.op .sub [vv pzF, .const 1], vv pzNs, vv pzNn, vv pzB])
          (.return (vv pzX))))))))
      (.return (.const 0)))))

structure PZCodes (C : Ctx) : Prop where
  mx : WC.MxCodes C
  self : C.code.lookup fPiDomsMA = some (pzParams.map (fun p => (p, ShapeHOL.one)), pzBody, .one)

section
variable {σ : Type}

theorem pz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pzLocals → (ctxEnv C ++ pzParams.zip vals).get x = none :=
  Knot.params_none C pzLocals pzParams vals (by decide) (by decide)

/-- **`piDomsMentionAny`** at every fuel. -/
theorem pz_spec (C : Ctx) (hok : CtxOK C) (hc : PZCodes C) (names : List NIdx) (pn : Nat)
    (hl : names.length < 2 ^ 59) (hns : Elems C.H pn names) :
    ∀ n, n < 2 ^ 64 → ∀ (e : EIdx) (H : List (BitVec 64)) (s : AState), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (pzParams.zip [BitVec.ofNat 64 n, cellA C pn, BitVec.ofNat 64 names.length,
        Enc.idxW e])) pzBody s (piDomsMentionAny names n e) (PostB (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro _ e H s hp
    refine specR_prologue (postB_locals _) (pz_none _ _) ?_
    rw [piDomsMentionAny]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, pzParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
  intro hn e H s hp
  refine specR_prologue (postB_locals _) (pz_none _ _) ?_
  rw [piDomsMentionAny]
  have hne := WC.ofNat_succ_ne n (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pzParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  have tagNo : ∀ (h : EIdx) (vh : ENodeView) (k : Nat) (u32 : UInt32), u32 = UInt32.ofNat k → k < 16 →
      h.tag = UInt32.ofNat vh.tagN → vh.tagN ≠ k → (h.tag == u32) = false := by
    intro h vh k u32 hu hk hat hne
    rw [hat, hu]
    have hl := ConPanqueque.T.Big.tagN_lt vh
    have : UInt32.ofNat vh.tagN ≠ UInt32.ofNat k := by
      intro e; have := congrArg UInt32.toNat e; simp at this; omega
    simpa using this
  have gTag : ∀ (Γ : Env) (vh : ENodeView) (k : Nat), k < 16 → Γ.get lDg = some (BitVec.ofNat 64 vh.tagN) →
      sev Γ (veEqC lDg k) = some (boolW (vh.tagN == k)) := by
    intro Γ vh k hk hg
    simp only [veEqC]
    rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vh.tagN) (BitVec.ofNat 64 k) (by simp only [sev, sev_vv]; exact hg) rfl,
      wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt vh; omega) (by omega)]
    by_cases h : vh.tagN = k <;> simp [h, boolW]
  unfold viewOf
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, pzParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv pzE) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons, Env.get, pzParams, ctxEnv]) ?_
  refine ConPanqueque.T.Big.specR_viewP e (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, pzParams, ctxEnv] <;> rfl) (by decide) (fun ve P hve htne hlene => ?_)
  have hate := tag_of_tagN htne
  by_cases h6 : ve.tagN = 6
  swap
  · refine specR_ifI _ _ (gTag _ ve 6 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, h6]))
      (fun _ => ?_)
    simp only [tagNo e ve 6 ETag.forallE rfl (by decide) hate h6, Bool.false_eq_true, ite_false]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ _ (gTag _ ve 6 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
    (fun h => absurd h (by simp [boolW, h6]))
  rcases ve with _ | _ | _ | _ | _ | _ | ⟨dom, bd⟩ | _ | _ | _ <;> simp [ENodeView.tagN] at h6
  have hte : e.tag = ETag.forallE := by rw [hate]; rfl
  simp only [hte, beq_self_eq_true, ite_true]
  refine specR_runBind (show viewBind e s = .ok (some (dom, bd), s) by
    rw [WC.viewBind_run, WC.viewBind_of_view_forallE hte hve]) ?_
  refine specR_loadI' pzTy _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW bd] []) ?_
  refine specR_loadI' pzB _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW bd) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW bd) [] []) ?_
  simp only [mentionsAnyConst, bind_assoc, pure_bind]
  refine specR_callNIH (C := ctxH C H) pzK WC.fMx WC.mxParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv pzNs, vv pzNn, vv pzTy, .const 0] (WC.mxBody C)
    [BitVec.ofNat 64 coreWalkFuel, cellA C pn, BitVec.ofNat 64 names.length, Enc.idxW dom, 0] (by decide) rfl
    (by decide) hc.mx.self
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, pzParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, pzParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (WC.PostLb (ctxH C H) s)
    (fun rm w s' H' => s' = s ∧ ∃ o pm', w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
      WC.LbRep C H' pm' rm.2)
    (fun rm w s' st ⟨h1, H', o, pm', hp', hw, h0, h1', hrep', hsr⟩ =>
      ⟨H', hp', ⟨h1, o, pm', hw, h0, h1', WC.lbRep_ofH hrep'⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu WC.mxParams _ rfl hlk)
      (WC.mx_spec C hok hc.mx names pn hl hns coreWalkFuel CV.coreWalkFuel_lt dom ∅ H s 0 hp (WC.lbRep_empty C H)))
    (fun rm w s' H1 hp1 ⟨hs', o, pm', hw, h0, h1', hrep'⟩ => ?_)
  subst s'; subst hw
  have hp1' : H <+: H1 := hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) pzR (vv pzK) o (boolW rm.1) h0 (by decide) (by simp [Env.get]; rfl) ?_
  cases hr : rm.1
  · refine specR_ifI _ 0 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ite_false]
    refine specR_congr (m' := piDomsMentionAny names n bd >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) pzX fPiDomsMA pzParams [.op .sub [vv pzF, .const 1], vv pzNs, vv pzNn, vv pzB]
      pzBody [BitVec.ofNat 64 n, cellA C pn, BitVec.ofNat 64 names.length, Enc.idxW bd] (by decide) rfl
      (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, pzParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
        by simp +decide [sev, Env.get_cons, Env.get, pzParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, pzParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pzParams _ rfl hlk)
        (ih (by omega) bd H1 s (hp.trans hp1')))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    exact specR_returnI _ _ (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H2, hp1'.trans hp2', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [ite_true]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def czNs := ofString "cz_ns"
def czNn := ofString "cz_nn"
def czL := ofString "cz_l"
def czI := ofString "cz_i"
def czN := ofString "cz_n"
def czO := ofString "cz_o"
def czT := ofString "cz_t"
def czR := ofString "cz_r"
def czX := ofString "cz_x"
def fCtorsAnyPD := ofString "ctorsAnyPD"

def czParams : List MlS := [czNs, czNn, czL, czI, czN]
def czLocals : List MlS := [czO, czT, czR, czX]

/-- Some constructor (pair block at `czL`, from `czI`) has a binder domain mentioning a name. -/
def czBody : ProgHOL 64 := prologue czLocals
  (.ite (.cmp .lower (vv czI) (vv czN))
    (.seq (.assign .local czO (.load .one (.op .add [vv czL, .op .add [.panop .mul [vv czI, .const 16], .const 8]])))
    (.seq (.assign .local czT (.load .one (.op .add [vv czO, .const 16])))
    (.seq (.call (some (some (.local, czR), none)) fPiDomsMA
      [.const (BitVec.ofNat 64 coreWalkFuel), vv czNs, vv czNn, vv czT])
    (.ite (.cmp .notEqual (vv czR) (.const 0)) (.return (.const 1))
      (.seq (.call (some (some (.local, czX), none)) fCtorsAnyPD
        [vv czNs, vv czNn, vv czL, .op .add [vv czI, .const 1], vv czN]) (.return (vv czX)))))))
    (.return (.const 0)))

def mzNs := ofString "mz_ns"
def mzNn := ofString "mz_nn"
def mzMs := ofString "mz_ms"
def mzI := ofString "mz_i"
def mzN := ofString "mz_n"
def mzO := ofString "mz_o"
def mzL := ofString "mz_l"
def mzC := ofString "mz_c"
def mzR := ofString "mz_r"
def mzX := ofString "mz_x"
def fMembersAnyPD := ofString "membersAnyPD"

def mzParams : List MlS := [mzNs, mzNn, mzMs, mzI, mzN]
def mzLocals : List MlS := [mzO, mzL, mzC, mzR, mzX]

/-- Some member (pointer block at `mzMs`, from `mzI`) has such a constructor. -/
def mzBody : ProgHOL 64 := prologue mzLocals
  (.ite (.cmp .lower (vv mzI) (vv mzN))
    (.seq (.assign .local mzO (.load .one (.op .add [vv mzMs, .op .add [.panop .mul [vv mzI, .const 8], .const 8]])))
    (.seq (.assign .local mzL (.load .one (.op .add [vv mzO, .const 24])))
    (.seq (.assign .local mzC (.load .one (vv mzL)))
    (.seq (.call (some (some (.local, mzR), none)) fCtorsAnyPD [vv mzNs, vv mzNn, vv mzL, .const 0, vv mzC])
    (.ite (.cmp .notEqual (vv mzR) (.const 0)) (.return (.const 1))
      (.seq (.call (some (some (.local, mzX), none)) fMembersAnyPD
        [vv mzNs, vv mzNn, vv mzMs, .op .add [vv mzI, .const 1], vv mzN]) (.return (vv mzX))))))))
    (.return (.const 0)))

structure BICodes (C : Ctx) : Prop where
  pz : PZCodes C
  cz : C.code.lookup fCtorsAnyPD = some (czParams.map (fun p => (p, ShapeHOL.one)), czBody, .one)
  mz : C.code.lookup fMembersAnyPD = some (mzParams.map (fun p => (p, ShapeHOL.one)), mzBody, .one)

section
variable {σ : Type}

theorem cz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ czLocals → (ctxEnv C ++ czParams.zip vals).get x = none :=
  Knot.params_none C czLocals czParams vals (by decide) (by decide)

theorem mz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mzLocals → (ctxEnv C ++ mzParams.zip vals).get x = none :=
  Knot.params_none C mzLocals mzParams vals (by decide) (by decide)

/-- The constructors from position `i`. -/
theorem cz_spec (C : Ctx) (hok : CtxOK C) (hc : BICodes C) (names : List NIdx) (pn : Nat)
    (hl : names.length < 2 ^ 59) (hns : Elems C.H pn names) (cs : List (IConstantVal × Nat)) (ol : Nat)
    (hcs : CtorsRep C C.H ol cs) :
    ∀ k i (H : List (BitVec 64)) (s : AState), cs.length - i = k → i ≤ cs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (czParams.zip [cellA C pn, BitVec.ofNat 64 names.length, cellA C ol,
        BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length])) czBody s
        ((cs.drop i).anyM fun c => piDomsMentionAny names coreWalkFuel c.1.type) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk hi hp
    refine specR_prologue (postB_locals _) (cz_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hcl : cs.length < 2 ^ 60 := by
      have h0 := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix hcs.1 hp)).1
      rcases Nat.lt_or_ge 0 cs.length with h | h
      · obtain ⟨oc, h1, -⟩ := hcs.2 (cs.length - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix h1 hp)).1; omega
      · omega
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, czParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega : cs.length ≤ i)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i H s hk hi hp
    have hix : i < cs.length := by omega
    refine specR_prologue (postB_locals _) (cz_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    obtain ⟨oc, h1, hcv, -⟩ := hcs.2 i hix
    have h1' := ConPanqueque.T.Decl.get_prefix h1 hp
    have hcl : cs.length < 2 ^ 60 := by
      obtain ⟨oc', h1l, -⟩ := hcs.2 (cs.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix h1l hp)).1; omega
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, czParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hix])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := ctxH C H) czO _ (ol + 1 + 2 * i) _ h1' (by decide)
      (by simp +decide [sev, Env.get, czParams, ctxEnv]; exact cellA_mul16 C ol i (by omega)) ?_
    have hty := ConPanqueque.T.Decl.get_prefix hcv.2.2 hp
    refine UD.specR_heapLoadI' (C := ctxH C H) czT _ (oc + 2) _ hty (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_plus C oc 2) ?_
    rw [List.drop_eq_getElem_cons hix, List.anyM_cons]
    refine specR_callNIH (C := ctxH C H) czR fPiDomsMA pzParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv czNs, vv czNn, vv czT] pzBody
      [BitVec.ofNat 64 coreWalkFuel, cellA C pn, BitVec.ofNat 64 names.length, Enc.idxW cs[i].1.type] (by decide) rfl
      (by decide) hc.pz.self
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, czParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, czParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pzParams _ rfl hlk)
        (pz_spec C hok hc.pz names pn hl hns coreWalkFuel CV.coreWalkFuel_lt _ H s hp))
      (fun r w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases r
    · refine specR_ifI _ 0 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ite_false]
      refine specR_congr (m' := (cs.drop (i + 1)).anyM (fun c => piDomsMentionAny names coreWalkFuel c.1.type) >>=
        fun r => pure r) (by rw [bind_pure]) ?_
      refine specR_callNIH (C := ctxH C H1) czX fCtorsAnyPD czParams
        [vv czNs, vv czNn, vv czL, .op .add [vv czI, .const 1], vv czN] czBody
        [cellA C pn, BitVec.ofNat 64 names.length, cellA C ol, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length]
        (by decide) rfl (by decide) hc.cz
        ⟨by simp +decide [sev, Env.get_cons, Env.get, czParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, czParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, czParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, czParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, czParams, ctxEnv], trivial⟩
        (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu czParams _ rfl hlk)
          (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
        (fun r w s2 H2 hp2 hw => ?_)
      subst hw
      have hp2' : H1 <+: H2 := hp2
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H2, hp1'.trans hp2', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [ite_true]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- The members from position `i`. -/
theorem mz_spec (C : Ctx) (hok : CtxOK C) (hc : BICodes C) (names : List NIdx) (pn : Nat)
    (hl : names.length < 2 ^ 59) (hns : Elems C.H pn names) (ms : List MemberShape) (om : Nat)
    (hms : PtrsRep C C.H om (MemberRep C C.H) ms) :
    ∀ k i (H : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (mzParams.zip [cellA C pn, BitVec.ofNat 64 names.length, cellA C om,
        BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length])) mzBody s
        ((ms.drop i).anyM fun m => m.ctors.anyM fun c => piDomsMentionAny names coreWalkFuel c.1.type)
        (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk hi hp
    refine specR_prologue (postB_locals _) (mz_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hml : ms.length < 2 ^ 61 := by
      have h0 := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix hms.1 hp)).1
      rcases Nat.lt_or_ge 0 ms.length with h | h
      · obtain ⟨oc, h1, -⟩ := hms.2 (ms.length - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix h1 hp)).1; omega
      · omega
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, mzParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega : ms.length ≤ i)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i H s hk hi hp
    have hix : i < ms.length := by omega
    refine specR_prologue (postB_locals _) (mz_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    obtain ⟨oi, h1, hmr⟩ := hms.2 i hix
    have h1' := ConPanqueque.T.Decl.get_prefix h1 hp
    have hml : ms.length < 2 ^ 61 := by
      obtain ⟨oc', h1l, -⟩ := hms.2 (ms.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix h1l hp)).1; omega
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mzParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hix])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := ctxH C H) mzO _ (om + 1 + i) _ h1' (by decide)
      (by simp +decide [sev, Env.get, mzParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    obtain ⟨ol, hol, hcs⟩ := hmr.2.2.2
    refine UD.specR_heapLoadI' (C := ctxH C H) mzL _ (oi + 3) _ (ConPanqueque.T.Decl.get_prefix hol hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_plus C oi 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mzC _ ol _ (ConPanqueque.T.Decl.get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hix, List.anyM_cons]
    refine specR_congr (m' := (ms[i].ctors.drop 0).anyM (fun c => piDomsMentionAny names coreWalkFuel c.1.type) >>=
      fun b => if b = true then pure true else (ms.drop (i + 1)).anyM fun m => m.ctors.anyM fun c =>
        piDomsMentionAny names coreWalkFuel c.1.type) (by rw [List.drop_zero]) ?_
    refine specR_callNIH (C := ctxH C H) mzR fCtorsAnyPD czParams [vv mzNs, vv mzNn, vv mzL, .const 0, vv mzC] czBody
      [cellA C pn, BitVec.ofNat 64 names.length, cellA C ol, BitVec.ofNat 64 0, BitVec.ofNat 64 ms[i].ctors.length]
      (by decide) rfl (by decide) hc.cz
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mzParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mzParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl,
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu czParams _ rfl hlk)
        (cz_spec C hok hc names pn hl hns ms[i].ctors ol hcs _ 0 H s rfl (Nat.zero_le _) hp))
      (fun r w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases r
    · refine specR_ifI _ 0 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ite_false]
      refine specR_congr (m' := (ms.drop (i + 1)).anyM (fun m => m.ctors.anyM fun c =>
        piDomsMentionAny names coreWalkFuel c.1.type) >>= fun r => pure r) (by rw [bind_pure]) ?_
      refine specR_callNIH (C := ctxH C H1) mzX fMembersAnyPD mzParams
        [vv mzNs, vv mzNn, vv mzMs, .op .add [vv mzI, .const 1], vv mzN] mzBody
        [cellA C pn, BitVec.ofNat 64 names.length, cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length]
        (by decide) rfl (by decide) hc.mz
        ⟨by simp +decide [sev, Env.get_cons, Env.get, mzParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mzParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mzParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, mzParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, mzParams, ctxEnv], trivial⟩
        (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mzParams _ rfl hlk)
          (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
        (fun r w s2 H2 hp2 hw => ?_)
      subst hw
      have hp2' : H1 <+: H2 := hp2
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H2, hp1'.trans hp2', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [ite_true]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def nmMs := ofString "nm_ms"
def nmD := ofString "nm_d"
def nmI := ofString "nm_i"
def nmK := ofString "nm_k"
def nmX := ofString "nm_x"
def nmY := ofString "nm_y"
def nmZ := ofString "nm_z"
def nmR := ofString "nm_r"
def fNmFill := ofString "memberNamesFill"

def nmParams : List MlS := [nmMs, nmD, nmI, nmK]
def nmLocals : List MlS := [nmX, nmY, nmZ, nmR]

/-- The members' names (pointer block at `nmMs`, from `nmI`) into the block at `nmD`. -/
def nmBody : ProgHOL 64 := prologue nmLocals
  (.ite (.cmp .lower (vv nmI) (vv nmK))
    (.seq (.assign .local nmX (.load .one (.op .add [vv nmMs, .op .add [.panop .mul [vv nmI, .const 8], .const 8]])))
    (.seq (.assign .local nmY (.load .one (vv nmX)))
    (.seq (.assign .local nmZ (.load .one (vv nmY)))
    (.seq (.store (.op .add [vv nmD, .op .add [.panop .mul [vv nmI, .const 8], .const 8]]) (vv nmZ))
    (.seq (.call (some (some (.local, nmR), none)) fNmFill [vv nmMs, vv nmD, .op .add [vv nmI, .const 1], vv nmK])
      (.return (.const 0)))))))
    (.return (.const 0)))

def biMs := ofString "bi_ms"
def biK := ofString "bi_k"
def biNb := ofString "bi_nb"
def biX := ofString "bi_x"
def biR := ofString "bi_r"
def fBlockIsRec := ofString "blockIsRec"

def biParams : List MlS := [biMs, biK]
def biLocals : List MlS := [biNb, biX, biR]

/-- `blockIsRec` at the members' pointer block `biMs` of `biK` members. -/
def biBody (C : Ctx) : ProgHOL 64 := prologue biLocals
  (guardP biK 58
  (allocP C biNb (.shift .lsl (.op .add [vv biK, .const 1]) (.const 3))
  (.seq (.store (vv biNb) (vv biK))
  (.seq (.call (some (some (.local, biX), none)) fNmFill [vv biMs, vv biNb, .const 0, vv biK])
  (.seq (.call (some (some (.local, biR), none)) fMembersAnyPD [vv biNb, vv biK, vv biMs, .const 0, vv biK])
    (.return (vv biR)))))))

section
variable {σ : Type}

/-- The names from position `i` on, past the frozen prefix `Hc`. -/
def PostNM (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (ms : List MemberShape) (i : Nat) (_ : Unit) (_ : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧
    ∀ j (hj : j < ms.length), i ≤ j → H'[o + 1 + j]? = some (Enc.idxW ms[j].cvT.name)

theorem postNM_locals (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (ms : List MemberShape) (i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNM C Hc o ms i a w s' st → PostNM C Hc o ms i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem nm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nmLocals → (ctxEnv C ++ nmParams.zip vals).get x = none :=
  Knot.params_none C nmLocals nmParams vals (by decide) (by decide)

/-- **The member-names fill** from position `i`. -/
theorem nm_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fNmFill = some (nmParams.map (fun p => (p, ShapeHOL.one)), nmBody, .one))
    (ms : List MemberShape) (om o : Nat) (H0 : List (BitVec 64)) (hms : PtrsRep C H0 om (MemberRep C H0) ms) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length → H0 <+: Hc →
      Hc.length ≤ o + 1 + i → Hc <+: H → o + 1 + ms.length ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (nmParams.zip [cellA C om, cellA C o, BitVec.ofNat 64 i,
        BitVec.ofNat 64 ms.length])) nmBody s (pure ()) (PostNM C Hc o ms i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi h0 hHc hp hl
    refine specR_prologue (postNM_locals _ _ _ _ _) (nm_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, nmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc s hk hi h0 hHc hp hl
    have hil : i < ms.length := by omega
    refine specR_prologue (postNM_locals _ _ _ _ _) (nm_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, nmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨oi, h1, hmr⟩ := hms.2 i hil
    obtain ⟨oc, hoc, hcv⟩ := hmr.1
    refine UD.specR_heapLoadI' (C := ctxH C H) nmX _ (om + 1 + i) _ (ConPanqueque.T.Decl.get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, nmParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nmY _ oi _ (ConPanqueque.T.Decl.get_prefix hoc h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nmZ _ oc _ (ConPanqueque.T.Decl.get_prefix hcv.1 h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hj : o + 1 + i < (ctxH C H).H.length := by show o + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_H hok H) _ (vv nmZ) (o + 1 + i) hj (Enc.idxW ms[i].cvT.name)
      (by simp +decide [sev, Env.get_cons, Env.get, nmParams, ctxEnv]; exact cellA_mulIdx C o i (by omega))
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H.set (o + 1 + i) (Enc.idxW ms[i].cvT.name))) _ _ _ _) _ _ _ _
    generalize hB : H.set (o + 1 + i) (Enc.idxW ms[i].cvT.name) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[o + 1 + i]? = some (Enc.idxW ms[i].cvT.name) := by rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hp
    let Hc' := B.take (o + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIG (C := ctxH C B) nmR fNmFill nmParams [vv nmMs, vv nmD, .op .add [vv nmI, .const 1], vv nmK]
      nmBody [cellA C om, cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, nmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, nmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, nmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, nmParams, ctxEnv], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostNM C Hc' o ms (i + 1) a w s' st)
      (fun a w s' H' => s' = s ∧ Hc' <+: H' ∧
        ∀ j (hj : j < ms.length), i + 1 ≤ j → H'[o + 1 + j]? = some (Enc.idxW ms[j].cvT.name))
      (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) B Hc' s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega) _
          (pre_of_lookups hu nmParams _ rfl hlk)))
      (fun a w s' H' ⟨hs', hp', hc'⟩ => ?_)
    subst hs'
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
      rcases Nat.lt_or_ge i j with h | h
      · exact hc' j hj (by omega)
      · have e : j = i := by omega
        subst e
        have := ConPanqueque.T.Decl.get_prefix (show Hc'[o + 1 + j]? = some (Enc.idxW ms[j].cvT.name) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'
        exact this⟩)

theorem biCodes_H {C : Ctx} (hc : BICodes C) (H : List (BitVec 64)) : BICodes (ctxH C H) :=
  ⟨⟨⟨hc.pz.mx.ml, hc.pz.mx.lh, hc.pz.mx.self⟩, hc.pz.self⟩, hc.cz, hc.mz⟩

theorem bi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ biLocals → (ctxEnv C ++ biParams.zip vals).get x = none :=
  Knot.params_none C biLocals biParams vals (by decide) (by decide)

/-- **`blockIsRec`** at the block's members. -/
theorem bi_spec (C : Ctx) (hok : CtxOK C) (hc : BICodes C)
    (hn : C.code.lookup fNmFill = some (nmParams.map (fun p => (p, ShapeHOL.one)), nmBody, .one))
    (p : BlockShape) (om : Nat) (hms : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (biParams.zip [cellA C om, BitVec.ofNat 64 p.members.length])) (biBody C) s
      (blockIsRec p) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (bi_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hml : p.members.length + 2 < 2 ^ 61 := by
    have h0 := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix hms.1 hp)).1
    rcases Nat.lt_or_ge 0 p.members.length with h | h
    · obtain ⟨oc, h1, -⟩ := hms.2 (p.members.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp (ConPanqueque.T.Decl.get_prefix h1 hp)).1; omega
    · omega
  refine specR_guardI biK p.members.length 58 (by decide) (by simp +decide [Env.get, biParams, ctxEnv]) (by omega)
    (fun hm58 => ?_)
  refine specR_allocI (C := ctxH C H) biNb _ (p.members.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get_cons, Env.get, biParams, ctxEnv]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : H <+: H2 := hp2
  have hq0 : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv biNb) (vv biK) H2.length hq0 (BitVec.ofNat 64 p.members.length)
    (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons, Env.get, biParams, ctxEnv]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 p.members.length))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 p.members.length) = B
  have hBlen : B.length = H2.length + (p.members.length + 1) := by rw [← hB]; simp [hws]
  have hpB : H2 <+: B := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc := B.take (H2.length + 1)
  have hpc : H2 <+: Hc := by
    refine prefix_of_get? (by simp [Hc]; omega) (fun j hj => ?_)
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
  refine specR_pureBind () ?_
  refine specR_callNIG (C := ctxH C B) biX fNmFill nmParams [vv biMs, vv biNb, .const 0, vv biK] nmBody
    [cellA C om, cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide) hn
    ⟨by simp +decide [sev, Env.get_cons, Env.get, biParams, ctxEnv], by simp +decide [sev, Env.get_cons]; rfl, rfl,
      by simp +decide [sev, Env.get_cons, Env.get, biParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostNM C Hc H2.length p.members 0 a w s' st)
    (fun a w s' H' => s' = s ∧ Hc <+: H' ∧
      ∀ j (hj : j < p.members.length), 0 ≤ j → H'[H2.length + 1 + j]? = some (Enc.idxW p.members[j].cvT.name))
    (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact nm_spec C hok hn p.members om H2.length C.H hms _ 0 B Hc s rfl (Nat.zero_le _)
        (hp.trans (hp2'.trans hpc)) (by simp [Hc]) (List.take_prefix _ _) (by omega) _
        (pre_of_lookups hu nmParams _ rfl hlk)))
    (fun a w s' H3 ⟨hs', hp3, hc3⟩ => ?_)
  subst s'
  have hp3' : H <+: H3 := hp2'.trans (hpc.trans hp3)
  have hns : Elems H3 H2.length p.memberNames := fun j hj => by
    simp only [BlockShape.memberNames, List.length_map] at hj
    simp only [BlockShape.memberNames, List.getElem_map]
    exact hc3 j hj (Nat.zero_le _)
  have hnl : p.memberNames.length = p.members.length := by simp [BlockShape.memberNames]
  refine specR_congr (m' := (p.members.drop 0).anyM (fun m => m.ctors.anyM fun c =>
    piDomsMentionAny p.memberNames coreWalkFuel c.1.type) >>= fun r => pure r)
    (by rw [List.drop_zero, bind_pure]; rfl) ?_
  refine specR_callNIH (C := ctxH C H3) biR fMembersAnyPD mzParams
    [vv biNb, vv biK, vv biMs, .const 0, vv biK] mzBody
    [cellA C H2.length, BitVec.ofNat 64 p.memberNames.length, cellA C om, BitVec.ofNat 64 0,
      BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide) hc.mz
    ⟨by simp +decide [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons, Env.get, biParams, ctxEnv, hnl],
      by simp +decide [sev, Env.get_cons, Env.get, biParams, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, biParams, ctxEnv], trivial⟩
    (PostB (ctxH C H3)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mzParams _ rfl hlk)
      (mz_spec (ctxH C H3) (ctxOK_H hok H3) (biCodes_H hc H3) p.memberNames H2.length (by rw [hnl]; omega) hns p.members om
        (ptrsRep_mono (hp.trans hp3') (fun oi a h => memberRep_mono (hp.trans hp3') h)
          (ptrsRep_mono (List.prefix_refl _) (fun oi a h => h) hms))
        _ 0 H3 s rfl (Nat.zero_le _) (List.prefix_refl _)))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  have hp4' : H3 <+: H4 := hp4
  exact specR_returnI _ _ (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H4, hp3'.trans hp4', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
