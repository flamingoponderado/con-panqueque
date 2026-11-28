import ConPanqueque.T.Ind.K53

/-!
# A class's constructor for the generator, recursive fields included (`classCtorOf`)

`ihk`: the inductive hypotheses at one field (none, one at class `0`, or other).  `cmi`: the inductive hypotheses
of a constructor's minor slot.  `cfs`: `classFieldsOf`, a field naming a member recursive at class `0` (other
classes hang).  `cco`/`ccl`: `classCtorOf`/`classCtorsOf` at the one class, node agreement (`cfg`) included.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

theorem cellA_pairA (C : Ctx) (o i : Nat) (hi : i < 2 ^ 60) :
    cellA C o + (BitVec.ofNat 64 i * 16#64 + 8#64) = cellA C (o + 1 + 2 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem cellA_pairB (C : Ctx) (o i : Nat) (hi : i < 2 ^ 60) :
    cellA C o + (BitVec.ofNat 64 i * 16#64 + 16#64) = cellA C (o + 1 + 2 * i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem pairsRep_len60 {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} (hHN : H.length ≤ C.HN) {o : Nat}
    {ps : List (Nat × Nat)} (h : PairsRep H o ps) : ps.length < 2 ^ 60 := by
  have hlay := hok.heapLay
  rcases Nat.eq_zero_or_pos ps.length with h0 | hpos
  · omega
  · have := (List.getElem?_eq_some_iff.mp (h.2.1 (ps.length - 1) (by omega)).1).1; omega

theorem pairsRep_mono' {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {ps : List (Nat × Nat)}
    (h : PairsRep H o ps) : PairsRep H' o ps :=
  ⟨get_prefix h.1 hp, fun k hk => ⟨get_prefix (h.2.1 k hk).1 hp, get_prefix (h.2.1 k hk).2 hp⟩, h.2.2⟩

/-! ## The inductive hypotheses at one field -/

/-- None (`0`), exactly one at class `0` (`1`), else `2`. -/
def ihkVal : List (Nat × Nat) → Nat
  | [] => 0
  | [q] => if q.2 = 0 then 1 else 2
  | _ :: _ :: _ => 2

theorem ihkVal_cons (q : Nat × Nat) (l : List (Nat × Nat)) :
    ihkVal (q :: l) = if ihkVal l = 0 then (if q.2 = 0 then 1 else 2) else 2 := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · by_cases h : a.2 = 0 <;> simp [ihkVal, h]
  · simp [ihkVal]

theorem ihkVal_le (l : List (Nat × Nat)) : ihkVal l ≤ 2 := by
  rcases l with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> simp only [ihkVal] <;> (try split) <;> omega

theorem ihkVal_zero {l : List (Nat × Nat)} (h : ihkVal l = 0) : l = [] := by
  rcases l with _ | ⟨q, _ | ⟨_, _⟩⟩
  · rfl
  · simp only [ihkVal] at h; split at h <;> omega
  · simp [ihkVal] at h

theorem ihkVal_one {l : List (Nat × Nat)} (h : ihkVal l = 1) : ∃ a, l = [(a, 0)] := by
  rcases l with _ | ⟨q, _ | ⟨_, _⟩⟩
  · simp [ihkVal] at h
  · simp only [ihkVal] at h; split at h
    · rename_i hq; exact ⟨q.1, by rw [← hq]⟩
    · omega
  · simp [ihkVal] at h

def ihkIh := ofString "ihk_ih"
def ihkJ := ofString "ihk_j"
def ihkN := ofString "ihk_n"
def ihkI := ofString "ihk_i"
def ihkA := ofString "ihk_a"
def ihkB := ofString "ihk_b"
def ihkR := ofString "ihk_r"
def fIhk := ofString "ihsAtField"

def ihkParams : List MlS := [ihkIh, ihkJ, ihkN, ihkI]
def ihkLocals : List MlS := [ihkA, ihkB, ihkR]

def ihkBody : ProgHOL 64 := prologue ihkLocals
  (.ite (.cmp .lower (vv ihkJ) (vv ihkN))
    (.seq (.assign .local ihkA (.load .one (.op .add [vv ihkIh, .op .add [.panop .mul [vv ihkJ, .const 16], .const 8]])))
    (.seq (.assign .local ihkB (.load .one (.op .add [vv ihkIh, .op .add [.panop .mul [vv ihkJ, .const 16], .const 16]])))
    (.seq (.call (some (some (.local, ihkR), none)) fIhk [vv ihkIh, .op .add [vv ihkJ, .const 1], vv ihkN, vv ihkI])
    (.ite (.cmp .equal (vv ihkA) (vv ihkI))
      (.ite (.cmp .equal (vv ihkR) (.const 0))
        (.ite (.cmp .equal (vv ihkB) (.const 0)) (.return (.const 1)) (.return (.const 2)))
        (.return (.const 2)))
      (.return (vv ihkR))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem ihk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ihkLocals → (ctxEnv C ++ ihkParams.zip vals).get x = none :=
  Knot.params_none C ihkLocals ihkParams vals (by decide) (by decide)

/-- A small count's answer, the state and heap kept. -/
def PostIK (C : Ctx) (s : AState) (r : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ 2 ∧ SR C s' st

set_option maxHeartbeats 16000000 in
theorem ihk_spec (C : Ctx) (hc : C.code.lookup fIhk = some (ihkParams.map (fun p => (p, ShapeHOL.one)), ihkBody, .one))
    (ps : List (Nat × Nat)) (oi : Nat) (H : List (BitVec 64)) (hpr : PairsRep H oi ps) (hpl : ps.length < 2 ^ 60)
    (i : Nat) (hi : i < 2 ^ 63) :
    ∀ f j (s : AState), ps.length - j = f → j ≤ ps.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ihkParams.zip [cellA C oi, BitVec.ofNat 64 j, BitVec.ofNat 64 ps.length,
        BitVec.ofNat 64 i])) ihkBody s (pure (ihkVal ((ps.drop j).filter (·.1 == i)))) (PostIK (ctxH C H) s) := by
  have hpost : ∀ (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostIK (ctxH C H) s a w s' st → PostIK (ctxH C H) s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ ⟨h0, h1, h2, h4⟩ => ⟨h0, h1, h2, sr_of_eq h4 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro j s hf hj
    have hin : j = ps.length := by omega
    subst hin
    refine specR_prologue (hpost s) (ihk_none _ _) ?_
    have hlw := nd_lt_iff ps.length ps.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ihkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, by simp [ihkVal], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j s hf hj
    have hin : j < ps.length := by omega
    refine specR_prologue (hpost s) (ihk_none _ _) ?_
    have hlw := nd_lt_iff j ps.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ihkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨ha, hb⟩ := hpr.2.1 j hin
    have hqb := hpr.2.2 ps[j] (List.getElem_mem hin)
    refine UD.specR_heapLoadI' (C := ctxH C H) ihkA _ (oi + 1 + 2 * j) _ ha (by decide)
      (by simp +decide [sev, Env.get, ihkParams, ctxEnv]; exact cellA_pairA C oi j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ihkB _ (oi + 1 + 2 * j + 1) _ hb (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, ihkParams, ctxEnv]; exact cellA_pairB C oi j (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin, List.filter_cons]
    refine specR_congr (m' := (pure (ihkVal ((ps.drop (j + 1)).filter (·.1 == i))) : AM Nat) >>= fun r =>
      pure (if (ps[j].1 == i) = true then (if r = 0 then (if ps[j].2 = 0 then 1 else 2) else 2) else r))
      (by simp only [pure_bind]; split <;> simp [ihkVal_cons]) ?_
    refine specR_callNIH (C := ctxH C H) ihkR fIhk ihkParams [vv ihkIh, .op .add [vv ihkJ, .const 1], vv ihkN, vv ihkI]
      ihkBody [cellA C oi, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 ps.length, BitVec.ofNat 64 i] (by decide) rfl
      (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ihkParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ihkParams, ctxEnv]; exact word_add1_eq j,
        by simp +decide [sev, Env.get_cons, Env.get, ihkParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ihkParams, ctxEnv], trivial⟩
      (PostIK (ctxH C H) s) (fun r w s' H' => H' = H ∧ s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ 2)
      (fun r w s' st ⟨h0, h1, h2, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, h1, h2⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ihkParams _ rfl hlk) (ih (j + 1) s (by omega) (by omega)))
      (fun r w s3 H3 hp3 ⟨eH, es, hw, hr⟩ => ?_)
    subst eH es hw
    by_cases hai : ps[j].1 = i
    swap
    · have hne : BitVec.ofNat 64 ps[j].1 ≠ BitVec.ofNat 64 i := fun e => hai (by
        have := congrArg BitVec.toNat e; simp at this; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ihkParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
      have hbf : (ps[j].1 == i) = false := by simpa using hai
      simp only [hbf, Bool.false_eq_true, ite_false]
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, rfl, hr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, ihkParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hai]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [hai, beq_self_eq_true, ite_true]
    by_cases hr0 : r = 0
    swap
    · have hne : BitVec.ofNat 64 r ≠ 0#64 := fun e => hr0 (by have := congrArg BitVec.toNat e; simp at this; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hr0, ite_false]
      exact specR_returnI _ 2 rfl (fun t ht => ⟨rfl, rfl, by omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    subst hr0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [ite_true]
    by_cases hb0 : ps[j].2 = 0
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb0])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [hb0, ite_true]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, rfl, by omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : BitVec.ofNat 64 ps[j].2 ≠ 0#64 := fun e => hb0 (by
        have := congrArg BitVec.toNat e; simp at this; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hb0, ite_false]
      exact specR_returnI _ 2 rfl (fun t ht => ⟨rfl, rfl, by omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The minor slot's inductive hypotheses -/

def cmiS := ofString "cmi_s"
def cmiI := ofString "cmi_i"
def cmiN := ofString "cmi_n"
def cmiCn := ofString "cmi_cn"
def cmiP := ofString "cmi_p"
def cmiTg := ofString "cmi_tg"
def cmiCc := ofString "cmi_cc"
def cmiCv := ofString "cmi_cv"
def cmiR := ofString "cmi_r"
def fCmi := ofString "minorSlotIhs"

def cmiParams : List MlS := [cmiS, cmiI, cmiN, cmiCn]
def cmiLocals : List MlS := [cmiP, cmiTg, cmiCc, cmiCv, cmiR]

def cmiRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, cmiR), none)) fCmi [vv cmiS, .op .add [vv cmiI, .const 1], vv cmiN, vv cmiCn])
    (.return (vv cmiR))

def cmiBody : ProgHOL 64 := prologue cmiLocals
  (.ite (.cmp .lower (vv cmiI) (vv cmiN))
    (.seq (.assign .local cmiP (.load .one (.op .add [vv cmiS, .op .add [.panop .mul [vv cmiI, .const 8], .const 8]])))
    (.seq (.assign .local cmiTg (.load .one (vv cmiP)))
    (.ite (.cmp .equal (vv cmiTg) (.const 1))
      (.seq (.assign .local cmiCc (.load .one (.op .add [vv cmiP, .const 8])))
      (.seq (.assign .local cmiCv (.load .one (.op .add [vv cmiP, .const 16])))
      (.ite (.cmp .equal (vv cmiCc) (.const 0))
        (.ite (.cmp .equal (vv cmiCv) (vv cmiCn))
          (.seq (.assign .local cmiR (.load .one (.op .add [vv cmiP, .const 24]))) (.return (vv cmiR)))
          cmiRec)
        cmiRec)))
      cmiRec)))
    hang)

section
variable {σ : Type}

theorem cmi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cmiLocals → (ctxEnv C ++ cmiParams.zip vals).get x = none :=
  Knot.params_none C cmiLocals cmiParams vals (by decide) (by decide)

/-- The first minor slot at `(0, cn)` from `i` on: its inductive hypotheses' pairs. -/
def PostCMI (C : Ctx) (sls : List ClassSlot) (cn : NIdx) (i : Nat) (s : AState) (_ : Unit) (w : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ r oi, w = cellA C oi ∧ i ≤ r ∧ ∃ hr : r < sls.length, isHitC cn sls[r] = true ∧
    (∀ k (hk : k < sls.length), i ≤ k → k < r → isHitC cn sls[k] = false) ∧ PairsRep C.H oi (ihsOf sls[r]) ∧
    SR C s' st

set_option maxHeartbeats 16000000 in
theorem cmi_spec (C : Ctx) (hc : C.code.lookup fCmi = some (cmiParams.map (fun p => (p, ShapeHOL.one)), cmiBody, .one))
    (sls : List ClassSlot) (os : Nat) (hsl : sls.length < 2 ^ 58) (cn : NIdx)
    (hcb : ∀ sl ∈ sls, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63) (H : List (BitVec 64))
    (hsb : SlotBlk C H os sls) :
    ∀ f i (s : AState), sls.length - i = f → i ≤ sls.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cmiParams.zip [cellA C os, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length,
        Enc.idxW cn])) cmiBody s (pure ()) (PostCMI (ctxH C H) sls cn i s) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hsb
  have hpost : ∀ (i : Nat) (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostCMI (ctxH C H) sls cn i s a w s' st → PostCMI (ctxH C H) sls cn i s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ _ ⟨h0, r, oi, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h0, r, oi, h1, h2, h3, h4, h5, h6, sr_of_eq h7 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (hpost _ s) (cmi_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, cmiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  | succ f ih =>
    intro i s hf hi
    have hin : i < sls.length := by omega
    refine specR_prologue (hpost _ s) (cmi_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cmiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hsr⟩ := hpsr i hin
    have hio : i < ps.length := by omega
    have hpe := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hpi : ps[i] = op := by simpa [List.getElem?_eq_getElem hio] using hop
    rw [hpi] at hpe
    refine UD.specR_heapLoadI' (C := ctxH C H) cmiP _ (os + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cmiParams, ctxEnv]; exact cellA_mulIdx C os i (by omega)) ?_
    have hrec : isHitC cn sls[i] = false → ∀ (Γ : Env), Γ.get cmiS = some (cellA C os) →
        Γ.get cmiI = some (BitVec.ofNat 64 i) → Γ.get cmiN = some (BitVec.ofNat 64 sls.length) →
        Γ.get cmiCn = some (Enc.idxW cn) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ cmiLocals)) cmiRec s (pure ())
          (PostCMI (ctxH C H) sls cn i s) := by
      intro hf0 Γ gS gI gN gC
      refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) cmiR fCmi cmiParams [vv cmiS, .op .add [vv cmiI, .const 1], vv cmiN, vv cmiCn]
        cmiBody [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length, Enc.idxW cn] (by decide) rfl (by decide) hc
        ⟨by simp [sev, gS], by simp [sev, sev_vv, gI]; exact word_add1_eq i, by simp [sev, gN], by simp [sev, gC], trivial⟩
        (PostCMI (ctxH C H) sls cn (i + 1) s)
        (fun _ w s' H' => H' = H ∧ s' = s ∧ ∃ r oi, w = cellA C oi ∧ i + 1 ≤ r ∧ ∃ hr : r < sls.length,
          isHitC cn sls[r] = true ∧ (∀ k (hk : k < sls.length), i + 1 ≤ k → k < r → isHitC cn sls[k] = false) ∧
          PairsRep H oi (ihsOf sls[r]))
        (fun a w s' st ⟨h0, r, oi, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, r, oi, h1, h2, h3, h4, h5, h6⟩, h7⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmiParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun _ w s3 H3 hp3 ⟨eH, es, r, oi, hw, hr1, hr2, hr3, hr4, hr5⟩ => ?_)
      subst eH es hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨rfl, r, oi, rfl, by omega, hr2, hr3,
        fun k hk h1 h2 => by
          rcases Nat.lt_or_ge i k with h | h
          · exact hr4 k hk h h2
          · have : k = i := by omega
            subst this; exact hf0, hr5, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hsli := List.getElem_mem hin
    generalize hsl : sls[i] = sl at hsr hsli hrec
    cases sl with
    | motive k =>
      obtain ⟨h0, -, -, -⟩ := hsr
      refine UD.specR_heapLoadI' (C := ctxH C H) cmiTg (vv cmiP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      exact hrec (by simp [isHitC]) _ (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
    | minor c C' ihs =>
      obtain ⟨h0, h1, h2, oi, h3, hpr⟩ := hsr
      have hc63 := hcb _ hsli c C' ihs rfl
      refine UD.specR_heapLoadI' (C := ctxH C H) cmiTg (vv cmiP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) cmiCc _ (op + 1) _ h1 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) cmiCv _ (op + 2) _ h2 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 2) ?_
      by_cases hc0 : c = 0
      swap
      · have hne : BitVec.ofNat 64 c ≠ 0#64 := fun e => hc0 (by have := congrArg BitVec.toNat e; simp at this; omega)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
        exact hrec (by simp [isHitC, hc0]) _ (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
      subst hc0
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases hcv : C' = cn
      swap
      · have hne : Enc.idxW C' ≠ Enc.idxW cn := fun e => hcv (Enc.idxW_inj e)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cmiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        exact hrec (by simp [isHitC, hcv]) _ (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
          (by simp +decide [Env.get_cons, Env.get, cmiParams, ctxEnv])
      subst hcv
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cmiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) cmiR _ (op + 3) _ h3 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 3) ?_
      exact specR_returnI _ (cellA C oi) (by simp +decide [sev, Env.get_cons])
        (fun t ht => ⟨rfl, i, oi, rfl, Nat.le_refl _, hin, by rw [hsl]; simp [isHitC],
          fun k hk h1 h2 => absurd h2 (by omega), by rw [hsl]; exact hpr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- The first hit's inductive hypotheses are `firstIhs`. -/
theorem firstIhs_eq (sls : List ClassSlot) (cn : NIdx) (r : Nat) (hr : r < sls.length) (h1 : isHitC cn sls[r] = true)
    (h2 : ∀ k (hk : k < sls.length), k < r → isHitC cn sls[k] = false) : firstIhs cn sls = ihsOf sls[r] := by
  unfold firstIhs
  have : sls.find? (isHitC cn) = some sls[r] := by
    rw [List.find?_eq_some_iff_getElem]
    exact ⟨h1, r, hr, rfl, fun j hj => by rw [h2 j (by omega) hj]; rfl⟩
  rw [this]; rfl

end

/-! ## `classFieldsOf`, recursive fields at class `0` -/

def cfsA := ofString "cfs_a"
def cfsI := ofString "cfs_i"
def cfsN := ofString "cfs_n"
def cfsMs := ofString "cfs_ms"
def cfsIh := ofString "cfs_ih"
def cfsIn := ofString "cfs_in"
def cfsX := ofString "cfs_x"
def cfsT := ofString "cfs_t"
def cfsO := ofString "cfs_o"
def cfsK := ofString "cfs_k"
def fCfs := ofString "classFieldsOf"

def cfsParams : List MlS := [cfsA, cfsI, cfsN, cfsMs, cfsIh, cfsIn]
def cfsLocals : List MlS := gaaLocals ++ [cfsX, cfsT, cfsO, cfsK]

def cfsRec : ProgHOL 64 :=
  .call (some (some (.local, ExS.lY), none)) fCfs [vv cfsA, .op .add [vv cfsI, .const 1], vv cfsN, vv cfsMs, vv cfsIh,
    vv cfsIn]

def cfsBody (C : Ctx) : ProgHOL 64 := prologue cfsLocals
  (.ite (.cmp .lower (vv cfsI) (vv cfsN))
    (.seq (.assign .local cfsX (.load .one (.op .add [vv cfsA, .op .add [.panop .mul [vv cfsI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, cfsT), none)) fFvt [vv cfsX])
    (.seq (.call (some (some (.local, cfsO), none)) fNocTop [vv cfsT, vv cfsMs, .const 0, .const 0])
    (.seq (.call (some (some (.local, cfsK), none)) fIhk [vv cfsIh, .const 0, vv cfsIn, vv cfsI])
    (.ite (.cmp .equal (vv cfsO) (.const 0))
      (.ite (.cmp .equal (vv cfsK) (.const 0))
        (.seq cfsRec (.seq (.assign .local cfsX (.const 0)) (prependP C cfsX)))
        hang)
      (.ite (.cmp .equal (vv cfsK) (.const 1))
        (.seq (.call (some (some (.local, cfsX), none)) fPbn [.const (BitVec.ofNat 64 coreWalkFuel), vv cfsT])
        (.seq (.assign .local cfsX (.op .add [vv cfsX, .const 1]))
        (.seq cfsRec (prependP C cfsX))))
        hang))))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure CFSCodes (C : Ctx) : Prop where
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  nt : NTCodes C
  ihk : C.code.lookup fIhk = some (ihkParams.map (fun p => (p, ShapeHOL.one)), ihkBody, .one)
  pbn : C.code.lookup fPbn = some ([(pFu, .one), (pH, .one)], pbnBody, .one)
  self : C.code.lookup fCfs = some (cfsParams.map (fun p => (p, ShapeHOL.one)), cfsBody C, .one)

section
variable {σ : Type}

theorem cfs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cfsLocals → (ctxEnv C ++ cfsParams.zip vals).get x = none :=
  Knot.params_none C cfsLocals cfsParams vals (by decide) (by decide)

/-- The kinds' answer: a fresh block of `cfKindW`s, `n` of them, recursive at class `0` only. -/
def PostKS (C : Ctx) (n : Nat) (ks : List ClassField) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o (ks.map cfKindW) ∧ ks.length = n ∧ KindsOK ks ∧ SR (ctxH C H') s' st

theorem postKS_locals (C : Ctx) (n : Nat) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostKS C n a w s' st → PostKS C n a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4, h5, h6⟩ => ⟨H', o, h1, h2, h3, h4, h5, sr_of_eq h6 rfl rfl rfl rfl⟩

set_option maxHeartbeats 32000000 in
/-- **`classFieldsOf p ihs i`** over the fields from `i` on (a field naming a member at another class hangs). -/
theorem cfs_spec (C : Ctx) (hok : CtxOK C) (hc : CFSCodes C) (p : BlockShape) (ms : List MemberShape) (om : Nat)
    (hms : p.members = ms) (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59)
    (ihs : List (Nat × Nat)) (oi : Nat) (hpr : PairsRep C.H oi ihs) (hil : ihs.length < 2 ^ 60)
    (fvs : List EIdx) (pa : Nat) (hfl : fvs.length < 2 ^ 58) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0)
    (hA : BlkAt H0 pa (fvs.map Enc.idxW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState), fvs.length - i = f → i ≤ fvs.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cfsParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 fvs.length,
        cellA C om, cellA C oi, BitVec.ofNat 64 ihs.length])) (cfsBody C) s (classFieldsOf p ihs i (fvs.drop i))
        (PostKS (ctxH C H) (fvs.length - i)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = fvs.length := by omega
    subst hin
    refine specR_prologue (postKS_locals _ _) (cfs_none _ _) ?_
    have hlw := nd_lt_iff fvs.length fvs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cfsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    simp only [classFieldsOf]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, by simp,
      fun k hk => by simp at hk, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < fvs.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (postKS_locals _ _) (cfs_none _ _) ?_
    have hlw := nd_lt_iff i fvs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cfsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) cfsX _ (pa + 1 + i) _ (get_prefix hx hp) (by decide)
      (by simp +decide [sev, Env.get, cfsParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin]
    unfold classFieldsOf
    refine ILP.callE_spec (C := ctxH C H) cfsT fFvt [pH] [vv cfsX] ExM.fvtBody [Enc.idxW fvs[i]] (by decide) rfl
      (by decide) hc.fvt ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (ExM.fvt_spec (ctxH C H) s fvs[i]) (fun w s1 => ?_)
    refine specR_callNIH (C := ctxH C H) cfsO fNocTop ntParams [vv cfsT, vv cfsMs, .const 0, .const 0] ntBody
      [Enc.idxW w, cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.nt.top
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv], rfl, rfl,
        trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
        (by simp only [BlockShape.memberNames, hms]; exact nt_spec C hok hc.nt ms om hM hml 0 0 (by decide) (by decide) w H s1 hpC))
      (fun b wb s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H <+: H2 := hp2
    refine specR_callPure (C := ctxH C H2) cfsK fIhk ihkParams [vv cfsIh, .const 0, vv cfsIn, vv cfsI] ihkBody
      [cellA C oi, BitVec.ofNat 64 0, BitVec.ofNat 64 ihs.length, BitVec.ofNat 64 i]
      (ihkVal ((ihs.drop 0).filter (·.1 == i))) (by decide) rfl (by decide) hc.ihk
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv],
        trivial⟩
      (PostIK (ctxH C H2) s2) (fun r w _ _ => w = BitVec.ofNat 64 r ∧ r ≤ 2)
      (fun r w s' st ⟨_, h1, h2, h4⟩ => ⟨H2, List.prefix_refl _, ⟨h1, h2⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ihkParams _ rfl hlk)
        (ihk_spec C hc.ihk ihs oi H2 (pairsRep_mono' (hpC.trans hp2') hpr) hil i (by omega) ihs.length 0 s2 (by omega) (by omega)))
      (fun w H3 hp3 ⟨hw, hkv⟩ => ?_)
    subst hw
    have hp3' : H2 <+: H3 := hp3
    simp only [List.drop_zero] at hkv ⊢
    generalize hhits : ihs.filter (·.1 == i) = hits at hkv ⊢
    cases b
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases hk0 : ihkVal hits = 0
      swap
      · have hne : BitVec.ofNat 64 (ihkVal hits) ≠ 0#64 := fun e => hk0 (by
          have := congrArg BitVec.toNat e; simp at this; omega)
        exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => specR_hangI)
      have hnil := ihkVal_zero hk0
      subst hnil
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk0])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.not_false, List.length_nil, beq_self_eq_true, Bool.and_self, ite_true, bind_assoc]
      unfold cfsRec
      refine specR_callNIH (C := ctxH C H3) ExS.lY fCfs cfsParams [vv cfsA, .op .add [vv cfsI, .const 1], vv cfsN, vv cfsMs,
          vv cfsIh, vv cfsIn] (cfsBody C)
        [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 fvs.length, cellA C om, cellA C oi, BitVec.ofNat 64 ihs.length]
        (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv],
          trivial⟩
        (PostKS (ctxH C H3) (fvs.length - (i + 1))) (fun ks w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ks.map cfKindW) ∧
          ks.length = fvs.length - (i + 1) ∧ KindsOK ks)
        (fun ks w s' st ⟨H', o, hp', hw, hb, hl, hk, hsr⟩ => ⟨H', hp', ⟨o, hw, hb, hl, hk⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfsParams _ rfl hlk)
          (ih (i + 1) H3 s2 (by omega) (by omega) (hp.trans (hp2'.trans hp3'))))
        (fun ks w s4 H4 hp4 ⟨oy, hw, hry, hkl, hko⟩ => ?_)
      subst hw
      have hp4' : H3 <+: H4 := hp4
      refine specR_assignI cfsX (.const 0) 0 (by decide) rfl ?_
      refine specR_congr (m' := pure (ClassField.ordinary :: ks)) (by simp) ?_
      refine ExPre.prepend_spec C hok (H := H4) cfsX (cfKindW .ordinary) oy (ks.map cfKindW) (by decide)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons, cfKindW]) hry (by decide)
        (by simp +decide [Env.get_cons, Env.get, cfsParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
      exact ⟨H', o, hp2'.trans (hp3'.trans (hp4'.trans hp')), rfl, by simpa using hb, by simp [hkl]; omega,
        fun k hk => by
          rcases List.mem_cons.mp hk with rfl | hk
          · exact Or.inl rfl
          · exact hko k hk, hsr⟩
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      by_cases hk1 : ihkVal hits = 1
      swap
      · have hne : BitVec.ofNat 64 (ihkVal hits) ≠ 1#64 := fun e => hk1 (by
          have := congrArg BitVec.toNat e; simp at this; omega)
        exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => specR_hangI)
      obtain ⟨a, rfl⟩ := ihkVal_one hk1
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk1])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, List.length_singleton, beq_self_eq_true,
        Bool.and_self, ite_true, bind_assoc]
      refine specR_callNIH (C := ctxH C H3) cfsX fPbn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cfsT] pbnBody
        [BitVec.ofNat 64 coreWalkFuel, Enc.idxW w] (by decide) rfl (by decide) hc.pbn
        ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
        (PostPBN (ctxH C H3) coreWalkFuel) (fun r w _ _ => w = BitVec.ofNat 64 r.1.length ∧ r.1.length ≤ coreWalkFuel)
        (fun r w s' st ⟨H', hp', hs, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
          (pbn_spec C hc.pbn coreWalkFuel CV.coreWalkFuel_lt H3 s2 w))
        (fun pb wb s4 H4 hp4 ⟨hw, hbl⟩ => ?_)
      subst hw
      obtain ⟨bs, e⟩ := pb
      simp only at hbl ⊢
      have hp4' : H3 <+: H4 := hp4
      have hcw : coreWalkFuel = 4000000000 := rfl
      refine specR_assignI cfsX _ (BitVec.ofNat 64 (bs.length + 1)) (by decide)
        (by simp +decide [sev, Env.get_cons]; exact word_add1_eq bs.length) ?_
      unfold cfsRec
      refine specR_callNIH (C := ctxH C H4) ExS.lY fCfs cfsParams [vv cfsA, .op .add [vv cfsI, .const 1], vv cfsN, vv cfsMs,
          vv cfsIh, vv cfsIn] (cfsBody C)
        [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 fvs.length, cellA C om, cellA C oi, BitVec.ofNat 64 ihs.length]
        (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfsParams, ctxEnv],
          trivial⟩
        (PostKS (ctxH C H4) (fvs.length - (i + 1))) (fun ks w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ks.map cfKindW) ∧
          ks.length = fvs.length - (i + 1) ∧ KindsOK ks)
        (fun ks w s' st ⟨H', o, hp', hw, hb, hl, hk, hsr⟩ => ⟨H', hp', ⟨o, hw, hb, hl, hk⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfsParams _ rfl hlk)
          (ih (i + 1) H4 s4 (by omega) (by omega) (hp.trans (hp2'.trans (hp3'.trans hp4')))))
        (fun ks w s5 H5 hp5 ⟨oy, hw, hry, hkl, hko⟩ => ?_)
      subst hw
      have hp5' : H4 <+: H5 := hp5
      refine specR_congr (m' := pure (ClassField.recursive 0 bs.length :: ks)) (by simp [List.getD]) ?_
      refine ExPre.prepend_spec C hok (H := H5) cfsX (cfKindW (.recursive 0 bs.length)) oy (ks.map cfKindW) (by decide)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons, cfKindW]) hry (by decide)
        (by simp +decide [Env.get_cons, Env.get, cfsParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
      exact ⟨H', o, hp2'.trans (hp3'.trans (hp4'.trans (hp5'.trans hp'))), rfl, by simpa using hb, by simp [hkl]; omega,
        fun k hk => by
          rcases List.mem_cons.mp hk with rfl | hk
          · exact Or.inr ⟨bs.length, rfl, by omega⟩
          · exact hko k hk, hsr⟩

end

/-! ## `classCtorOf` at the one class -/

def ccoTb := ofString "cco_tb"
def ccoTk := ofString "cco_tk"
def ccoCv := ofString "cco_cv"
def ccoNf := ofString "cco_nf"
def ccoSl := ofString "cco_sl"
def ccoSk := ofString "cco_sk"
def ccoNk := ofString "cco_nk"
def ccoMs := ofString "cco_ms"
def ccoDs := ofString "cco_ds"
def ccoDn := ofString "cco_dn"
def ccoInd := ofString "cco_ind"
def ccoNpc := ofString "cco_npc"
def ccoUs := ofString "cco_us"
def ccoOlp := ofString "cco_olp"
def ccoTy0 := ofString "cco_ty0"
def ccoPp := ofString "cco_pp"
def ccoPn := ofString "cco_pn"
def ccoNm := ofString "cco_nm"
def ccoCn := ofString "cco_cn"
def ccoE := ofString "cco_e"
def ccoCt := ofString "cco_ct"
def ccoIh := ofString "cco_ih"
def ccoIl := ofString "cco_il"
def ccoTy := ofString "cco_ty"
def ccoX := ofString "cco_x"
def ccoFv := ofString "cco_fv"
def ccoL := ofString "cco_l"
def ccoU := ofString "cco_u"
def ccoQ := ofString "cco_q"
def ccoT0 := ofString "cco_t0"
def ccoD := ofString "cco_d"
def ccoR := ofString "cco_r"
def fCco := ofString "classCtorOf"

def ccoParams : List MlS := [ccoTb, ccoTk, ccoCv, ccoNf, ccoSl, ccoSk, ccoNk, ccoMs, ccoDs, ccoDn, ccoInd, ccoNpc, ccoUs,
  ccoOlp, ccoTy0, ccoPp, ccoPn, ccoNm]
def ccoLocals : List MlS := [ccoCn, ccoE, ccoCt, ccoIh, ccoIl, ccoTy, ccoX, ccoFv, ccoL, ccoU, ccoQ, ccoT0, ccoD, ccoR]

def ccoBody (C : Ctx) : ProgHOL 64 := prologue ccoLocals
  (.seq (.assign .local ccoCn (.load .one (vv ccoCv)))
  (.seq (.call (some (some (.local, ccoE), none)) fFfe [vv ccoTb, .const 0, vv ccoTk, vv ccoCn])
  (.seq (.call (some (some (.local, ccoCt), none)) fCms [vv ccoSl, .const 0, vv ccoSk, vv ccoCn])
  (.ite (.cmp .equal (vv ccoCt) (.const 1))
  (.seq (.call (some (some (.local, ccoIh), none)) fCmi [vv ccoSl, .const 0, vv ccoSk, vv ccoCn])
  (.seq (.assign .local ccoIl (.load .one (vv ccoIh)))
  (.seq (.assign .local ccoTy (.load .one (.op .add [vv ccoE, .const 24])))
  (.seq (.call (some (some (.local, ccoX), none)) fOpenFvars [vv ccoNf, vv ccoTy, vv ccoNk])
  (.ite (.cmp .equal (vv ccoX) (.const 0))
  hang
  (.seq (.assign .local ccoFv (.load .one (vv ccoX)))
  (.seq (.assign .local ccoL (.load .one (vv ccoFv)))
  (.ite (.cmp .equal (vv ccoL) (vv ccoNf))
  (.ite (.cmp .lower (vv ccoNpc) (.const (BitVec.ofNat 64 (2 ^ 58))))
  (.seq (.call (some (some (.local, ccoU), none)) fCfs [vv ccoFv, .const 0, vv ccoL, vv ccoMs, vv ccoIh, vv ccoIl])
  (.seq (.call (some (some (.local, ccoQ), none)) fCfg [vv ccoU, .const 0, vv ccoL, vv ccoFv, vv ccoL, vv ccoTb, vv ccoTk,
      vv ccoCn, vv ccoInd, vv ccoNpc, vv ccoMs, vv ccoUs, vv ccoOlp, vv ccoTy0, vv ccoPp, vv ccoPn, vv ccoDs, vv ccoDn,
      vv ccoNm])
  (.seq (.assign .local ccoT0 (.load .one (.op .add [vv ccoCv, .const 16])))
  (.seq (.call (some (some (.local, ccoD), none)) fInstPis [vv ccoDs, .const 0, vv ccoDn, vv ccoT0])
  (alloc6 C ccoR (vv ccoCv) (vv ccoNf) (vv ccoD) (vv ccoTy) (vv ccoL) (vv ccoU) (.return (vv ccoR)))))))
  hang)
  hang))))))))
  hang))))

structure CCOCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  ffe : C.code.lookup fFfe = some (ffeParams.map (fun p => (p, ShapeHOL.one)), ffeBody, .one)
  cms : C.code.lookup fCms = some (cmsParams.map (fun p => (p, ShapeHOL.one)), cmsBody, .one)
  cmi : C.code.lookup fCmi = some (cmiParams.map (fun p => (p, ShapeHOL.one)), cmiBody, .one)
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  cfs : CFSCodes C
  cfg : CFGCodes mode C
  ipw : C.code.lookup fInstPis = some (ipwParams.map (fun p => (p, ShapeHOL.one)), ipwBody, .one)
  i1f : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  i1c : Codes C (ExI.body C)
  self : C.code.lookup fCco = some (ccoParams.map (fun p => (p, ShapeHOL.one)), ccoBody C, .one)

section
variable {σ : Type}

theorem cco_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ccoLocals → (ctxEnv C ++ ccoParams.zip vals).get x = none :=
  Knot.params_none C ccoLocals ccoParams vals (by decide) (by decide)

/-- A class constructor, as its record. -/
def PostCC (C : Ctx) (cc : ClassCtor) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ CCRep C H' o cc ∧ SR (ctxH C H') s' st

theorem postCC_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCC C a w s' st → PostCC C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

set_option maxHeartbeats 64000000 in
/-- **`classCtorOf`** at class `0` (a member of a one-member block): ordinary and recursive fields. -/
theorem cco_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CCOCodes mode C) (p : BlockShape) (ms0 : MemberShape) (hms : p.members = [ms0])
    (rd : ClassRead) (m : TargetMajor) (hmm : m.member = some 0) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (ctor : IConstantVal × Nat) (ocv : Nat) (hcv : CVRep C C.H ocv ctor.1) (hnf : ctor.2 < 2 ^ 56)
    (ot osl pd olp pp : Nat) (tbl : List NestCtorNf) (htl : tbl.length < 2 ^ 58)
    (htb : PRep C C.H ot (fun H o nf => NfRep C H o nf) tbl)
    (hnfe : m.nfs.filter (·.ctor == ctor.1.name) = tbl.filter (·.ctor == ctor.1.name))
    (hsl : rd.slots.length < 2 ^ 58) (hcb : ∀ sl ∈ rd.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63)
    (hsb : SlotBlk C C.H osl rd.slots) (hdl : m.ds.length < 2 ^ 58) (hds : BlkAt C.H pd (m.ds.map Enc.idxW))
    (hnk : p.nP + p.k < 2 ^ 56) (hlpl : ms0.cvT.levelParams.length < 2 ^ 59) (hpl : m.pfvs.length < 2 ^ 58)
    (hlp : EBlk C.H olp (ms0.cvT.levelParams.map Enc.idxW)) (hpf : BlkAt C.H pp (m.pfvs.map Enc.idxW))
    (hnpc0 : m.nPc < 2 ^ 62) (s : AState) :
    SpecR (σ := σ) (Pre C s (ccoParams.zip [cellA C ot, BitVec.ofNat 64 tbl.length, cellA C ocv,
        BitVec.ofNat 64 ctor.2, cellA C osl, BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 (p.nP + p.k), cellA C om,
        cellA C pd, BitVec.ofNat 64 m.ds.length, Enc.idxW m.ind, BitVec.ofNat 64 m.nPc, Enc.idxW m.lvls, cellA C olp,
        Enc.idxW ms0.cvT.type, cellA C pp, BitVec.ofNat 64 m.pfvs.length, Enc.idxW ms0.cvT.name])) (ccoBody C) s
      (classCtorOf mode C.fe p [ms0.cvT.type] rd [m] 0 ctor) (PostCC C) := by
  refine specR_prologue (postCC_locals _) (cco_none _ _) ?_
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine UD.specR_heapLoadI' (C := ctxH C C.H) ccoCn (vv ccoCv) ocv _ hcv.1 (by decide) (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv]; rfl) ?_
  unfold classCtorOf
  simp only [targetMajorAt, List.getElem?_cons_zero, pure_bind]
  rw [hnfe]
  refine specR_callPure (C := ctxH C C.H) ccoE fFfe ffeParams [vv ccoTb, .const 0, vv ccoTk, vv ccoCn] ffeBody
    [cellA C ot, BitVec.ofNat 64 0, BitVec.ofNat 64 tbl.length, Enc.idxW ctor.1.name]
    ((tbl.drop 0).filter (·.ctor == ctor.1.name)) (by decide) rfl (by decide) hc.ffe
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩ (PostFE (ctxH C C.H) s)
    (fun r w s' H' => H' = C.H ∧ ∃ e es o, r = e :: es ∧ w = cellA C o ∧ NfRep C C.H o e)
    (fun r w s' st ⟨_, e, es, o, h1, h2, h3, h4⟩ => ⟨C.H, hp0, ⟨rfl, e, es, o, h1, h2, h3⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ffeParams _ rfl hlk)
      (ffe_spec C hc.ffe tbl ot htl ctor.1.name C.H htb tbl.length 0 s (by omega) (by omega)))
    (fun w H1 hp1 ⟨eH, e, es, oe, hfe, hw, hnfr⟩ => ?_)
  subst eH hw
  simp only [List.drop_zero] at hfe
  rw [hfe]
  simp only
  refine specR_callPure (C := ctxH C C.H) ccoCt fCms cmsParams [vv ccoSl, .const 0, vv ccoSk, vv ccoCn] cmsBody
    [cellA C osl, BitVec.ofNat 64 0, BitVec.ofNat 64 rd.slots.length, Enc.idxW ctor.1.name]
    ((rd.slots.drop 0).filter (isHitC ctor.1.name)).length (by decide) rfl (by decide) hc.cms
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩ (PostCMS (ctxH C C.H) (rd.slots.drop 0) ctor.1.name s)
    (fun r w s' H' => H' = C.H ∧ w = BitVec.ofNat 64 r ∧ r ≤ (rd.slots.drop 0).length)
    (fun r w s' st ⟨_, h1, h2, h4⟩ => ⟨C.H, hp0, ⟨rfl, h1, h2⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmsParams _ rfl hlk)
      (cms_spec C hc.cms rd.slots osl hsl ctor.1.name hcb C.H hsb rd.slots.length 0 s (by omega) (by omega)))
    (fun w H2 hp2 ⟨eH, hw, hr⟩ => ?_)
  subst eH hw
  simp only [List.drop_zero] at hr
  by_cases hcnt : (rd.slots.filter (isHitC ctor.1.name)).length = 1
  swap
  · have hne : BitVec.ofNat 64 (rd.slots.filter (isHitC ctor.1.name)).length ≠ 1#64 := fun e => hcnt (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hcnt]) (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨k, hk⟩ := classMinorSlot_one rd ctor.1.name hcnt
  rw [hk]
  simp only [pure_bind]
  refine specR_callPure (C := ctxH C C.H) ccoIh fCmi cmiParams [vv ccoSl, .const 0, vv ccoSk, vv ccoCn] cmiBody
    [cellA C osl, BitVec.ofNat 64 0, BitVec.ofNat 64 rd.slots.length, Enc.idxW ctor.1.name] () (by decide) rfl (by decide)
    hc.cmi
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostCMI (ctxH C C.H) rd.slots ctor.1.name 0 s)
    (fun _ w s' H' => H' = C.H ∧ ∃ r oi, w = cellA C oi ∧ ∃ hr : r < rd.slots.length,
      isHitC ctor.1.name rd.slots[r] = true ∧ (∀ k (hk : k < rd.slots.length), k < r → isHitC ctor.1.name rd.slots[k] = false) ∧
      PairsRep C.H oi (ihsOf rd.slots[r]))
    (fun a w s' st ⟨_, r, oi, h1, _, h3, h4, h5, h6, h7⟩ => ⟨C.H, hp0, ⟨rfl, r, oi, h1, h3, h4, fun k hk h => h5 k hk (by omega) h, h6⟩, h7⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmiParams _ rfl hlk)
      (cmi_spec C hc.cmi rd.slots osl hsl ctor.1.name (fun sl h c C' ihs e => (hcb sl h c C' ihs e).1) C.H hsb
        rd.slots.length 0 s (by omega) (by omega)))
    (fun w H2' hp2' ⟨eH, r, oi, hw, hr', hhit, hfirst, hpri⟩ => ?_)
  subst eH hw
  rw [firstIhs_eq rd.slots ctor.1.name r hr' hhit hfirst]
  generalize hihs : ihsOf rd.slots[r] = ihs at hpri
  refine UD.specR_heapLoadI' (C := ctxH C C.H) ccoIl (vv ccoIh) oi _ hpri.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) ccoTy _ (oe + 3) _ hnfr.2.2.2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oe 3) ?_
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN0 => ?_)
  have hil : ihs.length < 2 ^ 60 := pairsRep_len60 hok hHN0 hpri
  refine specR_callNIH (C := ctxH C C.H) ccoX fOpenFvars ofParams [vv ccoNf, vv ccoTy, vv ccoNk]
    (ofBody C) [BitVec.ofNat 64 ctor.2, Enc.idxW e.ty, BitVec.ofNat 64 (p.nP + p.k)] (by decide) rfl
    (by decide) hc.ofc ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], trivial⟩
    (PostOF (ctxH C C.H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op ctor.2 e.ty (p.nP + p.k) (by omega) (by omega) C.H hp0 s))
    (fun o w s2 H3 hp3 ⟨hn, hsm⟩ => ?_)
  have hp3' : C.H <+: H3 := hp3
  rcases o with _ | ⟨fvs, e'⟩
  · have e0 := hn rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, oa, rfl, hob, hoe, hfb⟩ := hsm fvs e' rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol : ob < H3.length := (List.getElem?_eq_some_iff.mp hob).1
  have hHN' : H3.length ≤ C.HN := hHN
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H3) ccoFv (vv ccoX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfl : H3[oa]? = some (BitVec.ofNat 64 fvs.length) := by simpa using hfb.1
  refine UD.specR_heapLoadI' (C := ctxH C H3) ccoL (vv ccoFv) oa _ hfl (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hfvl : fvs.length < 2 ^ 63 := by
    rcases Nat.eq_zero_or_pos fvs.length with h0 | hpos
    · omega
    · have h1 := hfb.2 (fvs.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      have hlay := hok.heapLay
      omega
  by_cases hfn : fvs.length = ctor.2
  swap
  · have hne2 : BitVec.ofNat 64 fvs.length ≠ BitVec.ofNat 64 ctor.2 := fun e => hfn (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfn]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hlwn := nd_lt_iff m.nPc (2 ^ 58) (by omega) (by omega)
  by_cases hnpc : m.nPc < 2 ^ 58
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, ccoParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, ccoParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega) (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_callNIH (C := ctxH C H3) ccoU fCfs cfsParams [vv ccoFv, .const 0, vv ccoL, vv ccoMs, vv ccoIh, vv ccoIl]
    (cfsBody C) [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, cellA C om, cellA C oi,
      BitVec.ofNat 64 ihs.length] (by decide) rfl (by decide) hc.cfs.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostKS (ctxH C H3) (fvs.length - 0)) (fun ks w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ks.map cfKindW) ∧
      ks.length = fvs.length - 0 ∧ KindsOK ks)
    (fun ks w s' st ⟨H', o, hp', hw, hb, hl, hk, hsr⟩ => ⟨H', hp', ⟨o, hw, hb, hl, hk⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfsParams _ rfl hlk)
      (by have h := cfs_spec (σ := σ) C hok hc.cfs p p.members om rfl hM (by rw [hms]; simp) ihs oi hpri hil fvs oa
            (by omega) H3 hp3' hfb fvs.length 0 H3 s2 (by omega) (by omega) (List.prefix_refl _)
          simp only [List.drop_zero] at h; exact h))
    (fun kinds w s4 H4 hp4 ⟨ok, hw, hkb, hkl, hko⟩ => ?_)
  subst hw
  have hp4' : H3 <+: H4 := hp4
  have hpC4 : C.H <+: H4 := hp3'.trans hp4'
  rw [← hfe]
  refine specR_callNIH (C := ctxH C H4) ccoQ fCfg cfgParams [vv ccoU, .const 0, vv ccoL, vv ccoFv, vv ccoL, vv ccoTb,
      vv ccoTk, vv ccoCn, vv ccoInd, vv ccoNpc, vv ccoMs, vv ccoUs, vv ccoOlp, vv ccoTy0, vv ccoPp, vv ccoPn, vv ccoDs,
      vv ccoDn, vv ccoNm] cfgBody
    [cellA C ok, BitVec.ofNat 64 0, BitVec.ofNat 64 kinds.length, cellA C oa, BitVec.ofNat 64 fvs.length, cellA C ot,
      BitVec.ofNat 64 tbl.length, Enc.idxW ctor.1.name, Enc.idxW m.ind, BitVec.ofNat 64 m.nPc, cellA C om,
      Enc.idxW m.lvls, cellA C olp, Enc.idxW ms0.cvT.type, cellA C pp, BitVec.ofNat 64 m.pfvs.length, cellA C pd,
      BitVec.ofNat 64 m.ds.length, Enc.idxW ms0.cvT.name] (by decide) rfl (by decide) hc.cfg.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, hkl],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv],
      trivial⟩
    (Decl.PostU (ctxH C H4)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfgParams _ rfl hlk)
      (by have h := cfg_spec (σ := σ) mode ra C hok hs hc.cfg p ms0 hms om hM m olp pp pd hlpl hdl hpl hnpc tbl ot htl
            ctor.1.name fvs oa (by omega) kinds ok hko (by omega) H4 hpC4 (eblk_mono hlp hpC4) (blkAt_mono hpf hpC4)
            (blkAt_mono hds hpC4) (pRep_mono hpC4 (fun _ _ => nfRep_mono hpC4) htb) (blkAt_mono hfb hp4') hkb
            kinds.length 0 H4 s4 (by omega) (by omega) (List.prefix_refl _)
          simp only [List.drop_zero] at h; exact h))
    (fun _ w s5 H5 hp5 _ => ?_)
  have hp5' : H4 <+: H5 := hp5
  have hpC5 : C.H <+: H5 := hpC4.trans hp5'
  simp only [pure_bind, targetCtorAt, hmm]
  refine UD.specR_heapLoadI' (C := ctxH C H5) ccoT0 _ (ocv + 2) _ (get_prefix hcv.2.2 hpC5) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv]; exact cellA_add_ofNat C ocv 2) ?_
  refine specR_callNIH (C := ctxH C H5) ccoD fInstPis ipwParams [vv ccoDs, .const 0, vv ccoDn, vv ccoT0] ipwBody
    [cellA C pd, BitVec.ofNat 64 0, BitVec.ofNat 64 m.ds.length, Enc.idxW ctor.1.type] (by decide) rfl (by decide) hc.ipw
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostSome (ctxH C H5)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
    (fun o w s' st ⟨t, h1, h2, hsr⟩ => ⟨H5, List.prefix_refl _, ⟨t, h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipwParams _ rfl hlk)
      (by have hip := ipw_spec (σ := σ) ra C hok hc.ipw hc.i1f hc.i1c m.ds pd H5 (blkAt_mono hds hpC5) m.ds.length 0 s5 ctor.1.type (by omega) (by omega); simp only [List.drop_zero] at hip; exact hip))
    (fun o w s6 H6 hp6 ⟨t, ho, hw⟩ => ?_)
  subst ho hw
  have hp6' : H5 <+: H6 := hp6
  have hpC6 : C.H <+: H6 := hpC5.trans hp6'
  simp only
  refine specR_alloc6I (ctxOK_H hok H6) ccoR (vv ccoCv) (vv ccoNf) (vv ccoD) (vv ccoTy) (vv ccoL) (vv ccoU)
    (cellA C ocv) (BitVec.ofNat 64 ctor.2) (Enc.idxW t) (Enc.idxW e.ty) (BitVec.ofNat 64 fvs.length) (cellA C ok) (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv])
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, ccoParams, ctxEnv])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H7 ws hp7 hws => ?_)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := img6_get H7 ws (cellA C ocv) (BitVec.ofNat 64 ctor.2) (Enc.idxW t) (Enc.idxW e.ty)
    (BitVec.ofNat 64 fvs.length) (cellA C ok) hws
  have hp7' := (hp7 : H6 <+: H7).trans (img6_prefix H7 ws (cellA C ocv) (BitVec.ofNat 64 ctor.2) (Enc.idxW t)
    (Enc.idxW e.ty) (BitVec.ofNat 64 fvs.length) (cellA C ok) hws)
  intro _
  have hkl' : kinds.length = fvs.length := by omega
  exact specR_returnI _ (cellA C H7.length) rfl (fun tt htt =>
    ⟨_, H7.length, hpC6.trans hp7', rfl,
      ⟨⟨ocv, by simpa using g0, cvRep_mono (hpC6.trans hp7') hcv⟩, g1, g2, g3, by simpa [hkl'] using g4,
        ⟨ok, by simpa using g5, blkAt_mono hkb (hp5'.trans (hp6'.trans hp7'))⟩, hko, by simp; omega⟩,
      sr_of_eq htt.sr rfl rfl rfl rfl⟩)

end

/-! ## `classCtorsOf` (the member's constructors) -/

def cclCs := ofString "ccl_cs"
def cclI := ofString "ccl_i"
def cclN := ofString "ccl_n"
def cclTb := ofString "ccl_tb"
def cclTk := ofString "ccl_tk"
def cclSl := ofString "ccl_sl"
def cclSk := ofString "ccl_sk"
def cclNk := ofString "ccl_nk"
def cclMs := ofString "ccl_ms"
def cclDs := ofString "ccl_ds"
def cclDn := ofString "ccl_dn"
def cclO := ofString "ccl_o"
def cclF := ofString "ccl_f"
def cclX := ofString "ccl_x"
def cclInd := ofString "ccl_ind"
def cclNpc := ofString "ccl_npc"
def cclUs := ofString "ccl_us"
def cclOlp := ofString "ccl_olp"
def cclTy0 := ofString "ccl_ty0"
def cclPp := ofString "ccl_pp"
def cclPn := ofString "ccl_pn"
def cclNm := ofString "ccl_nm"
def fCcl := ofString "classCtorsOf"

def cclParams : List MlS := [cclCs, cclI, cclN, cclTb, cclTk, cclSl, cclSk, cclNk, cclMs, cclDs, cclDn, cclInd, cclNpc, cclUs,
  cclOlp, cclTy0, cclPp, cclPn, cclNm]
def cclLocals : List MlS := gaaLocals ++ [cclO, cclF, cclX]

def cclBody (C : Ctx) : ProgHOL 64 := prologue cclLocals
  (.ite (.cmp .lower (vv cclI) (vv cclN))
    (.seq (.assign .local cclO (.load .one (.op .add [vv cclCs, .op .add [.panop .mul [vv cclI, .const 16], .const 8]])))
    (.seq (.assign .local cclF (.load .one (.op .add [vv cclCs, .op .add [.panop .mul [vv cclI, .const 16], .const 16]])))
    (.seq (.call (some (some (.local, cclX), none)) fCco
        [vv cclTb, vv cclTk, vv cclO, vv cclF, vv cclSl, vv cclSk, vv cclNk, vv cclMs, vv cclDs, vv cclDn, vv cclInd,
          vv cclNpc, vv cclUs, vv cclOlp, vv cclTy0, vv cclPp, vv cclPn, vv cclNm])
    (.seq (.call (some (some (.local, ExS.lY), none)) fCcl
        [vv cclCs, .op .add [vv cclI, .const 1], vv cclN, vv cclTb, vv cclTk, vv cclSl, vv cclSk, vv cclNk, vv cclMs,
          vv cclDs, vv cclDn, vv cclInd, vv cclNpc, vv cclUs, vv cclOlp, vv cclTy0, vv cclPp, vv cclPn, vv cclNm])
      (prependP C cclX)))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure CCLCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  cco : CCOCodes mode C
  self : C.code.lookup fCcl = some (cclParams.map (fun p => (p, ShapeHOL.one)), cclBody C, .one)

section
variable {σ : Type}

theorem ccl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cclLocals → (ctxEnv C ++ cclParams.zip vals).get x = none :=
  Knot.params_none C cclLocals cclParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`classCtorsOf`** at class `0` from constructor `i` on. -/
theorem ccl_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CCLCodes mode C) (p : BlockShape) (ms0 : MemberShape) (hms : p.members = [ms0])
    (rd : ClassRead) (m : TargetMajor) (hmm : m.member = some 0) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (cs : List (IConstantVal × Nat)) (oq : Nat) (hcr : CtorsRep C C.H oq cs) (hcsl : cs.length < 2 ^ 58)
    (hnf : ∀ c ∈ cs, c.2 < 2 ^ 56)
    (ot osl pd : Nat) (tbl : List NestCtorNf) (htl : tbl.length < 2 ^ 58)
    (htb : PRep C C.H ot (fun H o nf => NfRep C H o nf) tbl)
    (hnfs : ∀ c ∈ cs, m.nfs.filter (·.ctor == c.1.name) = tbl.filter (·.ctor == c.1.name))
    (hsl : rd.slots.length < 2 ^ 58) (hcb : ∀ sl ∈ rd.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63)
    (hsb : SlotBlk C C.H osl rd.slots) (hdl : m.ds.length < 2 ^ 58) (hds : BlkAt C.H pd (m.ds.map Enc.idxW))
    (hnk : p.nP + p.k < 2 ^ 56) (olp pp : Nat) (hlpl : ms0.cvT.levelParams.length < 2 ^ 59)
    (hpl : m.pfvs.length < 2 ^ 58) (hlp : EBlk C.H olp (ms0.cvT.levelParams.map Enc.idxW))
    (hpf : BlkAt C.H pp (m.pfvs.map Enc.idxW)) (hnpc0 : m.nPc < 2 ^ 62) :
    ∀ f i (H : List (BitVec 64)) (s : AState), cs.length - i = f → i ≤ cs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cclParams.zip [cellA C oq, BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length,
        cellA C ot, BitVec.ofNat 64 tbl.length, cellA C osl, BitVec.ofNat 64 rd.slots.length,
        BitVec.ofNat 64 (p.nP + p.k), cellA C om, cellA C pd, BitVec.ofNat 64 m.ds.length, Enc.idxW m.ind,
        BitVec.ofNat 64 m.nPc, Enc.idxW m.lvls, cellA C olp, Enc.idxW ms0.cvT.type, cellA C pp,
        BitVec.ofNat 64 m.pfvs.length, Enc.idxW ms0.cvT.name])) (cclBody C) s
        (classCtorsOf mode C.fe p [ms0.cvT.type] rd [m] 0 (cs.drop i)) (PostCCs (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = cs.length := by omega
    subst hin
    refine specR_prologue (postCCs_locals _) (ccl_none _ _) ?_
    have hlw := nd_lt_iff cs.length cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    simp only [classCtorsOf]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
        fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < cs.length := by omega
    refine specR_prologue (postCCs_locals _) (ccl_none _ _) ?_
    have hlw := nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, hoc, hcv, hnfe⟩ := hcr.2 i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) cclO _ (oq + 1 + 2 * i) _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; exact cellA_pair1 C oq i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cclF _ (oq + 2 + 2 * i) _ (get_prefix hnfe.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; exact cellA_pair2 C oq i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin]
    simp only [classCtorsOf]
    refine specR_callNIH (C := ctxH C H) cclX fCco ccoParams
      [vv cclTb, vv cclTk, vv cclO, vv cclF, vv cclSl, vv cclSk, vv cclNk, vv cclMs, vv cclDs, vv cclDn, vv cclInd,
        vv cclNpc, vv cclUs, vv cclOlp, vv cclTy0, vv cclPp, vv cclPn, vv cclNm] (ccoBody C)
      [cellA C ot, BitVec.ofNat 64 tbl.length, cellA C oc, BitVec.ofNat 64 cs[i].2, cellA C osl,
        BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 (p.nP + p.k), cellA C om, cellA C pd, BitVec.ofNat 64 m.ds.length,
        Enc.idxW m.ind, BitVec.ofNat 64 m.nPc, Enc.idxW m.lvls, cellA C olp, Enc.idxW ms0.cvT.type, cellA C pp,
        BitVec.ofNat 64 m.pfvs.length, Enc.idxW ms0.cvT.name]
      (by decide) rfl (by decide) hc.cco.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], trivial⟩
      (PostCC (ctxH C H)) (fun cc w _ H' => ∃ o, w = cellA C o ∧ CCRep C H' o cc)
      (fun cc w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccoParams _ rfl hlk)
        (cco_spec mode ra (ctxH C H) (ctxOK_H hok H) hs (by ctx_tr hc.cco) p ms0 hms rd m hmm om
          (ptrsRep_mono hp (fun _ _ => memberRep_mono hp) hM) cs[i] oc (cvRep_mono hp hcv)
          (hnf cs[i] (List.getElem_mem hin)) ot osl pd olp pp tbl htl (pRep_mono hp (fun _ _ => nfRep_mono hp) htb)
          (hnfs cs[i] (List.getElem_mem hin)) hsl hcb
          (slotBlk_mono hp hsb) hdl (blkAt_mono hds hp) hnk hlpl hpl (eblk_mono hlp hp) (blkAt_mono hpf hp) hnpc0 s))
      (fun cc w s1 H1 hp1 ⟨ox, hw, hrx⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fCcl cclParams
      [vv cclCs, .op .add [vv cclI, .const 1], vv cclN, vv cclTb, vv cclTk, vv cclSl, vv cclSk, vv cclNk, vv cclMs,
        vv cclDs, vv cclDn, vv cclInd, vv cclNpc, vv cclUs, vv cclOlp, vv cclTy0, vv cclPp, vv cclPn, vv cclNm] (cclBody C)
      [cellA C oq, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length, cellA C ot, BitVec.ofNat 64 tbl.length,
        cellA C osl, BitVec.ofNat 64 rd.slots.length, BitVec.ofNat 64 (p.nP + p.k), cellA C om, cellA C pd,
        BitVec.ofNat 64 m.ds.length, Enc.idxW m.ind, BitVec.ofNat 64 m.nPc, Enc.idxW m.lvls, cellA C olp,
        Enc.idxW ms0.cvT.type, cellA C pp, BitVec.ofNat 64 m.pfvs.length, Enc.idxW ms0.cvT.name] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cclParams, ctxEnv], trivial⟩
      (PostCCs (ctxH C H1)) (fun ccs w _ H' => ∃ o, w = cellA C o ∧ PRep C H' o (fun H o cc => CCRep C H o cc) ccs)
      (fun ccs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cclParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun ccs w s2 H2 hp2 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    obtain ⟨oss, hossl, hossb, hossr⟩ := hry
    refine ExPre.prepend_spec C hok (H := H2) cclX (cellA C ox) oy (oss.map (cellA C)) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hossb (by decide)
      (by simp +decide [Env.get_cons, Env.get, cclParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, hp1'.trans (hp2'.trans hp'), rfl,
      ⟨ox :: oss, by simp [hossl], hb, fun j hj hjo => by
        rcases j with _ | j
        · exact ccRep_mono (hp2'.trans hp') hrx
        · exact ccRep_mono hp' (hossr j (by simpa using hj) (by simpa using hjo))⟩, hsr⟩

end


end ConPanqueque.T.Ind
