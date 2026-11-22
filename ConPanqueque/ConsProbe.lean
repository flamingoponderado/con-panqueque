import ConPanqueque.ConsIntern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsLoop ConPanqueque.ConsIns ConPanqueque.ConsTbl
open ConPanqueque.ConsIntern
open ConRon.Arena

/-!
# Probing one tier without appending

The persistent half of the two-tier probe: `internTier` with the miss branch
replaced by `skip`. On a hit it returns the twin's handle; on a miss it falls
through with memory and every local as they were.
-/

namespace ConPanqueque.ConsProbe

def probeTier : ProgHOL 64 :=
  .dec lJ .one homeE (.dec lC .one (.op .add [ConsIntern.vv lM, .const 1])
   (.dec lG .one (.const 1) (.dec lRes .one (.const 0) (.dec lV .one (.const 0)
    (.seq probeLoop
     (.ite (.cmp .notEqual (ConsIntern.vv lRes) (.const 0)) (.return (hwE (.op .sub [ConsIntern.vv lRes, .const 1]))) .skip))))))

/-- Locals agree outside `A`. -/
def Fr (A : List MlS) (u t : HolFiniteMapExact MlS (ValueHOL 64)) : Prop := ∀ y, y ∉ A → u.lookup y = t.lookup y

theorem lookup_resVar_same (m : HolFiniteMapExact MlS (ValueHOL 64)) (x : MlS) (o : Option (ValueHOL 64)) :
    (HolFiniteMapExact.resVarEq m (x, o)).lookup x = o := by
  cases o <;> simp [FDOMSUB_HOL, FUPDATE_HOL]

theorem fr_dec {σ : Type} {s : PanSemStateFiniteExact 64 σ} {x : MlS} {v : ValueHOL 64} {A : List MlS}
    {m : HolFiniteMapExact MlS (ValueHOL 64)} (h : Fr (x :: A) m (setVarHOLFinite x v s).locals) :
    Fr A (HolFiniteMapExact.resVarEq m (x, s.locals.lookup x)) s.locals := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; exact lookup_resVar_same _ _ _
  · rw [lookup_resVar_other _ _ _ _ hyx, h y (by simp [hyx, hy])]; exact lookup_setVar_other _ _ hyx

/-- What `probeTier` guarantees, with the locals agreeing outside `A`. -/
def PRes {σ : Type} (A : List MlS) (t : PanSemStateFiniteExact 64 σ) (tb : Tbl AppNode EIdx UInt64) (n : Nat)
    (x : AppNode) (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  r.2.memory = t.memory ∧ r.2.memaddrs = t.memaddrs ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
  r.2.topAddr = t.topAddr ∧
  ((∃ h, tb.find? x = some h ∧ r.1 = some (.returned (.val (.word h.word.toUInt64.toBitVec)))) ∨
   (tb.find? x = none ∧ r.1 = none ∧ t.clock ≤ r.2.clock + (n + 1) ∧ Fr A r.2.locals t.locals))

theorem pres_dec {σ : Type} {s : PanSemStateFiniteExact 64 σ} {x : MlS} {v : BitVec 64} {A : List MlS}
    {tb : Tbl AppNode EIdx UInt64} {n : Nat} {a : AppNode}
    {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : PRes (x :: A) (setVarHOLFinite x (.val (.word v)) s) tb n a r) :
    PRes A s tb n a (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (x, s.locals.lookup x) }) := by
  obtain ⟨m, d, c, g, ta, h | ⟨hf, hr, hc, hfr⟩⟩ := h
  · exact ⟨m, d, c, g, ta, Or.inl h⟩
  · exact ⟨m, d, c, g, ta, Or.inr ⟨hf, hr, hc, fr_dec hfr⟩⟩

theorem skip_eval {σ : Type} (s : PanSemStateFiniteExact 64 σ) : evaluateHOLFiniteState s .skip = (none, s) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]

theorem probeTier_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (tb : Tbl AppNode EIdx UInt64)
    (rows : List AppNode) (ders : List (BitVec 64)) (slots : List Nat) (n b cap : Nat) (C S R D : BitVec 64)
    (x : AppNode) (dv : BitVec 64) (tier : UInt32)
    (hn : n = 2 ^ b) (hb : b ≤ 56) (hcap : cap < 2 ^ 30)
    (hT : TMem t encApp rows ders slots n cap C S R D) (hinv : Inv (α := AppNode) (homeApp b) rows slots n)
    (hrel : TblRel tb rows (fun i => Idx.mkWide tier (UInt32.ofNat i))) (htier : tier ≤ 1)
    (hL : Locals t x n cap C S R D dv tier.toUInt64.toBitVec) (hck : n + 2 ≤ t.clock) :
    PRes [] t tb n x (evaluateHOLFiniteState t probeTier) := by
  have hpos : 0 < n := hinv.pos
  let hx := homeApp b x
  have hxn : hx < n := hinv.home_lt x
  have ehome : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) homeE =
      some (.val (.word (BitVec.ofNat 64 hx))) := by
    simp [homeE, ConsIntern.vv, evalHOLExact, evalListHOLExact, hL.kf, hL.ka, hL.m, wordOpHOL, wordOp, panOpHOL, valueIsWord,
      valueWord]
    rw [show (n - 1) = 2 ^ b - 1 by rw [hn]]
    show _ &&& (_ &&& (18446744073709551615#64)) = _
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes, home_mask _ b hb]
    rfl
  unfold probeTier
  rw [dec_word_eq t lJ homeE _ _ ehome]; apply pres_dec
  let t1 := setVarHOLFinite lJ (.val (.word (BitVec.ofNat 64 hx))) t
  have hM1 : t1.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (n - 1)))) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hL.m
  rw [dec_word_eq t1 lC (.op .add [ConsIntern.vv lM, .const 1]) (BitVec.ofNat 64 n) _
    (by simp [ConsIntern.vv, evalHOLExact, evalListHOLExact, hM1, wordOpHOL, wordOp, valueIsWord, valueWord]
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)]; apply pres_dec
  let t2 := setVarHOLFinite lC (.val (.word (BitVec.ofNat 64 n))) t1
  rw [dec_word_eq t2 lG (.const 1) 1 _ (by simp [evalHOLExact])]; apply pres_dec
  let t3 := setVarHOLFinite lG (.val (.word 1)) t2
  rw [dec_word_eq t3 lRes (.const 0) 0 _ (by simp [evalHOLExact])]; apply pres_dec
  let t4 := setVarHOLFinite lRes (.val (.word 0)) t3
  rw [dec_word_eq t4 lV (.const 0) 0 _ (by simp [evalHOLExact])]; apply pres_dec
  let t5 := setVarHOLFinite lV (.val (.word 0)) t4
  have l5 : ∀ y, y ≠ lV → y ≠ lRes → y ≠ lG → y ≠ lC → y ≠ lJ → t5.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5; simp only [t5, t4, t3, t2, t1]
    rw [lookup_setVar_other _ _ a1, lookup_setVar_other _ _ a2, lookup_setVar_other _ _ a3, lookup_setVar_other _ _ a4,
      lookup_setVar_other _ _ a5]
  let ans := probeR rows slots n x n hx
  have hI : LInv t5 encApp rows slots n S R x ans t5 :=
    ⟨rfl, rfl, rfl, rfl, rfl, by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.s,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.r,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.m,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.kf,
      by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.ka,
      fun _ _ _ _ _ _ => rfl, n, hx, hxn,
      by simp only [t5, t4, t3]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide),
        lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
      by simp only [t5, t4, t3, t2]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide),
        lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
      ⟨0, lookup_setVar_same _ _ _⟩,
      Or.inl ⟨by simp only [t5, t4]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
              by simp only [t5]; rw [lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
              rfl, Nat.le_refl _, by show n + 1 ≤ t.clock; omega, by omega⟩⟩
  have hmem5 : Mem t5 encApp rows slots n S R := ⟨hT.mem.slot, hT.mem.row⟩
  obtain ⟨t6, ev6, hI6, hg6⟩ := probeLoop_spec t5 encApp rows slots n b S R x ans hn (by omega) hmem5
    hinv.named encApp_inj hI
  rw [seq_normal _ ev6]
  obtain ⟨m6, d6, c6, g6, ta6, hS6, hR6, hM6, hKf6, hKa6, hfr6, f, j, hj, hC6, hJ6, hV6, br⟩ := hI6
  obtain ⟨_, hres6, hemp, hfull, hclk6⟩ := br.resolve_left (fun ⟨hg, _⟩ => by rw [hg6] at hg; cases hg)
  have hprobe := probeR_toOpt rows slots n x n hx
  have hfind := find_probe (homeApp b) tb rows slots n _ hrel hinv x
  cases hto : ans.toOpt with
  | some i =>
    rw [hto] at hres6
    simp only [Option.map_some, Option.getD_some] at hres6
    have hi : rows[i]? = some x := (probe_correct (homeApp b) rows slots n hinv x).1 i (by rw [← hprobe]; exact hto)
    have hil : i < rows.length := (List.getElem?_eq_some_iff.mp hi).1
    have hcapl : rows.length ≤ cap := hT.le
    have hne : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.cmp .notEqual (ConsIntern.vv lRes) (.const 0)) = some (.val (.word 1)) := by
      simp [ConsIntern.vv, evalHOLExact, hres6, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    rw [ite_word t6 _ _ _ _ hne]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    have htw : t6.locals.lookup lTier = some (.val (.word tier.toUInt64.toBitVec)) := by
      rw [hfr6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL.tier
    have hw : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (hwE (.op .sub [ConsIntern.vv lRes, .const 1])) =
        some (.val (.word (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec)) := by
      rw [mkWide_word tier i htier (by omega)]
      simp [hwE, ConsIntern.vv, evalHOLExact, evalListHOLExact, htw, hres6, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      have : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
      rw [this, BitVec.add_assoc]
    have eret : evaluateHOLFiniteState t6 (.return (hwE (.op .sub [ConsIntern.vv lRes, .const 1]))) =
        (some (.returned (.val (.word (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec))),
          emptyLocalsHOLFinite t6) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only [hw]; simp [shapeOfHOLExact]
    rw [eret]
    have hfi : tb.find? x = some (Idx.mkWide tier (UInt32.ofNat i)) := by
      rw [hfind, ← hprobe, hto]; rfl
    refine ⟨m6, d6, ?_, ?_, ?_,
      Or.inl ⟨_, hfi, rfl⟩⟩
    all_goals (simp [emptyLocalsHOLFinite, c6, g6, ta6]; try rfl)
  | none =>
    rw [hto] at hres6
    simp only [Option.map_none, Option.getD_none] at hres6
    have hne : @evalHOLExact 64 σ _ t6.toExact (fun a => Classical.propDecidable (t6.memaddrs a))
        (.cmp .notEqual (ConsIntern.vv lRes) (.const 0)) = some (.val (.word 0)) := by
      simp [ConsIntern.vv, evalHOLExact, hres6, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [ite_word t6 _ _ _ _ hne]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    rw [skip_eval]
    have hfi : tb.find? x = none := by rw [hfind, ← hprobe, hto]; rfl
    refine ⟨m6, d6, by rw [c6], by rw [g6], by rw [ta6], Or.inr ⟨hfi, rfl, hclk6, ?_⟩⟩
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨a1, a2, a3, a4, a5⟩ := hy
    exact hfr6 y a5 a4 a3 a2 a1

end ConPanqueque.ConsProbe
