import ConPanqueque.T.Ex.Prepend
import ConPanqueque.T.Ex.Abstract1
import ConPanqueque.T.CallN
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `stripLams` / `stripPis`

`strip(k, h)`: strip `k` leading binders of one kind. `none` is the word `0`; `some (tys, b)` is a heap
block `[|tys| + 1, tys…, b]`. One program and one proof, for either binder tag.
-/

namespace ConPanqueque.T.ExSP
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG ConPanqueque.T.ExPre
open ConPanqueque.T.ExA

def stripBody (C : Ctx) (fn : MlS) (T : Nat) : ProgHOL 64 :=
  prologue gaaLocals
  (.ite (.cmp .equal (vv pFu) (.const 0))
    (allocP C lW (.const 16) (.seq (.store (vv lW) (.const 1))
      (.seq (.store (.op .add [vv lW, .const 8]) (vv pH)) (.return (vv lW)))))
    (.ite (tagIsE pH T)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, lY), none)) fn [.op .sub [vv pFu, .const 1], vv lA2])
      (.ite (.cmp .equal (vv lY) (.const 0)) (.return (.const 0)) (prependP C lA1))))))))
      (.return (.const 0))))

section
variable {σ : Type}

/-- The strip's post: `0` for `none`, else the block of the binder types and the body. -/
def PostSP (C : Ctx) (o : Option (List EIdx × EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ tys b, o = some (tys, b) → ∃ ob, w = cellA C ob ∧ BlkAt H' ob (tys.map Enc.idxW ++ [Enc.idxW b])

theorem postSP_locals (C : Ctx) : ∀ (a : Option (List EIdx × EIdx)) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostSP C a w s' st → PostSP C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem params_noneSP (va vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ [(pFu, va), (pH, vb)]).get x = none := by
  intro x hx
  simp only [gaaLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem cellA_ne0 (C : Ctx) (hok : CtxOK C) (o : Nat) (ho : o < C.HN) : cellA C o ≠ 0 := by
  have hlay := hok.heapLay
  have hhi := hok.heapHigh
  intro e; have := congrArg BitVec.toNat e; simp [cellA, BitVec.toNat_add] at this; omega

theorem strip_spec (C : Ctx) (hok : CtxOK C) (fn : MlS) (T : Nat) (hT5 : T = 5 ∨ T = 6)
    (strip : Nat → EIdx → AM (Option (List EIdx × EIdx)))
    (heq0 : ∀ h, strip 0 h = pure (some ([], h)))
    (heqS : ∀ k h, strip (k + 1) h = if h.tag == UInt32.ofNat T then (do
        match ← viewBind h with
        | none => failDanglingE
        | some (ty, b) => do
          match ← strip k b with
          | some p => pure (some (ty :: p.1, p.2))
          | none => pure none) else pure none)
    (hcode : C.code.lookup fn = some ([(pFu, .one), (pH, .one)], stripBody C fn T, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) (stripBody C fn T) s
        (strip k h) (PostSP (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro _ H s h
    refine specR_prologue (postSP_locals _) (params_noneSP _ _ _) ?_
    rw [heq0]
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    refine specR_allocI (C := ctxH C H) lW (.const 16) 2 (by decide) (by decide) (fun _ => rfl)
      (fun H2 ws hp2 hws hroom => ?_)
    have hp2' : H <+: H2 := hp2
    have hroom' : H2.length + 2 ≤ C.HN := hroom
    have hq0 : H2.length < (ctxH C (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok (H2 ++ ws)) (vv lW) (.const 1) H2.length hq0 1
      (by simp +decide [cellA, ctxH]) rfl ?_
    generalize hB1 : (ctxH C (H2 ++ ws)).H.set H2.length 1 = B1
    have hB1len : B1.length = H2.length + 2 := by rw [← hB1]; show ((H2 ++ ws).set _ _).length = _; simp [hws]
    have hq1 : H2.length + 1 < (ctxH C B1).H.length := by show _ < B1.length; omega
    refine specR_heapStoreI (ctxOK_H hok B1) (.op .add [vv lW, .const 8]) (vv pH) (H2.length + 1) hq1 (Enc.idxW h)
      (by simp +decide [sev]; exact cellA_add8 C _) (by simp +decide [ctxEnv]) ?_
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    refine ⟨B1.set (H2.length + 1) (Enc.idxW h), ?_, sr_of_eq ht.sr rfl rfl rfl rfl, fun e => by simp at e,
      fun tys b e => ?_⟩
    · refine hp2'.trans (prefix_of_get? (by simp; omega) (fun k hk => ?_))
      rw [List.getElem?_set_ne (by omega), ← hB1]
      show ((H2 ++ ws).set _ _)[k]? = _
      rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk]
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨H2.length, rfl, ?_, fun i hi => ?_⟩
      · rw [List.getElem?_set_ne (by omega), ← hB1]
        show ((H2 ++ ws).set _ _)[H2.length]? = _
        rw [List.getElem?_set_self (by simp; omega)]; simp
      · simp at hi; subst hi
        rw [List.getElem?_set_self (by omega)]; simp
  | succ k ih =>
    intro hk H s h
    have ih' := ih (by omega)
    refine specR_prologue (postSP_locals _) (params_noneSP _ _ _) ?_
    rw [heqS]
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (k + 1) (by omega) hk
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ctxEnv] at hw; exact absurd hw this
    obtain ⟨w, hw, hiff⟩ := sev_tagIs (ctxEnv (ctxH C H) ++ [(pFu, BitVec.ofNat 64 (k + 1)), (pH, Enc.idxW h)])
      pH h (by simp +decide [ctxEnv]) T (by omega) (by omega)
    by_cases ht : h.tag = UInt32.ofNat T
    case neg =>
      have hb : (h.tag == UInt32.ofNat T) = false := by simp [ht]
      rw [hb]; simp only [Bool.false_eq_true, ite_false]
      refine specR_ifI _ w hw (fun e => absurd (hiff.mp e) ht) (fun _ => ?_)
      exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨H, List.prefix_refl _, sr_of_eq ht'.sr rfl rfl rfl rfl,
        fun _ => rfl, fun _ _ e => by simp at e⟩)
    have hb : (h.tag == UInt32.ofNat T) = true := by simp [ht]
    rw [hb]; simp only [ite_true]
    refine specR_ifI _ w hw (fun _ => ?_) (fun e => absurd (hiff.mpr ht) (by simp [e]))
    have hb56 : h.tag = 5 ∨ h.tag = 6 := by rcases hT5 with rfl | rfl <;> simp [ht]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
    refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h hb56 s vw hvw)
      (by simp) (by simp +decide <;> rfl) (by simp +decide [ctxEnv] <;> rfl) (by decide) (fun vw P htg hsh => ?_)
    obtain ⟨ty, b, hpb, hwv⟩ : ∃ ty b, projBind vw = some (ty, b) ∧ encEView vw = [Enc.idxW ty, Enc.idxW b] := by
      have htT : h.tag.toNat = T := by rw [ht]; simp; omega
      rw [htT] at htg
      cases vw with
      | lam ty b => exact ⟨ty, b, rfl, rfl⟩
      | forallE ty b => exact ⟨ty, b, rfl, rfl⟩
      | _ => simp [ENodeView.tagN] at htg <;> omega
    rw [hpb]; simp only
    refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
      (by rw [hwv]; exact wordsAt_mem0 _ _ _ _) ?_
    refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by rw [hwv]; exact wordsAt_mem1 _ _ _ _ _) ?_
    refine specR_callNIH lY fn [pFu, pH] [.op .sub [vv pFu, .const 1], vv lA2] (stripBody C fn T)
      [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, ctxEnv]; exact ofNat_succ_sub_one k, by simp +decide, trivial⟩
      (PostSP (ctxH C H)) (fun o w s' H' => (o = none → w = 0) ∧
        ∀ tys b', o = some (tys, b') → ∃ ob, w = cellA C ob ∧ BlkAt H' ob (tys.map Enc.idxW ++ [Enc.idxW b']))
      (fun o w s' st ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, ⟨h1, h2⟩, hs⟩)
      (fun u hu _ hlk => fun w hw => by subst hw; exact ih' H s b _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
      (fun o wy s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
    rcases o with _ | ⟨tys, b'⟩
    · have e0 := hn rfl
      subst e0
      refine specR_ifI _ 1 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
      exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨H1, hp1, sr_of_eq ht'.sr rfl rfl rfl rfl,
        fun _ => rfl, fun _ _ e => by simp at e⟩)
    · obtain ⟨ob, rfl, hblk⟩ := hsm tys b' rfl
      refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
      have hol := blkAt_lt hblk
      have hHN' : H1.length ≤ C.HN := hHN
      have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun hw => absurd rfl hw) (fun _ => ?_)
      exact prepend_spec C hok lA1 (Enc.idxW ty) ob _ (by decide) (by simp +decide) (by simp +decide) hblk
        (by decide) (by simp +decide [ctxEnv]) (by decide)
        (fun H' o t hpH hbk hsr => ⟨H', hp1.trans hpH, hsr, fun e => by simp at e, fun tys2 b2 e => by
          simp only [Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact ⟨o, rfl, by simpa using hbk⟩⟩)

end

def fStripLams := ofString "stripLams"
def fStripPis := ofString "stripPis"

section
variable {σ : Type}

theorem stripLams_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fStripLams = some ([(pFu, .one), (pH, .one)], stripBody C fStripLams 5, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) (stripBody C fStripLams 5) s
        (stripLams k h) (PostSP (ctxH C H)) :=
  strip_spec C hok fStripLams 5 (Or.inl rfl) stripLams (fun h => by rw [stripLams])
    (fun k h => by rw [stripLams]; rfl) hcode

theorem stripPis_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) (stripBody C fStripPis 6) s
        (stripPis k h) (PostSP (ctxH C H)) :=
  strip_spec C hok fStripPis 6 (Or.inr rfl) stripPis (fun h => by rw [stripPis])
    (fun k h => by rw [stripPis]; rfl) hcode

end

end ConPanqueque.T.ExSP
