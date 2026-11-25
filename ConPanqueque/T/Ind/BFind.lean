import ConPanqueque.T.Ind.RecFire

/-!
# The block-aware finder

`blockReadsAt` reads the recursors' rules against the environment with the block's constants pushed. The port does
not push: the block's records sit in the environment heap, listed in a value-heap table `[k, n₀, r₀, n₁, r₁, …]`
(name, record pointer), and lookups on that path scan the table from its end (the latest push wins) before the index.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI

/-- The block table at `ob`: entries `(name, record offset, constant)`, records in the environment heap. -/
def BTabAt (C : Ctx) (H : List (BitVec 64)) (ob : Nat) (es : List (NIdx × Nat × IConstantInfo)) : Prop :=
  H[ob]? = some (BitVec.ofNat 64 es.length) ∧ ∀ j (hj : j < es.length),
    H[ob + 1 + 2 * j]? = some (Enc.idxW es[j].1) ∧ H[ob + 2 + 2 * j]? = some (ecell C es[j].2.1) ∧
    CIE C.EB C.EH es[j].2.1 es[j].2.2

/-- The lookup the table and the index answer together: the table's last entry at `n`, else the index. -/
def bfLook (es : List (NIdx × Nat × IConstantInfo)) (fe : IFEnv) (n : NIdx) : Option IConstantInfo :=
  match es.reverse.find? (fun e => e.1 == n) with
  | some e => some e.2.2
  | none => fe.find? n

def bfT := ofString "bf_t"
def bfN := ofString "bf_n"
def bfI := ofString "bf_i"
def bfX := ofString "bf_x"
def bfR := ofString "bf_r"
def fBFindGo := ofString "bfindGo"

def bfParams : List MlS := [bfT, bfN, bfI]
def bfLocals : List MlS := [bfX, bfR]

/-- Entries `i - 1, …, 0` of the table, then the index. -/
def bfBody (C : Ctx) : ProgHOL 64 := prologue bfLocals
  (.ite (.cmp .equal (vv bfI) (.const 0))
    (envFindP C bfR (vv bfN) (.return (vv bfR)))
    (.seq (.assign .local bfX (.load .one (.op .add [vv bfT, .shift .lsl (.op .sub [.shift .lsl (vv bfI) (.const 1),
      .const 1]) (.const 3)])))
    (.ite (.cmp .equal (vv bfX) (vv bfN))
      (.seq (.assign .local bfR (.load .one (.op .add [vv bfT, .shift .lsl (.shift .lsl (vv bfI) (.const 1)) (.const 3)])))
        (.return (.op .add [vv bfR, .const 1])))
      (.seq (.call (some (some (.local, bfR), none)) fBFindGo [vv bfT, vv bfN, .op .sub [vv bfI, .const 1]])
        (.return (vv bfR))))))

section
variable {σ : Type}

/-- The finder's answer: `0` for none, else the record's cell plus one. -/
def PostBF (C : Ctx) (r : Option IConstantInfo) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  SR C s' st ∧ (r = none → w = 0) ∧ ∀ ci, r = some ci → ∃ o, w = ecell C o + 1 ∧ CIE C.EB C.EH o ci

theorem postBF_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBF C a w s' st → PostBF C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨hs, h1, h2⟩ => ⟨sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem bf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bfLocals → (ctxEnv C ++ bfParams.zip vals).get x = none :=
  Knot.params_none C bfLocals bfParams vals (by decide) (by decide)

theorem bfLook_take_succ (es : List (NIdx × Nat × IConstantInfo)) (fe : IFEnv) (n : NIdx) (i : Nat)
    (hi : i < es.length) :
    bfLook (es.take (i + 1)) fe n = if es[i].1 = n then some es[i].2.2 else bfLook (es.take i) fe n := by
  unfold bfLook
  rw [List.take_succ_eq_append_getElem hi, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, List.find?_cons]
  by_cases e : es[i].1 = n
  · simp [e]
  · have : (es[i].1 == n) = false := by simpa using e
    simp [this, e]

/-- **The finder** from entry `i - 1` down. -/
theorem bf_spec (C : Ctx) (hok : CtxOK C)
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcode : C.code.lookup fBFindGo = some (bfParams.map (fun p => (p, ShapeHOL.one)), bfBody C, .one))
    (es : List (NIdx × Nat × IConstantInfo)) (ob : Nat) (n : NIdx) (H : List (BitVec 64))
    (hT : BTabAt C H ob es) :
    ∀ i (s : AState), i ≤ es.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (bfParams.zip [cellA C ob, Enc.idxW n, BitVec.ofNat 64 i])) (bfBody C) s
        (pure (bfLook (es.take i) C.fe n)) (PostBF (ctxH C H)) := by
  intro i
  induction i with
  | zero =>
    intro s _
    refine specR_prologue (postBF_locals _) (bf_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, bfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [List.take_zero, bfLook, List.reverse_nil, List.find?_nil]
    refine specR_envFindI (C := ctxH C H) (ctxOK_H hok H) hcG hcP bfR (vv bfN) n (by decide)
      (by simp +decide [sev, Env.get, bfParams, ctxEnv]) (by simp +decide [Env.get, bfParams, ctxEnv] <;> rfl) ?_
    have hfr := find_rel (ctxOK_H hok H) n
    have efe : (ctxH C H).fe = C.fe := rfl
    rw [efe] at hfr
    refine specR_returnI _ (optWG id (ctxH C H).envM[n]?) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨sr_of_eq ht.sr rfl rfl rfl rfl, ?_, ?_⟩)
    · intro e; rw [e] at hfr; simp only [hfr, optWG]
    · intro ci e; rw [e] at hfr
      obtain ⟨o, he, hcie⟩ := hfr
      exact ⟨o, by simp [he, optWG], hcie⟩
  | succ i ih =>
    intro s hi
    refine specR_prologue (postBF_locals _) (bf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    obtain ⟨hn0, hcie0, hrec⟩ := hT.2 i (by omega)
    have hlast : ob + 2 + 2 * i < H.length := (List.getElem?_eq_some_iff.mp hcie0).1
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, bfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        intro e; have := congrArg BitVec.toNat e; simp at this; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [bfLook_take_succ es C.fe n i (by omega)]
    have hnm : (ctxH C H).H[ob + 1 + 2 * i]? = some (Enc.idxW es[i].1) := hn0
    refine UD.specR_heapLoadI' (C := ctxH C H) bfX _ (ob + 1 + 2 * i) _ hnm (by decide)
      (by
        simp +decide [sev, Env.get, bfParams, ctxEnv]
        show _ = cellA C (ob + 1 + 2 * i)
        apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        omega) ?_
    by_cases hname : es[i].1 = n
    · rw [if_pos hname]
      refine specR_ifI _ 1 (by
          simp +decide [sev, Env.get_cons, Env.get, bfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hname])
        (fun _ => ?_) (fun h => absurd h (by decide))
      have hrc : (ctxH C H).H[ob + 2 + 2 * i]? = some (ecell C es[i].2.1) := hcie0
      refine UD.specR_heapLoadI' (C := ctxH C H) bfR _ (ob + 2 + 2 * i) _ hrc (by decide)
        (by
          simp +decide [sev, Env.get_cons, Env.get, bfParams, ctxEnv]
          show _ = cellA C (ob + 2 + 2 * i)
          apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          omega) ?_
      refine specR_returnI _ (ecell C es[i].2.1 + 1) (by simp [sev, Env.get_cons])
        (fun t ht => ⟨sr_of_eq ht.sr rfl rfl rfl rfl, fun e => by simp at e, fun ci e => ?_⟩)
      simp only [Option.some.injEq] at e
      subst e
      exact ⟨es[i].2.1, rfl, hrec⟩
    · rw [if_neg hname]
      have hne : Enc.idxW es[i].1 ≠ Enc.idxW n := fun h => hname (Enc.idxW_inj h)
      refine specR_ifI _ 0 (by
          simp +decide [sev, Env.get_cons, Env.get, bfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_congr (m' := (pure (bfLook (es.take i) C.fe n) : AM _) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIM bfR fBFindGo bfParams [vv bfT, vv bfN, .op .sub [vv bfI, .const 1]] (bfBody C)
        [cellA C ob, Enc.idxW n, BitVec.ofNat 64 i] (by decide) rfl (by decide) hcode
        ⟨by simp +decide [sev, Env.get_cons, Env.get, bfParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, bfParams, ctxEnv],
          by
            show sev _ _ = _
            rw [sev_sub2 _ _ _ (BitVec.ofNat 64 (i + 1)) _ (by simp +decide [sev, Env.get_cons, Env.get, bfParams, ctxEnv])
              rfl]
            exact congrArg some (ofNat_succ_sub_one i), trivial⟩
        (PostBF (ctxH C H)) (fun a w s' st h => h.1)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bfParams _ rfl hlk) (ih s (by omega)))
        (fun r w s' st ⟨hsr, h1, h2⟩ => ?_)
      exact specR_returnI _ w (by simp [sev, Env.get_cons])
        (fun t ht => ⟨sr_of_eq ht.sr rfl rfl rfl rfl, h1, h2⟩)

end

end ConPanqueque.T.Ind
