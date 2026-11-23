import ConPanqueque.T.Ex.Inst1Fast
import ConPanqueque.T.Ex.BinderPair
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `instSpine`: instantiate a telescope-context expression at an argument spine

`instSpine(fu, as, i, t, e)`: the arguments are a heap block; from position `i`, instantiate `e` at the
argument with `instantiate1` (cursor `t`, then `t - 1`, saturating), and recurse.
-/

namespace ConPanqueque.T.ExIS
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG
open ConPanqueque.T.ExBP

def fInstSpine := ofString "instSpine"
def pSa := ofString "sa"
def pSi := ofString "si"
def isParams : List MlS := [pFu, pSa, pSi, pD, pH]

def isBody : ProgHOL 64 :=
  prologue gaaLocals
  (.seq (.assign .local lCn (.load .one (vv pSa)))
  (.ite (.cmp .lower (vv pSi) (vv lCn))
    (.seq (.assign .local lA1 (.load .one (.op .add [vv pSa, .op .add [.shift .lsl (vv pSi) (.const 3), .const 8]])))
    (.seq (.call (some (some (.local, lW), none)) fInst1F [vv pFu, vv pH, vv lA1, vv pD])
    (.seq (.assign .local lA2 (.op .sub [vv pD, .cmp .notEqual (vv pD) (.const 0)]))
    (.seq (.call (some (some (.local, lY), none)) fInstSpine [vv pFu, vv pSa, .op .add [vv pSi, .const 1], vv lA2, vv lW])
      (.return (vv lY))))))
    (.return (vv pH))))

section
variable {σ : Type}

set_option maxHeartbeats 4000000 in
theorem body_H (C : Ctx) (H : List (BitVec 64)) : ExI.body (ctxH C H) = ExI.body C := by
  unfold ExI.body; rfl

theorem codes_H (C : Ctx) (H : List (BitVec 64)) (hc : Codes C (ExI.body C)) : Codes (ctxH C H) (ExI.body (ctxH C H)) := by
  rw [body_H]
  exact ⟨hc.inst1, hc.memoGet, hc.memoProbe, hc.memoSet, hc.memoIns, hc.internApp, hc.internLam, hc.internForallE,
    hc.internLet, hc.internBVar, hc.internProj⟩

theorem callPE {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM EIdx} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s m (PostE C))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIM x f ps es B vs hnd hl hx hC hes (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hlk => fun w hw => by subst hw; exact hspec _ (pre_of_lookups hu ps vs hl hlk))
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

theorem params_noneIS (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ isParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ isParams := by
    simp only [gaaLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [gaaLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have hz : ∀ (ps : List MlS) (vs : List (BitVec 64)), x ∉ ps → Env.get (ps.zip vs) x = none := by
    intro ps vs hp
    induction ps generalizing vs with
    | nil => rfl
    | cons p ps ih =>
      cases vs with
      | nil => rfl
      | cons v vs =>
        simp only [List.mem_cons, not_or] at hp
        simp only [List.zip_cons_cons, Env.get, hp.1, ite_false]; exact ih vs hp.2
  have happ : ∀ (A B : Env), A.get x = none → B.get x = none → (A ++ B).get x = none := by
    intro A B hA hB
    induction A with
    | nil => exact hB
    | cons p A ih =>
      obtain ⟨y, v⟩ := p
      simp only [List.cons_append, Env.get] at hA ⊢
      split at hA
      · simp at hA
      · rename_i e; simp only [e, ite_false]; exact ih hA
  exact happ _ _ hc (hz _ _ hnot)

theorem cellA_idxS (C : Ctx) (o i : Nat) (h : C.HB.toNat + 8 * (o + 1 + i) < 2 ^ 64) :
    cellA C o + (BitVec.ofNat 64 i <<< 3 + 8#64) = cellA C (o + 1 + i) := by
  apply BitVec.eq_of_toNat_eq
  simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem satPred (t : Nat) (ht : t < 2 ^ 63) :
    BitVec.ofNat 64 t - (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 t) 0 then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (t - 1) := by
  by_cases h0 : t = 0
  · subst h0; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have hne : BitVec.ofNat 64 t ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem is_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : Codes C (body C))
    (hcF : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcS : C.code.lookup fInstSpine = some (isParams.map (fun p => (p, ShapeHOL.one)), isBody, .one))
    (fuel : Nat) (hf : fuel < 2 ^ 64) (ko : Nat) (as : List EIdx) :
    ∀ n (H : List (BitVec 64)) (s : AState) (i t : Nat) (e : EIdx), as.length - i = n → i ≤ as.length →
      t < 2 ^ 63 → BlkAt H ko (as.map Enc.idxW) →
      SpecR (Pre (σ := σ) (ctxH C H) s (isParams.zip [BitVec.ofNat 64 fuel, cellA C ko, BitVec.ofNat 64 i,
        BitVec.ofNat 64 t, Enc.idxW e])) isBody s (instSpine fuel (as.drop i) t e) (PostE (ctxH C H)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro H s i t e hn hi ht hb
    refine specR_prologue (postE_locals _) (params_noneIS _ _) ?_
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
    have hlay := hok.heapLay
    have hbl := blkAt_len hb
    simp only [List.length_map] at hbl
    have hHN' : H.length ≤ C.HN := hHN
    obtain ⟨h0l, h0v⟩ := blkAt_get0 hb
    refine specR_heapLoadI (C := ctxH C H) lCn (vv pSa) ko h0l (by decide)
      (by simp +decide [ctxEnv, isParams] <;> rfl) ?_
    simp only [show (ctxH C H).H = H from rfl, h0v, List.length_map]
    by_cases c : i < as.length
    · refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, isParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
        (by omega : as.length < 2 ^ 64), c]) (fun _ => ?_) (fun h => absurd h (by decide))
      obtain ⟨hil, hiv⟩ := blkAt_get hb i (by simpa using c)
      refine specR_heapLoadI (C := ctxH C H) lA1 _ (ko + 1 + i) hil (by decide)
        (by simp +decide [sev, ctxEnv, isParams]; exact cellA_idxS C ko i (by omega)) ?_
      rw [List.drop_eq_getElem_cons c]
      simp only [instSpine, show (ctxH C H).H = H from rfl, hiv, List.getElem_map]
      refine callPE (C := ctxH C H) lW fInst1F [pFu, pH, pV, pD] [vv pFu, vv pH, vv lA1, vv pD] (fastBody C)
        [BitVec.ofNat 64 fuel, Enc.idxW e, Enc.idxW as[i], BitVec.ofNat 64 t] (by decide) rfl (by decide) hcF
        ⟨by simp +decide [ctxEnv, isParams], by simp +decide [ctxEnv, isParams], by simp +decide,
          by simp +decide [ctxEnv, isParams], trivial⟩
        (fast_spec ra (ctxH C H) (ctxOK_H hok H) (codes_H C H hc) s fuel e as[i] t hf ht) (fun e' s1 => ?_)
      refine specR_assignI lA2 _ (BitVec.ofNat 64 (t - 1)) (by decide)
        (by simp +decide [sev, ctxEnv, isParams]; exact satPred t ht) ?_
      refine specR_congr (m' := instSpine fuel (as.drop (i + 1)) (t - 1) e' >>= fun r => pure r) (by simp) ?_
      refine callPE (C := ctxH C H) lY fInstSpine isParams
        [vv pFu, vv pSa, .op .add [vv pSi, .const 1], vv lA2, vv lW] isBody
        [BitVec.ofNat 64 fuel, cellA C ko, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 (t - 1), Enc.idxW e'] (by decide)
        rfl (by decide) hcS
        ⟨by simp +decide [ctxEnv, isParams], by simp +decide [ctxEnv, isParams] <;> rfl,
          by simp +decide [sev, ctxEnv, isParams]; exact word_add1_eq i, by simp +decide, by simp +decide, trivial⟩
        (ih (n - 1) (by omega) H s1 (i + 1) (t - 1) e' (by omega) (by omega) (by omega) hb) (fun r s2 => ?_)
      exact specR_returnI (vv lY) (Enc.idxW r) (by simp) (fun t' ht' => ⟨rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, isParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
        (by omega : as.length < 2 ^ 64), c]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.drop_eq_nil_of_le (by omega)]
      exact specR_returnI (vv pH) (Enc.idxW e) (by simp +decide [ctxEnv, isParams])
        (fun t' ht' => ⟨rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExIS
