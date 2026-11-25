import ConPanqueque.T.Ind.NestCtx
import ConRon.Arena.Inductives.ClassRead

/-!
# The generated-recursor pre-pass (`classRead`)

`fhBody`: `fvarHead e` as a word (`0` at `none`, `p + 1` at `some p`; an index at or past `2^63` halts).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- An optional index as a word. -/
def optNatW : Option Nat → BitVec 64
  | none => 0
  | some p => BitVec.ofNat 64 (p + 1)

def fhE := ofString "fh_e"
def fhH := ofString "fh_h"
def fhB := ofString "fh_b"
def fFvarHead := ofString "fvarHead"

def fhParams : List MlS := [fhE]
def fhLocals : List MlS := gaaLocals ++ [fhH, fhB]

def fhBody : ProgHOL 64 := prologue fhLocals
  (.seq (.call (some (some (.local, fhH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv fhE])
  (.ite (tagIsE fhH 1)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv fhH)) (.seq eViewP
      (.ite (.cmp .equal (vv lRn) (.const 1)) (.return (.const 1))
        (.ite (.cmp .equal (vv lRn) (.const 2))
          (.seq (.assign .local fhB (.load .one (.op .add [vv lRp, .const 8])))
            (.ite (.cmp .lower (vv fhB) (.const (BitVec.ofNat 64 (2 ^ 63))))
              (.return (.op .add [vv fhB, .const 1])) hang))
          hang)))))
    (.return (.const 0))))

section
variable {σ : Type}

theorem fh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fhLocals → (ctxEnv C ++ fhParams.zip vals).get x = none :=
  Knot.params_none C fhLocals fhParams vals (by decide) (by decide)

/-- An optional index's answer: its word, the index below `2^63`; the heap kept. -/
def PostON (C : Ctx) (o : Option Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = optNatW o ∧ (∀ p, o = some p → p < 2 ^ 63) ∧ SR C s' st

theorem postON_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostON C a w s' st → PostON C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

/-- **`fvarHead`**. -/
theorem fh_spec (C : Ctx) (hgf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (fhParams.zip [Enc.idxW e])) fhBody s (fvarHead e) (PostON C) := by
  refine specR_prologue (postON_locals _) (fh_none _ _) ?_
  unfold fvarHead
  refine specR_callNIM fhH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv fhE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hgf
    ⟨rfl, by simp +decide [sev, Env.get, fhParams, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel e s = .ok (a, s') ∧ Post C s a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hgf coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨_, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  obtain ⟨w, hw, hiff⟩ := sev_tagIs ((fhH, Enc.idxW hd) :: (ctxEnv C ++ fhParams.zip [Enc.idxW e])) fhH hd
    (by simp) 1 (by omega) (by omega)
  by_cases ht : hd.tag = UInt32.ofNat 1
  case neg =>
    have hb : (hd.tag == ETag.fvar) = false := by simp; intro e'; exact ht e'
    rw [hb]; simp only [Bool.false_eq_true, ite_false]
    exact specR_ifI _ w hw (fun e' => absurd (hiff.mp e') ht)
      (fun _ => specR_returnI _ 0 rfl (fun t ht' => ⟨rfl, (fun _ h => by cases h), sr_of_eq ht'.sr rfl rfl rfl rfl⟩))
  have hb : (hd.tag == ETag.fvar) = true := by simp [ht]; rfl
  rw [hb]; simp only [ite_true]
  refine specR_ifI _ w hw (fun _ => ?_) (fun e' => absurd (hiff.mpr ht) (by simp [e']))
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, fhParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv fhH) (Enc.idxW hd) (by decide) (by simp +decide [Env.get_cons]) ?_
  refine specR_viewXI ConRon.Arena.viewFVarIdx projFVarIdx hd (fun vw hvw => viewFVarIdx_run hd ht s vw hvw)
    (by simp) (by simp +decide) (by simp +decide [Env.get_cons, Env.get, fhParams, ctxEnv] <;> rfl) (by decide)
    (fun vw P htg hsh => ?_)
  have htT : hd.tag.toNat = 1 := by rw [ht]; simp
  rw [htT] at htg
  cases vw with
  | fvar idx ty =>
    have hlen : (encEView (.fvar idx ty)).length = 1 + (Enc.limbs idx).length := by
      simp [encEView, Enc.encFVar]; omega
    simp only [projFVarIdx]
    by_cases i0 : idx = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      exact specR_returnI _ 1 rfl (fun t ht' => ⟨rfl, (fun p hp => by cases hp; decide), sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
    by_cases ib : idx < 2 ^ 64
    swap
    · have hge : 2 ≤ (Enc.limbs idx).length := by
        have := (Big.limbs_length_lt_iff idx 1).not.mpr (by simp [Big.B]; omega); omega
      have hsh' : 1 + (Enc.limbs idx).length < 2 ^ 61 := by rw [← hlen]; exact hsh
      have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 1#64 := by
        intro h; have := congrArg BitVec.toNat h; simp at this; omega
      have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 2#64 := by
        intro h; have := congrArg BitVec.toNat h; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn1)
        (fun hw => absurd rfl hw) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp +decide [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn2)
        (fun hw => absurd rfl hw) (fun _ => specR_hangI)
    have hl : Enc.limbs idx = [BitVec.ofNat 64 idx] := by rw [limbs_small idx ib]; simp [i0]
    refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_loadI' fhB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 idx) (by decide)
      (by simp +decide [sev]) rfl
      (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 idx) [] (M := [])
          simpa [encEView, Enc.encFVar, hl] using this) ?_
    by_cases hlt : idx < 2 ^ 63
    · have hw' := ConPanqueque.T.Decl.nd_lt_iff idx (2 ^ 63) ib (by decide)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      exact specR_returnI _ (BitVec.ofNat 64 (idx + 1)) (by simp [sev, Env.get_cons]; exact word_add1_eq idx)
        (fun t ht' => ⟨rfl, (fun p hp => by cases hp; exact hlt), sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
    · have hw' := ConPanqueque.T.Decl.nd_lt_iff idx (2 ^ 63) ib (by decide)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
        (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  | _ => simp [ENodeView.tagN] at htg

end

/-! ## `classOfMotiveVar` -/

def cmvA := ofString "cmv_a"
def cmvQ := ofString "cmv_q"
def cmvI := ofString "cmv_i"
def cmvN := ofString "cmv_n"
def cmvY := ofString "cmv_y"
def cmvR := ofString "cmv_r"
def fFindIdx := ofString "blkFindIdx"

def cmvParams : List MlS := [cmvA, cmvQ, cmvI, cmvN]
def cmvLocals : List MlS := [cmvY, cmvR]

/-- The first position from `i` holding `q`, as `optNatW`. -/
def cmvBody : ProgHOL 64 := prologue cmvLocals
  (.ite (.cmp .lower (vv cmvI) (vv cmvN))
    (.seq (.assign .local cmvY (.load .one (.op .add [vv cmvA, .op .add [.panop .mul [vv cmvI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv cmvY) (vv cmvQ)) (.return (.op .add [vv cmvI, .const 1]))
      (.seq (.call (some (some (.local, cmvR), none)) fFindIdx [vv cmvA, vv cmvQ, .op .add [vv cmvI, .const 1], vv cmvN])
        (.return (vv cmvR)))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem cmv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cmvLocals → (ctxEnv C ++ cmvParams.zip vals).get x = none :=
  Knot.params_none C cmvLocals cmvParams vals (by decide) (by decide)

theorem findIdx_drop (xs : List Nat) (q i : Nat) (hi : i < xs.length) :
    ((xs.drop i).findIdx? (· == q)).map (· + i) =
      if xs[i] = q then some i else ((xs.drop (i + 1)).findIdx? (· == q)).map (· + (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, List.findIdx?_cons]
  by_cases h : xs[i] = q
  · simp [h]
  · simp [h, Option.map_map, Function.comp_def]; congr 1; funext x; omega

/-- **`blkFindIdx`** from position `i` (a block of naturals below `2^63`). -/
theorem cmv_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fFindIdx = some (cmvParams.map (fun p => (p, ShapeHOL.one)), cmvBody, .one))
    (xs : List Nat) (q : Nat) (pa : Nat) (H : List (BitVec 64))
    (hA : BlkAt H pa (xs.map (BitVec.ofNat 64))) (hxs : ∀ x ∈ xs, x < 2 ^ 63) (hq : q < 2 ^ 63) :
    ∀ f i (s : AState), xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cmvParams.zip [cellA C pa, BitVec.ofNat 64 q, BitVec.ofNat 64 i,
        BitVec.ofNat 64 xs.length])) cmvBody s (pure (((xs.drop i).findIdx? (· == q)).map (· + i)))
        (PostON (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postON_locals _) (cmv_none _ _) ?_
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cmvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, (fun _ h => by simp at h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < xs.length := by omega
    refine specR_prologue (postON_locals _) (cmv_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cmvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [findIdx_drop xs q i hin]
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) cmvY _ (pa + 1 + i) _ hx (by decide)
      (by simp +decide [sev, Env.get, cmvParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    have hxi := hxs xs[i] (List.getElem_mem hin)
    by_cases he : xs[i] = q
    · rw [if_pos he]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cmvParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (BitVec.ofNat 64 (i + 1))
        (by simp +decide [sev, Env.get_cons, Env.get, cmvParams, ctxEnv]; exact word_add1_eq i) (fun t ht => ⟨rfl, (fun p hp => by cases hp; omega), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_neg he]
    have hw : BitVec.ofNat 64 xs[i] ≠ BitVec.ofNat 64 q := by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cmvParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := (pure (((xs.drop (i + 1)).findIdx? (· == q)).map (· + (i + 1))) : AM (Option Nat)) >>=
      fun r => pure r) (by simp) ?_
    refine specR_callNIM cmvR fFindIdx cmvParams [vv cmvA, vv cmvQ, .op .add [vv cmvI, .const 1], vv cmvN] cmvBody
      [cellA C pa, BitVec.ofNat 64 q, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cmvParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmvParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cmvParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cmvParams, ctxEnv], trivial⟩
      (PostON (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmvParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun r w s1 st ⟨hw', hb, _⟩ => ?_)
    subst hw'
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨rfl, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
