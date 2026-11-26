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

/-! ## `piBinders`' count is `piTele`'s -/

theorem piTele_piBinders (fuel : Nat) : ∀ (h : EIdx) (s : AState) (n : Nat) (e : EIdx) (s' : AState),
    piTele fuel h s = .ok ((n, e), s') → ∃ bs, piBinders fuel h s = .ok ((bs, e), s') ∧ bs.length = n := by
  induction fuel with
  | zero => intro h s n e s' hr; rw [piTele] at hr; exact (WC.fail_ok_inv hr).elim
  | succ fuel ih =>
    intro h s n e s' hr
    rw [piTele] at hr; rw [piBinders]
    by_cases ht : (h.tag == ETag.forallE) = true
    · simp only [ht, ite_true] at hr ⊢
      obtain ⟨o, s1, h1, h2⟩ := WC.bind_ok_inv hr
      rcases o with _ | ⟨ty, b⟩
      · exact (WC.failDanglingE_ok_inv h2).elim
      obtain ⟨r, s2, h3, h4⟩ := WC.bind_ok_inv h2
      obtain ⟨e1, e2⟩ := WC.pure_ok_inv h4
      obtain ⟨n0, e0⟩ := r
      simp only [Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      subst s'
      obtain ⟨bs, hb, hl⟩ := ih b s1 n0 e s2 h3
      refine ⟨ty :: bs, ?_, by simp [hl]⟩
      simp only [bind, StateT.bind] at h1 ⊢
      rw [h1]
      simp only [Except.bind, StateT.bind, hb, StateT.pure, pure, Except.pure]; rfl
    · simp only [ht, Bool.false_eq_true, ite_false] at hr ⊢
      obtain ⟨e1, e2⟩ := WC.pure_ok_inv hr
      simp only [Prod.mk.injEq] at e1; obtain ⟨rfl, rfl⟩ := e1; subst s'
      exact ⟨[], rfl, rfl⟩

/-! ## One field's inductive hypothesis (the `filterMapM` body of `classReadMinor`) -/

/-- The twin's per-field reading, named. -/
def ihOf (nP : Nat) (motPos : List Nat) (d : Nat) (x : EIdx) : AM (Option (Nat × Nat)) := do
  let ty ← fvarTypeD x
  let r ← piResult coreWalkFuel ty
  match ← fvarHead r with
  | none => pure none
  | some p2 =>
    match classOfMotiveVar nP motPos p2 with
    | none => pure none
    | some t => do
      let rargs ← getAppArgs coreWalkFuel r
      match rargs.getLast? with
      | none => pure none
      | some a =>
        match ← fvarHead a with
        | none => pure none
        | some f => pure (if d ≤ f then some (f - d, t) else none)

theorem classOfMotiveVar_eq (nP : Nat) (motPos : List Nat) (p : Nat) :
    classOfMotiveVar nP motPos p =
      if nP ≤ p then ((motPos.drop 0).findIdx? (· == p - nP)).map (· + 0) else none := by
  simp [classOfMotiveVar]

def ioX := ofString "io_x"
def ioP := ofString "io_p"
def ioMp := ofString "io_mp"
def ioMn := ofString "io_mn"
def ioD := ofString "io_d"
def ioT := ofString "io_t"
def ioR := ofString "io_r"
def ioH := ofString "io_h"
def ioC := ofString "io_c"
def ioA := ofString "io_a"
def ioK := ofString "io_k"
def ioL := ofString "io_l"
def ioF := ofString "io_f"
def ioW := ofString "io_w"
def fIhOf := ofString "ihOf"

def ioParams : List MlS := [ioX, ioP, ioMp, ioMn, ioD]
def ioLocals : List MlS := [ioT, ioR, ioH, ioC, ioA, ioK, ioL, ioF, ioW]

def ioBody (C : Ctx) : ProgHOL 64 := prologue ioLocals
  (.seq (.call (some (some (.local, ioT), none)) fFvt [vv ioX])
  (.seq (.call (some (some (.local, ioR), none)) ExM.fPir [.const (BitVec.ofNat 64 coreWalkFuel), vv ioT])
  (.seq (.call (some (some (.local, ioH), none)) fFvarHead [vv ioR])
  (.ite (.cmp .equal (vv ioH) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ioH (.op .sub [vv ioH, .const 1]))
  (.ite (.cmp .lower (vv ioH) (vv ioP)) (.return (.const 0))
  (.seq (.call (some (some (.local, ioC), none)) fFindIdx [vv ioMp, .op .sub [vv ioH, vv ioP], .const 0, vv ioMn])
  (.ite (.cmp .equal (vv ioC) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, ioA), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv ioR])
  (.seq (.assign .local ioK (.load .one (vv ioA)))
  (.ite (.cmp .equal (vv ioK) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ioL (.load .one (.op .add [vv ioA, .shift .lsl (vv ioK) (.const 3)])))
  (.seq (.call (some (some (.local, ioF), none)) fFvarHead [vv ioL])
  (.ite (.cmp .equal (vv ioF) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ioF (.op .sub [vv ioF, .const 1]))
  (.ite (.cmp .lower (vv ioF) (vv ioD)) (.return (.const 0))
  (alloc2 C ioW (.op .sub [vv ioF, vv ioD]) (.op .sub [vv ioC, .const 1]) (.return (vv ioW)))))))))))))))))))

/-- The code `ihOf` runs. -/
structure IOCodes (C : Ctx) : Prop where
  self : C.code.lookup fIhOf = some (ioParams.map (fun p => (p, ShapeHOL.one)), ioBody C, .one)
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  pir : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one)
  fh : C.code.lookup fFvarHead = some (fhParams.map (fun p => (p, ShapeHOL.one)), fhBody, .one)
  gf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  cmv : C.code.lookup fFindIdx = some (cmvParams.map (fun p => (p, ShapeHOL.one)), cmvBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)

section
variable {σ : Type}

theorem io_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ioLocals → (ctxEnv C ++ ioParams.zip vals).get x = none :=
  Knot.params_none C ioLocals ioParams vals (by decide) (by decide)

/-- An optional pair's answer: `0`, or a fresh cell `[f, t]` (both below `2^63`). -/
def PostIO (C : Ctx) (o : Option (Nat × Nat)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧ ∀ f t, o = some (f, t) →
    f < 2 ^ 63 ∧ t < 2 ^ 63 ∧ ∃ ow, w = cellA C ow ∧ H'[ow]? = some (BitVec.ofNat 64 f) ∧
      H'[ow + 1]? = some (BitVec.ofNat 64 t)

theorem postIO_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostIO C a w s' st → PostIO C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem word_sub_eq (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

end

section
variable {σ : Type}

set_option maxHeartbeats 4000000 in
/-- **`ihOf`**: one field's inductive hypothesis. -/
theorem io_spec (C : Ctx) (hok : CtxOK C) (hc : IOCodes C) (nP : Nat) (motPos : List Nat) (pm d : Nat)
    (H : List (BitVec 64)) (hMp : BlkAt H pm (motPos.map (BitVec.ofNat 64))) (hmp : ∀ x ∈ motPos, x < 2 ^ 63)
    (hnP : nP < 2 ^ 63) (hd : d < 2 ^ 63) (s : AState) (x : EIdx) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ioParams.zip [Enc.idxW x, BitVec.ofNat 64 nP, cellA C pm,
      BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d])) (ioBody C) s (ihOf nP motPos d x) (PostIO (ctxH C H)) := by
  refine specR_prologue (postIO_locals _) (io_none _ _) ?_
  unfold ihOf
  have hokH := ctxOK_H hok H
  refine ILP.callE_spec (C := ctxH C H) ioT fFvt [pH] [vv ioX] ExM.fvtBody [Enc.idxW x] (by decide) rfl
    (by decide) hc.fvt ⟨by simp +decide [sev, Env.get, ioParams, ctxEnv], trivial⟩
    (ExM.fvt_spec (ctxH C H) s x) (fun ta s1 => ?_)
  refine ILP.callE_spec (C := ctxH C H) ioR ExM.fPir [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ioT]
    ExM.pirBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW ta] (by decide) rfl (by decide) hc.pir
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (ExM.pir_spec (ctxH C H) hc.pir coreWalkFuel CV.coreWalkFuel_lt ta s1) (fun r s2 => ?_)
  refine specR_callNIM ioH fFvarHead fhParams [vv ioR] fhBody [Enc.idxW r] (by decide) rfl (by decide) hc.fh
    ⟨by simp +decide [sev, Env.get_cons], trivial⟩ (PostON (ctxH C H)) (fun _ _ _ _ h => h.2.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fhParams _ rfl hlk) (fh_spec (ctxH C H) hc.gf s2 r))
    (fun o w s3 st ⟨hw, hb, _⟩ => ?_)
  subst hw
  rcases o with _ | p2
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun _ => rfl, fun _ _ h => by cases h⟩)
  have hp2 := hb p2 rfl
  have hne : BitVec.ofNat 64 (p2 + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI ioH _ (BitVec.ofNat 64 p2) (by decide)
    (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (p2 + 1) 1 (by omega) (by omega)) ?_
  simp only
  rw [classOfMotiveVar_eq]
  have hlw := ConPanqueque.T.Decl.nd_lt_iff p2 nP (by omega) (by omega)
  by_cases hle : nP ≤ p2
  swap
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr (by omega)]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_neg hle]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun _ => rfl, fun _ _ h => by cases h⟩)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_pos hle]
  refine specR_pureBind (((motPos.drop 0).findIdx? (· == p2 - nP)).map (· + 0)) ?_
  refine specR_callNIM ioC fFindIdx cmvParams [vv ioMp, .op .sub [vv ioH, vv ioP], .const 0, vv ioMn] cmvBody
    [cellA C pm, BitVec.ofNat 64 (p2 - nP), BitVec.ofNat 64 0, BitVec.ofNat 64 (List.map (BitVec.ofNat 64) motPos).length]
    (by decide) rfl (by decide) hc.cmv
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv]; exact word_sub_eq p2 nP hle (by omega), rfl,
      by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure (((motPos.drop 0).findIdx? (· == p2 - nP)).map (· + 0)) : AM (Option Nat)) s3 = .ok (a, s') ∧
      PostON (ctxH C H) a w s' st) (fun _ _ _ _ h => h.2.2.2)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cmvParams _ rfl hlk) (by
      have := cmv_spec (σ := σ) C hok hc.cmv motPos (p2 - nP) pm H hMp hmp (by omega) _ 0 s3 rfl (by omega)
      simpa only [List.length_map] using this)))
    (fun a w s4 st ⟨hrun, hw, hb2, _⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs4⟩ := hrun
  subst hw; subst hs4
  rw [hra]
  rcases a with _ | t
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun _ => rfl, fun _ _ h => by cases h⟩)
  have ht63 := hb2 t rfl
  have hnt : BitVec.ofNat 64 (t + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnt)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine specR_callNIH (C := ctxH C H) ioA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ioR]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW r] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
    (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H) hokH hc.gaa coreWalkFuel CV.coreWalkFuel_lt H r s3))
    (fun rargs w s5 H5 hp5 ⟨oa, hw, hba⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H5) ioK (vv ioA) oa _ hba.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hal := Big.blk_small0 (ctxOK_H hok H5) ht5.sr hba
  simp only [List.length_map] at hal
  rcases hrl : rargs.getLast? with _ | a
  · have hnil : rargs = [] := List.getLast?_eq_none_iff.mp hrl
    subst hnil
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H5, hp5, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun _ _ h => by cases h⟩)
  have hne0 : rargs ≠ [] := by intro h; subst h; simp at hrl
  have hlen0 : 0 < rargs.length := List.length_pos_iff.mpr hne0
  have hK : BitVec.ofNat 64 rargs.length ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hK)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hlast : rargs[rargs.length - 1]'(by omega) = a := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hrl; simpa using hrl
  have hcl := hba.2 (rargs.length - 1) (by simp; omega)
  simp only [List.getElem_map, hlast] at hcl
  refine UD.specR_heapLoadI' (C := ctxH C H5) ioL _ (oa + 1 + (rargs.length - 1)) _ hcl (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C oa + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  simp only
  refine specR_callNIM ioF fFvarHead fhParams [vv ioL] fhBody [Enc.idxW a] (by decide) rfl (by decide) hc.fh
    ⟨by simp +decide [sev, Env.get_cons], trivial⟩ (PostON (ctxH C H5)) (fun _ _ _ _ h => h.2.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fhParams _ rfl hlk) (fh_spec (ctxH C H5) hc.gf s5 a))
    (fun o w s6 st ⟨hw, hb3, _⟩ => ?_)
  subst hw
  rcases o with _ | f
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H5, hp5, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun _ _ h => by cases h⟩)
  have hf63 := hb3 f rfl
  have hnf : BitVec.ofNat 64 (f + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnf)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI ioF _ (BitVec.ofNat 64 f) (by decide)
    (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (f + 1) 1 (by omega) (by omega)) ?_
  simp only
  have hlw2 := ConPanqueque.T.Decl.nd_lt_iff f d (by omega) (by omega)
  by_cases hdf : d ≤ f
  swap
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr (by omega)]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_neg hdf]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H5, hp5, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun _ _ h => by cases h⟩)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_pos hdf]
  refine specR_alloc2I (ctxOK_H hok H5) ioW _ _ (BitVec.ofNat 64 (f - d)) (BitVec.ofNat 64 t) (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, ioParams, ctxEnv]; exact word_sub_eq f d hdf (by omega))
    (fun _ => by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (t + 1) 1 (by omega) (by omega))
    (fun H6 ws hp6 hws => ?_)
  obtain ⟨g0, g1⟩ := img2_get H6 ws (BitVec.ofNat 64 (f - d)) (BitVec.ofNat 64 t) hws
  exact specR_returnI _ _ (by simp +decide [sev] <;> rfl) (fun t' ht' => ⟨_, (hp5.trans hp6).trans (img2_prefix _ _ _ _ hws),
    sr_of_eq ht'.sr rfl rfl rfl rfl, (fun h => by cases h), (fun f' t'' h => by
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, ht63, H6.length, rfl, g0, g1⟩)⟩)

end

/-! ## The inductive hypotheses (`fvs.filterMapM ihOf`) -/

def ihqA := ofString "fmi_a"
def ihqI := ofString "fmi_i"
def ihqN := ofString "fmi_n"
def ihqW := ofString "fmi_w"
def ihqJ := ofString "fmi_j"
def ihqP := ofString "fmi_p"
def ihqMp := ofString "fmi_mp"
def ihqMn := ofString "fmi_mn"
def ihqD := ofString "fmi_d"
def ihqX := ofString "fmi_x"
def ihqR := ofString "fmi_r"
def ihqF := ofString "fmi_f"
def ihqT := ofString "fmi_t"
def fIhs := ofString "ihsFill"

def fmiParams : List MlS := [ihqA, ihqI, ihqN, ihqW, ihqJ, ihqP, ihqMp, ihqMn, ihqD]
def fmiLocals : List MlS := [ihqX, ihqR, ihqF, ihqT]

def fmiBody : ProgHOL 64 := prologue fmiLocals
  (.ite (.cmp .lower (vv ihqI) (vv ihqN))
    (.seq (.assign .local ihqX (.load .one (.op .add [vv ihqA, .op .add [.panop .mul [vv ihqI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, ihqR), none)) fIhOf [vv ihqX, vv ihqP, vv ihqMp, vv ihqMn, vv ihqD])
    (.ite (.cmp .equal (vv ihqR) (.const 0))
      (.seq (.call (some (some (.local, ihqR), none)) fIhs
          [vv ihqA, .op .add [vv ihqI, .const 1], vv ihqN, vv ihqW, vv ihqJ, vv ihqP, vv ihqMp, vv ihqMn, vv ihqD])
        (.return (vv ihqR)))
      (.seq (.assign .local ihqF (.load .one (vv ihqR)))
      (.seq (.assign .local ihqT (.load .one (.op .add [vv ihqR, .const 8])))
      (.seq (.store (.op .add [vv ihqW, .panop .mul [vv ihqJ, .const 16]]) (vv ihqF))
      (.seq (.store (.op .add [vv ihqW, .op .add [.panop .mul [vv ihqJ, .const 16], .const 8]]) (vv ihqT))
      (.seq (.call (some (some (.local, ihqR), none)) fIhs
          [vv ihqA, .op .add [vv ihqI, .const 1], vv ihqN, vv ihqW, .op .add [vv ihqJ, .const 1], vv ihqP, vv ihqMp, vv ihqMn,
            vv ihqD])
        (.return (vv ihqR))))))))))
    (.return (vv ihqJ)))

section
variable {σ : Type}

theorem fmi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fmiLocals → (ctxEnv C ++ fmiParams.zip vals).get x = none :=
  Knot.params_none C fmiLocals fmiParams vals (by decide) (by decide)

/-- Pairs written from slot `j`: `ys`, each `(f, t)` at `ow + 2(j + k)`; the count returned. -/
def PostFMI (C : Ctx) (Hb : List (BitVec 64)) (ow j cap : Nat) (ys : List (Nat × Nat)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', Hb <+: H' ∧ ow + 2 * cap ≤ H'.length ∧ SR (ctxH C H') s' st ∧ w = BitVec.ofNat 64 (j + ys.length) ∧
    j + ys.length ≤ cap ∧ ∀ k (hk : k < ys.length), H'[ow + 2 * (j + k)]? = some (BitVec.ofNat 64 ys[k].1) ∧
      H'[ow + 2 * (j + k) + 1]? = some (BitVec.ofNat 64 ys[k].2)

theorem postFMI_locals (C : Ctx) (Hb : List (BitVec 64)) (ow j cap : Nat) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostFMI C Hb ow j cap a w s' st → PostFMI C Hb ow j cap a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hl, hs, h⟩ => ⟨H', hp, hl, sr_of_eq hs rfl rfl rfl rfl, h⟩

end

section
variable {σ : Type}

theorem cellA_mul16z (C : Ctx) (o j : Nat) (hj : j < 2 ^ 59) :
    cellA C o + BitVec.ofNat 64 j * 16#64 = cellA C (o + 2 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 4000000 in
/-- **`ihsFill`** from field `i`, slot `j`. -/
theorem ihq_spec (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fIhs = some (fmiParams.map (fun p => (p, ShapeHOL.one)), fmiBody, .one)) (hio : IOCodes C)
    (nP : Nat) (motPos : List Nat) (pm d : Nat) (xs : List EIdx) (pa ow cap : Nat) (H0 : List (BitVec 64))
    (hA : BlkAt H0 pa (xs.map Enc.idxW)) (hMp : BlkAt H0 pm (motPos.map (BitVec.ofNat 64)))
    (hmp : ∀ x ∈ motPos, x < 2 ^ 63) (hnP : nP < 2 ^ 63) (hd : d < 2 ^ 63) (hcap : cap < 2 ^ 58) :
    ∀ f i j (Hb H : List (BitVec 64)) (s : AState), xs.length - i = f → i ≤ xs.length → H0 <+: Hb → Hb <+: H →
      Hb.length ≤ ow + 2 * j → ow + 2 * cap ≤ H.length → j + (xs.length - i) ≤ cap →
      SpecR (σ := σ) (Pre (ctxH C H) s (fmiParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length,
          cellA C ow, BitVec.ofNat 64 j, BitVec.ofNat 64 nP, cellA C pm, BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d]))
        fmiBody s (List.filterMapM (ihOf nP motPos d) (xs.drop i)) (PostFMI C Hb ow j cap) := by
  intro f
  induction f with
  | zero =>
    intro i j Hb H s hf hi hb0 hbH hbl hroom hjc
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postFMI_locals _ _ _ _ _) (fmi_none _ _) ?_
    have hal := blkAt_len_le (blkAt_mono hA (hb0.trans hbH))
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, fmiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.filterMapM_nil]
    exact specR_returnI _ (BitVec.ofNat 64 j) (by simp +decide [sev, Env.get, fmiParams, ctxEnv])
      (fun t ht => ⟨H, hbH, hroom, sr_of_eq ht.sr rfl rfl rfl rfl, by simp, by simp; omega, fun k hk => absurd hk (by simp)⟩)
  | succ f ih =>
    intro i j Hb H s hf hi hb0 hbH hbl hroom hjc
    have hin : i < xs.length := by omega
    refine specR_prologue (postFMI_locals _ _ _ _ _) (fmi_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le (blkAt_mono hA (hb0.trans hbH))
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, fmiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, List.filterMapM_cons]
    have h0H := hb0.trans hbH
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) ihqX _ (pa + 1 + i) _ (get_prefix hx h0H) (by decide)
      (by simp +decide [sev, Env.get, fmiParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine specR_callNIH (C := ctxH C H) ihqR fIhOf ioParams [vv ihqX, vv ihqP, vv ihqMp, vv ihqMn, vv ihqD] (ioBody C)
      [Enc.idxW xs[i], BitVec.ofNat 64 nP, cellA C pm, BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d]
      (by decide) rfl (by decide) hio.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], trivial⟩
      (PostIO (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ f t, o = some (f, t) →
        f < 2 ^ 63 ∧ t < 2 ^ 63 ∧ ∃ ow', w = cellA C ow' ∧ H'[ow']? = some (BitVec.ofNat 64 f) ∧
          H'[ow' + 1]? = some (BitVec.ofNat 64 t))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ioParams _ rfl hlk)
        (io_spec C hok hio nP motPos pm d H (blkAt_mono hMp h0H) hmp hnP hd s xs[i]))
      (fun o w s1 H1 hp1 ⟨hn1, hs1⟩ => ?_)
    have hp1' : H <+: H1 := hp1
    rcases o with _ | ⟨f0, t0⟩
    · rw [hn1 rfl]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      refine specR_congr (m' := List.filterMapM (ihOf nP motPos d) (xs.drop (i + 1)) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIG (C := ctxH C H1) ihqR fIhs fmiParams
        [vv ihqA, .op .add [vv ihqI, .const 1], vv ihqN, vv ihqW, vv ihqJ, vv ihqP, vv ihqMp, vv ihqMn, vv ihqD] fmiBody
        [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length, cellA C ow, BitVec.ofNat 64 j, BitVec.ofNat 64 nP,
          cellA C pm, BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d] (by decide) rfl (by decide) hcl
        ⟨by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], trivial⟩
        (PostFMI C Hb ow j cap) (fun ys w _ H' => Hb <+: H' ∧ ow + 2 * cap ≤ H'.length ∧ w = BitVec.ofNat 64 (j + ys.length) ∧
          j + ys.length ≤ cap ∧ ∀ k (hk : k < ys.length), H'[ow + 2 * (j + k)]? = some (BitVec.ofNat 64 ys[k].1) ∧
            H'[ow + 2 * (j + k) + 1]? = some (BitVec.ofNat 64 ys[k].2))
        (fun ys w s' st ⟨H', hp', hl', hs', h1⟩ => ⟨H', ⟨hp', hl', h1⟩, hs'⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmiParams _ rfl hlk)
          (ih (i + 1) j Hb H1 s1 (by omega) (by omega) hb0 (hbH.trans hp1') hbl
            (le_trans hroom (List.IsPrefix.length_le hp1')) (by omega)))
        (fun ys w s2 H2 ⟨hp2, hl2, hw, hjc', hcells⟩ => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H2, hp2, hl2, sr_of_eq ht.sr rfl rfl rfl rfl, rfl, hjc', hcells⟩)
    obtain ⟨hf63, ht63, ow', rfl, hcf, hct⟩ := hs1 f0 t0 rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
    have hol' : ow' < H1.length := (List.getElem?_eq_some_iff.mp hcf).1
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hne : cellA C ow' ≠ 0 := cellA_ne0 C hok ow' (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H1) ihqF (vv ihqR) ow' _ hcf (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) ihqT _ (ow' + 1) _ hct (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ow') ?_
    have hH1l : H.length ≤ H1.length := List.IsPrefix.length_le hp1'
    have hjlt : j < cap := by omega
    have hj60 : j < 2 ^ 60 := by omega
    refine specR_heapStoreI (ctxOK_H hok H1) (.op .add [vv ihqW, .panop .mul [vv ihqJ, .const 16]]) (vv ihqF) (ow + 2 * j)
      (by show _ < H1.length; omega) (BitVec.ofNat 64 f0)
      (by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv]; exact cellA_mul16z C ow j (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv ihqW, .op .add [.panop .mul [vv ihqJ, .const 16], .const 8]])
      (vv ihqT) (ow + 2 * j + 1) (by show _ < (H1.set _ _).length; simp; omega) (BitVec.ofNat 64 t0)
      (by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv]
          rw [cellA_mul16 C ow j hj60, show ow + 1 + 2 * j = ow + 2 * j + 1 by omega]; rfl)
      (by simp [sev, Env.get_cons]) ?_
    let H2 := (H1.set (ow + 2 * j) (BitVec.ofNat 64 f0)).set (ow + 2 * j + 1) (BitVec.ofNat 64 t0)
    have hl2 : H2.length = H1.length := by simp [H2]
    have hbH1 : Hb <+: H1 := hbH.trans hp1'
    have hb2 : Hb <+: H2 := prefix_set (prefix_set hbH1 hbl _) (by omega) _
    let Hb' := H2.take (ow + 2 * j + 2)
    have hbb' : Hb <+: Hb' := prefix_take_of hb2 (by omega)
    have hb'2 : Hb' <+: H2 := List.take_prefix _ _
    have hc0 : Hb'[ow + 2 * j]? = some (BitVec.ofNat 64 f0) := by
      simp only [Hb', H2, List.getElem?_take]; rw [if_pos (by omega)]
      rw [List.getElem?_set_ne (by omega)]; exact List.getElem?_set_self (by omega)
    have hc1 : Hb'[ow + 2 * j + 1]? = some (BitVec.ofNat 64 t0) := by
      simp only [Hb', H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by simp; omega)
    simp only
    refine specR_callNIG (C := ctxH (ctxH C H1) H2) ihqR fIhs fmiParams
      [vv ihqA, .op .add [vv ihqI, .const 1], vv ihqN, vv ihqW, .op .add [vv ihqJ, .const 1], vv ihqP, vv ihqMp, vv ihqMn,
        vv ihqD] fmiBody
      [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length, cellA C ow, BitVec.ofNat 64 (j + 1),
        BitVec.ofNat 64 nP, cellA C pm, BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d] (by decide) rfl (by decide) hcl
      ⟨by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv]; exact word_add1_eq j,
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, fmiParams, ctxEnv], trivial⟩
      (PostFMI C Hb' ow (j + 1) cap) (fun ys w _ H' => Hb' <+: H' ∧ ow + 2 * cap ≤ H'.length ∧
        w = BitVec.ofNat 64 (j + 1 + ys.length) ∧ j + 1 + ys.length ≤ cap ∧
        ∀ k (hk : k < ys.length), H'[ow + 2 * (j + 1 + k)]? = some (BitVec.ofNat 64 ys[k].1) ∧
          H'[ow + 2 * (j + 1 + k) + 1]? = some (BitVec.ofNat 64 ys[k].2))
      (fun ys w s' st ⟨H', hp', hl', hs', h1⟩ => ⟨H', ⟨hp', hl', h1⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmiParams _ rfl hlk)
        (ih (i + 1) (j + 1) Hb' H2 s1 (by omega) (by omega) (hb0.trans hbb') hb'2 (by simp [Hb', hl2]; omega)
          (by rw [hl2]; omega) (by omega)))
      (fun ys w s2 H3 ⟨hp3, hl3, hw, hjc', hcells⟩ => ?_)
    subst hw
    exact specR_returnI _ (BitVec.ofNat 64 (j + 1 + ys.length)) (by simp [Env.get]) (fun t ht => ⟨H3, hbb'.trans hp3, hl3,
      sr_of_eq ht.sr rfl rfl rfl rfl,
      by rw [List.length_cons, show j + (ys.length + 1) = j + 1 + ys.length by omega], by simp; omega, fun k hk => by
        cases k with
        | zero => exact ⟨get_prefix (by simpa using hc0) hp3, get_prefix (by simpa using hc1) hp3⟩
        | succ k =>
          simp only [List.getElem_cons_succ]
          have := hcells k (by simpa using hk)
          rw [show j + (k + 1) = j + 1 + k by omega]; exact this⟩)

end

/-! ## `classReadMinor` (off-shape halts: the pre-pass's caller fails there) -/

/-- A list of pairs at `o`: the count, then `f, t` per pair. -/
def PairsRep (H : List (BitVec 64)) (o : Nat) (ps : List (Nat × Nat)) : Prop :=
  H[o]? = some (BitVec.ofNat 64 ps.length) ∧ ∀ k (hk : k < ps.length),
    H[o + 1 + 2 * k]? = some (BitVec.ofNat 64 ps[k].1) ∧ H[o + 1 + 2 * k + 1]? = some (BitVec.ofNat 64 ps[k].2)

/-- A prefix slot at `o`: `[0, ind, lvls, ds block]` or `[1, class, ctor, ihs pairs]`. -/
def SlotRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) : ClassSlot → Prop
  | .motive k => H[o]? = some 0 ∧ H[o + 1]? = some (Enc.idxW k.ind) ∧ H[o + 2]? = some (Enc.idxW k.lvls) ∧
      ∃ od, H[o + 3]? = some (cellA C od) ∧ BlkAt H od (k.ds.map Enc.idxW)
  | .minor c cn ihs => H[o]? = some 1 ∧ H[o + 1]? = some (BitVec.ofNat 64 c) ∧ H[o + 2]? = some (Enc.idxW cn) ∧
      ∃ oi, H[o + 3]? = some (cellA C oi) ∧ PairsRep H oi ihs

/-- A slot that is `some`, as a record. -/
def PostSlot (C : Ctx) (o : Option ClassSlot) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ sl os, o = some sl ∧ w = cellA C os ∧ SlotRep C H' os sl

theorem postSlot_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSlot (σ := σ) C a w s' st → PostSlot C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

def crmD := ofString "crm_d"
def crmP := ofString "crm_p"
def crmMp := ofString "crm_mp"
def crmMn := ofString "crm_mn"
def crmDd := ofString "crm_dd"
def crmT := ofString "crm_t"
def crmN := ofString "crm_n"
def crmQ := ofString "crm_q"
def crmFv := ofString "crm_fv"
def crmCc := ofString "crm_cc"
def crmH := ofString "crm_h"
def crmC := ofString "crm_c"
def crmA := ofString "crm_a"
def crmK := ofString "crm_k"
def crmL := ofString "crm_l"
def crmHd := ofString "crm_hd"
def crmCn := ofString "crm_cn"
def crmNf := ofString "crm_nf"
def crmIb := ofString "crm_ib"
def crmR := ofString "crm_r"
def crmW := ofString "crm_w"
def fClassReadMinor := ofString "classReadMinor"

def crmParams : List MlS := [crmD, crmP, crmMp, crmMn, crmDd]
def crmLocals : List MlS := gaaLocals ++ [crmT, crmN, crmQ, crmFv, crmCc, crmH, crmC, crmA, crmK, crmL, crmHd, crmCn,
  crmNf, crmIb, crmR, crmW]

def crmTail (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv crmHd)) (.seq eViewP
  (.seq (.assign .local crmCn (.load .one (vv lRp)))
  (.seq (.assign .local crmNf (.load .one (vv crmFv)))
  (allocP C crmIb (.op .add [.panop .mul [vv crmNf, .const 16], .const 8])
  (.seq (.call (some (some (.local, crmR), none)) fIhs
      [vv crmFv, .const 0, vv crmNf, .op .add [vv crmIb, .const 8], .const 0, vv crmP, vv crmMp, vv crmMn, vv crmDd])
  (.seq (.store (vv crmIb) (vv crmR))
  (alloc4 C crmW (.const 1) (.op .sub [vv crmC, .const 1]) (vv crmCn) (vv crmIb) (.return (vv crmW))))))))))

def crmBody (C : Ctx) : ProgHOL 64 := prologue crmLocals
  (.seq (.call (some (some (.local, crmT), none)) fPiTele [.const (BitVec.ofNat 64 coreWalkFuel), vv crmD])
  (.seq (.assign .local crmN (.load .one (vv crmT)))
  (.seq (.call (some (some (.local, crmQ), none)) fOpenFvars [vv crmN, vv crmD, vv crmDd])
  (.ite (.cmp .equal (vv crmQ) (.const 0)) hang
  (.seq (.assign .local crmFv (.load .one (vv crmQ)))
  (.seq (.assign .local crmCc (.load .one (.op .add [vv crmQ, .const 8])))
  (.seq (.call (some (some (.local, crmH), none)) fFvarHead [vv crmCc])
  (.ite (.cmp .equal (vv crmH) (.const 0)) hang
  (.seq (.assign .local crmH (.op .sub [vv crmH, .const 1]))
  (.ite (.cmp .lower (vv crmH) (vv crmP)) hang
  (.seq (.call (some (some (.local, crmC), none)) fFindIdx [vv crmMp, .op .sub [vv crmH, vv crmP], .const 0, vv crmMn])
  (.ite (.cmp .equal (vv crmC) (.const 0)) hang
  (.seq (.call (some (some (.local, crmA), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv crmCc])
  (.seq (.assign .local crmK (.load .one (vv crmA)))
  (.ite (.cmp .equal (vv crmK) (.const 0)) hang
  (.seq (.assign .local crmL (.load .one (.op .add [vv crmA, .shift .lsl (vv crmK) (.const 3)])))
  (.seq (.call (some (some (.local, crmHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv crmL])
  (.ite (tagIsE crmHd 3) (crmTail C) hang))))))))))))))))))

/-- The code `classReadMinor` runs. -/
structure CRMCodes (C : Ctx) : Prop where
  self : C.code.lookup fClassReadMinor = some (crmParams.map (fun p => (p, ShapeHOL.one)), crmBody C, .one)
  pt : C.code.lookup fPiTele = some ([(pFu, .one), (pH, .one)], ptBody C fPiTele, .one)
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  io : IOCodes C
  ihs : C.code.lookup fIhs = some (fmiParams.map (fun p => (p, ShapeHOL.one)), fmiBody, .one)

section
variable {σ : Type}

/-- A spec for a twin with fewer successful runs is a spec for one with more. -/
theorem specR_okMono {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m m' : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (hm : ∀ a s', m' s = .ok (a, s') → m s = .ok (a, s'))
    (h : SpecR P c s m' R) : SpecR P c s m R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a, s', hm', hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', hm a s' hm', hq⟩

/-- `piBinders` read through `piTele`, when the continuation looks only at the binder count. -/
theorem specR_piBinders {β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {R : β → BitVec 64 → AState → PState σ → Prop}
    (fuel : Nat) (h : EIdx) (k : List EIdx × EIdx → AM β)
    (hk : ∀ bs e, k (bs, e) = k (List.replicate bs.length default, default))
    (hs : SpecR P c s (piTele fuel h >>= fun r => k (List.replicate r.1 default, default)) R) :
    SpecR P c s (piBinders fuel h >>= k) R := by
  refine specR_okMono (fun a s' hrun => ?_) hs
  obtain ⟨r, s1, h1, h2⟩ := WC.bind_ok_inv hrun
  obtain ⟨n, e⟩ := r
  obtain ⟨bs, hb, hl⟩ := piTele_piBinders fuel h s n e s1 h1
  simp only [bind, StateT.bind, hb]
  show k (bs, e) s1 = _
  rw [hk, hl]; exact h2

end

section
variable {σ : Type}

theorem crm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crmLocals → (ctxEnv C ++ crmParams.zip vals).get x = none :=
  Knot.params_none C crmLocals crmParams vals (by decide) (by decide)

set_option maxHeartbeats 8000000 in
/-- **`classReadMinor`**. -/
theorem crm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CRMCodes C)
    (nP : Nat) (motPos : List Nat) (pm d : Nat) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hMp : BlkAt H pm (motPos.map (BitVec.ofNat 64))) (hmp : ∀ x ∈ motPos, x < 2 ^ 63) (hnP : nP < 2 ^ 63)
    (hd : d < 2 ^ 62) (s : AState) (dom : EIdx) :
    SpecR (σ := σ) (Pre (ctxH C H) s (crmParams.zip [Enc.idxW dom, BitVec.ofNat 64 nP, cellA C pm,
      BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d])) (crmBody C) s (classReadMinor nP motPos d dom)
      (PostSlot (ctxH C H)) := by
  refine specR_prologue (postSlot_locals _) (crm_none _ _) ?_
  unfold classReadMinor
  refine specR_piBinders coreWalkFuel dom _ (fun bs e => by simp) ?_
  refine specR_callNIH (C := ctxH C H) crmT fPiTele [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv crmD]
    (ptBody C fPiTele) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom] (by decide) rfl (by decide) hc.pt
    ⟨rfl, by simp +decide [sev, Env.get, crmParams, ctxEnv], trivial⟩
    (PostPT (ctxH C H) coreWalkFuel) (fun r w _ H' => r.1 < coreWalkFuel ∧
      ∃ ob, w = cellA C ob ∧ H'[ob]? = some (BitVec.ofNat 64 r.1) ∧ H'[ob + 1]? = some (Enc.idxW r.2))
    (fun r w s' st ⟨H', hp', hs, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (pt_spec C hok hc.pt coreWalkFuel (by decide) H s dom))
    (fun r w s1 H1 hp1 ⟨hrk, ob, hw, hc0, _⟩ => ?_)
  subst hw
  have hp1' : H <+: H1 := hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) crmN (vv crmT) ob _ hc0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  simp only [List.length_replicate]
  have hfuel : coreWalkFuel = 4000000000 := rfl
  refine specR_callNIH (C := ctxH C H1) crmQ fOpenFvars ofParams [vv crmN, vv crmD, vv crmDd] (ofBody C)
    [BitVec.ofNat 64 r.1, Enc.idxW dom, BitVec.ofNat 64 d] (by decide) rfl (by decide) hc.ofc
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv], trivial⟩
    (PostOF (ctxH C H1)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op r.1 dom d (by omega) (by omega) H1 (hp.trans hp1') s1))
    (fun o1 w s2 H2 hp2 ⟨hn2, hs2⟩ => ?_)
  have hp2' : H1 <+: H2 := hp2
  rcases o1 with _ | ⟨fvs, concl⟩
  · rw [hn2 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨q1, oq, rfl, hq1a, hq1b, hfvs⟩ := hs2 fvs concl rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN2 => ?_)
  have hq1l : q1 < H2.length := (List.getElem?_eq_some_iff.mp hq1a).1
  have hHN2' : H2.length ≤ C.HN := hHN2
  have hne1 : cellA C q1 ≠ 0 := cellA_ne0 C hok q1 (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H2) crmFv (vv crmQ) q1 _ hq1a (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) crmCc _ (q1 + 1) _ hq1b (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q1) ?_
  simp only
  refine specR_callNIM crmH fFvarHead fhParams [vv crmCc] fhBody [Enc.idxW concl] (by decide) rfl (by decide) hc.io.fh
    ⟨by simp +decide [sev, Env.get_cons], trivial⟩ (PostON (ctxH C H2)) (fun _ _ _ _ h => h.2.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fhParams _ rfl hlk) (fh_spec (ctxH C H2) hc.io.gf s2 concl))
    (fun o w s3 st ⟨hw, hb, _⟩ => ?_)
  subst hw
  rcases o with _ | p2
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have hp2b := hb p2 rfl
  have hne : BitVec.ofNat 64 (p2 + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI crmH _ (BitVec.ofNat 64 p2) (by decide)
    (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (p2 + 1) 1 (by omega) (by omega)) ?_
  simp only
  rw [classOfMotiveVar_eq]
  have hlw := ConPanqueque.T.Decl.nd_lt_iff p2 nP (by omega) (by omega)
  by_cases hle : nP ≤ p2
  swap
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_pos hle]
  refine specR_pureBind (((motPos.drop 0).findIdx? (· == p2 - nP)).map (· + 0)) ?_
  have hMp2 : BlkAt H2 pm (motPos.map (BitVec.ofNat 64)) := blkAt_mono hMp (hp1'.trans hp2')
  refine specR_callNIM crmC fFindIdx cmvParams [vv crmMp, .op .sub [vv crmH, vv crmP], .const 0, vv crmMn] cmvBody
    [cellA C pm, BitVec.ofNat 64 (p2 - nP), BitVec.ofNat 64 0, BitVec.ofNat 64 (List.map (BitVec.ofNat 64) motPos).length]
    (by decide) rfl (by decide) hc.io.cmv
    ⟨by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv]; exact word_sub_eq p2 nP hle (by omega), rfl,
      by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure (((motPos.drop 0).findIdx? (· == p2 - nP)).map (· + 0)) : AM (Option Nat)) s3 = .ok (a, s') ∧
      PostON (ctxH C H2) a w s' st) (fun _ _ _ _ h => h.2.2.2)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cmvParams _ rfl hlk) (by
      have := cmv_spec (σ := σ) C hok hc.io.cmv motPos (p2 - nP) pm H2 hMp2 hmp (by omega) _ 0 s3 rfl (by omega)
      simpa only [List.length_map] using this)))
    (fun a w s4 st ⟨hrun, hw, hb2, _⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs4⟩ := hrun
  subst hw; subst hs4
  rw [hra]
  rcases a with _ | c
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have hc63 := hb2 c rfl
  have hnc : BitVec.ofNat 64 (c + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnc)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  have hok2 := ctxOK_H hok H2
  refine specR_callNIH (C := ctxH C H2) crmA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv crmCc]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW concl] (by decide) rfl (by decide) hc.io.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H2)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
    (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H2) hok2 hc.io.gaa coreWalkFuel CV.coreWalkFuel_lt H2 concl s3))
    (fun args w s5 H5 hp5 ⟨oa, hw, hba⟩ => ?_)
  subst hw
  have hp5' : H2 <+: H5 := hp5
  refine UD.specR_heapLoadI' (C := ctxH C H5) crmK (vv crmA) oa _ hba.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hal := Big.blk_small0 (ctxOK_H hok H5) ht5.sr hba
  simp only [List.length_map] at hal
  rcases hrl : args.getLast? with _ | last
  · have hnil : args = [] := List.getLast?_eq_none_iff.mp hrl
    subst hnil
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have hne0 : args ≠ [] := by intro h; subst h; simp at hrl
  have hlen0 : 0 < args.length := List.length_pos_iff.mpr hne0
  have hK : BitVec.ofNat 64 args.length ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hK)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hlast : args[args.length - 1]'(by omega) = last := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hrl; simpa using hrl
  have hcl := hba.2 (args.length - 1) (by simp; omega)
  simp only [List.getElem_map, hlast] at hcl
  refine UD.specR_heapLoadI' (C := ctxH C H5) crmL _ (oa + 1 + (args.length - 1)) _ hcl (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C oa + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  simp only
  refine specR_callNIM crmHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv crmL]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW last] (by decide) rfl (by decide) hc.io.gf
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel last s5 = .ok (a, s') ∧ Post (ctxH C H5) s5 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H5) hc.io.gf coreWalkFuel last s5 CV.coreWalkFuel_lt t
        ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨_, hw, hsA, _⟩ => ?_)
  subst hw
  have hs' : s5 = s' := hsA.symm
  subst hs'
  refine Knot.specR_tagIteV crmHd hd 3 (by decide) (by decide) (by simp +decide [Env.get_cons]) (fun htc => ?_)
    (fun htc => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hd.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_hangI
  rw [ite_eq_left (show (hd.tag == ETag.const) = true by simp [htc, ETag.const])]
  unfold crmTail
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, crmParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv crmHd) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP hd (by simp) (by simp +decide [Env.get_cons, Env.get, crmParams, ctxEnv] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, crmParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨cn, us, rfl⟩ := UD.tagN_const h3
  have hvc : s5.store.viewConst hd = some (cn, us) := ConPanqueque.T.WC.viewConst_of_view (by rw [htc]; rfl) hv
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' crmCn (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cn) (by decide)
    (by simp [sev, Env.get_cons]) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW cn) [Enc.idxW us] []) ?_
  have hfvs5 : BlkAt H5 oq (fvs.map Enc.idxW) := blkAt_mono hfvs hp5'
  have hfl := Big.blk_small0 (ctxOK_H hok H5) ht5.sr hfvs5
  simp only [List.length_map] at hfl
  refine UD.specR_heapLoadI' (C := ctxH C H5) crmNf (vv crmFv) oq _ hfvs5.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN5 => ?_)
  have hHN5' : H5.length ≤ C.HN := hHN5
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H5) crmIb _ (2 * fvs.length + 1) (by omega) (by decide)
    (fun v => by
      simp +decide [sev, Env.get_cons, List.length_map]; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H6 ws hp6 hws hroom6 => ?_)
  have hp6' : H5 <+: H6 := hp6
  have hl6 : (H6 ++ ws).length = H6.length + (2 * fvs.length + 1) := by simp [hws]
  have hMp6 : BlkAt H6 pm (motPos.map (BitVec.ofNat 64)) := blkAt_mono hMp2 (hp5'.trans hp6')
  refine specR_callNIG (C := ctxH (ctxH C H5) (H6 ++ ws)) crmR fIhs fmiParams
    [vv crmFv, .const 0, vv crmNf, .op .add [vv crmIb, .const 8], .const 0, vv crmP, vv crmMp, vv crmMn, vv crmDd] fmiBody
    [cellA C oq, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, cellA C (H6.length + 1), BitVec.ofNat 64 0,
      BitVec.ofNat 64 nP, cellA C pm, BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d] (by decide) rfl (by decide) hc.ihs
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, List.length_map],
      by simp +decide [sev, Env.get_cons]; exact cellA_add8 C H6.length, rfl,
      by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crmParams, ctxEnv],
      trivial⟩
    (PostFMI C H6 (H6.length + 1) 0 fvs.length) (fun ys w _ H' => H6 <+: H' ∧ H6.length + 1 + 2 * fvs.length ≤ H'.length ∧
      w = BitVec.ofNat 64 (0 + ys.length) ∧ 0 + ys.length ≤ fvs.length ∧
      ∀ k (hk : k < ys.length), H'[H6.length + 1 + 2 * (0 + k)]? = some (BitVec.ofNat 64 ys[k].1) ∧
        H'[H6.length + 1 + 2 * (0 + k) + 1]? = some (BitVec.ofNat 64 ys[k].2))
    (fun ys w s' st ⟨H', hp', hl', hs', h1⟩ => ⟨H', ⟨hp', hl', h1⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmiParams _ rfl hlk) (by
      have := ihq_spec (σ := σ) C hok hc.ihs hc.io nP motPos pm d fvs oq (H6.length + 1) fvs.length H6
        (blkAt_mono hfvs5 hp6') hMp6 hmp hnP (by omega) (by omega) fvs.length 0 0 H6 (H6 ++ ws) s5 (by simp) (by omega)
        (List.prefix_refl _) (List.prefix_append _ _) (by omega) (by omega) (by omega)
      exact this))
    (fun ys w s6 H7 ⟨hp7, hl7, hw, hyl, hcells⟩ => ?_)
  subst hw
  refine specR_heapStoreI (ctxOK_H hok H7) (vv crmIb) (vv crmR) H6.length (by show _ < H7.length; omega)
    (BitVec.ofNat 64 ys.length) (by simp [sev, Env.get_cons]; rfl) (by simp +decide [sev, Env.get_cons]) ?_
  let H8 := H7.set H6.length (BitVec.ofNat 64 ys.length)
  have h68 : H6 <+: H8 := prefix_set hp7 (Nat.le_refl _) _
  have hl8 : H8.length = H7.length := by simp [H8]
  have hpr : PairsRep H8 H6.length ys := by
    refine ⟨List.getElem?_set_self (by omega), fun k hk => ?_⟩
    obtain ⟨h1, h2⟩ := hcells k hk
    simp only [Nat.zero_add] at h1 h2
    exact ⟨by rw [List.getElem?_set_ne (by omega)]; exact h1, by rw [List.getElem?_set_ne (by omega)]; exact h2⟩
  refine specR_alloc4I (ctxOK_H hok H8) crmW (.const 1) (.op .sub [vv crmC, .const 1]) (vv crmCn) (vv crmIb)
    1 (BitVec.ofNat 64 c) (Enc.idxW cn) (cellA C H6.length) (by decide) (fun _ => rfl)
    (fun _ => by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (c + 1) 1 (by omega) (by omega))
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons]; rfl)
    (fun H9 ws9 hp9 hws9 _ => ?_)
  obtain ⟨g0, g1, g2, g3⟩ := img4_get H9 ws9 1 (BitVec.ofNat 64 c) (Enc.idxW cn) (cellA C H6.length) hws9
  have h9 := img4_prefix H9 ws9 1 (BitVec.ofNat 64 c) (Enc.idxW cn) (cellA C H6.length) hws9
  have hp89 : H8 <+: H9 := hp9
  refine specR_returnI (vv crmW) (cellA C H9.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ?_)
  refine ⟨_, (((hp1'.trans hp2').trans hp5').trans hp6').trans (h68.trans (hp89.trans h9)), sr_of_eq ht.sr rfl rfl rfl rfl,
    .minor c cn ys, H9.length, rfl, rfl, g0, g1, g2, H6.length, g3, ?_⟩
  obtain ⟨hp0, hpk⟩ := hpr
  exact ⟨get_prefix hp0 (hp89.trans h9), fun k hk => ⟨get_prefix (hpk k hk).1 (hp89.trans h9),
    get_prefix (hpk k hk).2 (hp89.trans h9)⟩⟩

end

/-! ## `classNPcOf` -/

def mncM := ofString "mnc_m"
def mncX := ofString "mnc_x"
def mncI := ofString "mnc_i"
def mncN := ofString "mnc_n"
def mncP := ofString "mnc_p"
def mncC := ofString "mnc_c"
def mncY := ofString "mnc_y"
def mncR := ofString "mnc_r"
def fMemNameIn := ofString "memberNameIn"

def mncParams : List MlS := [mncM, mncX, mncI, mncN]
def mncLocals : List MlS := [mncP, mncC, mncY, mncR]

/-- Whether a member from `i` on is named `x`. -/
def mncBody : ProgHOL 64 := prologue mncLocals
  (.ite (.cmp .lower (vv mncI) (vv mncN))
    (.seq (.assign .local mncP (.load .one (.op .add [vv mncM, .op .add [.panop .mul [vv mncI, .const 8], .const 8]])))
    (.seq (.assign .local mncC (.load .one (vv mncP)))
    (.seq (.assign .local mncY (.load .one (vv mncC)))
    (.ite (.cmp .equal (vv mncY) (vv mncX)) (.return (.const 1))
      (.seq (.call (some (some (.local, mncR), none)) fMemNameIn [vv mncM, vv mncX, .op .add [vv mncI, .const 1], vv mncN])
        (.return (vv mncR)))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem mnc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mncLocals → (ctxEnv C ++ mncParams.zip vals).get x = none :=
  Knot.params_none C mncLocals mncParams vals (by decide) (by decide)

/-- **`memberNameIn`** from member `i`. -/
theorem mnc_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMemNameIn = some (mncParams.map (fun p => (p, ShapeHOL.one)), mncBody, .one))
    (ms : List MemberShape) (x : NIdx) (om : Nat) (H : List (BitVec 64)) (hM : PtrsRep C H om (MemberRep C H) ms)
    (hml : ms.length < 2 ^ 59) :
    ∀ f i (s : AState), ms.length - i = f → i ≤ ms.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (mncParams.zip [cellA C om, Enc.idxW x, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length]))
        mncBody s (pure (((ms.drop i).map (·.cvT.name)).contains x)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = ms.length := by omega
    subst hin
    refine specR_prologue (postB_locals _) (mnc_none _ _) ?_
    have hlw := nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mncParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < ms.length := by omega
    refine specR_prologue (postB_locals _) (mnc_none _ _) ?_
    have hlw := nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mncParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, List.map_cons, List.contains_cons]
    obtain ⟨omi, hmi, hrep⟩ := hM.2 i hin
    obtain ⟨⟨oc, hoc, hcv⟩, -⟩ := hrep
    obtain ⟨hnm, -, -⟩ := hcv
    refine UD.specR_heapLoadI' (C := ctxH C H) mncP _ (om + 1 + i) _ hmi (by decide)
      (by simp +decide [sev, Env.get, mncParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mncC (vv mncP) omi _ hoc (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mncY (vv mncC) oc _ hnm (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    by_cases he : ms[i].cvT.name = x
    · rw [he]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mncParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, Bool.true_or]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hw : Enc.idxW ms[i].cvT.name ≠ Enc.idxW x := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, mncParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    have hf' : (x == ms[i].cvT.name) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he e.symm
    rw [hf', Bool.false_or]
    refine specR_congr (m' := (pure (((ms.drop (i + 1)).map (·.cvT.name)).contains x) : AM Bool) >>= fun b => pure b)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H) mncR fMemNameIn mncParams [vv mncM, vv mncX, .op .add [vv mncI, .const 1], vv mncN]
      mncBody [cellA C om, Enc.idxW x, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mncParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mncParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mncParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, mncParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mncParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def cnpM := ofString "cnp_m"
def cnpN := ofString "cnp_n"
def cnpX := ofString "cnp_x"
def cnpK := ofString "cnp_k"
def cnpR := ofString "cnp_r"
def cnpW := ofString "cnp_w"
def cnpQ := ofString "cnp_q"
def cnpT := ofString "cnp_t"
def cnpV := ofString "cnp_v"
def fClassNPc := ofString "classNPcOf"

def cnpParams : List MlS := [cnpM, cnpN, cnpX]
def cnpLocals : List MlS := [cnpK, cnpR, cnpW, cnpQ, cnpT, cnpV]

def cnpBody (C : Ctx) : ProgHOL 64 := prologue cnpLocals
  (.seq (.assign .local cnpK (.load .one (vv cnpM)))
  (.seq (.call (some (some (.local, cnpR), none)) fMemNameIn [vv cnpM, vv cnpX, .const 0, vv cnpK])
  (.ite (.cmp .equal (vv cnpR) (.const 0))
    (envFindP C cnpW (vv cnpX)
      (.ite (.cmp .equal (vv cnpW) (.const 0)) (.return (.const 0))
      (.seq (.assign .local cnpQ (.op .sub [vv cnpW, .const 1]))
      (.seq (.assign .local cnpT (.load .one (vv cnpQ)))
      (.ite (.cmp .equal (vv cnpT) (.const 3))
        (.seq (.assign .local cnpV (.load .one (.op .add [vv cnpQ, .const 48]))) (.return (vv cnpV)))
        (.return (.const 0)))))))
    (.return (vv cnpN)))))

section
variable {σ : Type}

theorem cnp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnpLocals → (ctxEnv C ++ cnpParams.zip vals).get x = none :=
  Knot.params_none C cnpLocals cnpParams vals (by decide) (by decide)

/-- **`classNPcOf`** at the context's environment. -/
theorem cnp_spec (C : Ctx) (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hmn : C.code.lookup fMemNameIn = some (mncParams.map (fun p => (p, ShapeHOL.one)), mncBody, .one))
    (p : BlockShape) (om : Nat) (H : List (BitVec 64)) (hM : PtrsRep C H om (MemberRep C H) p.members)
    (hml : p.members.length < 2 ^ 59) (hnP : p.nP < 2 ^ 63) (s : AState) (x : NIdx) :
    SpecR (σ := σ) (Pre (ctxH C H) s (cnpParams.zip [cellA C om, BitVec.ofNat 64 p.nP, Enc.idxW x])) (cnpBody C) s
      (pure (classNPcOf p C.fe x)) (PostN (ctxH C H)) := by
  refine specR_prologue (postN_locals _) (cnp_none _ _) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) cnpK (vv cnpM) om _ hM.1 (by decide)
    (by simp +decide [sev, Env.get, cnpParams, ctxEnv]; rfl) ?_
  refine specR_pureBind (((p.members.drop 0).map (·.cvT.name)).contains x) ?_
  refine specR_callNIH (C := ctxH C H) cnpR fMemNameIn mncParams [vv cnpM, vv cnpX, .const 0, vv cnpK] mncBody
    [cellA C om, Enc.idxW x, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide) hmn
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cnpParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cnpParams, ctxEnv],
      rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => (pure (((p.members.drop 0).map (·.cvT.name)).contains x) : AM Bool) s = .ok (a, s') ∧
      PostB (ctxH C H) a w s' st)
    (fun a w s' _ => (pure (((p.members.drop 0).map (·.cvT.name)).contains x) : AM Bool) s = .ok (a, s') ∧ w = boolW a)
    (fun a w s' st ⟨hrun, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hrun, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mncParams _ rfl hlk)
      (mnc_spec C hok hmn p.members x om H hM hml _ 0 s rfl (by omega))))
    (fun a w s1 H1 hp1 ⟨hrun, hw⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs1⟩ := hrun
  subst hw; subst hs1
  have hp1' : H <+: H1 := hp1
  simp only [List.drop_zero] at hra
  unfold classNPcOf
  by_cases hmem : (p.members.map (·.cvT.name)).contains x = true
  · have ha : a = true := by rw [← hra]; exact hmem
    subst ha
    have hmem' : p.memberNames.contains x = true := by simpa [BlockShape.memberNames] using hmem
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_pos hmem']
    exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons, Env.get, cnpParams, ctxEnv])
      (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hf : a = false := by rw [← hra]; simpa using hmem
  subst hf
  have hmem' : ¬ p.memberNames.contains x = true := by simpa [BlockShape.memberNames] using hmem
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  rw [if_neg hmem']
  have hok1 := ctxOK_H (ctxOK_H hok H) H1
  refine specR_envFindI hok1 hcodeG hcodeP cnpW (vv cnpX) x (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cnpParams, ctxEnv]) (by simp +decide [Env.get, ctxEnv]; rfl) ?_
  have hrel := find_rel hok1 x
  revert hrel
  show (match C.fe.find? x with
    | none => C.envM[x]? = none
    | some ci => ∃ o, C.envM[x]? = some (ecell C o) ∧ CIE C.EB C.EH o ci) → _
  rcases hfind : C.fe.find? x with _ | ci
  · intro hrel; simp only at hrel
    rw [show (ctxH (ctxH C H) H1).envM = C.envM from rfl, hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩))
      (fun h => absurd h (by decide))
  intro ⟨o, hm, hci⟩
  rw [show (ctxH (ctxH C H) H1).envM = C.envM from rfl, hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI cnpQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  refine specR_envLoadI (C := ctxH C H1) cnpT (vv cnpQ) o _ (by decide) (by simp; rfl) (UD.cie_tag hci) ?_
  cases ci
  case indInfo cvT caps =>
    obtain ⟨-, -, -, -, ⟨hnpW, -⟩, -⟩ := hci
    dsimp only
    refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_envLoadI (C := ctxH C H1) cnpV _ (o + 6) _ (by decide)
      (by simp +decide [sev, Env.get_cons]; exact ecell_addk C o 6) hnpW ?_
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  all_goals
    dsimp only
    refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## A telescope's last binder domain (`(piBinders fuel h).1.getLast?`) -/

/-- The walk the port runs: the last domain seen, starting from `acc`. -/
def lastDomGo : Nat → EIdx → Option EIdx → AM (Option EIdx)
  | 0, _, _ => fail (.internal "fuel exhausted: lastDom")
  | fuel + 1, h, acc => do
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (ty, b) => lastDomGo fuel b (some ty)
    else pure acc

theorem lastDomGo_piBinders (fuel : Nat) : ∀ (h : EIdx) (acc : Option EIdx) (s : AState) (o : Option EIdx) (s' : AState),
    lastDomGo fuel h acc s = .ok (o, s') →
      ∃ bs e, piBinders fuel h s = .ok ((bs, e), s') ∧ o = (bs.getLast?).or acc := by
  induction fuel with
  | zero => intro h acc s o s' hr; rw [lastDomGo] at hr; exact (WC.fail_ok_inv hr).elim
  | succ fuel ih =>
    intro h acc s o s' hr
    rw [lastDomGo] at hr; rw [piBinders]
    by_cases ht : (h.tag == ETag.forallE) = true
    · simp only [ht, ite_true] at hr ⊢
      obtain ⟨v, s1, h1, h2⟩ := WC.bind_ok_inv hr
      rcases v with _ | ⟨ty, b⟩
      · exact (WC.failDanglingE_ok_inv h2).elim
      obtain ⟨bs, e, hb, ho⟩ := ih b (some ty) s1 o s' h2
      refine ⟨ty :: bs, e, ?_, ?_⟩
      · simp only [bind, StateT.bind] at h1 ⊢
        rw [h1]
        simp only [Except.bind, StateT.bind, hb, StateT.pure, pure, Except.pure]; rfl
      · rw [ho]; cases bs <;> simp [List.getLast?_cons]
    · simp only [ht, Bool.false_eq_true, ite_false] at hr ⊢
      obtain ⟨e1, e2⟩ := WC.pure_ok_inv hr
      subst e1; subst s'
      exact ⟨[], h, rfl, by simp⟩

section
variable {σ : Type}

/-- `piBinders` read through `lastDomGo`, when the continuation looks only at the last domain. -/
theorem specR_piBindersLast {β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState}
    {R : β → BitVec 64 → AState → PState σ → Prop} (fuel : Nat) (h : EIdx) (k : List EIdx × EIdx → AM β)
    (hk : ∀ bs e bs' e', bs.getLast? = bs'.getLast? → k (bs, e) = k (bs', e'))
    (hs : SpecR P c s (lastDomGo fuel h none >>= fun o => k (o.toList, default)) R) :
    SpecR P c s (piBinders fuel h >>= k) R := by
  refine specR_okMono (fun a s' hrun => ?_) hs
  obtain ⟨o, s1, h1, h2⟩ := WC.bind_ok_inv hrun
  obtain ⟨bs, e, hb, ho⟩ := lastDomGo_piBinders fuel h none s o s1 h1
  simp only [bind, StateT.bind, hb]
  show k (bs, e) s1 = _
  rw [hk bs e o.toList default (by rw [ho]; cases bs.getLast? <;> simp)]; exact h2

end

def ldmA := ofString "ldm_a"
def fLastDom := ofString "lastDom"

def ldmCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
    (.ite (tagIsE pH 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
        (.seq (.assign .local lA1 (.load .one (vv lRp)))
        (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.call (some (some (.local, ExS.lY), none)) fLastDom
            [.op .sub [vv pFu, .const 1], vv lA2, .op .add [vv lA1, .const 1]])
          (.return (vv ExS.lY))))))))
      (.return (vv ldmA)))

def ldmBody : ProgHOL 64 := prologue inst1Locals ldmCore

section
variable {σ : Type}

theorem ldm_none (va vb vc : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pFu, va), (pH, vb), (ldmA, vc)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- An optional handle as `optWG idxW`; the heap kept. -/
def PostOE (C : Ctx) (o : Option EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = optWG Enc.idxW o ∧ SR C s' st

theorem postOE_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOE C a w s' st → PostOE C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

theorem ldm_spec (C : Ctx) (hcode : C.code.lookup fLastDom = some ([(pFu, .one), (pH, .one), (ldmA, .one)], ldmBody, .one)) :
    ∀ n, n < 2 ^ 64 → ∀ (h : EIdx) (acc : Option EIdx) (s : AState),
      SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h), (ldmA, optWG Enc.idxW acc)]) ldmBody s
        (lastDomGo n h acc) (PostOE C) := by
  intro n
  induction n with
  | zero =>
    intro _ h acc s
    refine specR_prologue (postOE_locals C) (ldm_none _ _ _ C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf h acc s
    refine specR_prologue (postOE_locals C) (ldm_none _ _ _ C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    rw [lastDomGo]
    refine specR_iteI (tagIsE pH 6) (tagW h 6) ?_ (by rw [tagW_iff h 6 (by decide) (by decide)]; simp [ETag.forallE])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h6 : h.tag = 6 := by simpa [ETag.forallE] using hb
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h (Or.inr h6) s vw hvw)
        (by simp) (by simp +decide) (by simp +decide [ctxEnv]) (by decide) (fun vw P htg hsh => ?_)
      cases vw with
      | forallE ty b =>
        refine specR_loadI' lA1 _ P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide [sev]) (by simp)
          (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
        refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
          (wordsAt_mem1 _ _ _ _ _) ?_
        refine specR_congr (m' := lastDomGo n b (some ty) >>= fun a => pure a) (by simp [projBind]) ?_
        refine specR_callNIM ExS.lY fLastDom [pFu, pH, ldmA] [.op .sub [vv pFu, .const 1], vv lA2, .op .add [vv lA1, .const 1]]
          ldmBody [BitVec.ofNat 64 n, Enc.idxW b, optWG Enc.idxW (some ty)] (by decide) rfl (by decide) hcode
          ⟨by simp +decide [sev, ctxEnv]; exact ofNat_succ_sub_one n, by simp +decide [sev],
            by simp +decide [sev, optWG], trivial⟩
          (PostOE C) (fun _ _ _ _ hp => hp.2)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH, ldmA] _ rfl hlk) (ih (by omega) b (some ty) s))
          (fun a w s' st ⟨hw, _⟩ => ?_)
        subst hw
        exact specR_returnI (vv ExS.lY) _ (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      | lam ty b => simp [ENodeView.tagN, h6] at htg
      | _ => simp [ENodeView.tagN, h6] at htg
    · exact specR_returnI (vv ldmA) _ (by simp +decide [ctxEnv])
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classReadSlot` -/

theorem mapM_dropVars0 (l : List EIdx) : l.mapM (exprDropVars 0) = pure l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapM_cons, ih]; simp [exprDropVars]

def cslD := ofString "csl_d"
def cslP := ofString "csl_p"
def cslMp := ofString "csl_mp"
def cslMn := ofString "csl_mn"
def cslDd := ofString "csl_dd"
def cslM := ofString "csl_m"
def cslNp := ofString "csl_np"
def cslR := ofString "csl_r"
def cslLd := ofString "csl_ld"
def cslMd := ofString "csl_md"
def cslHd := ofString "csl_hd"
def cslIn := ofString "csl_in"
def cslUs := ofString "csl_us"
def cslA := ofString "csl_a"
def cslK := ofString "csl_k"
def cslQ := ofString "csl_q"
def cslMm := ofString "csl_mm"
def cslDs := ofString "csl_ds"
def cslW := ofString "csl_w"
def fClassReadSlot := ofString "classReadSlot"

def cslParams : List MlS := [cslD, cslP, cslMp, cslMn, cslDd, cslM, cslNp]
def cslLocals : List MlS := gaaLocals ++ [cslR, cslLd, cslMd, cslHd, cslIn, cslUs, cslA, cslK, cslQ, cslMm, cslDs, cslW]

def cslTake (C : Ctx) (x : MlS) : ProgHOL 64 :=
  .seq (.call (some (some (.local, cslDs), none)) fDropMap [vv cslA, .const 0, vv x, .const 0])
    (alloc4 C cslW (.const 0) (vv cslIn) (vv cslUs) (vv cslDs) (.return (vv cslW)))

def cslMotive (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, cslLd), none)) fLastDom [.const (BitVec.ofNat 64 coreWalkFuel), vv cslD, .const 0])
  (.ite (.cmp .equal (vv cslLd) (.const 0)) hang
  (.seq (.assign .local cslMd (.op .sub [vv cslLd, .const 1]))
  (.seq (.call (some (some (.local, cslHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv cslMd])
  (.ite (tagIsE cslHd 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv cslHd)) (.seq eViewP
    (.seq (.assign .local cslIn (.load .one (vv lRp)))
    (.seq (.assign .local cslUs (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.call (some (some (.local, cslA), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv cslMd])
    (.seq (.call (some (some (.local, cslQ), none)) fClassNPc [vv cslM, vv cslNp, vv cslIn])
    (.seq (.assign .local cslK (.load .one (vv cslA)))
    (.ite (.cmp .lower (vv cslQ) (vv cslK)) (cslTake C cslQ) (cslTake C cslK))))))))))
    hang))))

def cslBody (C : Ctx) : ProgHOL 64 := prologue cslLocals
  (.seq (.call (some (some (.local, cslR), none)) ExM.fPir [.const (BitVec.ofNat 64 coreWalkFuel), vv cslD])
  (.ite (tagIsE cslR 2) (cslMotive C)
    (.seq (.call (some (some (.local, cslW), none)) fClassReadMinor [vv cslD, vv cslP, vv cslMp, vv cslMn, vv cslDd])
      (.return (vv cslW)))))

/-- The code `classReadSlot` runs. -/
structure CSLCodes (C : Ctx) : Prop where
  self : C.code.lookup fClassReadSlot = some (cslParams.map (fun p => (p, ShapeHOL.one)), cslBody C, .one)
  crm : CRMCodes C
  crmc : C.code.lookup fClassReadMinor = some (crmParams.map (fun p => (p, ShapeHOL.one)), crmBody C, .one)
  ldm : C.code.lookup fLastDom = some ([(pFu, .one), (pH, .one), (ldmA, .one)], ldmBody, .one)
  cnp : C.code.lookup fClassNPc = some (cnpParams.map (fun p => (p, ShapeHOL.one)), cnpBody C, .one)
  mnc : C.code.lookup fMemNameIn = some (mncParams.map (fun p => (p, ShapeHOL.one)), mncBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  dm : C.code.lookup fDropMap = some (dmParams.map (fun p => (p, ShapeHOL.one)), dmBody C, .one)
  dv : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  i1 : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  ic : Codes C (ExI.body C)

section
variable {σ : Type}

theorem csl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cslLocals → (ctxEnv C ++ cslParams.zip vals).get x = none :=
  Knot.params_none C cslLocals cslParams vals (by decide) (by decide)


theorem classNPcOf_lt {C : Ctx} (hok : CtxOK C) (p : BlockShape) (hpnP : p.nP < 2 ^ 63) (x : NIdx) :
    classNPcOf p C.fe x < 2 ^ 63 := by
  unfold classNPcOf
  split
  · exact hpnP
  · have hrel := find_rel hok x
    revert hrel
    rcases C.fe.find? x with _ | ci
    · intro _; simp
    · intro ⟨o, _, hci⟩
      cases ci with
      | indInfo cv caps => obtain ⟨-, -, -, -, ⟨_, h⟩, -⟩ := hci; simpa using h
      | _ => simp

set_option maxHeartbeats 8000000 in
/-- **`classReadSlot`** (off-shape halts). -/
theorem csl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CSLCodes C)
    (p : BlockShape) (om : Nat) (np : Nat) (motPos : List Nat) (pm d : Nat) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hM : PtrsRep C H om (MemberRep C H) p.members) (hml : p.members.length < 2 ^ 59) (hpnP : p.nP < 2 ^ 63)
    (hMp : BlkAt H pm (motPos.map (BitVec.ofNat 64))) (hmp : ∀ x ∈ motPos, x < 2 ^ 63) (hnP : np < 2 ^ 63)
    (hd : d < 2 ^ 62) (s : AState) (dom : EIdx) :
    SpecR (σ := σ) (Pre (ctxH C H) s (cslParams.zip [Enc.idxW dom, BitVec.ofNat 64 np, cellA C pm,
      BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d, cellA C om, BitVec.ofNat 64 p.nP])) (cslBody C) s
      (classReadSlot p C.fe np motPos d dom) (PostSlot (ctxH C H)) := by
  refine specR_prologue (postSlot_locals _) (csl_none _ _) ?_
  unfold classReadSlot
  refine ILP.callE_spec (C := ctxH C H) cslR ExM.fPir [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cslD]
    ExM.pirBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom] (by decide) rfl (by decide) hc.crm.io.pir
    ⟨rfl, by simp +decide [sev, Env.get, cslParams, ctxEnv], trivial⟩
    (ExM.pir_spec (ctxH C H) hc.crm.io.pir coreWalkFuel CV.coreWalkFuel_lt dom s) (fun r s1 => ?_)
  refine Knot.specR_tagIteV cslR r 2 (by decide) (by decide) (by simp +decide [Env.get_cons]) (fun hts => ?_)
    (fun hts => ?_)
  swap
  · rw [ite_eq_right (show ¬ (r.tag == ETag.sort) = true by simpa [ETag.sort] using hts)]
    refine specR_congr (m' := classReadMinor np motPos d dom >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) cslW fClassReadMinor crmParams [vv cslD, vv cslP, vv cslMp, vv cslMn, vv cslDd]
      (crmBody C) [Enc.idxW dom, BitVec.ofNat 64 np, cellA C pm, BitVec.ofNat 64 motPos.length, BitVec.ofNat 64 d]
      (by decide) rfl (by decide) hc.crmc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv], trivial⟩
      (PostSlot (ctxH C H)) (fun o w _ H' => ∃ sl os, o = some sl ∧ w = cellA C os ∧ SlotRep C H' os sl)
      (fun o w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crmParams _ rfl hlk)
        (crm_spec ra C hok hc.crm np motPos pm d H hp hMp hmp hnP hd s1 dom))
      (fun o w s2 H2 hp2 ⟨sl, os, ho, hw, hsl⟩ => ?_)
    subst hw
    exact specR_returnI _ (cellA C os) (by simp [Env.get]) (fun t ht => ⟨H2, hp2, sr_of_eq ht.sr rfl rfl rfl rfl, sl, os, ho, rfl, hsl⟩)
  rw [ite_eq_left (show (r.tag == ETag.sort) = true by simp [hts, ETag.sort])]
  unfold cslMotive
  refine specR_piBindersLast coreWalkFuel dom _ (fun bs e bs' e' h => by simp only [h]) ?_
  refine specR_callNIM cslLd fLastDom [pFu, pH, ldmA] [.const (BitVec.ofNat 64 coreWalkFuel), vv cslD, .const 0]
    ldmBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom, optWG Enc.idxW none] (by decide) rfl (by decide) hc.ldm
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv], by simp [optWG]; rfl, trivial⟩
    (PostOE (ctxH C H)) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH, ldmA] _ rfl hlk)
      (ldm_spec (ctxH C H) hc.ldm coreWalkFuel CV.coreWalkFuel_lt dom none s1))
    (fun o w s2 st ⟨hw, _⟩ => ?_)
  subst hw
  rcases o with _ | md
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have hmd1 : Enc.idxW md + 1 ≠ 0#64 := by
    intro e; have := congrArg BitVec.toNat e
    have hlt : (Enc.idxW md).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact md.word.toNat_lt
    simp [BitVec.toNat_add] at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hmd1)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI cslMd _ (Enc.idxW md) (by decide) (by simp +decide [sev, Env.get_cons, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  simp only [Option.toList_some, List.getLast?_singleton]
  refine specR_callNIM cslHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cslMd]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW md] (by decide) rfl (by decide) hc.crm.io.gf
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel md s2 = .ok (a, s') ∧ Post (ctxH C H) s2 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H) hc.crm.io.gf coreWalkFuel md s2 CV.coreWalkFuel_lt t
        ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨_, hw, hsA, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hsA.symm
  subst hs'
  refine Knot.specR_tagIteV cslHd hd 3 (by decide) (by decide) (by simp +decide [Env.get_cons]) (fun htc => ?_)
    (fun htc => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hd.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_hangI
  rw [ite_eq_left (show (hd.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, cslParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv cslHd) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP hd (by simp) (by simp +decide [Env.get_cons, Env.get, cslParams, ctxEnv] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, cslParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨iName, us, rfl⟩ := UD.tagN_const h3
  have hvc : s2.store.viewConst hd = some (iName, us) := ConPanqueque.T.WC.viewConst_of_view (by rw [htc]; rfl) hv
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' cslIn (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW iName) (by decide)
    (by simp [sev, Env.get_cons]) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW iName) [Enc.idxW us] []) ?_
  refine specR_loadI' cslUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW iName) (Enc.idxW us) [] []) ?_
  have hokH := ctxOK_H hok H
  refine specR_callNIH (C := ctxH C H) cslA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cslMd]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW md] (by decide) rfl (by decide) hc.crm.io.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
    (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H) hokH hc.crm.io.gaa coreWalkFuel CV.coreWalkFuel_lt H md s2))
    (fun args w s3 H3 hp3 ⟨oa, hw, hba⟩ => ?_)
  subst hw
  have hp3' : H <+: H3 := hp3
  refine specR_atEntry fun t3 ht3 => ?_
  have hal := Big.blk_small0 (ctxOK_H hok H3) ht3.sr hba
  simp only [List.length_map] at hal
  -- the class's parameter count
  refine specR_pureBind (classNPcOf p C.fe iName) ?_
  have hM3 : PtrsRep C H3 om (MemberRep C H3) p.members := ptrsRep_mono hp3' (fun _ _ h => memberRep_mono hp3' h) hM
  refine specR_callNIH (C := ctxH C H3) cslQ fClassNPc cnpParams [vv cslM, vv cslNp, vv cslIn] (cnpBody C)
    [cellA C om, BitVec.ofNat 64 p.nP, Enc.idxW iName] (by decide) rfl (by decide) hc.cnp
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cslParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => (pure (classNPcOf p C.fe iName) : AM Nat) s3 = .ok (a, s') ∧ PostN (ctxH C H3) a w s' st)
    (fun a w s' _ => (pure (classNPcOf p C.fe iName) : AM Nat) s3 = .ok (a, s') ∧ w = BitVec.ofNat 64 a)
    (fun a w s' st ⟨hrun, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hrun, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cnpParams _ rfl hlk)
      (cnp_spec C hok hc.mg hc.mp hc.mnc p om H3 hM3 hml hpnP s3 iName)))
    (fun a w s4 H4 hp4 ⟨hrun, hw⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs4⟩ := hrun
  subst hw; subst hs4; subst hra
  have hp4' : H3 <+: H4 := hp4
  have hba4 : BlkAt H4 oa (args.map Enc.idxW) := blkAt_mono hba hp4'
  refine UD.specR_heapLoadI' (C := ctxH C H4) cslK (vv cslA) oa _ hba4.1 (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
  have htk : ∀ (Γ : Env) (M : Mem) (x : MlS) (m : Nat), x ∈ ctxLocals ++ cslLocals → m ≤ args.length →
      args.take m = args.take (classNPcOf p C.fe iName) →
      Γ.get cslA = some (cellA C oa) → Γ.get x = some (BitVec.ofNat 64 m) → Γ.get cslIn = some (Enc.idxW iName) →
      Γ.get cslUs = some (Enc.idxW us) → x ≠ cslDs → x ≠ cslW →
      SpecR (σ := σ) (Inv (ctxH C H4) s3 Γ M (ctxLocals ++ cslLocals)) (cslTake C x) s3
        (pure (some (ClassSlot.motive ⟨iName, us, args.take (classNPcOf p C.fe iName)⟩))) (PostSlot (ctxH C H)) := by
    intro Γ M x m hx hm ht gA gx gI gU hxd hxw
    unfold cslTake
    refine specR_congr (m' := ((args.take m).drop 0).mapM (exprDropVars 0) >>= fun ds =>
      pure (some (ClassSlot.motive ⟨iName, us, ds⟩))) (by rw [List.drop_zero, mapM_dropVars0, pure_bind, ht]) ?_
    refine specR_callNIH (C := ctxH C H4) cslDs fDropMap dmParams [vv cslA, .const 0, vv x, .const 0] (dmBody C)
      [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 m, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.dm
      ⟨gA, rfl, gx, rfl, trivial⟩
      (PostA (ctxH C H4)) (fun a w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW))
      (fun a w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dmParams _ rfl hlk)
        (dm_spec ra C hok hc.dm hc.dv hc.srt hc.i1 hc.ic args oa m 0 hm (by omega) (by decide) _ 0 H4 s3
          ((hp.trans hp3').trans hp4') hba4 rfl (by omega)))
      (fun ds w s5 H5 hp5 ⟨od, hw, hbd⟩ => ?_)
    subst hw
    have hp5' : H4 <+: H5 := hp5
    refine specR_alloc4I (ctxOK_H hok H5) cslW (.const 0) (vv cslIn) (vv cslUs) (vv cslDs)
      0 (Enc.idxW iName) (Enc.idxW us) (cellA C od) (by decide) (fun _ => rfl)
      (fun _ => by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gI)
      (fun _ => by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gU)
      (fun _ => by simp +decide [sev, Env.get_cons])
      (fun H6 ws6 hp6 hws6 _ => ?_)
    obtain ⟨g0, g1, g2, g3⟩ := img4_get H6 ws6 0 (Enc.idxW iName) (Enc.idxW us) (cellA C od) hws6
    have h6 := img4_prefix H6 ws6 0 (Enc.idxW iName) (Enc.idxW us) (cellA C od) hws6
    have hp56 : H5 <+: H6 := hp6
    refine specR_returnI (vv cslW) (cellA C H6.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ?_)
    exact ⟨_, ((hp3'.trans hp4').trans hp5').trans (hp56.trans h6), sr_of_eq ht.sr rfl rfl rfl rfl,
      .motive ⟨iName, us, ds⟩, H6.length, rfl, rfl, g0, g1, g2, od, g3, blkAt_mono hbd (hp56.trans h6)⟩
  have hcn := classNPcOf_lt hok p hpnP iName
  have hlw := ConPanqueque.T.Decl.nd_lt_iff (classNPcOf p C.fe iName) args.length (by omega) (by omega)
  by_cases hlt : classNPcOf p C.fe iName < args.length
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hlt])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact htk _ _ cslQ _ (by decide) (by omega) rfl (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (by decide) (by decide)
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
      (fun h => absurd rfl h) (fun _ => ?_)
    exact htk _ _ cslK args.length (by decide) (Nat.le_refl _)
      (by rw [List.take_of_length_le (Nat.le_refl _), List.take_of_length_le (by omega)])
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
      (by simp +decide [Env.get_cons]) (by decide) (by decide)

end

/-! ## `classReadSlots` -/

theorem slotRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {sl : ClassSlot}
    (h : SlotRep C H o sl) : SlotRep C H' o sl := by
  cases sl with
  | motive k =>
    obtain ⟨a, b, c, od, d, e⟩ := h
    exact ⟨get_prefix a hp, get_prefix b hp, get_prefix c hp, od, get_prefix d hp, blkAt_mono e hp⟩
  | minor c cn ihs =>
    obtain ⟨a, b, d, oi, e, f0, f1⟩ := h
    exact ⟨get_prefix a hp, get_prefix b hp, get_prefix d hp, oi, get_prefix e hp, get_prefix f0 hp,
      fun k hk => ⟨get_prefix (f1 k hk).1 hp, get_prefix (f1 k hk).2 hp⟩⟩

/-- A block of slot pointers. -/
def SlotBlk (C : Ctx) (H : List (BitVec 64)) (o : Nat) (sls : List ClassSlot) : Prop :=
  ∃ ps : List Nat, ps.length = sls.length ∧ BlkAt H o (ps.map (cellA C)) ∧
    ∀ k (hk : k < sls.length), ∃ op, ps[k]? = some op ∧ SlotRep C H op sls[k]

theorem slotBlk_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {sls : List ClassSlot}
    (h : SlotBlk C H o sls) : SlotBlk C H' o sls :=
  let ⟨ps, hl, hb, hr⟩ := h
  ⟨ps, hl, blkAt_mono hb hp, fun k hk => let ⟨op, h1, h2⟩ := hr k hk; ⟨op, h1, slotRep_mono hp h2⟩⟩

/-- The slots' answer: `some`, as a block of slot records. -/
def PostSlots (C : Ctx) (o : Option (List ClassSlot)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ sls ob, o = some sls ∧ w = cellA C ob ∧ SlotBlk C H' ob sls

theorem postSlots_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSlots (σ := σ) C a w s' st → PostSlots C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

def slsE := ofString "sls_e"
def slsN := ofString "sls_n"
def slsDd := ofString "sls_dd"
def slsMp := ofString "sls_mp"
def slsP := ofString "sls_p"
def slsM := ofString "sls_m"
def slsNp := ofString "sls_np"
def slsDm := ofString "sls_dm"
def slsBd := ofString "sls_bd"
def slsMn := ofString "sls_mn"
def slsS := ofString "sls_s"
def slsT := ofString "sls_t"
def slsMq := ofString "sls_mq"
def slsFv := ofString "sls_fv"
def slsB2 := ofString "sls_b2"
def fClassReadSlots := ofString "classReadSlots"

def slsParams : List MlS := [slsE, slsN, slsDd, slsMp, slsP, slsM, slsNp]
def slsLocals : List MlS := gaaLocals ++ [slsDm, slsBd, slsMn, slsS, slsT, slsMq, slsFv, slsB2]

/-- After the slot: open the binder, read the rest at motive positions `mp`, prepend the slot. -/
def slsRest (C : Ctx) (mp : MlS) : ProgHOL 64 :=
  .seq (.call (some (some (.local, slsFv), none)) fInternFVar [vv slsDm, vv slsDd])
  (.seq (.call (some (some (.local, slsB2), none)) fInst1F
      [.const (BitVec.ofNat 64 coreWalkFuel), vv slsBd, vv slsFv, .const 0])
  (.seq (.call (some (some (.local, ExS.lY), none)) fClassReadSlots
      [vv slsB2, .op .sub [vv slsN, .const 1], .op .add [vv slsDd, .const 1], vv mp, vv slsP, vv slsM, vv slsNp])
    (prependP C slsS)))

def slsBody (C : Ctx) : ProgHOL 64 := prologue slsLocals
  (.ite (.cmp .equal (vv slsN) (.const 0)) (alloc1 C lW (.const 0) (.return (vv lW)))
  (.ite (tagIsE slsE 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv slsE)) (.seq eViewP
    (.seq (.assign .local slsDm (.load .one (vv lRp)))
    (.seq (.assign .local slsBd (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local slsMn (.load .one (vv slsMp)))
    (.seq (.call (some (some (.local, slsS), none)) fClassReadSlot
        [vv slsDm, vv slsP, vv slsMp, vv slsMn, vv slsDd, vv slsM, vv slsNp])
    (.seq (.assign .local slsT (.load .one (vv slsS)))
    (.ite (.cmp .equal (vv slsT) (.const 0))
      (.seq (.call (some (some (.local, slsMq), none)) ExPre.fAppend [vv slsMp, .op .sub [vv slsDd, vv slsP]])
        (slsRest C slsMq))
      (slsRest C slsMp))))))))))
    hang))

/-- The code `classReadSlots` runs. -/
structure SLSCodes (C : Ctx) : Prop where
  self : C.code.lookup fClassReadSlots = some (slsParams.map (fun p => (p, ShapeHOL.one)), slsBody C, .one)
  csl : CSLCodes C
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)

section
variable {σ : Type}

theorem sls_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ slsLocals → (ctxEnv C ++ slsParams.zip vals).get x = none :=
  Knot.params_none C slsLocals slsParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`classReadSlots`** (off-shape halts). -/
theorem sls_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : SLSCodes C)
    (p : BlockShape) (om np : Nat) (hml : p.members.length < 2 ^ 59) (hpnP : p.nP < 2 ^ 63) (hnP : np < 2 ^ 63) :
    ∀ n (motPos : List Nat) (pm d : Nat) (H : List (BitVec 64)) (s : AState) (e : EIdx), C.H <+: H →
      PtrsRep C H om (MemberRep C H) p.members → BlkAt H pm (motPos.map (BitVec.ofNat 64)) →
      (∀ x ∈ motPos, x < 2 ^ 63) → np ≤ d → d + n < 2 ^ 62 →
      SpecR (σ := σ) (Pre (ctxH C H) s (slsParams.zip [Enc.idxW e, BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C pm,
        BitVec.ofNat 64 np, cellA C om, BitVec.ofNat 64 p.nP])) (slsBody C) s
        (classReadSlots p C.fe np n motPos d e) (PostSlots (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro motPos pm d H s e hp hM hMp hmp hdn hdb
    refine specR_prologue (postSlots_locals _) (sls_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, slsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [classReadSlots]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, hp2.trans hpr, sr_of_eq ht.sr rfl rfl rfl rfl,
      [], H2.length, rfl, rfl, [], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, fun k hk => absurd hk (by simp)⟩)
  | succ n ih =>
    intro motPos pm d H s e hp hM hMp hmp hdn hdb
    refine specR_prologue (postSlots_locals _) (sls_none _ _) ?_
    have hn0 : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by intro e'; have := congrArg BitVec.toNat e'; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, slsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hn0])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [classReadSlots]
    refine Knot.specR_tagIteV slsE e 6 (by decide) (by decide) (by simp +decide [Env.get, slsParams, ctxEnv])
      (fun ht => ?_) (fun ht => ?_)
    swap
    · rw [ite_eq_right (show ¬ (e.tag == ETag.forallE) = true by simpa [ETag.forallE] using ht)]
      exact specR_hangI
    rw [ite_eq_left (show (e.tag == ETag.forallE) = true by simp [ht, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, slsParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv slsE) (Enc.idxW e) (by decide) (by simp +decide [Env.get_cons, Env.get, slsParams, ctxEnv]) ?_
    refine specR_viewXI ConRon.Arena.viewBind projBind e (fun vw hvw => viewBind_run e (Or.inr ht) s vw hvw)
      (by simp) (by simp +decide <;> rfl) (by simp +decide [Env.get_cons, Env.get, slsParams, ctxEnv] <;> rfl) (by decide)
      (fun vw P htg hsh => ?_)
    obtain ⟨dom, body, hpb, hwv⟩ : ∃ ty b, projBind vw = some (ty, b) ∧ encEView vw = [Enc.idxW ty, Enc.idxW b] := by
      have htT : e.tag.toNat = 6 := by rw [ht]; simp
      rw [htT] at htg
      cases vw with
      | lam ty b => exact ⟨ty, b, rfl, rfl⟩
      | forallE ty b => exact ⟨ty, b, rfl, rfl⟩
      | _ => simp [ENodeView.tagN] at htg <;> omega
    rw [hpb]; simp only
    refine specR_loadI' slsDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp [sev, Env.get_cons])
      (by simp) (by rw [hwv]; simpa using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW body] []) ?_
    refine specR_loadI' slsBd _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW body) (by decide) (by simp +decide [sev])
      rfl (by rw [hwv]; exact wordsAt_mem1 _ _ _ _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) slsMn (vv slsMp) pm _ hMp.1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv]; rfl) ?_
    have hD0 : ∀ x, x ∈ [lCn, lW, lSrc, lDst, lCi, lCz] → x ∈ ctxLocals ++ slsLocals := by decide
    -- the rest after the slot, at either motive-position block
    have hrest : ∀ (mp' : MlS) (motPos' : List Nat) (pm' : Nat) (sl : ClassSlot) (os : Nat) (Γ : Env) (M : Mem)
        (H1 : List (BitVec 64)) (s1 : AState), H <+: H1 → BlkAt H1 pm' (motPos'.map (BitVec.ofNat 64)) →
        (∀ x ∈ motPos', x < 2 ^ 63) → SlotRep C H1 os sl →
        Γ.get slsDm = some (Enc.idxW dom) → Γ.get slsDd = some (BitVec.ofNat 64 d) →
        Γ.get slsBd = some (Enc.idxW body) → Γ.get mp' = some (cellA C pm') → Γ.get slsP = some (BitVec.ofNat 64 np) →
        Γ.get slsM = some (cellA C om) → Γ.get slsNp = some (BitVec.ofNat 64 p.nP) →
        Γ.get slsN = some (BitVec.ofNat 64 (n + 1)) → Γ.get slsS = some (cellA C os) → Γ.get lCz = none →
        mp' ≠ slsFv ∧ mp' ≠ slsB2 ∧ mp' ≠ ExS.lY →
        SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ M (ctxLocals ++ slsLocals)) (slsRest C mp') s1
          (do
            let fv ← internFVarE d dom
            let b2 ← instantiate1Fast coreWalkFuel body fv 0
            match ← classReadSlots p C.fe np n motPos' (d + 1) b2 with
            | none => pure none
            | some rest => pure (some (sl :: rest)))
          (PostSlots (ctxH C H)) := by
      intro mp' motPos' pm' sl os Γ M H1 s1 hp1 hMp' hmp' hsl gDm gDd gBd gmp gP gM gNp gN gS gz hne
      unfold slsRest
      refine WC.specR_internFVarR ra (ctxOK_H hok H1) hc.fv slsFv (vv slsDm) (vv slsDd) dom d (by omega) (by decide)
        (by simp [sev, gDm]) (by simp [sev, gDd]) (fun fv s2 _ => ?_)
      refine ILP.callE_spec (C := ctxH C H1) slsB2 fInst1F [pFu, pH, pV, pD]
        [.const (BitVec.ofNat 64 coreWalkFuel), vv slsBd, vv slsFv, .const 0]
        (fastBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl
        (by decide) hc.csl.i1 ⟨rfl, by simp +decide [sev, Env.get_cons, gBd], by simp [sev, Env.get_cons], rfl, trivial⟩
        (fast_spec ra (ctxH C H1) (ctxOK_H hok H1) (by ctx_tr hc.csl.ic) s2 coreWalkFuel body fv 0 (by decide) (by decide))
        (fun b2 s3 => ?_)
      have hM1 : PtrsRep C H1 om (MemberRep C H1) p.members :=
        ptrsRep_mono hp1 (fun _ _ h => memberRep_mono hp1 h) hM
      refine specR_callNIH (C := ctxH C H1) ExS.lY fClassReadSlots slsParams
        [vv slsB2, .op .sub [vv slsN, .const 1], .op .add [vv slsDd, .const 1], vv mp', vv slsP, vv slsM, vv slsNp]
        (slsBody C) [Enc.idxW b2, BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), cellA C pm', BitVec.ofNat 64 np,
          cellA C om, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hc.self
        ⟨by simp [sev, Env.get_cons],
          by simp +decide [sev, Env.get_cons, gN]; exact ofNat_succ_sub_one n,
          by simp +decide [sev, Env.get_cons, gDd]; exact word_add1_eq d,
          by simp only [sev, sev_vv, Env.get_cons, if_neg hne.2.1, if_neg hne.1, gmp],
          by simp +decide [sev, Env.get_cons, gP], by simp +decide [sev, Env.get_cons, gM],
          by simp +decide [sev, Env.get_cons, gNp], trivial⟩
        (PostSlots (ctxH C H1)) (fun o w _ H' => ∃ sls ob, o = some sls ∧ w = cellA C ob ∧ SlotBlk C H' ob sls)
        (fun o w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu slsParams _ rfl hlk)
          (ih motPos' pm' (d + 1) H1 s3 b2 (hp.trans hp1) hM1 hMp' hmp' (by omega) (by omega)))
        (fun o w s4 H4 hp4 ⟨sls, ob, ho, hw, hsb⟩ => ?_)
      subst ho; subst hw
      simp only
      obtain ⟨ps, hpl, hpb, hpr⟩ := hsb
      refine ExPre.prepend_spec C hok (H := H4) slsS (cellA C os) ob (ps.map (cellA C))
        ⟨hD0 _ (by simp), hD0 _ (by simp), hD0 _ (by simp), hD0 _ (by simp), hD0 _ (by simp), hD0 _ (by simp)⟩
        (by simp [Env.get_cons]) (by simp +decide [Env.get_cons, gS]) hpb (by decide)
        (by simp +decide [Env.get_cons, gz]) (by decide) (fun H' o t hp' hb hsr => ?_)
      have hp14 : H1 <+: H4 := hp4
      exact ⟨H', (hp1.trans hp14).trans hp', hsr, sl :: sls, o, rfl, rfl, os :: ps, by simp [hpl],
        by simp only [List.map_cons]; exact hb, fun k hk => by
          cases k with
          | zero => exact ⟨os, rfl, slotRep_mono (hp14.trans hp') hsl⟩
          | succ k =>
            obtain ⟨op, h1, h2⟩ := hpr k (by simpa using hk)
            exact ⟨op, by simpa using h1, slotRep_mono hp' h2⟩⟩
    refine specR_callNIH (C := ctxH C H) slsS fClassReadSlot cslParams
      [vv slsDm, vv slsP, vv slsMp, vv slsMn, vv slsDd, vv slsM, vv slsNp] (cslBody C)
      [Enc.idxW dom, BitVec.ofNat 64 np, cellA C pm, BitVec.ofNat 64 (List.map (BitVec.ofNat 64) motPos).length,
        BitVec.ofNat 64 d, cellA C om, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hc.csl.self
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv], trivial⟩
      (PostSlot (ctxH C H)) (fun o w _ H' => ∃ sl os, o = some sl ∧ w = cellA C os ∧ SlotRep C H' os sl)
      (fun o w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cslParams _ rfl hlk) (by
        have := csl_spec (σ := σ) ra C hok hc.csl p om np motPos pm d H hp hM hml hpnP hMp hmp hnP (by omega) s dom
        simpa only [List.length_map] using this))
      (fun o w s1 H1 hp1 ⟨sl, os, ho, hw, hsl⟩ => ?_)
    subst ho; subst hw
    have hp1' : H <+: H1 := hp1
    simp only
    have hMp1 : BlkAt H1 pm (motPos.map (BitVec.ofNat 64)) := blkAt_mono hMp hp1'
    cases sl with
    | motive k =>
      obtain ⟨h0, -⟩ := id hsl
      refine UD.specR_heapLoadI' (C := ctxH C H1) slsT (vv slsS) os _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      refine specR_pureBind (motPos.map (BitVec.ofNat 64) ++ [BitVec.ofNat 64 (d - np)]) ?_
      refine specR_callNIH (C := ctxH C H1) slsMq ExPre.fAppend ExPre.appParams [vv slsMp, .op .sub [vv slsDd, vv slsP]]
        (ExPre.appBody C) [cellA C pm, BitVec.ofNat 64 (d - np)] (by decide) rfl (by decide) hc.app
        ⟨by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, slsParams, ctxEnv]; exact word_sub_eq d np hdn (by omega), trivial⟩
        (fun a w s' st => (pure (motPos.map (BitVec.ofNat 64) ++ [BitVec.ofNat 64 (d - np)]) : AM (List (BitVec 64))) s1 =
          .ok (a, s') ∧ ExPre.PostBW (ctxH C H1) s1 a w s' st)
        (fun a w s' H' => (pure (motPos.map (BitVec.ofNat 64) ++ [BitVec.ofNat 64 (d - np)]) : AM (List (BitVec 64))) s1 =
          .ok (a, s') ∧ ∃ o, w = cellA C o ∧ BlkAt H' o a)
        (fun a w s' st ⟨hrun, _, H', o, hp', _, hw, hb, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hb⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ExPre.appParams _ rfl hlk)
          (ExPre.app_spec (ctxH C H1) (ctxOK_H hok H1) s1 pm (motPos.map (BitVec.ofNat 64)) (BitVec.ofNat 64 (d - np)) hMp1)))
        (fun a w s2 H2 hp2 ⟨hrun, om2, hw, hb2⟩ => ?_)
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hra, hs2⟩ := hrun
      subst hw; subst hs2; subst hra
      have hp2' : H1 <+: H2 := hp2
      have hb2' : BlkAt H2 om2 ((motPos ++ [d - np]).map (BitVec.ofNat 64)) := by simpa using hb2
      refine hrest slsMq (motPos ++ [d - np]) om2 (.motive k) os _ _ H2 s1 (hp1'.trans hp2') hb2'
        (fun x hx => by simp at hx; rcases hx with hx | hx; exact hmp x hx; omega) (slotRep_mono hp2' hsl)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        first | (simp +decide [Env.get_cons, Env.get, slsParams, ctxEnv]) | decide
    | minor c cn ihs =>
      obtain ⟨h0, -⟩ := id hsl
      refine UD.specR_heapLoadI' (C := ctxH C H1) slsT (vv slsS) os _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only
      refine hrest slsMp motPos pm (.minor c cn ihs) os _ _ H1 s1 hp1' hMp1 hmp hsl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        first | (simp +decide [Env.get_cons, Env.get, slsParams, ctxEnv]) | decide

end

/-! ## The motive positions of a slot list -/

def isMotive : ClassSlot → Bool
  | .motive _ => true
  | .minor _ _ _ => false

/-- Positions `≥ i` of the motives among `sls` (read from position `i`). -/
def motPosFrom : List ClassSlot → Nat → List Nat
  | [], _ => []
  | sl :: r, i => (if isMotive sl then [i] else []) ++ motPosFrom r (i + 1)

theorem motPosFrom_eq (sls : List ClassSlot) :
    (List.range sls.length).filter (fun s => match sls[s]? with
      | some (.motive _) => true
      | _ => false) = motPosFrom sls 0 := by
  have key : ∀ (r : List ClassSlot) (i : Nat) (pre : List ClassSlot), pre.length = i →
      ((List.range r.length).map (· + i)).filter (fun s => match (pre ++ r)[s]? with
        | some (.motive _) => true
        | _ => false) = motPosFrom r i := by
    intro r
    induction r with
    | nil => intro i pre _; simp [motPosFrom]
    | cons sl r ih =>
      intro i pre hpre
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.filter_cons]
      have h0 : (pre ++ sl :: r)[i]? = some sl := by
        rw [List.getElem?_append_right (by omega)]; simp [hpre]
      have hrest := ih (i + 1) (pre ++ [sl]) (by simp [hpre])
      have hcomp : ((List.range r.length).map (Nat.succ)).map (· + i) = (List.range r.length).map (· + (i + 1)) := by
        simp [List.map_map, Function.comp_def]; omega
      simp only [motPosFrom]
      rw [show ((List.range r.length).map ((· + i) ∘ Nat.succ)) = (List.range r.length).map (· + (i + 1)) by
        simp [Function.comp_def]; omega]
      have hsplit : pre ++ sl :: r = (pre ++ [sl]) ++ r := by simp
      have h0' : (pre ++ [sl] ++ r)[i]? = some sl := by rw [← hsplit]; exact h0
      rw [hsplit, hrest]
      cases sl <;> simp [h0, h0', isMotive]
  have := key sls 0 [] rfl
  simpa using this

def mpsS := ofString "mps_s"
def mpsI := ofString "mps_i"
def mpsN := ofString "mps_n"
def mpsP := ofString "mps_p"
def mpsT := ofString "mps_t"
def fMotPos := ofString "motPosFrom"

def mpsParams : List MlS := [mpsS, mpsI, mpsN]
def mpsLocals : List MlS := gaaLocals ++ [mpsP, mpsT]

def mpsBody (C : Ctx) : ProgHOL 64 := prologue mpsLocals
  (.ite (.cmp .lower (vv mpsI) (vv mpsN))
    (.seq (.assign .local mpsP (.load .one (.op .add [vv mpsS, .op .add [.panop .mul [vv mpsI, .const 8], .const 8]])))
    (.seq (.assign .local mpsT (.load .one (vv mpsP)))
    (.seq (.call (some (some (.local, ExS.lY), none)) fMotPos [vv mpsS, .op .add [vv mpsI, .const 1], vv mpsN])
    (.ite (.cmp .equal (vv mpsT) (.const 0)) (prependP C mpsI) (.return (vv ExS.lY))))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem mps_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mpsLocals → (ctxEnv C ++ mpsParams.zip vals).get x = none :=
  Knot.params_none C mpsLocals mpsParams vals (by decide) (by decide)

/-- A list of naturals as a fresh block. -/
def PostNs (C : Ctx) (ns : List Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o (ns.map (BitVec.ofNat 64)) ∧ SR (ctxH C H') s' st

theorem postNs_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNs C a w s' st → PostNs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, hb, hs⟩ => ⟨H', o, hp, hw, hb, sr_of_eq hs rfl rfl rfl rfl⟩

theorem motPosFrom_drop (sls : List ClassSlot) (i : Nat) (hi : i < sls.length) :
    motPosFrom (sls.drop i) i = (if isMotive sls[i] then [i] else []) ++ motPosFrom (sls.drop (i + 1)) (i + 1) := by
  rw [List.drop_eq_getElem_cons hi]; rfl

/-- **`motPosFrom`** over a slot block from position `i`. -/
theorem mps_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMotPos = some (mpsParams.map (fun p => (p, ShapeHOL.one)), mpsBody C, .one))
    (sls : List ClassSlot) (ob : Nat) (H0 : List (BitVec 64)) (hS : SlotBlk C H0 ob sls) (hsl : sls.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), sls.length - i = f → i ≤ sls.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (mpsParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length]))
        (mpsBody C) s (pure (motPosFrom (sls.drop i) i)) (PostNs (ctxH C H)) := by
  obtain ⟨ps, hpl, hpb, hpr⟩ := hS
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (postNs_locals _) (mps_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mpsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      hp2.trans hpr', rfl, ⟨by simpa [motPosFrom] using hg, fun i hi => absurd hi (by simp [motPosFrom])⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < sls.length := by omega
    refine specR_prologue (postNs_locals _) (mps_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mpsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [motPosFrom_drop sls i hin]
    obtain ⟨op, hop, hrep⟩ := hpr i hin
    have hpi : (ps.map (cellA C))[i]'(by simp; omega) = cellA C op := by
      simp only [List.getElem_map]; rw [List.getElem?_eq_some_iff] at hop; obtain ⟨_, h⟩ := hop; rw [h]
    have hcell := hpb.2 i (by simp; omega)
    rw [hpi] at hcell
    refine UD.specR_heapLoadI' (C := ctxH C H) mpsP _ (ob + 1 + i) _ (get_prefix hcell hp) (by decide)
      (by simp +decide [sev, Env.get, mpsParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    have htag : H0[op]? = some (if isMotive sls[i] then 0 else 1) := by
      cases h : sls[i] with
      | motive k => rw [h] at hrep; exact hrep.1
      | minor c cn ihs => rw [h] at hrep; exact hrep.1
    refine UD.specR_heapLoadI' (C := ctxH C H) mpsT (vv mpsP) op _ (get_prefix htag hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine specR_congr (m' := (pure (motPosFrom (sls.drop (i + 1)) (i + 1)) : AM (List Nat)) >>= fun r =>
      pure ((if isMotive sls[i] then [i] else []) ++ r)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fMotPos mpsParams [vv mpsS, .op .add [vv mpsI, .const 1], vv mpsN]
      (mpsBody C) [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mpsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mpsParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, mpsParams, ctxEnv], trivial⟩
      (PostNs (ctxH C H)) (fun r w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (r.map (BitVec.ofNat 64)))
      (fun r w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mpsParams _ rfl hlk) (ih (i + 1) H s (by omega) (by omega) hp))
      (fun r w s1 H1 hp1 ⟨o1, hw, hb1⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    by_cases hm : isMotive sls[i] = true
    · simp only [hm, ite_true]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine ExPre.prepend_spec C hok (H := H1) mpsI (BitVec.ofNat 64 i) o1 (r.map (BitVec.ofNat 64))
        (by decide) (by simp [Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, mpsParams, ctxEnv]) hb1 (by decide)
        (by simp +decide [Env.get_cons, Env.get, mpsParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
      exact ⟨H', o, hp1'.trans hp', rfl, by simpa using hb, hsr⟩
    · have hm' : isMotive sls[i] = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ite_false, List.nil_append]
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ (cellA C o1) (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H1, o1, hp1', rfl, hb1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classReadRecCls` -/

def rccR := ofString "rcc_r"
def rccI := ofString "rcc_i"
def rccN := ofString "rcc_n"
def rccP := ofString "rcc_p"
def rccMp := ofString "rcc_mp"
def rccMn := ofString "rcc_mn"
def rccRp := ofString "rcc_rp"
def rccCv := ofString "rcc_cv"
def rccTy := ofString "rcc_ty"
def rccMI := ofString "rcc_mi"
def rccQ := ofString "rcc_q"
def rccCc := ofString "rcc_cc"
def rccH := ofString "rcc_h"
def rccC := ofString "rcc_c"
def fRecCls := ofString "classReadRecCls"

def rccParams : List MlS := [rccR, rccI, rccN, rccP, rccMp, rccMn]
def rccLocals : List MlS := gaaLocals ++ [rccRp, rccCv, rccTy, rccMI, rccQ, rccCc, rccH, rccC]

def rccBody (C : Ctx) : ProgHOL 64 := prologue rccLocals
  (.ite (.cmp .lower (vv rccI) (vv rccN))
    (.seq (.assign .local rccRp (.load .one (.op .add [vv rccR, .op .add [.panop .mul [vv rccI, .const 8], .const 8]])))
    (.seq (.assign .local rccCv (.load .one (vv rccRp)))
    (.seq (.assign .local rccTy (.load .one (.op .add [vv rccCv, .const 16])))
    (.seq (.assign .local rccMI (.load .one (.op .add [vv rccRp, .const 16])))
    (.seq (.call (some (some (.local, rccQ), none)) fOpenFvars [.op .add [vv rccMI, .const 1], vv rccTy, .const 0])
    (.ite (.cmp .equal (vv rccQ) (.const 0)) hang
    (.seq (.assign .local rccCc (.load .one (.op .add [vv rccQ, .const 8])))
    (.seq (.call (some (some (.local, rccH), none)) fFvarHead [vv rccCc])
    (.ite (.cmp .equal (vv rccH) (.const 0)) hang
    (.seq (.assign .local rccH (.op .sub [vv rccH, .const 1]))
    (.ite (.cmp .lower (vv rccH) (vv rccP)) hang
    (.seq (.call (some (some (.local, rccC), none)) fFindIdx [vv rccMp, .op .sub [vv rccH, vv rccP], .const 0, vv rccMn])
    (.ite (.cmp .equal (vv rccC) (.const 0)) hang
    (.seq (.call (some (some (.local, ExS.lY), none)) fRecCls
        [vv rccR, .op .add [vv rccI, .const 1], vv rccN, vv rccP, vv rccMp, vv rccMn])
    (.seq (.assign .local rccC (.op .sub [vv rccC, .const 1]))
      (prependP C rccC))))))))))))))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

/-- The code `classReadRecCls` runs. -/
structure RCCCodes (C : Ctx) : Prop where
  self : C.code.lookup fRecCls = some (rccParams.map (fun p => (p, ShapeHOL.one)), rccBody C, .one)
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  fh : C.code.lookup fFvarHead = some (fhParams.map (fun p => (p, ShapeHOL.one)), fhBody, .one)
  gf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  cmv : C.code.lookup fFindIdx = some (cmvParams.map (fun p => (p, ShapeHOL.one)), cmvBody, .one)

section
variable {σ : Type}

theorem rcc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rccLocals → (ctxEnv C ++ rccParams.zip vals).get x = none :=
  Knot.params_none C rccLocals rccParams vals (by decide) (by decide)

/-- An optional list of naturals that is `some`, as a fresh block. -/
def PostONs (C : Ctx) (o : Option (List Nat)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ cs ob, o = some cs ∧ w = cellA C ob ∧ BlkAt H' ob (cs.map (BitVec.ofNat 64))

theorem postONs_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostONs (σ := σ) C a w s' st → PostONs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem classReadRecCls_drop (nP : Nat) (motPos : List Nat) (recs : List RecShape) (i : Nat) (hi : i < recs.length) :
    classReadRecCls nP motPos (recs.drop i) = (do
      match ← openPisAtFvarsF (recs[i].mI + 1) recs[i].cvR.type 0 with
      | none => pure none
      | some (_, concl) =>
        match ← fvarHead concl with
        | none => pure none
        | some p =>
          match classOfMotiveVar nP motPos p with
          | none => pure none
          | some c =>
            match ← classReadRecCls nP motPos (recs.drop (i + 1)) with
            | none => pure none
            | some cs => pure (some (c :: cs))) := by
  rw [List.drop_eq_getElem_cons hi, classReadRecCls]; rfl

end

section
variable {σ : Type}

set_option maxHeartbeats 8000000 in
/-- **`classReadRecCls`** from recursor `i` (off-shape halts). -/
theorem rcc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RCCCodes C)
    (nP : Nat) (motPos : List Nat) (recs : List RecShape) (orr pm : Nat) (H0 : List (BitVec 64))
    (hR : PtrsRep C H0 orr (RecRep C H0) recs) (hMp : BlkAt H0 pm (motPos.map (BitVec.ofNat 64)))
    (hmp : ∀ x ∈ motPos, x < 2 ^ 63) (hnP : nP < 2 ^ 63) (hrl : recs.length < 2 ^ 59)
    (hmI : ∀ i (hi : i < recs.length), recs[i].mI < 2 ^ 56) :
    ∀ f i (H : List (BitVec 64)) (s : AState), recs.length - i = f → i ≤ recs.length → C.H <+: H → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (rccParams.zip [cellA C orr, BitVec.ofNat 64 i, BitVec.ofNat 64 recs.length,
        BitVec.ofNat 64 nP, cellA C pm, BitVec.ofNat 64 motPos.length])) (rccBody C) s
        (classReadRecCls nP motPos (recs.drop i)) (PostONs (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp h0
    have hin : i = recs.length := by omega
    subst hin
    refine specR_prologue (postONs_locals _) (rcc_none _ _) ?_
    have hlw := nd_lt_iff recs.length recs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, classReadRecCls]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, hp2.trans hpr',
      sr_of_eq ht.sr rfl rfl rfl rfl, [], H2.length, rfl, rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩⟩)
  | succ f ih =>
    intro i H s hf hi hp h0
    have hin : i < recs.length := by omega
    refine specR_prologue (postONs_locals _) (rcc_none _ _) ?_
    have hlw := nd_lt_iff i recs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [classReadRecCls_drop nP motPos recs i hin]
    obtain ⟨ori, hori, hrep⟩ := hR.2 i hin
    obtain ⟨⟨oc, hoc, hcv⟩, -, ⟨hmIW, -⟩, -⟩ := hrep
    obtain ⟨-, -, hty⟩ := hcv
    have hmI' := hmI i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) rccRp _ (orr + 1 + i) _ (get_prefix hori h0) (by decide)
      (by simp +decide [sev, Env.get, rccParams, ctxEnv]; exact cellA_mulIdx C orr i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rccCv (vv rccRp) ori _ (get_prefix hoc h0) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rccTy _ (oc + 2) _ (get_prefix hty h0) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rccMI _ (ori + 2) _ (get_prefix hmIW h0) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ori 2) ?_
    refine specR_callNIH (C := ctxH C H) rccQ fOpenFvars ofParams [.op .add [vv rccMI, .const 1], vv rccTy, .const 0]
      (ofBody C) [BitVec.ofNat 64 (recs[i].mI + 1), Enc.idxW recs[i].cvR.type, BitVec.ofNat 64 0] (by decide) rfl
      (by decide) hc.ofc
      ⟨by simp +decide [sev, Env.get_cons]; exact word_add1_eq _, by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (PostOF (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
        w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
        (of_spec ra C hok hc.op (recs[i].mI + 1) recs[i].cvR.type 0 (by omega) (by omega) H hp s))
      (fun o1 w s1 H1 hp1 ⟨hn1, hs1⟩ => ?_)
    have hp1' : H <+: H1 := hp1
    rcases o1 with _ | ⟨fvs, concl⟩
    · rw [hn1 rfl]
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨q1, oq, rfl, hq1a, hq1b, -⟩ := hs1 fvs concl rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
    have hq1l : q1 < H1.length := (List.getElem?_eq_some_iff.mp hq1a).1
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hne1 : cellA C q1 ≠ 0 := cellA_ne0 C hok q1 (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H1) rccCc _ (q1 + 1) _ hq1b (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q1) ?_
    simp only
    refine specR_callNIM rccH fFvarHead fhParams [vv rccCc] fhBody [Enc.idxW concl] (by decide) rfl (by decide) hc.fh
      ⟨by simp +decide [sev, Env.get_cons], trivial⟩ (PostON (ctxH C H1)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fhParams _ rfl hlk) (fh_spec (ctxH C H1) hc.gf s1 concl))
      (fun o w s2 st ⟨hw, hb, _⟩ => ?_)
    subst hw
    rcases o with _ | p2
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    have hp2b := hb p2 rfl
    have hne : BitVec.ofNat 64 (p2 + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI rccH _ (BitVec.ofNat 64 p2) (by decide)
      (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (p2 + 1) 1 (by omega) (by omega)) ?_
    simp only
    rw [classOfMotiveVar_eq]
    have hlw2 := ConPanqueque.T.Decl.nd_lt_iff p2 nP (by omega) (by omega)
    by_cases hle : nP ≤ p2
    swap
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_pos hle]
    refine specR_pureBind (((motPos.drop 0).findIdx? (· == p2 - nP)).map (· + 0)) ?_
    have hMp1 : BlkAt H1 pm (motPos.map (BitVec.ofNat 64)) := blkAt_mono hMp (h0.trans hp1')
    refine specR_callNIM rccC fFindIdx cmvParams [vv rccMp, .op .sub [vv rccH, vv rccP], .const 0, vv rccMn] cmvBody
      [cellA C pm, BitVec.ofNat 64 (p2 - nP), BitVec.ofNat 64 0, BitVec.ofNat 64 (List.map (BitVec.ofNat 64) motPos).length]
      (by decide) rfl (by decide) hc.cmv
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv]; exact word_sub_eq p2 nP hle (by omega), rfl,
        by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv], trivial⟩
      (fun a w s' st => (pure (((motPos.drop 0).findIdx? (· == p2 - nP)).map (· + 0)) : AM (Option Nat)) s2 = .ok (a, s') ∧
        PostON (ctxH C H1) a w s' st) (fun _ _ _ _ h => h.2.2.2)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cmvParams _ rfl hlk) (by
        have := cmv_spec (σ := σ) C hok hc.cmv motPos (p2 - nP) pm H1 hMp1 hmp (by omega) _ 0 s2 rfl (by omega)
        simpa only [List.length_map] using this)))
      (fun a w s3 st ⟨hrun, hw, hb2, _⟩ => ?_)
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨hra, hs3⟩ := hrun
    subst hw; subst hs3
    rw [hra]
    rcases a with _ | c
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    have hc63 := hb2 c rfl
    have hnc : BitVec.ofNat 64 (c + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnc)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only
    refine specR_callNIH (C := ctxH C H1) ExS.lY fRecCls rccParams
      [vv rccR, .op .add [vv rccI, .const 1], vv rccN, vv rccP, vv rccMp, vv rccMn] (rccBody C)
      [cellA C orr, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 recs.length, BitVec.ofNat 64 nP, cellA C pm,
        BitVec.ofNat 64 motPos.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, rccParams, ctxEnv],
        trivial⟩
      (PostONs (ctxH C H1)) (fun o w _ H' => ∃ cs ob, o = some cs ∧ w = cellA C ob ∧ BlkAt H' ob (cs.map (BitVec.ofNat 64)))
      (fun o w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rccParams _ rfl hlk)
        (ih (i + 1) H1 s2 (by omega) (by omega) (hp.trans hp1') (h0.trans hp1')))
      (fun o w s4 H4 hp4 ⟨cs, ob, ho, hw, hcs⟩ => ?_)
    subst ho; subst hw
    simp only
    refine specR_assignI rccC _ (BitVec.ofNat 64 c) (by decide)
      (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (c + 1) 1 (by omega) (by omega)) ?_
    refine ExPre.prepend_spec C hok (H := H4) rccC (BitVec.ofNat 64 c) ob (cs.map (BitVec.ofNat 64))
      (by decide) (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hcs (by decide)
      (by simp +decide [Env.get_cons, Env.get, rccParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    have hp14 : H1 <+: H4 := hp4
    exact ⟨H', (hp1'.trans hp14).trans hp', hsr, c :: cs, o, rfl, rfl, by simpa using hb⟩

end

/-! ## `classRead` -/

theorem motPosFrom_lt : ∀ (sls : List ClassSlot) (i : Nat), ∀ x ∈ motPosFrom sls i, x < i + sls.length
  | [], _ => by simp [motPosFrom]
  | sl :: r, i => by
    intro x hx
    simp only [motPosFrom, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx <;> simp at hx; simp [hx]
    · have := motPosFrom_lt r (i + 1) x hx; simp; omega

/-- The pre-pass's record at `o`: `[slots block, recursor classes block]`. -/
def ClassReadRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (rd : ClassRead) : Prop :=
  ∃ os orc, H[o]? = some (cellA C os) ∧ SlotBlk C H os rd.slots ∧ H[o + 1]? = some (cellA C orc) ∧
    BlkAt H orc (rd.recCls.map (BitVec.ofNat 64))

/-- The pre-pass's answer: `some`, as its record. -/
def PostCR (C : Ctx) (o : Option ClassRead) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ rd ob, o = some rd ∧ w = cellA C ob ∧ ClassReadRep C H' ob rd

theorem postCR_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCR (σ := σ) C a w s' st → PostCR C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

def crdM := ofString "crd_m"
def crdNp := ofString "crd_np"
def crdP := ofString "crd_p"
def crdR := ofString "crd_r"
def crdK := ofString "crd_k"
def crdR0 := ofString "crd_r0"
def crdCv := ofString "crd_cv"
def crdTy := ofString "crd_ty"
def crdRP := ofString "crd_rp"
def crdQ := ofString "crd_q"
def crdB := ofString "crd_b"
def crdMz := ofString "crd_mz"
def crdSs := ofString "crd_ss"
def crdSn := ofString "crd_sn"
def crdMp := ofString "crd_mp"
def crdMn := ofString "crd_mn"
def crdRc := ofString "crd_rc"
def crdW := ofString "crd_w"
def fClassRead := ofString "classRead"

def crdParams : List MlS := [crdM, crdNp, crdP, crdR]
def crdLocals : List MlS := [crdK, crdR0, crdCv, crdTy, crdRP, crdQ, crdB, crdMz, crdSs, crdSn, crdMp, crdMn, crdRc, crdW]

def crdBody (C : Ctx) : ProgHOL 64 := prologue crdLocals
  (.seq (.assign .local crdK (.load .one (vv crdR)))
  (.ite (.cmp .equal (vv crdK) (.const 0)) hang
  (.seq (.assign .local crdR0 (.load .one (.op .add [vv crdR, .const 8])))
  (.seq (.assign .local crdCv (.load .one (vv crdR0)))
  (.seq (.assign .local crdTy (.load .one (.op .add [vv crdCv, .const 16])))
  (.seq (.assign .local crdRP (.load .one (.op .add [vv crdR0, .const 8])))
  (.ite (.cmp .lower (vv crdRP) (vv crdP)) hang
  (.seq (.call (some (some (.local, crdQ), none)) fOpenFvars [vv crdP, vv crdTy, .const 0])
  (.ite (.cmp .equal (vv crdQ) (.const 0)) hang
  (.seq (.assign .local crdB (.load .one (.op .add [vv crdQ, .const 8])))
  (alloc1 C crdMz (.const 0)
  (.seq (.call (some (some (.local, crdSs), none)) fClassReadSlots
      [vv crdB, .op .sub [vv crdRP, vv crdP], vv crdP, vv crdMz, vv crdP, vv crdM, vv crdNp])
  (.seq (.assign .local crdSn (.load .one (vv crdSs)))
  (.seq (.call (some (some (.local, crdMp), none)) fMotPos [vv crdSs, .const 0, vv crdSn])
  (.seq (.assign .local crdMn (.load .one (vv crdMp)))
  (.seq (.call (some (some (.local, crdRc), none)) fRecCls [vv crdR, .const 0, vv crdK, vv crdP, vv crdMp, vv crdMn])
  (alloc2 C crdW (vv crdSs) (vv crdRc) (.return (vv crdW)))))))))))))))))))

/-- The code `classRead` runs. -/
structure CRDCodes (C : Ctx) : Prop where
  self : C.code.lookup fClassRead = some (crdParams.map (fun p => (p, ShapeHOL.one)), crdBody C, .one)
  sls : SLSCodes C
  mps : C.code.lookup fMotPos = some (mpsParams.map (fun p => (p, ShapeHOL.one)), mpsBody C, .one)
  rcc : RCCCodes C

section
variable {σ : Type}

theorem crd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crdLocals → (ctxEnv C ++ crdParams.zip vals).get x = none :=
  Knot.params_none C crdLocals crdParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`classRead`** (off-shape halts). -/
theorem crd_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CRDCodes C)
    (p : BlockShape) (nP : Nat) (recs : List RecShape) (om orr : Nat) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hM : PtrsRep C H om (MemberRep C H) p.members) (hR : PtrsRep C H orr (RecRep C H) recs)
    (hml : p.members.length < 2 ^ 59) (hpnP : p.nP < 2 ^ 63) (hnP : nP < 2 ^ 56) (hrl : recs.length < 2 ^ 59)
    (hmI : ∀ i (hi : i < recs.length), recs[i].mI < 2 ^ 56) (hrP : ∀ i (hi : i < recs.length), recs[i].rP < 2 ^ 61)
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (crdParams.zip [cellA C om, BitVec.ofNat 64 p.nP, BitVec.ofNat 64 nP, cellA C orr]))
      (crdBody C) s (classRead p C.fe nP recs) (PostCR (ctxH C H)) := by
  refine specR_prologue (postCR_locals _) (crd_none _ _) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) crdK (vv crdR) orr _ hR.1 (by decide)
    (by simp +decide [sev, Env.get, crdParams, ctxEnv]; rfl) ?_
  unfold classRead
  rcases hrs : recs with _ | ⟨rc0, rest⟩
  · subst hrs
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have hrl' := hrl
  rw [hrs] at hrl'; simp only [List.length_cons] at hrl'
  have hK0 : BitVec.ofNat 64 (rest.length + 1) ≠ 0#64 := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hK0)
    (fun h => absurd rfl h) (fun _ => ?_)
  obtain ⟨or0, hor0, hrep0⟩ := hR.2 0 (by rw [hrs]; simp)
  have hr0e : (recs[0]'(by rw [hrs]; simp)) = rc0 := by simp [hrs]
  rw [hr0e] at hrep0
  obtain ⟨⟨oc, hoc, hcv⟩, ⟨hrPW, -⟩, -⟩ := hrep0
  obtain ⟨-, -, hty⟩ := hcv
  have hrP0 : rc0.rP < 2 ^ 61 := by have := hrP 0 (by rw [hrs]; simp); simpa [hrs] using this
  refine UD.specR_heapLoadI' (C := ctxH C H) crdR0 _ (orr + 1 + 0) _ hor0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv]; exact cellA_add8 C orr) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) crdCv (vv crdR0) or0 _ hoc (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) crdTy _ (oc + 2) _ hty (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) crdRP _ (or0 + 1) _ hrPW (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C or0) ?_
  have hlw := ConPanqueque.T.Decl.nd_lt_iff rc0.rP nP (by omega) (by omega)
  by_cases hle : nP ≤ rc0.rP
  swap
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_callNIH (C := ctxH C H) crdQ fOpenFvars ofParams [vv crdP, vv crdTy, .const 0] (ofBody C)
    [BitVec.ofNat 64 nP, Enc.idxW rc0.cvR.type, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.rcc.ofc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostOF (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.rcc.op nP rc0.cvR.type 0 (by omega) (by omega) H hp s))
    (fun o1 w s1 H1 hp1 ⟨hn1, hs1⟩ => ?_)
  have hp1' : H <+: H1 := hp1
  rcases o1 with _ | ⟨fvs, body⟩
  · rw [hn1 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨q1, oq, rfl, hq1a, hq1b, -⟩ := hs1 fvs body rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
  have hq1l : q1 < H1.length := (List.getElem?_eq_some_iff.mp hq1a).1
  have hHN1' : H1.length ≤ C.HN := hHN1
  have hne1 : cellA C q1 ≠ 0 := cellA_ne0 C hok q1 (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H1) crdB _ (q1 + 1) _ hq1b (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q1) ?_
  simp only
  refine specR_alloc1I (ctxOK_H hok H1) crdMz (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
  let H2' := (H2 ++ ws).set H2.length (0 : BitVec 64)
  have hg : H2'[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
  have hpr2 : H2 <+: H2' := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
  have hp12 : H1 <+: H2' := (hp2 : H1 <+: H2).trans hpr2
  have hMz : BlkAt H2' H2.length (([] : List Nat).map (BitVec.ofNat 64)) := ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩
  have hM2 : PtrsRep C H2' om (MemberRep C H2') p.members :=
    ptrsRep_mono (hp1'.trans hp12) (fun _ _ h => memberRep_mono (hp1'.trans hp12) h) hM
  refine specR_callNIH (C := ctxH C H2') crdSs fClassReadSlots slsParams
    [vv crdB, .op .sub [vv crdRP, vv crdP], vv crdP, vv crdMz, vv crdP, vv crdM, vv crdNp] (slsBody C)
    [Enc.idxW body, BitVec.ofNat 64 (rc0.rP - nP), BitVec.ofNat 64 nP, cellA C H2.length, BitVec.ofNat 64 nP,
      cellA C om, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hc.sls.self
    ⟨by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv]; exact word_sub_eq rc0.rP nP hle (by omega),
      by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv], by simp +decide [sev, Env.get_cons]; rfl,
      by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv], trivial⟩
    (PostSlots (ctxH C H2')) (fun o w _ H' => ∃ sls ob, o = some sls ∧ w = cellA C ob ∧ SlotBlk C H' ob sls)
    (fun o w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu slsParams _ rfl hlk)
      (sls_spec ra C hok hc.sls p om nP hml hpnP (by omega) (rc0.rP - nP) [] H2.length nP H2' s1 body
        (hp.trans (hp1'.trans hp12)) hM2 hMz (fun x hx => by simp at hx) (Nat.le_refl _) (by omega)))
    (fun o w s3 H3 hp3 ⟨sls, ob, ho, hw, hS⟩ => ?_)
  subst ho; subst hw
  simp only
  have hp3' : H2' <+: H3 := hp3
  obtain ⟨ps, hpl, hpb, hpr⟩ := id hS
  refine UD.specR_heapLoadI' (C := ctxH C H3) crdSn (vv crdSs) ob _ hpb.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t3 ht3 => ?_
  have hsl := Big.blk_small0 (ctxOK_H hok H3) ht3.sr hpb
  simp only [List.length_map] at hsl
  refine specR_congr (m' := (pure (motPosFrom (sls.drop 0) 0) : AM (List Nat)) >>= fun mp =>
      classReadRecCls nP mp (rc0 :: rest) >>= fun o => match o with
        | none => pure none
        | some recCls => pure (some ⟨sls, recCls⟩))
    (by simp only [pure_bind, List.drop_zero]; rw [← motPosFrom_eq sls]; rfl) ?_
  refine specR_callNIH (C := ctxH C H3) crdMp fMotPos mpsParams [vv crdSs, .const 0, vv crdSn] (mpsBody C)
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 sls.length] (by decide) rfl (by decide) hc.mps
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, List.length_map, hpl], trivial⟩
    (fun a w s' st => (pure (motPosFrom (sls.drop 0) 0) : AM (List Nat)) s3 = .ok (a, s') ∧ PostNs (ctxH C H3) a w s' st)
    (fun a w s' H' => (pure (motPosFrom (sls.drop 0) 0) : AM (List Nat)) s3 = .ok (a, s') ∧
      ∃ o, w = cellA C o ∧ BlkAt H' o (a.map (BitVec.ofNat 64)))
    (fun a w s' st ⟨hrun, H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mpsParams _ rfl hlk)
      (mps_spec C hok hc.mps sls ob H3 hS (by omega) _ 0 H3 s3 rfl (by omega) (List.prefix_refl _))))
    (fun a w s4 H4 hp4 ⟨hrun, om4, hw, hb4⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs4⟩ := hrun
  subst hw; subst hs4; subst hra
  simp only [List.drop_zero]
  have hp4' : H3 <+: H4 := hp4
  refine UD.specR_heapLoadI' (C := ctxH C H4) crdMn (vv crdMp) om4 _ hb4.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  have hpH4 : H <+: H4 := ((hp1'.trans hp12).trans hp3').trans hp4'
  have hmpl := motPosFrom_lt sls 0
  refine specR_congr (m' := classReadRecCls nP (motPosFrom sls 0) (recs.drop 0) >>= fun o => match o with
      | none => pure none
      | some recCls => pure (some ⟨sls, recCls⟩)) (by rw [hrs, List.drop_zero]) ?_
  refine specR_callNIH (C := ctxH C H4) crdRc fRecCls rccParams [vv crdR, .const 0, vv crdK, vv crdP, vv crdMp, vv crdMn]
    (rccBody C) [cellA C orr, BitVec.ofNat 64 0, BitVec.ofNat 64 recs.length, BitVec.ofNat 64 nP, cellA C om4,
      BitVec.ofNat 64 (motPosFrom sls 0).length] (by decide) rfl (by decide) hc.rcc.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv, hrs],
      by simp +decide [sev, Env.get_cons, Env.get, crdParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, List.length_map], trivial⟩
    (PostONs (ctxH C H4)) (fun o w _ H' => ∃ cs oc, o = some cs ∧ w = cellA C oc ∧ BlkAt H' oc (cs.map (BitVec.ofNat 64)))
    (fun o w s' st ⟨H', hp', hsr, h⟩ => ⟨H', hp', h, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rccParams _ rfl hlk)
      (rcc_spec ra C hok hc.rcc nP (motPosFrom sls 0) recs orr om4 H4 (ptrsRep_mono hpH4 (fun _ _ h => recRep_mono hpH4 h) hR)
        hb4 (fun x hx => by have := hmpl x hx; omega) (by omega) hrl hmI _ 0 H4 s3 rfl (by omega) (hp.trans hpH4)
        (List.prefix_refl _)))
    (fun o w s5 H5 hp5 ⟨cs, oc5, ho, hw, hb5⟩ => ?_)
  subst ho; subst hw
  simp only
  have hp5' : H4 <+: H5 := hp5
  refine specR_alloc2I (ctxOK_H hok H5) crdW (vv crdSs) (vv crdRc) (cellA C ob) (cellA C oc5) (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun H6 ws hp6 hws => ?_)
  obtain ⟨g0, g1⟩ := img2_get H6 ws (cellA C ob) (cellA C oc5) hws
  have h6 := img2_prefix H6 ws (cellA C ob) (cellA C oc5) hws
  have hp56 : H5 <+: H6 := hp6
  refine specR_returnI (vv crdW) (cellA C H6.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ?_)
  exact ⟨_, (hpH4.trans hp5').trans (hp56.trans h6), sr_of_eq ht.sr rfl rfl rfl rfl, ⟨sls, cs⟩, H6.length, rfl, rfl,
    ob, oc5, g0, slotBlk_mono ((hp4'.trans hp5').trans (hp56.trans h6)) hS, g1, blkAt_mono hb5 (hp56.trans h6)⟩

end

end ConPanqueque.T.Ind
