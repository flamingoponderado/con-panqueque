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

end ConPanqueque.T.Ind
