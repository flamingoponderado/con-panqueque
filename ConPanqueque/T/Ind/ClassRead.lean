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

end ConPanqueque.T.Ind
