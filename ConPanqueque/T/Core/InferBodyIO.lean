import ConPanqueque.T.Core.InferAppIO
import ConPanqueque.T.Core.InferArms
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `inferBodyIO`: the io grade's dispatcher

`inferBody`'s dispatcher with the io grade's own arms (`ibForallIOT`, `ibLamIOT`, `inferAppIOAt`, `ibLetIOT`)
and its constant clause (`ibConstIOT`, read through `viewLsLen`); the sort, literal and projection arms are
shared.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def fIapIO := ofString "inferAppIO"
def fIbcIO := ofString "inferConstIO"
def fIprIO := ofString "inferProjIO"

/-- The projection tail at the io grade: its own function, as the plain grade's `fIpr` runs `pjBody`. -/
def ibPrKIO : ProgHOL 64 :=
  .seq (.call (some (some (.local, ibX), none)) fIprIO [vv kFu, vv kD, vv ibA, vv ibI, vv ibB]) (.return (vv ibX))

def ibConstIOT (fe : IFEnv) (n : NIdx) (us : LsIdx) : AM EIdx := do
  match fe.find? n with
  | none => do
    let err ← unknownConstError n
    fail err
  | some ci => do
    let cv := ci.toConstantVal
    match ← viewLsLen us with
    | none => failDanglingLs
    | some usl =>
    if usl != cv.levelParams.length then do
      fail (.invalid "incorrect number of universe levels")
    else constTyAt cv us

theorem inferBodyIO_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) :
    ConRon.Arena.inferBodyIO r fe depth e = (view e >>= fun v => match v with
      | .sort u => ibSortT u
      | .fvar idx ty => if idx < depth then pure ty else fail (.invalid "free variable out of scope")
      | .const n us => ibConstIOT fe n us
      | .lit l => ibLitT fe l
      | .forallE ty body => ibForallIOT r fe depth ty body
      | .lam ty body => ibLamIOT r depth ty body
      | .app _ _ => inferAppIOAt r fe depth e
      | .proj sn i pe => inferProj r fe depth sn i pe
      | .letE _ v b => ibLetIOT r depth v b
      | .bvar _ => fail (.notImplemented "inferType beyond the supported fragment")) := by
  unfold ConRon.Arena.inferBodyIO
  congr 1
  funext v
  cases v with
  | lit l => cases l <;> rfl
  | _ => rfl

def ibioCore : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv kE)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 2))
    (.seq (.assign .local ibA (.load .one (vv lRp)))
      (.seq (.call (some (some (.local, ibX), none)) fIbs [vv ibA]) (.return (vv ibX))))
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.seq (.assign .local ibA (.load .one (vv lRp)))
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local ibI (.const 0)) ibFvK)
      (.ite (.cmp .equal (vv lRn) (.const 2))
        (.seq (.assign .local ibI (.load .one (.op .add [vv lRp, .const 8]))) ibFvK) hang)))
  (.ite (.cmp .equal (vv lDg) (.const 3))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, ibX), none)) fIbcIO [vv ibA, vv ibB]) (.return (vv ibX)))))
  (.ite (.cmp .equal (vv lDg) (.const 8))
    (.seq (.call (some (some (.local, ibX), none)) fIbl [vv kE]) (.return (vv ibX)))
  (.ite (.cmp .equal (vv lDg) (.const 6))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, ibX), none)) fIfaIO [vv kFu, vv kD, vv ibA, vv ibB]) (.return (vv ibX)))))
  (.ite (.cmp .equal (vv lDg) (.const 5))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, ibX), none)) fIlaIO [vv kFu, vv kD, vv ibA, vv ibB]) (.return (vv ibX)))))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.call (some (some (.local, ibX), none)) fIapIO [vv kFu, vv kD, vv kE]) (.return (vv ibX)))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local ibI (.const 0)) ibPrKIO)
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local ibI (.load .one (.op .add [vv lRp, .const 16]))) ibPrKIO) hang))))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.assign .local ibC (.load .one (.op .add [vv lRp, .const 16])))
        (.seq (.call (some (some (.local, ibX), none)) fIltIO [vv kFu, vv kD, vv ibA, vv ibB, vv ibC]) (.return (vv ibX))))))
    hang)))))))))))

def ibioBody : ProgHOL 64 := prologue ibLocals ibioCore

structure IbioCodes (C : Ctx) (Bs Bc Bl Bfa Bla Bap Bpr Blt : ProgHOL 64) : Prop where
  s : C.code.lookup fIbs = some (ibsParams.map (fun p => (p, ShapeHOL.one)), Bs, .one)
  c : C.code.lookup fIbcIO = some (ibcParams.map (fun p => (p, ShapeHOL.one)), Bc, .one)
  l : C.code.lookup fIbl = some (iblParams.map (fun p => (p, ShapeHOL.one)), Bl, .one)
  fa : C.code.lookup fIfaIO = some (ifaParams.map (fun p => (p, ShapeHOL.one)), Bfa, .one)
  la : C.code.lookup fIlaIO = some (ifaParams.map (fun p => (p, ShapeHOL.one)), Bla, .one)
  ap : C.code.lookup fIapIO = some (kParams.map (fun p => (p, ShapeHOL.one)), Bap, .one)
  pr : C.code.lookup fIprIO = some (iprParams.map (fun p => (p, ShapeHOL.one)), Bpr, .one)
  lt : C.code.lookup fIltIO = some (iltParams.map (fun p => (p, ShapeHOL.one)), Blt, .one)

section
variable {σ : Type}

theorem ibio_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (Bs Bc Bl Bfa Bla Bap Bpr Blt : ProgHOL 64)
    (hc : IbioCodes C Bs Bc Bl Bfa Bla Bap Bpr Blt) (s : AState) (d : Nat) (e : EIdx) (hd : d < 2 ^ 64)
    (hSort : ∀ u, SpecR (σ := σ) (Pre C s (ibsParams.zip [Enc.idxW u])) Bs s (ibSortT u) (PostK C))
    (hConst : ∀ c us, s.store.view e = some (.const c us) → SpecR (σ := σ) (Pre C s (ibcParams.zip [Enc.idxW c, Enc.idxW us])) Bc s (ibConstIOT C.fe c us)
      (PostK C))
    (hLit : ∀ l, s.store.view e = some (.lit l) →
      SpecR (σ := σ) (Pre C s (iblParams.zip [Enc.idxW e])) Bl s (ibLitT C.fe l) (PostK C))
    (hFa : ∀ ty b, SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty,
      Enc.idxW b])) Bfa s (ibForallIOT (CoreFnsA.ioView (knot mode C n)) C.fe d ty b) (PostK C))
    (hLa : ∀ ty b, SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty,
      Enc.idxW b])) Bla s (ibLamIOT (CoreFnsA.ioView (knot mode C n)) d ty b) (PostK C))
    (hAp : SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) Bap s
      (inferAppIOAt (CoreFnsA.ioView (knot mode C n)) C.fe d e) (PostK C))
    (hPr : ∀ sn i pe, i < 2 ^ 64 → SpecR (σ := σ) (Pre C s (iprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW pe])) Bpr s (inferProj (CoreFnsA.ioView (knot mode C n)) C.fe d sn i pe) (PostK C))
    (hLet : ∀ (ty : EIdx) v b, SpecR (σ := σ) (Pre C s (iltParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty,
      Enc.idxW v, Enc.idxW b])) Blt s (ibLetIOT (CoreFnsA.ioView (knot mode C n)) d v b) (PostK C)) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) ibioBody s
      (ConRon.Arena.inferBodyIO (CoreFnsA.ioView (knot mode C n)) C.fe d e) (PostK C) := by
  refine specR_prologue (postK_locals C) (ib_none C _) ?_
  rw [inferBodyIO_eq]
  unfold ibioCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv kE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, kParams, ctxEnv]) ?_
  refine specR_viewP e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn hsh => ?_)
  refine specR_congr (view_bind_eq e v _ s hv) ?_
  rcases v with i | ⟨idx, ty⟩ | u | ⟨c, us⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, v, b⟩ | l | ⟨sn, i, pe⟩
  · -- bvar
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_hangI
  · -- fvar
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P _ _ []) ?_
    have hK : ∀ (Γ' : Env) (M' : Mem), idx < 2 ^ 64 → Γ'.get ibI = some (BitVec.ofNat 64 idx) →
        Γ'.get ibA = some (Enc.idxW ty) → Γ'.get kD = some (BitVec.ofNat 64 d) →
        SpecR (σ := σ) (Inv C s Γ' M' (ctxLocals ++ ibLocals)) ibFvK s
          (if idx < d then pure ty else fail (.invalid "free variable out of scope")) (PostK C) := by
      intro Γ' M' hib hI hA hD
      unfold ibFvK
      have hlt := Big.word_lt_iff idx d (by unfold B; omega) (by unfold B; omega)
      by_cases hid : idx < d
      · rw [if_pos hid]
        refine specR_ifI _ 1 (by simp [sev, hI, hD, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.mpr hid]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        exact specR_returnI _ (Enc.idxW ty) (by simp [hA]) (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 0 (by simp [sev, hI, hD, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
          (fun h => absurd rfl h) (fun _ => specR_hangI)
    have hlen : (encEView (.fvar idx ty)).length = 1 + (Enc.limbs idx).length := by
      simp [encEView, Enc.encFVar]; omega
    by_cases i0 : idx = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun hw => absurd hw (by decide))
      refine specR_assignI ibI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      refine hK _ _ (by decide) ?_ ?_ ?_ <;> simp +decide [Env.get, kParams, ctxEnv]
    · by_cases ib : idx < 2 ^ 64
      · have hl : Enc.limbs idx = [BitVec.ofNat 64 idx] := by rw [limbs_small idx ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' ibI _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 idx) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 idx) [] (M := []); simpa [encEView, Enc.encFVar, hl] using this) ?_
        refine hK _ _ ib ?_ ?_ ?_ <;> simp +decide [Env.get, kParams, ctxEnv]
      · have hl := ExI.limbs_len_ge2 idx (by omega)
        have hlt : 1 + (Enc.limbs idx).length < 2 ^ 61 := by rw [← hlen]; exact hsh
        have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 2#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
        exact specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  · -- sort
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P _ _ []) ?_
    exact specR_callKR ibX fIbs ibsParams [vv ibA] Bs [Enc.idxW u] (by decide) rfl (by decide) hc.s
      ⟨by simp, trivial⟩ (hSort u)
  · -- const
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P _ _ [] []) ?_
    exact specR_callKR ibX fIbcIO ibcParams [vv ibA, vv ibB] Bc [Enc.idxW c, Enc.idxW us] (by decide) rfl (by decide) hc.c
      ⟨by simp, by simp, trivial⟩ (hConst c us hv)
  · -- app
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_callKR ibX fIapIO kParams [vv kFu, vv kD, vv kE] Bap [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e]
      (by decide) rfl (by decide) hc.ap ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ hAp
  · -- la
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    exact specR_callKR ibX fIlaIO ifaParams [vv kFu, vv kD, vv ibA, vv ibB] Bla
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b] (by decide) rfl (by decide) hc.la
      ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, trivial⟩ (hLa ty b)
  · -- fa
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    exact specR_callKR ibX fIfaIO ifaParams [vv kFu, vv kD, vv ibA, vv ibB] Bfa
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b] (by decide) rfl (by decide) hc.fa
      ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, trivial⟩ (hFa ty b)
  · -- letE
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P _ _ [Enc.idxW b] []) ?_
    refine specR_loadI' ibC _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using (wordsAt_get P [Enc.idxW ty, Enc.idxW v, Enc.idxW b] 2 (by simp) [] : (P + BitVec.ofNat 64 (8 * 2), Enc.idxW b) ∈ _)) ?_
    exact specR_callKR ibX fIltIO iltParams [vv kFu, vv kD, vv ibA, vv ibB, vv ibC] Blt
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW v, Enc.idxW b] (by decide) rfl (by decide) hc.lt
      ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, by simp, trivial⟩ (hLet ty v b)
  · -- lit
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_callKR ibX fIbl iblParams [vv kE] Bl [Enc.idxW e] (by decide) rfl (by decide) hc.l
      ⟨by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ (hLit l hv)
  · -- proj
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    have er : encEView (.proj sn i pe) = Enc.idxW sn :: Enc.idxW pe :: Enc.limbs i := rfl
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW sn) (by decide) (by simp) (by simp)
      (by simpa [er] using wordsAt_mem0 P (Enc.idxW sn) (Enc.idxW pe :: Enc.limbs i) []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW pe) (by decide) (by simp +decide [sev]) rfl
      (by simpa [er] using wordsAt_mem1 P (Enc.idxW sn) (Enc.idxW pe) (Enc.limbs i) []) ?_
    have hlen : (encEView (.proj sn i pe)).length = (Enc.limbs i).length + 2 := by rw [er]; simp
    have hl58 : (Enc.limbs i).length + 2 < 2 ^ 61 := by rw [← hlen]; exact hsh
    rcases (by omega : (Enc.limbs i).length = 0 ∨ (Enc.limbs i).length = 1 ∨ 2 ≤ (Enc.limbs i).length) with h0 | h1 | h2
    · have hi0 : i = 0 := by have := (limbs_length_lt_iff i 0).mp (by omega); simpa using this
      subst hi0
      refine specR_ifI _ 1 (by simp [sev, hlen, h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine specR_assignI ibI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      exact specR_callKR ibX fIprIO iprParams [vv kFu, vv kD, vv ibA, vv ibI, vv ibB] Bpr
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 0, Enc.idxW pe] (by decide) rfl (by decide) hc.pr
        ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, by simp, trivial⟩ (hPr sn 0 pe (by decide))
    · have hiB : i < B := by have := (limbs_length_lt_iff i 1).mp (by omega); simpa using this
      have h2w : BitVec.ofNat 64 ((Enc.limbs i).length + 2) ≠ 2#64 := by rw [h1]; decide
      refine specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, hlen, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      have hx2 : (Enc.idxW sn :: Enc.idxW pe :: Enc.limbs i)[2]'(by simp; omega) = BitVec.ofNat 64 i := by
        show (Enc.limbs i)[0]'(by omega) = _
        rw [limbs_getElem i 0 (by omega)]; simp [Nat.mod_eq_of_lt hiB]
      refine specR_loadI' ibI _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 i) (by decide)
        (by simp +decide [sev]) rfl (by
          have := wordsAt_get P (Enc.idxW sn :: Enc.idxW pe :: Enc.limbs i) 2 (by simp; omega) []
          rw [hx2] at this; simpa [er] using this) ?_
      exact specR_callKR ibX fIprIO iprParams [vv kFu, vv kD, vv ibA, vv ibI, vv ibB] Bpr
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW pe] (by decide) rfl (by decide) hc.pr
        ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, by simp, trivial⟩ (hPr sn i pe hiB)
    · have h2w : BitVec.ofNat 64 ((Enc.limbs i).length + 2) ≠ 2#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      have h3w : BitVec.ofNat 64 ((Enc.limbs i).length + 2) ≠ 3#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w)
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h3w)
        (fun h => absurd rfl h) (fun _ => specR_hangI)

theorem run_bind_ok {α β : Type} {m : AM α} {k : α → AM β} {s s1 : AState} {a : α}
    (h : m s = .ok (a, s1)) : (m >>= k) s = k a s1 := by
  show (do let r ← m s; match r with | (a, s) => k a s) = _
  rw [h]; rfl

theorem run_bind_err {α β : Type} {m : AM α} {k : α → AM β} {s : AState} {e : CheckError}
    (h : m s = .error e) : (m >>= k) s = .error e := by
  show (do let r ← m s; match r with | (a, s) => k a s) = _
  rw [h]; rfl

theorem fail_run {α : Type} (e : CheckError) (s : AState) : (fail e : AM α) s = .error e := rfl

theorem ibConst_ok (fe : IFEnv) (c : NIdx) (us : LsIdx) (s s' : AState) (a : EIdx)
    (h : ibConstT fe c us s = .ok (a, s')) : ibConstIOT fe c us s = .ok (a, s') := by
  unfold ibConstT at h
  unfold ibConstIOT
  rcases hf : fe.find? c with _ | ci <;> simp only [hf] at h ⊢
  · exfalso
    rcases hu : unknownConstError c s with e | ⟨err, s1⟩
    · rw [run_bind_err hu] at h; cases h
    · rw [run_bind_ok hu, fail_run] at h; cases h
  · rcases hv : s.store.lss.view us with _ | v
    · exfalso
      have : viewLs us s = .error (.internal "arena: dangling level-list handle") := by
        show (do let st ← (get : AM AState); match st.store.lss.view us with | some v => pure v | none => fail _) s = _
        simp [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, hv, fail, throwThe, MonadExceptOf.throw,
          StateT.lift, Except.bind, throw, pure, Except.pure]
      rw [run_bind_err this] at h; cases h
    · have h1 : viewLs us s = .ok (v, s) := by
        show (do let st ← (get : AM AState); match st.store.lss.view us with | some v => pure v | none => fail _) s = _
        simp [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, hv, pure, StateT.pure, Except.bind, Except.pure]
      rw [run_bind_ok h1] at h
      rw [run_bind_ok (viewLsLen_run us s v hv)]
      simpa using h

theorem specR_okImp {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m m' : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : ∀ a s', m s = .ok (a, s') → m' s = .ok (a, s'))
    (hs : SpecR P c s m R) : SpecR P c s m' R := by
  intro t ht
  rcases hs t ht with h1 | ⟨w, hw, a, s', hm, hr⟩
  · exact Or.inl h1
  · exact Or.inr ⟨w, hw, a, s', h a s' hm, hr⟩

theorem ikIO_spec (C : Ctx) (hok : CtxOK C)
    (hmg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hmp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hct : C.code.lookup CT.fCT = some (CV.cvParams.map (fun p => (p, ShapeHOL.one)), CT.ctBody C, .one))
    (s : AState) (c : NIdx) (us : LsIdx)
    (hCt : ∀ ci o ok, C.fe.find? c = some ci → CIE C.EB C.EH o ci →
      EBlk C.EH ok (ci.toConstantVal.levelParams.map Enc.idxW) →
      SpecR (σ := σ) (Pre C s (CV.cvParams.zip [Enc.idxW ci.toConstantVal.name, ecell C ok,
        Enc.idxW ci.toConstantVal.type, Enc.idxW us])) (CT.ctBody C) s (constTyAt ci.toConstantVal us) (PostK C)) :
    SpecR (σ := σ) (Pre C s (ibcParams.zip [Enc.idxW c, Enc.idxW us])) (ikBody C) s (ibConstIOT C.fe c us) (PostK C) :=
  specR_okImp (fun a s' h => ibConst_ok C.fe c us s s' a h) (ik_spec C hok hmg hmp hct s c us hCt)

end

end ConPanqueque.T.WC
