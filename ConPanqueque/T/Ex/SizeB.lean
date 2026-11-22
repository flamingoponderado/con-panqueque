import ConPanqueque.T.Ex.GetAppFn2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `sizeB`: a multi-arm walk with `Nat` results

The twin's `sizeB` (binder node count; five leaf constructors, three child arms) as a Pancake
function. `Nat` results are words below `2^63`; a sum that would reach `2^63` halts (a resource
limit), which keeps every intermediate sum exact.
-/

namespace ConPanqueque.T.ExS
open ConPanqueque.T ConPanqueque.T.Ex

def fSizeB := ofString "sizeB"
def lA1 := ofString "a1"
def lA2 := ofString "a2"
def lA3 := ofString "a3"
def lY := ofString "y"
def lZ := ofString "z"
def lS1 := ofString "s1"

def callS (x arg : MlS) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fSizeB [.op .sub [vv pFu, .const 1], vv arg]

/-- Return `e` unless it reaches `2^63`. -/
def guardRet (e : ExpHOL 64) : ProgHOL 64 := .ite (.shift .lsr e (.const 63)) hang (.return e)

def arm2 : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (callS lX lA1) (.seq (callS lY lA2)
    (guardRet (.op .add [.op .add [vv lX, vv lY], .const 1])))))

def arm3 : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
  (.seq (callS lX lA1) (.seq (callS lY lA2) (.seq (callS lZ lA3)
  (.seq (.assign .local lS1 (.op .add [vv lX, vv lY]))
    (.ite (.shift .lsr (vv lS1) (.const 63)) hang
      (guardRet (.op .add [.op .add [vv lS1, vv lZ], .const 1])))))))))

def armP : ProgHOL 64 :=
  .seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (callS lX lA2) (guardRet (.op .add [vv lX, .const 1])))

def core : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
     (.ite (.op .or [.cmp .equal (vv lDg) (.const 4),
             .op .or [.cmp .equal (vv lDg) (.const 5), .cmp .equal (vv lDg) (.const 6)]]) arm2
      (.ite (.cmp .equal (vv lDg) (.const 7)) arm3
       (.ite (.cmp .equal (vv lDg) (.const 9)) armP (.return (.const 1))))))))

def locals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, lA1, lA2, lA3, lX, lY, lZ, lS1]
def body : ProgHOL 64 := prologue locals core

section
variable {σ : Type}

def PostN (C : Ctx) (s : AState) (a : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  a < 2 ^ 63 ∧ w = BitVec.ofNat 64 a ∧ s' = s ∧ SR C s st

theorem postN_locals (C : Ctx) (s : AState) : ∀ (a : Nat) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostN C s a w s' st → PostN C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

abbrev D : List MlS := ctxLocals ++ locals

/-- The spec of a recursive call at fuel `n`. -/
def Rec (C : Ctx) (n : Nat) : Prop :=
  ∀ (h : EIdx) (s : AState), SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)]) body s
    (sizeB n h) (PostN C s)

theorem callS_spec {β : Type} (C : Ctx) (hcode : C.code.lookup fSizeB = some ([(pFu, .one), (pH, .one)], body, .one))
    (n : Nat) (ih : Rec (σ := σ) C n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {c : EIdx} {k : Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (hx : x ∈ D)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (harg : Γ.get arg = some (Enc.idxW c))
    (hk : ∀ a, a < 2 ^ 63 → SpecR (Inv C s ((x, BitVec.ofNat 64 a) :: Γ) [] D) rest s (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (callS x arg) rest) s (sizeB n c >>= k) R := by
  refine specR_call2I x fSizeB pFu pH (by decide) _ _ body (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW c) hx hcode
    (by simp [sev, hfu]) (by simp [harg]) (PostN C s) (fun _ _ _ _ hp => by rw [hp.2.2.1]; exact hp.2.2.2)
    (fun u hu h1 h2 v hv => by
      subst hv
      exact ih c s _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; rw [h1, ofNat_succ_sub_one]
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun a w s' st hp => ?_)
  obtain ⟨ha, hw, hs, _⟩ := hp
  subst hw hs
  exact hk a ha

theorem guardRet_spec (C : Ctx) {s : AState} {Γ : Env} {M : Mem} (e : ExpHOL 64) (c : Nat) (hc : c < 2 ^ 64)
    (he : sev Γ e = some (BitVec.ofNat 64 c)) :
    SpecR (Inv (σ := σ) C s Γ M D) (guardRet e) s (pure c) (PostN C s) := by
  refine specR_ifI (.shift .lsr e (.const 63)) (BitVec.ofNat 64 c >>> (63 : BitVec 64).toNat) (by simp [sev, he])
    (fun _ => specR_hangI) (fun hw => ?_)
  have hlt := (shr63_eq_zero c hc).mp hw
  exact specR_returnI e _ he (fun t ht => ⟨hlt, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem arm2_spec (C : Ctx) (hcode : C.code.lookup fSizeB = some ([(pFu, .one), (pH, .one)], body, .one))
    (n : Nat) (ih : Rec (σ := σ) C n) {s : AState} {Γ : Env} {M : Mem} (P : BitVec 64) (c1 c2 : EIdx)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hrp : Γ.get lRp = some P)
    (hm1 : (P + BitVec.ofNat 64 0, Enc.idxW c1) ∈ M) (hm2 : (P + BitVec.ofNat 64 8, Enc.idxW c2) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M D) arm2 s (do let x ← sizeB n c1; let y ← sizeB n c2; pure (x + y + 1)) (PostN C s) := by
  refine specR_loadI' lA1 _ _ _ _ (by decide) (by simp [sev, hrp]) rfl hm1 ?_
  refine specR_loadI' lA2 _ _ _ _ (by decide) (by simp +decide [sev, hrp]) rfl hm2 ?_
  refine callS_spec C hcode n ih lX lA1 (by decide) (by simp +decide [hfu]) (by simp +decide)
    (fun a ha => ?_)
  refine callS_spec C hcode n ih lY lA2 (by decide) (by simp +decide [hfu]) (by simp +decide)
    (fun b hb => ?_)
  exact guardRet_spec C _ (a + b + 1) (by omega)
    (by simp +decide [sev]; rw [word_add_eq a b ha hb, word_add1_eq])

theorem arm3_spec (C : Ctx) (hcode : C.code.lookup fSizeB = some ([(pFu, .one), (pH, .one)], body, .one))
    (n : Nat) (ih : Rec (σ := σ) C n) {s : AState} {Γ : Env} {M : Mem} (P : BitVec 64) (c1 c2 c3 : EIdx)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hrp : Γ.get lRp = some P)
    (hm1 : (P + BitVec.ofNat 64 0, Enc.idxW c1) ∈ M) (hm2 : (P + BitVec.ofNat 64 8, Enc.idxW c2) ∈ M)
    (hm3 : (P + BitVec.ofNat 64 16, Enc.idxW c3) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M D) arm3 s
      (do let x ← sizeB n c1; let y ← sizeB n c2; let z ← sizeB n c3; pure (x + y + z + 1)) (PostN C s) := by
  refine specR_loadI' lA1 _ _ _ _ (by decide) (by simp [sev, hrp]) rfl hm1 ?_
  refine specR_loadI' lA2 _ _ _ _ (by decide) (by simp +decide [sev, hrp]) rfl hm2 ?_
  refine specR_loadI' lA3 _ _ _ _ (by decide) (by simp +decide [sev, hrp]) rfl hm3 ?_
  refine callS_spec C hcode n ih lX lA1 (by decide) (by simp +decide [hfu]) (by simp +decide)
    (fun a ha => ?_)
  refine callS_spec C hcode n ih lY lA2 (by decide) (by simp +decide [hfu]) (by simp +decide)
    (fun b hb => ?_)
  refine callS_spec C hcode n ih lZ lA3 (by decide) (by simp +decide [hfu]) (by simp +decide)
    (fun c hc => ?_)
  refine specR_assignI lS1 _ (BitVec.ofNat 64 (a + b)) (by decide)
    (by simp +decide [sev]; rw [word_add_eq a b ha hb]) ?_
  refine specR_ifI (.shift .lsr (vv lS1) (.const 63)) (BitVec.ofNat 64 (a + b) >>> (63 : BitVec 64).toNat)
    (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
  have hab := (shr63_eq_zero (a + b) (by omega)).mp hw
  exact guardRet_spec C _ (a + b + c + 1) (by omega)
    (by simp +decide [sev]; rw [word_add_eq (a + b) c hab hc, word_add1_eq])

theorem armP_spec (C : Ctx) (hcode : C.code.lookup fSizeB = some ([(pFu, .one), (pH, .one)], body, .one))
    (n : Nat) (ih : Rec (σ := σ) C n) {s : AState} {Γ : Env} {M : Mem} (P : BitVec 64) (c : EIdx)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hrp : Γ.get lRp = some P)
    (hm : (P + BitVec.ofNat 64 8, Enc.idxW c) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M D) armP s (do let x ← sizeB n c; pure (x + 1)) (PostN C s) := by
  refine specR_loadI' lA2 _ _ _ _ (by decide) (by simp [sev, hrp]) rfl hm ?_
  refine callS_spec C hcode n ih lX lA2 (by decide) (by simp +decide [hfu]) (by simp +decide)
    (fun a ha => ?_)
  exact guardRet_spec C _ (a + 1) (by omega) (by simp +decide [sev]; rw [word_add1_eq])

end

section
variable {σ : Type}

theorem hL_locals (C : Ctx) (Γ : Env) (hΓ : ∀ x, x ∈ locals → Γ.get x = none) :
    ∀ x, x ∈ locals → (ctxEnv C ++ Γ).get x = none := by
  intro x hx
  have := hΓ x hx
  simp only [locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (simp +decide [ctxEnv]; exact this)

theorem params_none (n : Nat) (h : EIdx) :
    ∀ x, x ∈ locals → Env.get [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)] x = none := by
  intro x hx
  simp only [locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem sizeB_spec (C : Ctx) (hcode : C.code.lookup fSizeB = some ([(pFu, .one), (pH, .one)], body, .one)) :
    ∀ fuel, fuel < 2 ^ 64 → Rec (σ := σ) C fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ h s
    refine specR_prologue (postN_locals C s) (hL_locals C _ (params_none 0 h)) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf h s
    have ih' := ih (by omega)
    refine specR_prologue (postN_locals C s) (hL_locals C _ (params_none (n + 1) h)) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (m' := ConRon.Arena.view h >>= fun v => match v with
      | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure 1
      | .app f a => sizeBArmApp n f a
      | .lam ty body | .forallE ty body => sizeBArmBind n ty body
      | .letE ty val body => sizeBArmLet n ty val body
      | .proj _ _ sub => sizeBArmProj n sub) (by rw [sizeB]; rfl) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) rfl ?_
    refine specR_viewI h rfl rfl rfl (by decide) (fun v P _ => ?_)
    cases v with
    | bvar i =>
      refine specR_congr (m' := pure 1) rfl ?_
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (.const 1) _ rfl (fun t ht => ⟨by decide, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | fvar idx ty =>
      refine specR_congr (m' := pure 1) rfl ?_
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (.const 1) _ rfl (fun t ht => ⟨by decide, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | sort u =>
      refine specR_congr (m' := pure 1) rfl ?_
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (.const 1) _ rfl (fun t ht => ⟨by decide, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | const c us =>
      refine specR_congr (m' := pure 1) rfl ?_
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (.const 1) _ rfl (fun t ht => ⟨by decide, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | lit l =>
      refine specR_congr (m' := pure 1) rfl ?_
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (.const 1) _ rfl (fun t ht => ⟨by decide, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | app f a =>
      refine specR_congr (m' := sizeBArmApp n f a) rfl ?_
      refine specR_congr (by rw [sizeBArmApp]) ?_
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      exact arm2_spec C hcode n ih' P f a rfl rfl (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _)
    | lam ty b =>
      refine specR_congr (m' := sizeBArmBind n ty b) rfl ?_
      refine specR_congr (by rw [sizeBArmBind]) ?_
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      exact arm2_spec C hcode n ih' P ty b rfl rfl (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _)
    | forallE ty b =>
      refine specR_congr (m' := sizeBArmBind n ty b) rfl ?_
      refine specR_congr (by rw [sizeBArmBind]) ?_
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      exact arm2_spec C hcode n ih' P ty b rfl rfl (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _)
    | letE ty val b =>
      refine specR_congr (m' := sizeBArmLet n ty val b) rfl ?_
      refine specR_congr (by rw [sizeBArmLet]) ?_
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      exact arm3_spec C hcode n ih' P ty val b rfl rfl (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _)
        (wordsAt_mem2 _ _ _ _ _ _)
    | proj c i e =>
      refine specR_congr (m' := sizeBArmProj n e) rfl ?_
      refine specR_congr (by rw [sizeBArmProj]) ?_
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      exact armP_spec C hcode n ih' P e rfl rfl (wordsAt_mem1 _ _ _ _ _)

end

end ConPanqueque.T.ExS
