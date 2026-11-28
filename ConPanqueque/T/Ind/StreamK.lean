import ConPanqueque.T.Ind.GenRecHead

/-!
# The K flag a recursor of an unnested block has (`recKExpected`)

`kexpBody`: one constructor, the block a proposition, one member (read from the shape: any member count), the
constructor without fields.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.WC

def kxSh := ofString "kx_sh"
def kxQ := ofString "kx_q"
def kxN := ofString "kx_n"
def kxP := ofString "kx_p"
def kxF := ofString "kx_f"
def kxM := ofString "kx_m"
def kxK := ofString "kx_k"
def fKexp := ofString "recKExpected"

def kxParams : List MlS := [kxSh, kxQ]
def kxLocals : List MlS := [kxN, kxP, kxF, kxM, kxK]

def kxBody : ProgHOL 64 := prologue kxLocals
  (.seq (.assign .local kxN (.load .one (vv kxQ)))
  (.ite (.cmp .equal (vv kxN) (.const 1))
    (.seq (.assign .local kxP (.load .one (.op .add [vv kxSh, .const 48])))
    (.ite (.cmp .equal (vv kxP) (.const 0)) (.return (.const 0))
      (.seq (.assign .local kxM (.load .one (vv kxSh)))
      (.seq (.assign .local kxK (.load .one (vv kxM)))
      (.ite (.cmp .equal (vv kxK) (.const 1))
        (.seq (.assign .local kxF (.load .one (.op .add [vv kxQ, .const 16])))
        (.ite (.cmp .equal (vv kxF) (.const 0)) (.return (.const 1)) (.return (.const 0))))
        (.return (.const 0)))))))
    (.return (.const 0))))

section
variable {σ : Type}

theorem kx_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kxLocals → (ctxEnv C ++ kxParams.zip vals).get x = none :=
  Knot.params_none C kxLocals kxParams vals (by decide) (by decide)

def PostKX (C : Ctx) (s : AState) (b : Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = boolW b ∧ SR C s' st

theorem kx_spec (C : Ctx) (p : BlockShape) (osh : Nat) (hip : C.H[osh + 6]? = some (boolW p.isProp))
    (om : Nat) (hom : C.H[osh]? = some (cellA C om)) (hkm : C.H[om]? = some (BitVec.ofNat 64 p.k))
    (hkb : p.k < 2 ^ 63) (m : TargetMajor) (t : Nat) (hmm : m.member = some t) (oq : Nat) (hcr : CtorsRep C C.H oq m.ctors)
    (hcsl : m.ctors.length < 2 ^ 63) (s : AState) :
    SpecR (σ := σ) (Pre C s (kxParams.zip [cellA C osh, cellA C oq])) kxBody s (pure (recKExpected p m))
      (PostKX C s) := by
  refine specR_prologue (fun a w s' st L ⟨h0, h1, h2⟩ => ⟨h0, h1, sr_of_eq h2 rfl rfl rfl rfl⟩) (kx_none C _) ?_
  refine UD.specR_heapLoadI' (C := C) kxN _ oq _ hcr.1 (by decide) (by simp +decide [sev, Env.get, kxParams, ctxEnv]) ?_
  have hret : ∀ (Γ : Env) (b : Bool) (v : BitVec 64), recKExpected p m = b → v = boolW b →
      SpecR (σ := σ) (Inv C s Γ [] (ctxLocals ++ kxLocals)) (.return (.const v)) s (pure (recKExpected p m)) (PostKX C s) :=
    fun Γ b v hb hv => specR_returnI _ v rfl (fun t ht => ⟨rfl, by rw [hb, hv], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rcases hcs : m.ctors with _ | ⟨c0, _ | ⟨c1, cs⟩⟩
  · have : recKExpected p m = false := by simp [recKExpected, hmm, hcs]
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hcs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => hret _ false 0 this rfl)
  · rw [hcs] at hcr
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := C) kxP _ (osh + 6) _ hip (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, kxParams, ctxEnv]; exact cellA_add_ofNat C osh 6) ?_
    cases hp : p.isProp
    · have : recKExpected p m = false := by simp [recKExpected, hmm, hcs, hp]
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => hret _ false 0 this rfl) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := C) kxM _ osh _ hom (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, kxParams, ctxEnv]) ?_
    refine UD.specR_heapLoadI' (C := C) kxK _ om _ hkm (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, kxParams, ctxEnv]) ?_
    by_cases hk' : ¬ p.k = 1
    · have : recKExpected p m = false := by simp [recKExpected, hmm, hcs, hk']
      have hne : BitVec.ofNat 64 p.k ≠ 1#64 := fun e => hk' (by have := congrArg BitVec.toNat e; simp at this; omega)
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => hret _ false 0 this rfl)
    have hk : p.k = 1 := Decidable.of_not_not hk'
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, -, -, ⟨hnf, hnfb⟩⟩ := hcr.2 0 (by simp)
    refine UD.specR_heapLoadI' (C := C) kxF _ (oq + 2 + 2 * 0) _ hnf (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, kxParams, ctxEnv]; exact cellA_add_ofNat C oq 2) ?_
    simp only [List.getElem_cons_zero] at hnfb ⊢
    by_cases h0 : c0.2 = 0
    · have : recKExpected p m = true := by simp [recKExpected, hmm, hcs, hp, hk, h0]
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => hret _ true 1 this rfl) (fun h => absurd h (by decide))
    · have : recKExpected p m = false := by simp [recKExpected, hmm, hcs, hp, h0]
      have hne : BitVec.ofNat 64 c0.2 ≠ 0#64 := fun e => h0 (by have := congrArg BitVec.toNat e; simp at this; omega)
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => hret _ false 0 this rfl)
  · have : recKExpected p m = false := by simp [recKExpected, hmm, hcs]
    have hne : BitVec.ofNat 64 (c0 :: c1 :: cs).length ≠ 1#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [hcs] at hcsl; simp at this hcsl; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hcs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => hret _ false 0 this rfl)

end

end ConPanqueque.T.Ind
