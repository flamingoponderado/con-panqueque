import ConPanqueque.T.LvlImax
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `rest`: the cases of `leqCore` after the `zero` short-cuts

Both sides are viewed once; the tags pick con-leche's first matching case.
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub

/-! ## The twin's case order -/

theorem rest_pp (n : Nat) (a x : ConLeche.Name) (d : Int) :
    ConLeche.Level.rest n (.param a) (.param x) d = some (decide (a = x) && decide (d ≥ 0)) := by
  unfold ConLeche.Level.rest; simp

theorem rest_pz (n : Nat) (a : ConLeche.Name) (d : Int) : ConLeche.Level.rest n (.param a) .zero d = some false := by
  unfold ConLeche.Level.rest; simp

theorem rest_zp (n : Nat) (a : ConLeche.Name) (d : Int) : ConLeche.Level.rest n .zero (.param a) d = some (decide (d ≥ 0)) := by
  unfold ConLeche.Level.rest; simp

theorem rest_sl (n : Nat) (u r : ConLeche.Level) (d : Int) : ConLeche.Level.rest n (.succ u) r d = ConLeche.Level.leqCore n u r (d - 1) := by
  unfold ConLeche.Level.rest; cases r <;> simp

theorem rest_sr (n : Nat) (l u : ConLeche.Level) (d : Int) (h : ltag l ≠ 1) :
    ConLeche.Level.rest n l (.succ u) d = ConLeche.Level.leqCore n l u (d + 1) := by
  unfold ConLeche.Level.rest; cases l <;> simp_all [ltag]

theorem rest_ml (n : Nat) (a b r : ConLeche.Level) (d : Int) (h : ltag r ≠ 1) :
    ConLeche.Level.rest n (.max a b) r d = (match ConLeche.Level.leqCore n a r d with
      | none => none | some false => some false | some true => ConLeche.Level.leqCore n b r d) := by
  unfold ConLeche.Level.rest; cases r <;> simp_all [ltag] <;> rcases ConLeche.Level.leqCore n a _ d with _ | _ | _ <;> rfl

theorem rest_mr (n : Nat) (l x y : ConLeche.Level) (d : Int) (h : ltag l = 0 ∨ ltag l = 4) :
    ConLeche.Level.rest n l (.max x y) d = (match ConLeche.Level.leqCore n l x d with
      | none => none | some true => some true | some false => ConLeche.Level.leqCore n l y d) := by
  unfold ConLeche.Level.rest; cases l <;> simp_all [ltag] <;> rcases ConLeche.Level.leqCore n _ x d with _ | _ | _ <;> rfl

theorem rest_ii (n : Nat) (a b x y : ConLeche.Level) (d : Int) :
    ConLeche.Level.rest n (.imax a b) (.imax x y) d =
      if decide (a = x) && decide (b = y) && decide (d ≥ 0) then some true
      else ConLeche.Level.imaxRules n (.imax a b) (.imax x y) d := by
  unfold ConLeche.Level.rest; simp

theorem rest_else (n : Nat) (l r : ConLeche.Level) (d : Int) (h1 : ltag l ≠ 1) (h2 : ltag r ≠ 1) (h3 : ltag l ≠ 2)
    (h4 : ¬ (ltag l = 4 ∧ ltag r = 4)) (h5 : ¬ (ltag l = 4 ∧ ltag r = 0)) (h6 : ¬ (ltag l = 0 ∧ ltag r = 4))
    (h7 : ¬ (ltag r = 2 ∧ ltag l ≠ 3)) (h8 : ¬ (ltag l = 3 ∧ ltag r = 3)) :
    ConLeche.Level.rest n l r d = ConLeche.Level.imaxRules n l r d := by
  unfold ConLeche.Level.rest; cases l <;> cases r <;> simp_all [ltag]

/-! ## The program -/

def retK (k : Nat) : ProgHOL 64 := .return (.const (BitVec.ofNat 64 k))
def and2 (e1 e2 : ExpHOL 64) : ExpHOL 64 := .op .and [e1, e2]
def signNeg : ExpHOL 64 := .shift .lsr (vv pD) (.const 63)

def callIm : ProgHOL 64 :=
  .seq (.call (some (some (.local, lV), none)) fImax [vv pFu, vv pLa, vv pLb, vv pD]) (.return (vv lV))

def ppP : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (vv lA3))) (.seq (.assign .local lB (.load .one (vv lY)))
  (.seq (.call (some (some (.local, lZ), none)) fNeq [vv lA1, vv lB])
  (.ite (eqC lZ 0) (retK 1) (.ite signNeg (retK 1) (retK 2)))))

def succL : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (vv lA3)))
  (.seq (callLeqP lV lA1 pLb (.op .sub [vv pD, .const 1])) (.return (vv lV)))

def succR : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (vv lY)))
  (.seq (callLeqP lV pLa lA1 (.op .add [vv pD, .const 1])) (.return (vv lV)))

def maxL : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (vv lA3))) (.seq (.assign .local lB (.load .one (.op .add [vv lA3, .const 8])))
  (.seq (callLeqP lV lA1 pLb (vv pD)) (.ite (eqC lV 0) (retK 0) (.ite (eqC lV 1) (retK 1)
  (.seq (callLeqP lV lB pLb (vv pD)) (.return (vv lV)))))))

def maxR : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (vv lY))) (.seq (.assign .local lB (.load .one (.op .add [vv lY, .const 8])))
  (.seq (callLeqP lV pLa lA1 (vv pD)) (.ite (eqC lV 0) (retK 0) (.ite (eqC lV 2) (retK 2)
  (.seq (callLeqP lV pLa lB (vv pD)) (.return (vv lV)))))))

def iiP : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (vv lA3))) (.seq (.assign .local lB (.load .one (.op .add [vv lA3, .const 8])))
  (.seq (.assign .local lZ (.load .one (vv lY))) (.seq (.assign .local lD1 (.load .one (.op .add [vv lY, .const 8])))
  (.seq (.call (some (some (.local, lE0), none)) fLvlEq [vv lA1, vv lZ])
  (.ite (eqC lE0 0) callIm
  (.seq (.call (some (some (.local, lE0), none)) fLvlEq [vv lB, vv lD1])
  (.ite (eqC lE0 0) callIm (.ite signNeg callIm (retK 2)))))))))

def restBody : ProgHOL 64 :=
  prologue leqLocals
  (.seq (.assign .local lQ (vv pLa)) (lvViewP (.seq (.assign .local lA2 (vv lX)) (.seq (.assign .local lA3 (vv lY))
  (.seq (.assign .local lQ (vv pLb)) (lvViewP
  (.ite (and2 (eqC lA2 4) (eqC lX 4)) ppP
  (.ite (and2 (eqC lA2 4) (eqC lX 0)) (retK 1)
  (.ite (and2 (eqC lA2 0) (eqC lX 4)) (.ite signNeg (retK 1) (retK 2))
  (.ite (eqC lA2 1) succL
  (.ite (eqC lX 1) succR
  (.ite (eqC lA2 2) maxL
  (.ite (eqC lX 2) (.ite (eqC lA2 3) callIm maxR)
  (.ite (and2 (eqC lA2 3) (eqC lX 3)) iiP callIm))))))))))))))

section
variable {σ : Type}

theorem lvScratch_DQ : ∀ z, z ∈ lvScratch → z ∈ DQ := by
  intro z hz
  simp only [lvScratch, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem lkids_mono {HB : BitVec 64} {H : List (BitVec 64)} {ls : LStore} {Pc : BitVec 64} {M M' : Mem}
    (hm : ∀ p, p ∈ M → p ∈ M') : ∀ l, LKids HB H ls Pc M l → LKids HB H ls Pc M' l
  | .zero, _ => trivial
  | .succ _, ⟨wu, mu, ru⟩ => ⟨wu, hm _ mu, ru⟩
  | .max _ _, ⟨wu, wv, mu, mv, ru, rv⟩ => ⟨wu, wv, hm _ mu, hm _ mv, ru, rv⟩
  | .imax _ _, ⟨wu, wv, mu, mv, ru, rv⟩ => ⟨wu, wv, hm _ mu, hm _ mv, ru, rv⟩
  | .param _, ⟨nh, f, mu, hd⟩ => ⟨nh, f, hm _ mu, hd⟩

theorem specR_ifAnd2 {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : MlS) (va a vb b : Nat) (hva : va < 2 ^ 64)
    (ha : a < 2 ^ 64) (hvb : vb < 2 ^ 64) (hb : b < 2 ^ 64)
    (hx : Γ.get x = some (BitVec.ofNat 64 va)) (hy : Γ.get y = some (BitVec.ofNat 64 vb))
    (h1 : va = a ∧ vb = b → SpecR (Inv C s Γ M D) c1 s m R) (h2 : ¬ (va = a ∧ vb = b) → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite (and2 (eqC x a) (eqC y b)) c1 c2) s m R := by
  by_cases e1 : va = a <;> by_cases e2 : vb = b
  · subst e1 e2
    exact specR_ifI _ 1 (by simp [and2, eqC, sev, hx, hy, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => h1 ⟨rfl, rfl⟩) (fun h => absurd h (by decide))
  all_goals exact specR_ifI _ 0 (by simp [and2, eqC, sev, hx, hy, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      word_eq_iff va a hva ha, word_eq_iff vb b hvb hb, e1, e2]) (fun h => absurd rfl h) (fun _ => h2 (by omega))

theorem specR_ifSign {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (d : Int) (hl : -2 ^ 63 ≤ d) (hh : d < 2 ^ 63)
    (hx : Γ.get pD = some (iW d))
    (h1 : d < 0 → SpecR (Inv C s Γ M D) c1 s m R) (h2 : 0 ≤ d → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite signNeg c1 c2) s m R := by
  refine specR_ifI _ (iW d >>> (63 : BitVec 64).toNat) (by simp [signNeg, sev, hx]) (fun h => h1 ?_)
    (fun h => h2 ((iW_sign d hl hh).mp h))
  by_cases h0 : 0 ≤ d
  · exact absurd ((iW_sign d hl hh).mpr h0) h
  · omega

theorem params_noneQ (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ leqLocals → (ctxEnv C ++ leqParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ leqParams := by
    simp only [leqLocals, lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [leqLocals, lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
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

end

end ConPanqueque.T.LLeq
