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

theorem specR_retOB {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (k : Nat) (o : Option Bool)
    (hk : BitVec.ofNat 64 k = obW o) : SpecR (σ := σ) (Inv C s Γ M D) (retK k) s (pure o) (PostOB C) :=
  specR_returnI _ _ rfl (fun t ht => ⟨hk, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem callRetOB {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : lV ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs) (o : Option Bool)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s (pure o) (PostOB C)) :
    SpecR (Inv (σ := σ) C s Γ M D) (.seq (.call (some (some (.local, lV), none)) f es) (.return (vv lV))) s (pure o)
      (PostOB C) := by
  refine specR_congr (m' := pure o >>= fun o => pure o) (by simp) ?_
  exact callOB_spec lV f ps es B vs hnd hl hx hC hes o hspec
    (specR_returnI (vv lV) _ (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩))

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

section
variable {σ : Type}

theorem rest_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (hcB : C.code.lookup fByC = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody C, .one))
    (hcI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one))
    (hcR : C.code.lookup fImax = some (leqParams.map (fun p => (p, ShapeHOL.one)), imBody C, .one))
    (hcE : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    (B : ProgHOL 64) (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), B, .one))
    (n : Nat) (hn : n < 2 ^ 64) (ih : RecLeq (σ := σ) C B n) :
    ∀ (H : List (BitVec 64)) (l r : ConLeche.Level) (wl wr : BitVec 64) (d : Int) (s : AState),
      LRep C.HB H s.store.ls wl l → LRep C.HB H s.store.ls wr r → d.natAbs + n + 1 < 2 ^ 62 →
      SpecR (Pre (σ := σ) (ctxH C H) s (leqParams.zip [BitVec.ofNat 64 n, wl, wr, iW d])) restBody s
        (pure (ConLeche.Level.rest n l r d)) (PostOB (ctxH C H)) := by
  intro H l r wl wr d s hl hr hd
  have hok' := ctxOK_H hok H
  have hdl : -2 ^ 63 ≤ d := by omega
  have hdh : d < 2 ^ 63 := by omega
  have hd0 : d.natAbs + n < 2 ^ 62 := by omega
  refine specR_prologue (postOB_locals _) (params_noneQ _ _) ?_
  refine specR_assignI lQ (vv pLa) wl (by decide) (by simp +decide [ctxEnv, leqParams]) ?_
  refine specR_lvViewI hok' wl l (by simp) hl (by simp +decide [ctxEnv, leqParams] <;> rfl)
    (by simp +decide [ctxEnv, leqParams] <;> rfl) lvScratch_DQ (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => ?_)
  refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 (ltag l)) (by decide) (by simp [hx1]) ?_
  refine specR_assignI lA3 (vv lY) Pc (by decide) (by simp +decide [hy1]) ?_
  refine specR_assignI lQ (vv pLb) wr (by decide)
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, leqParams]) ?_
  refine specR_lvViewI hok' wr r (by simp) hr
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, leqParams] <;> rfl)
    (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, leqParams] <;> rfl) lvScratch_DQ
    (fun Γ2 M2 Pr hp2 hx2 hy2 hmm2 hk2 => ?_)
  have hk1' := lkids_mono hmm2 l hk1
  have base : ∀ z, z ∉ lvScratch → z ≠ lQ → z ≠ lA2 → z ≠ lA3 →
      Env.get Γ2 z = Env.get (ctxEnv (ctxH C H) ++ leqParams.zip [BitVec.ofNat 64 n, wl, wr, iW d]) z := by
    intro z h1 h2 h3 h4
    rw [hp2 z h1]; simp only [Env.get_cons, h2, h3, h4, ite_false]; rw [hp1 z h1]; simp [h2]
  have gFu : Env.get Γ2 pFu = some (BitVec.ofNat 64 n) := by
    rw [base _ (by decide) (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
  have gLa : Env.get Γ2 pLa = some wl := by
    rw [base _ (by decide) (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
  have gLb : Env.get Γ2 pLb = some wr := by
    rw [base _ (by decide) (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
  have gD : Env.get Γ2 pD = some (iW d) := by
    rw [base _ (by decide) (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
  have gA2 : Env.get Γ2 lA2 = some (BitVec.ofNat 64 (ltag l)) := by rw [hp2 _ (by decide)]; simp +decide
  have gA3 : Env.get Γ2 lA3 = some Pc := by rw [hp2 _ (by decide)]; simp +decide
  have tl := ltag_lt l
  have tr := ltag_lt r
  refine specR_ifAnd2 lA2 lX (ltag l) 4 (ltag r) 4 (by omega) (by decide) (by omega) (by decide) gA2 hx2
    (fun ⟨e1, e2⟩ => ?_) (fun c1 => ?_)
  · obtain ⟨a, rfl⟩ : ∃ a, l = .param a := by cases l <;> simp_all [ltag]
    obtain ⟨x, rfl⟩ : ∃ x, r = .param x := by cases r <;> simp_all [ltag]
    obtain ⟨nh1, f1, m1, hd1⟩ := hk1'
    obtain ⟨nh2, f2, m2, hd2⟩ := hk2
    rw [rest_pp]
    unfold ppP
    refine specR_loadI' lA1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) _ (by decide) (by simp [gA3]) (by simp) m1 ?_
    refine specR_loadI' lB (vv lY) Pr (Pr + BitVec.ofNat 64 (8 * 0)) _ (by decide) (by simp +decide [hy2])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (decide (a = x)) >>= fun e => pure (some (e && decide (d ≥ 0)))) (by simp) ?_
    refine callNeq_spec (C := ctxH C H) hcN lZ lA1 lB nh1 nh2 a x f1 f2 hd1 hd2 (by decide) (by simp +decide)
      (by simp +decide) ?_
    by_cases hax : a = x
    · simp only [hax, decide_true, Bool.true_and, ite_true]
      refine specR_ifI _ 0 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifSign d hdl hdh (by simp +decide [gD]) (fun hneg => specR_retOB 1 _ ?_)
        (fun hpos => specR_retOB 2 _ (by simp [obW, hpos]))
      have : ¬ (0 ≤ d) := by omega
      simp [obW, this]
    · simp only [hax, decide_false, Bool.false_and]
      refine specR_ifI _ 1 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_retOB 1 _ rfl) (fun h => absurd h (by decide))
  refine specR_ifAnd2 lA2 lX (ltag l) 4 (ltag r) 0 (by omega) (by decide) (by omega) (by decide) gA2 hx2
    (fun ⟨e1, e2⟩ => ?_) (fun c2 => ?_)
  · obtain ⟨a, rfl⟩ : ∃ a, l = .param a := by cases l <;> simp_all [ltag]
    obtain rfl : r = .zero := by cases r <;> simp_all [ltag]
    rw [rest_pz]; exact specR_retOB 1 _ rfl
  refine specR_ifAnd2 lA2 lX (ltag l) 0 (ltag r) 4 (by omega) (by decide) (by omega) (by decide) gA2 hx2
    (fun ⟨e1, e2⟩ => ?_) (fun c3 => ?_)
  · obtain rfl : l = .zero := by cases l <;> simp_all [ltag]
    obtain ⟨a, rfl⟩ : ∃ a, r = .param a := by cases r <;> simp_all [ltag]
    rw [rest_zp]
    refine specR_ifSign d hdl hdh gD (fun hneg => specR_retOB 1 _ ?_) (fun hpos => specR_retOB 2 _ (by simp [obW, hpos]))
    have : ¬ (0 ≤ d) := by omega
    simp [obW, this]
  refine specR_ifEq lA2 (ltag l) 1 (by omega) (by decide) gA2 (fun e => ?_) (fun c4 => ?_)
  · obtain ⟨u, rfl⟩ : ∃ u, l = .succ u := by cases l <;> simp_all [ltag]
    obtain ⟨wu, mu, ru⟩ := hk1'
    rw [rest_sl]
    unfold succL
    refine specR_loadI' lA1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp [gA3]) (by simp) mu ?_
    exact callRetOB (C := ctxH C H) fLeq leqParams [vv pFu, vv lA1, vv pLb, .op .sub [vv pD, .const 1]] B
        [BitVec.ofNat 64 n, wu, wr, iW (d - 1)] (by decide) rfl (by decide) hcL
        ⟨by simp +decide [gFu], by simp +decide [], by simp +decide [gLb], by simp +decide [sev, gD]; exact iW_sub1 d, trivial⟩ _
        (ih H _ _ wu wr (d - 1) s ru hr (by omega))
  refine specR_ifEq lX (ltag r) 1 (by omega) (by decide) hx2 (fun e => ?_) (fun c5 => ?_)
  · obtain ⟨u, rfl⟩ : ∃ u, r = .succ u := by cases r <;> simp_all [ltag]
    obtain ⟨wu, mu, ru⟩ := hk2
    rw [rest_sr n l u d c4]
    unfold succR
    refine specR_loadI' lA1 (vv lY) Pr (Pr + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [hy2])
      (by simp) mu ?_
    exact callRetOB (C := ctxH C H) fLeq leqParams [vv pFu, vv pLa, vv lA1, .op .add [vv pD, .const 1]] B
        [BitVec.ofNat 64 n, wl, wu, iW (d + 1)] (by decide) rfl (by decide) hcL
        ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide [], by simp +decide [sev, gD]; exact iW_add1 d, trivial⟩ _
        (ih H _ _ wl wu (d + 1) s hl ru (by omega))
  refine specR_ifEq lA2 (ltag l) 2 (by omega) (by decide) gA2 (fun e => ?_) (fun c6 => ?_)
  · obtain ⟨a, b, rfl⟩ : ∃ a b, l = .max a b := by cases l <;> simp_all [ltag]
    obtain ⟨wa, wb, ma, mb, ra, rb⟩ := hk1'
    rw [rest_ml n a b r d c5]
    unfold maxL
    refine specR_loadI' lA1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wa (by decide) (by simp [gA3]) (by simp) ma ?_
    refine specR_loadI' lB (.op .add [vv lA3, .const 8]) (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wb (by decide)
      (by simp +decide [sev, gA3]) (by simp) mb ?_
    refine specR_congr (m' := pure (ConLeche.Level.leqCore n a r d) >>= fun o => pure (match o with
      | none => none | some false => some false | some true => ConLeche.Level.leqCore n b r d)) (by simp) ?_
    refine callOB_spec (C := ctxH C H) lV fLeq leqParams [vv pFu, vv lA1, vv pLb, vv pD] B
      [BitVec.ofNat 64 n, wa, wr, iW d] (by decide) rfl (by decide) hcL
      ⟨by simp +decide [gFu], by simp +decide, by simp +decide [gLb], by simp +decide [gD], trivial⟩ _
      (ih H a r wa wr d s ra hr hd0) ?_
    rcases ho : ConLeche.Level.leqCore n a r d with _ | b0
    · refine specR_ifI _ 1 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_retOB 0 _ rfl) (fun h => absurd h (by decide))
    cases b0
    · refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_retOB 1 _ rfl) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact callRetOB (C := ctxH C H) fLeq leqParams [vv pFu, vv lB, vv pLb, vv pD] B
        [BitVec.ofNat 64 n, wb, wr, iW d] (by decide) rfl (by decide) hcL
        ⟨by simp +decide [gFu], by simp +decide, by simp +decide [gLb], by simp +decide [gD], trivial⟩ _
        (ih H b r wb wr d s rb hr hd0)
  refine specR_ifEq lX (ltag r) 2 (by omega) (by decide) hx2 (fun e => ?_) (fun c7 => ?_)
  · refine specR_ifEq lA2 (ltag l) 3 (by omega) (by decide) gA2 (fun e' => ?_) (fun c8 => ?_)
    · have hl3 : ltag l = 3 := e'
      rw [rest_else n l r d c4 c5 c6 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact callRetOB (C := ctxH C H) fImax leqParams [vv pFu, vv pLa, vv pLb, vv pD] (imBody C)
          [BitVec.ofNat 64 n, wl, wr, iW d] (by decide) rfl (by decide) hcR
          ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide [gLb], by simp +decide [gD], trivial⟩ _
          (im_spec C hok hcS hcN hcM hcC hcB hcI B hcL n hn ih H l r wl wr d s hl hr hd0)
    · obtain ⟨x, y, rfl⟩ : ∃ x y, r = .max x y := by cases r <;> simp_all [ltag]
      obtain ⟨wx, wy, mx, my, rx, ry⟩ := hk2
      rw [rest_mr n l x y d (by omega)]
      unfold maxR
      refine specR_loadI' lA1 (vv lY) Pr (Pr + BitVec.ofNat 64 (8 * 0)) wx (by decide) (by simp +decide [hy2])
        (by simp) mx ?_
      refine specR_loadI' lB (.op .add [vv lY, .const 8]) (Pr + 8) (Pr + BitVec.ofNat 64 (8 * 1)) wy (by decide)
        (by simp +decide [sev, hy2]) (by simp) my ?_
      refine specR_congr (m' := pure (ConLeche.Level.leqCore n l x d) >>= fun o => pure (match o with
        | none => none | some true => some true | some false => ConLeche.Level.leqCore n l y d)) (by simp) ?_
      refine callOB_spec (C := ctxH C H) lV fLeq leqParams [vv pFu, vv pLa, vv lA1, vv pD] B
        [BitVec.ofNat 64 n, wl, wx, iW d] (by decide) rfl (by decide) hcL
        ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide, by simp +decide [gD], trivial⟩ _
        (ih H l x wl wx d s hl rx hd0) ?_
      rcases ho : ConLeche.Level.leqCore n l x d with _ | b0
      · refine specR_ifI _ 1 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => specR_retOB 0 _ rfl) (fun h => absurd h (by decide))
      cases b0
      · refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun h => absurd rfl h) (fun _ => ?_)
        exact callRetOB (C := ctxH C H) fLeq leqParams [vv pFu, vv pLa, vv lB, vv pD] B
            [BitVec.ofNat 64 n, wl, wy, iW d] (by decide) rfl (by decide) hcL
            ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide, by simp +decide [gD], trivial⟩ _
            (ih H l y wl wy d s hl ry hd0)
      refine specR_ifI _ 0 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [eqC, sev, obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_retOB 2 _ rfl) (fun h => absurd h (by decide))
  refine specR_ifAnd2 lA2 lX (ltag l) 3 (ltag r) 3 (by omega) (by decide) (by omega) (by decide) gA2 hx2
    (fun ⟨e1, e2⟩ => ?_) (fun c9 => ?_)
  · obtain ⟨a, b, rfl⟩ : ∃ a b, l = .imax a b := by cases l <;> simp_all [ltag]
    obtain ⟨x, y, rfl⟩ : ∃ x y, r = .imax x y := by cases r <;> simp_all [ltag]
    obtain ⟨wa, wb, ma, mb, ra, rb⟩ := hk1'
    obtain ⟨wx, wy, mx, my, rx, ry⟩ := hk2
    rw [rest_ii]
    unfold iiP
    refine specR_loadI' lA1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wa (by decide) (by simp [gA3]) (by simp) ma ?_
    refine specR_loadI' lB (.op .add [vv lA3, .const 8]) (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wb (by decide)
      (by simp +decide [sev, gA3]) (by simp) mb ?_
    refine specR_loadI' lZ (vv lY) Pr (Pr + BitVec.ofNat 64 (8 * 0)) wx (by decide) (by simp +decide [hy2])
      (by simp) mx ?_
    refine specR_loadI' lD1 (.op .add [vv lY, .const 8]) (Pr + 8) (Pr + BitVec.ofNat 64 (8 * 1)) wy (by decide)
      (by simp +decide [sev, hy2]) (by simp) my ?_
    generalize hV : (if decide (a = x) && decide (b = y) && decide (d ≥ 0) then some true
      else ConLeche.Level.imaxRules n (.imax a b) (.imax x y) d) = V
    refine specR_congr (m' := pure (decide (a = x)) >>= fun _ => pure V) (by simp) ?_
    refine callEq_spec (C := ctxH C H) hcE lE0 lA1 lZ a x wa wx (by decide) (by simp +decide) (by simp +decide)
      (lvlEq_spec (ctxH C H) hok' hcN hcE a wa wx x s ra rx) ?_
    rcases Classical.em (a = x) with hax | hax
    case inr =>
      simp [hax] at hV
      subst hV
      refine specR_ifI _ 1 (by simp +decide [eqC, sev, hax, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact callRetOB (C := ctxH C H) fImax leqParams [vv pFu, vv pLa, vv pLb, vv pD] (imBody C)
          [BitVec.ofNat 64 n, wl, wr, iW d] (by decide) rfl (by decide) hcR
          ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide [gLb], by simp +decide [gD], trivial⟩ _
          (im_spec C hok hcS hcN hcM hcC hcB hcI B hcL n hn ih H (.imax a b) (.imax x y) wl wr d s hl hr hd0)
    subst hax
    simp only [decide_true, Bool.true_and] at hV
    refine specR_ifI _ 0 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := pure (decide (b = y)) >>= fun _ => pure V) (by simp) ?_
    refine callEq_spec (C := ctxH C H) hcE lE0 lB lD1 b y wb wy (by decide) (by simp +decide) (by simp +decide)
      (lvlEq_spec (ctxH C H) hok' hcN hcE b wb wy y s rb ry) ?_
    rcases Classical.em (b = y) with hby | hby
    case inr =>
      simp [hby] at hV
      subst hV
      refine specR_ifI _ 1 (by simp +decide [eqC, sev, hby, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact callRetOB (C := ctxH C H) fImax leqParams [vv pFu, vv pLa, vv pLb, vv pD] (imBody C)
          [BitVec.ofNat 64 n, wl, wr, iW d] (by decide) rfl (by decide) hcR
          ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide [gLb], by simp +decide [gD], trivial⟩ _
          (im_spec C hok hcS hcN hcM hcC hcB hcI B hcL n hn ih H _ _ wl wr d s hl hr hd0)
    subst hby
    simp only [decide_true, Bool.true_and] at hV
    refine specR_ifI _ 0 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifSign d hdl hdh (by simp +decide [gD]) (fun hneg => ?_) (fun hpos => ?_)
    · have : ¬ (0 ≤ d) := by omega
      simp only [ge_iff_le, this, decide_false, ite_false] at hV
      subst hV
      exact callRetOB (C := ctxH C H) fImax leqParams [vv pFu, vv pLa, vv pLb, vv pD] (imBody C)
          [BitVec.ofNat 64 n, wl, wr, iW d] (by decide) rfl (by decide) hcR
          ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide [gLb], by simp +decide [gD], trivial⟩ _
          (im_spec C hok hcS hcN hcM hcC hcB hcI B hcL n hn ih H _ _ wl wr d s hl hr hd0)
    · simp only [ge_iff_le, hpos, decide_true, ite_true] at hV
      subst hV
      exact specR_retOB 2 _ rfl
  rw [rest_else n l r d c4 c5 c6 (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact callRetOB (C := ctxH C H) fImax leqParams [vv pFu, vv pLa, vv pLb, vv pD] (imBody C)
      [BitVec.ofNat 64 n, wl, wr, iW d] (by decide) rfl (by decide) hcR
      ⟨by simp +decide [gFu], by simp +decide [gLa], by simp +decide [gLb], by simp +decide [gD], trivial⟩ _
      (im_spec C hok hcS hcN hcM hcC hcB hcI B hcL n hn ih H l r wl wr d s hl hr hd0)

end

end ConPanqueque.T.LLeq
