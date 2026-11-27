import ConPanqueque.Logic.InternRerun

/-!
# Interning a literal without the memo

`internExprGo m e` interns a transient expression tree, skipping the subterms its memo `m` already holds.
`plainE e` interns the same tree with no memo: every node, children first, in the same order. When every
memo entry is a subterm that `plainE` re-interns to its handle without moving the state (`MemoOK`), the two
agree: same handle, same state (`internExprGo_plain`). A port that interns a literal node by node therefore
refines the memoised walk.
-/

namespace ConPanqueque.Logic.PlainIntern

open ConPanqueque.Logic.InternRerun ConRon.Arena ConRon.Bridge ConRon.Arena.Frontend

/-- Intern a transient expression, every node, children first. -/
def plainE : ConLeche.Expr → AM EIdx
  | .bvar i => internE (.bvar i)
  | .sort u => do
    let hu ← internLevel u
    internE (.sort hu)
  | .const n us => do
    let hn ← internName n
    let hus ← internLevels us
    internE (.const hn hus)
  | .lit l => internE (.lit l)
  | .fvar i ty => do
    let t ← plainE ty
    internE (.fvar i t)
  | .app f a => do
    let hf ← plainE f
    let ha ← plainE a
    internE (.app hf ha)
  | .lam ty b => do
    let ht ← plainE ty
    let hb ← plainE b
    internE (.lam ht hb)
  | .forallE ty b => do
    let ht ← plainE ty
    let hb ← plainE b
    internE (.forallE ht hb)
  | .letE ty v b => do
    let ht ← plainE ty
    let hv ← plainE v
    let hb ← plainE b
    internE (.letE ht hv hb)
  | .proj n i sub => do
    let hn ← internName n
    let hs ← plainE sub
    internE (.proj hn i hs)

theorem plainE_rr : ∀ e : ConLeche.Expr, RR (plainE e)
  | .bvar _ => by unfold plainE; exact internE_rr _
  | .sort u => by unfold plainE; exact RR.bind (internLevel_rr u) (fun _ => internE_rr _)
  | .const n us => by
    unfold plainE
    exact RR.bind (internName_rr n) (fun _ => RR.bind (internLevels_rr us) (fun _ => internE_rr _))
  | .lit _ => by unfold plainE; exact internE_rr _
  | .fvar i ty => by unfold plainE; exact RR.bind (plainE_rr ty) (fun _ => internE_rr _)
  | .app f a => by
    unfold plainE; exact RR.bind (plainE_rr f) (fun _ => RR.bind (plainE_rr a) (fun _ => internE_rr _))
  | .lam ty b => by
    unfold plainE; exact RR.bind (plainE_rr ty) (fun _ => RR.bind (plainE_rr b) (fun _ => internE_rr _))
  | .forallE ty b => by
    unfold plainE; exact RR.bind (plainE_rr ty) (fun _ => RR.bind (plainE_rr b) (fun _ => internE_rr _))
  | .letE ty v b => by
    unfold plainE
    exact RR.bind (plainE_rr ty) (fun _ => RR.bind (plainE_rr v) (fun _ => RR.bind (plainE_rr b)
      (fun _ => internE_rr _)))
  | .proj n i sub => by
    unfold plainE
    exact RR.bind (internName_rr n) (fun _ => RR.bind (plainE_rr sub) (fun _ => internE_rr _))

/-- Every memo entry re-interns to its handle without moving the state. -/
def MemoOK (m : EMemo) (s : AState) : Prop := ∀ e h, m[e]? = some h → plainE e s = .ok (h, s)

theorem memoOK_empty (s : AState) : MemoOK ∅ s := fun e h he => by simp at he

theorem memoOK_mono {m : EMemo} {s s' : AState} (h : MemoOK m s) (ho : Off s.store) (ho' : Off s'.store)
    (hp : FP s.store s'.store) : MemoOK m s' :=
  fun e x he => ((plainE_rr e) s x s ho (h e x he)).2.2 s' ho' hp

theorem memoOK_insert {m : EMemo} {s : AState} {e : ConLeche.Expr} {h : EIdx} (hm : MemoOK m s)
    (he : plainE e s = .ok (h, s)) : MemoOK (m.insert e h) s := by
  intro e' x hx
  rw [Std.HashMap.getElem?_insert] at hx
  split at hx
  · rename_i hee
    have : e = e' := by simpa using hee
    subst this; simp only [Option.some.injEq] at hx; subst hx; exact he
  · exact hm e' x hx

/-- A fresh run re-runs to itself at its end state. -/
theorem plainE_self {e : ConLeche.Expr} {s s' : AState} {r : EIdx} (ho : Off s.store)
    (h : plainE e s = .ok (r, s')) : Off s'.store ∧ FP s.store s'.store ∧ plainE e s' = .ok (r, s') := by
  obtain ⟨ho', hp, hr⟩ := (plainE_rr e) s r s' ho h
  exact ⟨ho', hp, hr s' ho' (FP.refl _)⟩

open ConLeche in
/-- **The memoised walk is the plain one** at a sound memo: same handle, same state, the memo still sound. -/
theorem internExprGo_plain : ∀ (e : ConLeche.Expr) (m : EMemo) (s : AState) (r : EIdx) (s' : AState),
    Off s.store → MemoOK m s → plainE e s = .ok (r, s') →
    ∃ m', internExprGo m e s = .ok ((m', r), s') ∧ MemoOK m' s'
  | .bvar i, m, s, r, s', ho, hm, hrun => by
    unfold plainE at hrun
    obtain ⟨ho', hp, -⟩ := (internE_rr _) s r s' ho hrun
    refine ⟨m, ?_, memoOK_mono hm ho ho' hp⟩
    unfold internExprGo; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, hrun]
  | .lit l, m, s, r, s', ho, hm, hrun => by
    unfold plainE at hrun
    obtain ⟨ho', hp, -⟩ := (internE_rr _) s r s' ho hrun
    refine ⟨m, ?_, memoOK_mono hm ho ho' hp⟩
    unfold internExprGo; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, hrun]
  | .sort u, m, s, r, s', ho, hm, hrun => by
    unfold plainE at hrun
    obtain ⟨ho', hp, -⟩ := (plainE_rr (.sort u)) s r s' ho (by unfold plainE; exact hrun)
    refine ⟨m, ?_, memoOK_mono hm ho ho' hp⟩
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
    unfold internExprGo; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, g1, r1]
  | .const n us, m, s, r, s', ho, hm, hrun => by
    unfold plainE at hrun
    obtain ⟨ho', hp, -⟩ := (plainE_rr (.const n us)) s r s' ho (by unfold plainE; exact hrun)
    refine ⟨m, ?_, memoOK_mono hm ho ho' hp⟩
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    unfold internExprGo; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, g1, g2, r2]
  | .fvar i ty, m, s, r, s', ho, hm, hrun => by
    unfold internExprGo
    cases hk : m[(.fvar i ty : ConLeche.Expr)]? with
    | some h =>
      have e := hm _ h hk
      rw [hrun] at e; simp only [Except.ok.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨m, rfl, hm⟩
    | none =>
      have hrun0 := hrun
      unfold plainE at hrun
      obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨ho1, hp1, -⟩ := plainE_self ho g1
      obtain ⟨m1, e1, hm1⟩ := internExprGo_plain ty m s x1 s1 ho hm g1
      obtain ⟨ho3, hp3, -⟩ := (internE_rr _) s1 r s' ho1 r1
      refine ⟨m1.insert (.fvar i ty) r, ?_, memoOK_insert (memoOK_mono hm1 ho1 ho3 hp3) (plainE_self ho hrun0).2.2⟩
      simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, r1]
  | .app f a, m, s, r, s', ho, hm, hrun => by
    unfold internExprGo
    cases hk : m[(.app f a : ConLeche.Expr)]? with
    | some h =>
      have e := hm _ h hk
      rw [hrun] at e; simp only [Except.ok.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨m, rfl, hm⟩
    | none =>
      have hrun0 := hrun
      unfold plainE at hrun
      obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
      obtain ⟨ho1, hp1, -⟩ := plainE_self ho g1
      obtain ⟨ho2, hp2, -⟩ := plainE_self ho1 g2
      obtain ⟨m1, e1, hm1⟩ := internExprGo_plain f m s x1 s1 ho hm g1
      obtain ⟨m2, e2, hm2⟩ := internExprGo_plain a m1 s1 x2 s2 ho1 hm1 g2
      obtain ⟨ho3, hp3, -⟩ := (internE_rr _) s2 r s' ho2 r2
      refine ⟨m2.insert (.app f a) r, ?_, memoOK_insert (memoOK_mono hm2 ho2 ho3 hp3) (plainE_self ho hrun0).2.2⟩
      simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2, r2]
  | .lam ty b, m, s, r, s', ho, hm, hrun => by
    unfold internExprGo
    cases hk : m[(.lam ty b : ConLeche.Expr)]? with
    | some h =>
      have e := hm _ h hk
      rw [hrun] at e; simp only [Except.ok.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨m, rfl, hm⟩
    | none =>
      have hrun0 := hrun
      unfold plainE at hrun
      obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
      obtain ⟨ho1, hp1, -⟩ := plainE_self ho g1
      obtain ⟨ho2, hp2, -⟩ := plainE_self ho1 g2
      obtain ⟨m1, e1, hm1⟩ := internExprGo_plain ty m s x1 s1 ho hm g1
      obtain ⟨m2, e2, hm2⟩ := internExprGo_plain b m1 s1 x2 s2 ho1 hm1 g2
      obtain ⟨ho3, hp3, -⟩ := (internE_rr _) s2 r s' ho2 r2
      refine ⟨m2.insert (.lam ty b) r, ?_, memoOK_insert (memoOK_mono hm2 ho2 ho3 hp3) (plainE_self ho hrun0).2.2⟩
      simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2, r2]
  | .forallE ty b, m, s, r, s', ho, hm, hrun => by
    unfold internExprGo
    cases hk : m[(.forallE ty b : ConLeche.Expr)]? with
    | some h =>
      have e := hm _ h hk
      rw [hrun] at e; simp only [Except.ok.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨m, rfl, hm⟩
    | none =>
      have hrun0 := hrun
      unfold plainE at hrun
      obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
      obtain ⟨ho1, hp1, -⟩ := plainE_self ho g1
      obtain ⟨ho2, hp2, -⟩ := plainE_self ho1 g2
      obtain ⟨m1, e1, hm1⟩ := internExprGo_plain ty m s x1 s1 ho hm g1
      obtain ⟨m2, e2, hm2⟩ := internExprGo_plain b m1 s1 x2 s2 ho1 hm1 g2
      obtain ⟨ho3, hp3, -⟩ := (internE_rr _) s2 r s' ho2 r2
      refine ⟨m2.insert (.forallE ty b) r, ?_, memoOK_insert (memoOK_mono hm2 ho2 ho3 hp3) (plainE_self ho hrun0).2.2⟩
      simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2, r2]
  | .letE ty v b, m, s, r, s', ho, hm, hrun => by
    unfold internExprGo
    cases hk : m[(.letE ty v b : ConLeche.Expr)]? with
    | some h =>
      have e := hm _ h hk
      rw [hrun] at e; simp only [Except.ok.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨m, rfl, hm⟩
    | none =>
      have hrun0 := hrun
      unfold plainE at hrun
      obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
      obtain ⟨x3, s3, g3, r3⟩ := AM.bind_ok r2
      obtain ⟨ho1, -, -⟩ := plainE_self ho g1
      obtain ⟨ho2, -, -⟩ := plainE_self ho1 g2
      obtain ⟨ho3, -, -⟩ := plainE_self ho2 g3
      obtain ⟨m1, e1, hm1⟩ := internExprGo_plain ty m s x1 s1 ho hm g1
      obtain ⟨m2, e2, hm2⟩ := internExprGo_plain v m1 s1 x2 s2 ho1 hm1 g2
      obtain ⟨m3, e3, hm3⟩ := internExprGo_plain b m2 s2 x3 s3 ho2 hm2 g3
      obtain ⟨ho4, hp4, -⟩ := (internE_rr _) s3 r s' ho3 r3
      refine ⟨m3.insert (.letE ty v b) r, ?_, memoOK_insert (memoOK_mono hm3 ho3 ho4 hp4) (plainE_self ho hrun0).2.2⟩
      simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2, e3, r3]
  | .proj n i sub, m, s, r, s', ho, hm, hrun => by
    unfold internExprGo
    cases hk : m[(.proj n i sub : ConLeche.Expr)]? with
    | some h =>
      have e := hm _ h hk
      rw [hrun] at e; simp only [Except.ok.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨m, rfl, hm⟩
    | none =>
      have hrun0 := hrun
      unfold plainE at hrun
      obtain ⟨x0, s0, g0, r0⟩ := AM.bind_ok hrun
      obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok r0
      obtain ⟨ho0, hp0, -⟩ := (internName_rr n) s x0 s0 ho g0
      obtain ⟨ho1, -, -⟩ := plainE_self ho0 g1
      obtain ⟨m1, e1, hm1⟩ := internExprGo_plain sub m s0 x1 s1 ho0 (memoOK_mono hm ho ho0 hp0) g1
      obtain ⟨ho3, hp3, -⟩ := (internE_rr _) s1 r s' ho1 r1
      refine ⟨m1.insert (.proj n i sub) r, ?_, memoOK_insert (memoOK_mono hm1 ho1 ho3 hp3) (plainE_self ho hrun0).2.2⟩
      simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, g0, e1, r1]

/-! ## Constants, rules, blocks -/

def plainEs : List ConLeche.Expr → AM (List EIdx)
  | [] => pure []
  | e :: es => do
    let h ← plainE e
    let hs ← plainEs es
    pure (h :: hs)

def plainCV (cv : ConLeche.ConstantVal) : AM IConstantVal := do
  let n ← internName cv.name
  let lps ← Frontend.internNameList cv.levelParams
  let ty ← plainE cv.type
  pure ⟨n, lps, ty⟩

def plainFire : ConLeche.RecRuleFire → AM IRecRuleFire
  | .plain => pure .plain
  | .nested lvls pins => do
    let hls ← internLevelList lvls
    let hps ← plainEs pins
    pure (.nested hls hps)
  | .levels lvls => do
    let hls ← internLevelList lvls
    pure (.levels hls)

def plainRule (rl : ConLeche.RecRule) : AM IRecRule := do
  let c ← internName rl.ctor
  let f ← plainFire rl.fire
  let r ← plainE rl.rhs
  pure ⟨c, rl.nfields, f, r⟩

def plainRules : List ConLeche.RecRule → AM (List IRecRule)
  | [] => pure []
  | r :: rs => do
    let h ← plainRule r
    let hs ← plainRules rs
    pure (h :: hs)

def plainCI : ConLeche.ConstantInfo → AM IConstantInfo
  | .axiomInfo v => do pure (.axiomInfo (← plainCV v))
  | .defnInfo v e h => do
    let cv ← plainCV v
    let x ← plainE e
    pure (.defnInfo cv x h)
  | .thmInfo v => do pure (.thmInfo (← plainCV v))
  | .indInfo v c => do
    let cv ← plainCV v
    let caps ← internCaps c
    pure (.indInfo cv caps)
  | .ctorInfo v nP nF T => do
    let cv ← plainCV v
    let t ← internName T
    pure (.ctorInfo cv nP nF t)
  | .recInfo v mI rP k rs => do
    let cv ← plainCV v
    let rules ← plainRules rs
    pure (.recInfo cv mI rP k rules)

def plainCIList : List ConLeche.ConstantInfo → AM (List IConstantInfo)
  | [] => pure []
  | c :: cs => do
    let h ← plainCI c
    let hs ← plainCIList cs
    pure (h :: hs)

/-- A memo-free step that is rerunnable keeps a sound memo sound. -/
theorem memo_step {α : Type} {x : AM α} (hx : RR x) {m : EMemo} {s s' : AState} {a : α}
    (ho : Off s.store) (hm : MemoOK m s) (h : x s = .ok (a, s')) : Off s'.store ∧ MemoOK m s' := by
  obtain ⟨ho', hp, -⟩ := hx s a s' ho h
  exact ⟨ho', memoOK_mono hm ho ho' hp⟩

theorem internExprList_plain : ∀ (es : List ConLeche.Expr) (m : EMemo) (s : AState) (r : List EIdx) (s' : AState),
    Off s.store → MemoOK m s → plainEs es s = .ok (r, s') →
    Off s'.store ∧ ∃ m', Frontend.internExprList m es s = .ok ((m', r), s') ∧ MemoOK m' s'
  | [], m, s, r, s', ho, hm, h => by
    unfold plainEs at h; obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ho, m, rfl, hm⟩
  | e :: es, m, s, r, s', ho, hm, h => by
    unfold plainEs at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, -, -⟩ := plainE_self ho g1
    obtain ⟨m1, e1, hm1⟩ := internExprGo_plain e m s x1 s1 ho hm g1
    obtain ⟨ho2, m2, e2, hm2⟩ := internExprList_plain es m1 s1 x2 s' ho1 hm1 g2
    refine ⟨ho2, m2, ?_, hm2⟩
    unfold Frontend.internExprList
    simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2]

theorem plainEs_rr : ∀ es : List ConLeche.Expr, RR (plainEs es)
  | [] => by unfold plainEs; exact RR.pure _
  | e :: es => by unfold plainEs; exact RR.bind (plainE_rr e) (fun _ => RR.bind (plainEs_rr es) (fun _ => RR.pure _))

theorem internCV_plain (cv : ConLeche.ConstantVal) (m : EMemo) (s : AState) (r : IConstantVal) (s' : AState)
    (ho : Off s.store) (hm : MemoOK m s) (h : plainCV cv s = .ok (r, s')) :
    Off s'.store ∧ ∃ m', Frontend.internCV m cv s = .ok ((m', r), s') ∧ MemoOK m' s' := by
  unfold plainCV at h
  obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
  obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨x3, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r3
  obtain ⟨ho1, hm1⟩ := memo_step (internName_rr _) ho hm g1
  obtain ⟨ho2, hm2⟩ := memo_step (internNameList_rr _) ho1 hm1 g2
  obtain ⟨ho3, -, -⟩ := plainE_self ho2 g3
  obtain ⟨m3, e3, hm3⟩ := internExprGo_plain _ m s2 x3 s' ho2 hm2 g3
  refine ⟨ho3, m3, ?_, hm3⟩
  unfold Frontend.internCV
  simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, g1, g2, e3]

theorem internFire_plain (f : ConLeche.RecRuleFire) (m : EMemo) (s : AState) (r : IRecRuleFire) (s' : AState)
    (ho : Off s.store) (hm : MemoOK m s) (h : plainFire f s = .ok (r, s')) :
    Off s'.store ∧ ∃ m', Frontend.internFire m f s = .ok ((m', r), s') ∧ MemoOK m' s' := by
  cases f with
  | plain =>
    unfold plainFire at h; obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ho, m, rfl, hm⟩
  | nested lvls pins =>
    unfold plainFire at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, hm1⟩ := memo_step (internLevelList_rr _) ho hm g1
    obtain ⟨ho2, m2, e2, hm2⟩ := internExprList_plain pins m s1 x2 s' ho1 hm1 g2
    refine ⟨ho2, m2, ?_, hm2⟩
    unfold Frontend.internFire
    simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, g1, e2]
  | levels lvls =>
    unfold plainFire at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
    obtain ⟨ho1, hm1⟩ := memo_step (internLevelList_rr _) ho hm g1
    refine ⟨ho1, m, ?_, hm1⟩
    unfold Frontend.internFire
    simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, g1]

theorem plainFire_rr (f : ConLeche.RecRuleFire) : RR (plainFire f) := by
  cases f with
  | plain => unfold plainFire; exact RR.pure _
  | nested lvls pins =>
    unfold plainFire
    exact RR.bind (internLevelList_rr _) (fun _ => RR.bind (plainEs_rr _) (fun _ => RR.pure _))
  | levels lvls => unfold plainFire; exact RR.bind (internLevelList_rr _) (fun _ => RR.pure _)

theorem internRule_plain (rl : ConLeche.RecRule) (m : EMemo) (s : AState) (r : IRecRule) (s' : AState)
    (ho : Off s.store) (hm : MemoOK m s) (h : plainRule rl s = .ok (r, s')) :
    Off s'.store ∧ ∃ m', Frontend.internRule m rl s = .ok ((m', r), s') ∧ MemoOK m' s' := by
  unfold plainRule at h
  obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
  obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨x3, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r3
  obtain ⟨ho1, hm1⟩ := memo_step (internName_rr _) ho hm g1
  obtain ⟨ho2, m2, e2, hm2⟩ := internFire_plain _ m s1 x2 s2 ho1 hm1 g2
  obtain ⟨ho3, -, -⟩ := plainE_self ho2 g3
  obtain ⟨m3, e3, hm3⟩ := internExprGo_plain _ m2 s2 x3 s' ho2 hm2 g3
  refine ⟨ho3, m3, ?_, hm3⟩
  unfold Frontend.internRule
  simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, g1, e2, e3]

theorem plainRule_rr (rl : ConLeche.RecRule) : RR (plainRule rl) := by
  unfold plainRule
  exact RR.bind (internName_rr _) (fun _ => RR.bind (plainFire_rr _) (fun _ => RR.bind (plainE_rr _)
    (fun _ => RR.pure _)))

theorem internRules_plain : ∀ (rs : List ConLeche.RecRule) (m : EMemo) (s : AState) (r : List IRecRule) (s' : AState),
    Off s.store → MemoOK m s → plainRules rs s = .ok (r, s') →
    Off s'.store ∧ ∃ m', Frontend.internRules m rs s = .ok ((m', r), s') ∧ MemoOK m' s'
  | [], m, s, r, s', ho, hm, h => by
    unfold plainRules at h; obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ho, m, rfl, hm⟩
  | rl :: rs, m, s, r, s', ho, hm, h => by
    unfold plainRules at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, m1, e1, hm1⟩ := internRule_plain rl m s x1 s1 ho hm g1
    obtain ⟨ho2, m2, e2, hm2⟩ := internRules_plain rs m1 s1 x2 s' ho1 hm1 g2
    refine ⟨ho2, m2, ?_, hm2⟩
    unfold Frontend.internRules
    simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2]

theorem plainRules_rr : ∀ rs : List ConLeche.RecRule, RR (plainRules rs)
  | [] => by unfold plainRules; exact RR.pure _
  | r :: rs => by
    unfold plainRules; exact RR.bind (plainRule_rr r) (fun _ => RR.bind (plainRules_rr rs) (fun _ => RR.pure _))

theorem plainCV_rr (cv : ConLeche.ConstantVal) : RR (plainCV cv) := by
  unfold plainCV
  exact RR.bind (internName_rr _) (fun _ => RR.bind (internNameList_rr _) (fun _ => RR.bind (plainE_rr _)
    (fun _ => RR.pure _)))

theorem internCI_plain (c : ConLeche.ConstantInfo) (m : EMemo) (s : AState) (r : IConstantInfo) (s' : AState)
    (ho : Off s.store) (hm : MemoOK m s) (h : plainCI c s = .ok (r, s')) :
    Off s'.store ∧ ∃ m', Frontend.internCI m c s = .ok ((m', r), s') ∧ MemoOK m' s' := by
  cases c with
  | axiomInfo v =>
    simp only [plainCI] at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
    obtain ⟨ho1, m1, e1, hm1⟩ := internCV_plain v m s x1 s' ho hm g1
    exact ⟨ho1, m1, by unfold Frontend.internCI; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1], hm1⟩
  | thmInfo v =>
    simp only [plainCI] at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
    obtain ⟨ho1, m1, e1, hm1⟩ := internCV_plain v m s x1 s' ho hm g1
    exact ⟨ho1, m1, by unfold Frontend.internCI; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1], hm1⟩
  | defnInfo v e hint =>
    simp only [plainCI] at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, m1, e1, hm1⟩ := internCV_plain v m s x1 s1 ho hm g1
    obtain ⟨ho2, -, -⟩ := plainE_self ho1 g2
    obtain ⟨m2, e2, hm2⟩ := internExprGo_plain e m1 s1 x2 s' ho1 hm1 g2
    exact ⟨ho2, m2, by unfold Frontend.internCI; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2], hm2⟩
  | indInfo v caps =>
    simp only [plainCI] at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, m1, e1, hm1⟩ := internCV_plain v m s x1 s1 ho hm g1
    obtain ⟨ho2, hm2⟩ := memo_step (internCaps_rr _) ho1 hm1 g2
    exact ⟨ho2, m1, by unfold Frontend.internCI; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, g2], hm2⟩
  | ctorInfo v nP nF T =>
    simp only [plainCI] at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, m1, e1, hm1⟩ := internCV_plain v m s x1 s1 ho hm g1
    obtain ⟨ho2, hm2⟩ := memo_step (internName_rr _) ho1 hm1 g2
    exact ⟨ho2, m1, by unfold Frontend.internCI; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, g2], hm2⟩
  | recInfo v mI rP k rs =>
    simp only [plainCI] at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, m1, e1, hm1⟩ := internCV_plain v m s x1 s1 ho hm g1
    obtain ⟨ho2, m2, e2, hm2⟩ := internRules_plain rs m1 s1 x2 s' ho1 hm1 g2
    exact ⟨ho2, m2, by unfold Frontend.internCI; simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2], hm2⟩

theorem internCIList_plain : ∀ (cs : List ConLeche.ConstantInfo) (m : EMemo) (s : AState) (r : List IConstantInfo)
    (s' : AState), Off s.store → MemoOK m s → plainCIList cs s = .ok (r, s') →
    Off s'.store ∧ ∃ m', Frontend.internCIList m cs s = .ok ((m', r), s') ∧ MemoOK m' s'
  | [], m, s, r, s', ho, hm, h => by
    unfold plainCIList at h; obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ho, m, rfl, hm⟩
  | c :: cs, m, s, r, s', ho, hm, h => by
    unfold plainCIList at h
    obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok h
    obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
    obtain ⟨ho1, m1, e1, hm1⟩ := internCI_plain c m s x1 s1 ho hm g1
    obtain ⟨ho2, m2, e2, hm2⟩ := internCIList_plain cs m1 s1 x2 s' ho1 hm1 g2
    refine ⟨ho2, m2, ?_, hm2⟩
    unfold Frontend.internCIList
    simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e1, e2]

theorem plainCI_rr (c : ConLeche.ConstantInfo) : RR (plainCI c) := by
  cases c with
  | axiomInfo v => simp only [plainCI]; exact RR.bind (plainCV_rr v) (fun _ => RR.pure _)
  | thmInfo v => simp only [plainCI]; exact RR.bind (plainCV_rr v) (fun _ => RR.pure _)
  | defnInfo v e h => simp only [plainCI]; exact RR.bind (plainCV_rr v) (fun _ => RR.bind (plainE_rr e) (fun _ => RR.pure _))
  | indInfo v c => simp only [plainCI]; exact RR.bind (plainCV_rr v) (fun _ => RR.bind (internCaps_rr c) (fun _ => RR.pure _))
  | ctorInfo v nP nF T =>
    simp only [plainCI]; exact RR.bind (plainCV_rr v) (fun _ => RR.bind (internName_rr T) (fun _ => RR.pure _))
  | recInfo v mI rP k rs =>
    simp only [plainCI]; exact RR.bind (plainCV_rr v) (fun _ => RR.bind (plainRules_rr rs) (fun _ => RR.pure _))

theorem plainCIList_rr : ∀ cs : List ConLeche.ConstantInfo, RR (plainCIList cs)
  | [] => by unfold plainCIList; exact RR.pure _
  | c :: cs => by
    unfold plainCIList; exact RR.bind (plainCI_rr c) (fun _ => RR.bind (plainCIList_rr cs) (fun _ => RR.pure _))

/-- **A pinned block's interning is its plain interning.** -/
theorem basisDecls_plain (k : ConLeche.BasisKind) {s s' : AState} {r : List IConstantInfo} (ho : Off s.store)
    (h : plainCIList (ConLeche.BasisKind.decls k) s = .ok (r, s')) :
    ConRon.Arena.BasisKind.decls k s = .ok (r, s') := by
  obtain ⟨-, m, e, -⟩ := internCIList_plain _ ∅ s r s' ho (memoOK_empty s) h
  unfold ConRon.Arena.BasisKind.decls ConRon.Arena.internCIList
  simp [AM.bind_apply, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e]

end ConPanqueque.Logic.PlainIntern
