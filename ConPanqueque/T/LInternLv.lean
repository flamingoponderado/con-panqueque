import ConPanqueque.T.LIntern
import ConPanqueque.T.ReIntern
import ConPanqueque.T.LvlEq
import ConRon.Bridge.Specs
import ConPanqueque.T.CallN
import ConPanqueque.T.MemoN
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `internLevel` over a level representation

`internLv(w)`: an arena word is returned as is (on a well-formed store the twin's re-intern finds the
same handle, `internLevel_denote`); a heap block interns its children, then its node.
-/

namespace ConPanqueque.T
open ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq

/-- Level-store growth: views kept, names untouched. -/
def LGrow (ls ls' : LStore) : Prop := (∀ i v, ls.view i = some v → ls'.view i = some v) ∧ ls'.ns = ls.ns

theorem LGrow.refl (ls : LStore) : LGrow ls ls := ⟨fun _ _ h => h, rfl⟩

theorem LGrow.trans {a b c : LStore} (h1 : LGrow a b) (h2 : LGrow b c) : LGrow a c :=
  ⟨fun i v h => h2.1 i v (h1.1 i v h), h2.2.trans h1.2⟩

theorem LGrow.intern (ls : LStore) (v : LNodeView) : LGrow ls (ls.intern v).1 := by
  refine ⟨fun i w h => LStore.view_intern_mono ls v h, ?_⟩
  simp only [LStore.intern]; split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem lrep_grow {HB : BitVec 64} {H : List (BitVec 64)} {ls ls' : LStore} (hg : LGrow ls ls') :
    ∀ (l : ConLeche.Level) (w : BitVec 64), LRep HB H ls w l → LRep HB H ls' w l := by
  have A : ∀ (f : Nat) (h : LIdx) (l : ConLeche.Level), denoteLAux ls f h = some l → denoteLAux ls' f h = some l :=
    denoteLAux_store_mono hg.1 hg.2
  intro l
  induction l with
  | zero => intro w h; rcases h with ⟨h, f, e, d⟩ | ⟨o, e, g⟩
            · exact Or.inl ⟨h, f, e, A f h _ d⟩
            · exact Or.inr ⟨o, e, g⟩
  | succ u ih => intro w h; rcases h with ⟨h, f, e, d⟩ | ⟨o, wu, e, g1, g2, r⟩
                 · exact Or.inl ⟨h, f, e, A f h _ d⟩
                 · exact Or.inr ⟨o, wu, e, g1, g2, ih wu r⟩
  | max u v ihu ihv => intro w h; rcases h with ⟨h, f, e, d⟩ | ⟨o, wu, wv, e, g1, g2, g3, r1, r2⟩
                       · exact Or.inl ⟨h, f, e, A f h _ d⟩
                       · exact Or.inr ⟨o, wu, wv, e, g1, g2, g3, ihu wu r1, ihv wv r2⟩
  | imax u v ihu ihv => intro w h; rcases h with ⟨h, f, e, d⟩ | ⟨o, wu, wv, e, g1, g2, g3, r1, r2⟩
                        · exact Or.inl ⟨h, f, e, A f h _ d⟩
                        · exact Or.inr ⟨o, wu, wv, e, g1, g2, g3, ihu wu r1, ihv wv r2⟩
  | param n => intro w h; rcases h with ⟨h, f, e, d⟩ | ⟨o, nh, f, e, g1, g2, d⟩
               · exact Or.inl ⟨h, f, e, A f h _ d⟩
               · exact Or.inr ⟨o, nh, f, e, g1, g2, by rw [hg.2]; exact d⟩

theorem internLNode_run_eq {s s' : AState} {v : LNodeView} {h : LIdx} (hr : internLNode v s = .ok (h, s')) :
    h = (s.store.ls.intern v).2 ∧ s' = { s with store := withL s.store (s.store.ls.intern v).1 } := by
  unfold internLNode at hr
  cases hf : s.store.ls.find? v with
  | some h' =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, hf, pure, StateT.pure, Except.bind,
      Except.pure] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [LStore.intern_of_find' hf]; exact ⟨rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.ls.scratchOn = true then s.store.ls.scr.sizeOf v else s.store.ls.pers.sizeOf v) <
        Idx.idxCap
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, hf, hc, pure, StateT.pure, Except.bind,
        Except.pure, set, StateT.set, EStore.internLevel, LsStore.internLevel] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨rfl, rfl⟩
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, hf, hc, pure, StateT.pure, Except.bind,
        Except.pure, fail, throw, throwThe, MonadExceptOf.throw, StateT.lift, liftM, monadLift,
        MonadLift.monadLift] at hr

def fInternLv := ofString "internLv"
def eqT (x : MlS) (k : Nat) : ExpHOL 64 := .cmp .equal (vv x) (.const (BitVec.ofNat 64 k))

def callRetW (f : MlS) (es : List (ExpHOL 64)) : ProgHOL 64 :=
  .seq (.call (some (some (.local, lW), none)) f es) (.return (vv lW))

def internLvBody : ProgHOL 64 :=
  prologue lvlLocals
  (.ite (.cmp .lower (vv pLa) (.const (BitVec.ofNat 64 (2 ^ 32)))) (.return (vv pLa))
  (.seq (.assign .local lQ (vv pLa)) (lvViewP
  (.ite (eqT lX 0) (callRetW fInternLZero [])
  (.ite (eqT lX 1)
    (.seq (.assign .local lA1 (.load .one (vv lY)))
    (.seq (.call (some (some (.local, lA1), none)) fInternLv [vv lA1]) (callRetW fInternLSucc [vv lA1])))
  (.ite (eqT lX 4)
    (.seq (.assign .local lA1 (.load .one (vv lY))) (callRetW fInternLParam [vv lA1]))
    (.seq (.assign .local lA1 (.load .one (vv lY)))
    (.seq (.assign .local lB (.load .one (.op .add [vv lY, .const 8])))
    (.seq (.call (some (some (.local, lA1), none)) fInternLv [vv lA1])
    (.seq (.call (some (some (.local, lB), none)) fInternLv [vv lB])
    (.ite (eqT lX 2) (callRetW fInternLMax [vv lA1, vv lB]) (callRetW fInternLImax [vv lA1, vv lB]))))))))))))

variable {σ : Type}

/-- `internLevel`'s post: the handle; the state represented, well formed, the level store grown; the
handle reads back to the level. -/
def PostIL (C : Ctx) (s : AState) (l : ConLeche.Level) (h : LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) :
    Prop :=
  w = Enc.idxW h ∧ SR C s' st ∧ StoreWF s'.store ∧
    (∃ ls', s' = { s with store := withL s.store ls' } ∧ LGrow s.store.ls ls') ∧
    ∃ f, denoteLAux s'.store.ls f h = some l

theorem postIL_locals (C : Ctx) (s : AState) (l : ConLeche.Level) : ∀ (a : LIdx) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostIL C s l a w s' st → PostIL C s l a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl, h3⟩

theorem specR_ofRun' {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s s' : AState} {m : AM α} {a : α}
    {R R' : α → BitVec 64 → AState → PState σ → Prop} (hrun : m s = .ok (a, s'))
    (h : SpecR P c s (pure a) R') (hR : ∀ w st, R' a w s st → R a w s' st) : SpecR P c s m R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a', s1, hm, hq⟩
  · exact Or.inl hs
  · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact Or.inr ⟨w, hr, a, s', hrun, hR w _ hq⟩

theorem specR_ifEqT {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (a b : Nat) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) (hx : Γ.get x = some (BitVec.ofNat 64 a))
    (h1 : a = b → SpecR (Inv C s Γ M D) c1 s m R) (h2 : a ≠ b → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite (eqT x b) c1 c2) s m R := by
  by_cases e : a = b
  · subst e
    exact specR_ifI _ 1 (by simp [eqT, sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => h1 rfl) (fun h => absurd h (by decide))
  · exact specR_ifI _ 0 (by simp [eqT, sev, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_eq_iff a b ha hb, e])
      (fun h => absurd rfl h) (fun _ => h2 e)

/-- A call of a level-node intern wrapper: the continuation learns the twin's run. -/
theorem callLN {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : LIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs) (v : LNodeView)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s (internLNode v) (PostL C))
    (hk : ∀ h s', internLNode v s = .ok (h, s') →
      SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (internLNode v >>= k) R :=
  specR_callNIM x f ps es B vs hnd hl hx hC hes
    (fun a w s' st => internLNode v s = .ok (a, s') ∧ PostL C a w s' st) (fun _ _ _ _ hp => hp.2.2)
    (fun u hu _ hlk => specR_run (fun w hw => by subst hw; exact hspec _ (pre_of_lookups hu ps vs hl hlk)))
    (fun h w s' st ⟨hr, hw, _⟩ => by subst hw; exact hk h s' hr)

theorem callIL {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : LIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (e : ExpHOL 64) (B : ProgHOL 64) (w : BitVec 64) (l : ConLeche.Level)
    (hx : x ∈ D) (hC : C.code.lookup fInternLv = some ([(pLa, .one)], B, .one)) (he : sev Γ e = some w)
    (hspec : SpecR (Pre (σ := σ) C s [(pLa, w)]) B s (internLevel l) (PostIL C s l))
    (hk : ∀ h s', internLevel l s = .ok (h, s') → StoreWF s'.store →
      (∃ ls', s' = { s with store := withL s.store ls' } ∧ LGrow s.store.ls ls') →
      (∃ f, denoteLAux s'.store.ls f h = some l) →
      SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternLv [e]) rest) s
      (internLevel l >>= k) R :=
  specR_callNIM x fInternLv [pLa] [e] B [w] (by decide) rfl hx hC ⟨he, trivial⟩
    (fun a w s' st => internLevel l s = .ok (a, s') ∧ PostIL C s l a w s' st) (fun _ _ _ _ hp => hp.2.2.1)
    (fun u hu _ hlk => specR_run (fun w' hw => by subst hw; exact hspec _ (pre_of_lookups hu [pLa] [w] rfl hlk)))
    (fun h w s' st ⟨hr, hw, _, hwf, hg, hd⟩ => by subst hw; exact hk h s' hr hwf hg hd)

/-- After a node intern: well formed, the node viewed at the handle, the level store grown. -/
theorem finishIL {s1 s2 : AState} {v : LNodeView} {h : LIdx} (hr : internLNode v s1 = .ok (h, s2))
    (hwf : StoreWF s1.store) (hvok : s1.store.ls.ViewOK v) :
    StoreWF s2.store ∧ s2.store.ls.view h = some v ∧
      s2 = { s1 with store := withL s1.store (s1.store.ls.intern v).1 } ∧ LGrow s1.store.ls s2.store.ls := by
  obtain ⟨q1, -, -, -, -, -, -, -, q9, -⟩ :=
    AM.of_run (P := fun t => t = s1) rfl hr (internLNode_spec s1 v hwf hvok)
  obtain ⟨-, e⟩ := internLNode_run_eq hr
  refine ⟨q1, q9, e, ?_⟩
  rw [e]; exact LGrow.intern _ _

theorem wf_parts {st : EStore} (h : StoreWF st) :
    (∃ rk, LWFAt st.ls rk) ∧ ∃ rk, NWFAt st.ls.ns rk := by
  obtain ⟨rkE, hE⟩ := h
  obtain ⟨rkL, hL⟩ := hE.lss.ls
  obtain ⟨rkN, hN⟩ := hL.ns
  exact ⟨⟨rkL, hL⟩, ⟨rkN, hN⟩⟩

theorem params_noneIL (va : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ lvlLocals → (ctxEnv C ++ [(pLa, va)]).get x = none := by
  intro x hx
  simp only [lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The arena case: the word itself. -/
theorem internLv_arena (X : ProgHOL 64) (C : Ctx) (H : List (BitVec 64)) (s : AState) (hwf : StoreWF s.store) (l : ConLeche.Level)
    (h0 : LIdx) (f : Nat) (hd : denoteLAux s.store.ls f h0 = some l) :
    SpecR (Inv (σ := σ) (ctxH C H) s (ctxEnv (ctxH C H) ++ [(pLa, Enc.idxW h0)]) [] (ctxLocals ++ lvlLocals))
      (.ite (.cmp .lower (vv pLa) (.const (BitVec.ofNat 64 (2 ^ 32)))) (.return (vv pLa)) X) s
      (internLevel l) (PostIL (ctxH C H) s l) := by
  have hlt : Enc.idxW h0 < BitVec.ofNat 64 (2 ^ 32) := by
    rw [BitVec.lt_def]; have := idxW_lt32 h0; simp; omega
  refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]) (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨⟨rkL, hL⟩, ⟨rkN, hN⟩⟩ := wf_parts hwf
  have hrun := internLevel_denote s rkL hL rkN hN l f h0 hd
  refine specR_ofRun' hrun (specR_returnI (vv pLa) (Enc.idxW h0) (by simp +decide [ctxEnv]) (fun t ht => ?_))
    (fun w st hp => hp)
  exact ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, hwf, ⟨s.store.ls, rfl, LGrow.refl _⟩, ⟨f, hd⟩⟩

end ConPanqueque.T
