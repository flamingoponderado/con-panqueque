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

theorem denoteN_of_aux (ns : NStore) (rk : NIdx → Nat) (h : NWFAt ns rk) (i : NIdx) (f : Nat) (n : ConLeche.Name)
    (hd : denoteNAux ns f i = some n) : denoteN ns i = some n := by
  unfold denoteN
  by_cases hf : f ≤ ns.nodeCount + 1
  · exact denoteNAux_mono ns f _ i n hf hd
  · obtain ⟨v, hv⟩ := nview_of_denote ns f i n hd
    have hr : rk i < ns.nodeCount := by
      cases hp : i.isPersistent with
      | true => have := h.rankP i hp (by simp [hv]); simp only [NStore.nodeCount] at *; omega
      | false => exact h.rankS i hp (by simp [hv])
    rw [denoteNAux_congr h (rk i + 1) i (ns.nodeCount + 1) f (by omega) (by omega) (by omega)]; exact hd

/-- The heap case up to the view of the block. -/
theorem internLv_heap {α : Type} (C : Ctx) (hok : CtxOK C) (H : List (BitVec 64)) (s : AState) (l : ConLeche.Level)
    (o : Nat) {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (REST : ProgHOL 64)
    (hl : LRep C.HB H s.store.ls (C.HB + BitVec.ofNat 64 (8 * o)) l) (hg : H[o]? = some (BitVec.ofNat 64 (ltag l)))
    (hk : ∀ (Γ1 : Env) (M1 : Mem) (Pc : BitVec 64),
      (∀ z, z ∉ lvScratch → Γ1.get z = Env.get ((lQ, C.HB + BitVec.ofNat 64 (8 * o)) ::
        (ctxEnv (ctxH C H) ++ [(pLa, C.HB + BitVec.ofNat 64 (8 * o))])) z) →
      Γ1.get lX = some (BitVec.ofNat 64 (ltag l)) → Γ1.get lY = some Pc → LKids C.HB H s.store.ls Pc M1 l →
      SpecR (Inv (ctxH C H) s Γ1 M1 (ctxLocals ++ lvlLocals)) REST s m R) :
    SpecR (Inv (σ := σ) (ctxH C H) s (ctxEnv (ctxH C H) ++ [(pLa, C.HB + BitVec.ofNat 64 (8 * o))]) []
      (ctxLocals ++ lvlLocals))
      (.ite (.cmp .lower (vv pLa) (.const (BitVec.ofNat 64 (2 ^ 32)))) (.return (vv pLa))
        (.seq (.assign .local lQ (vv pLa)) (lvViewP REST))) s m R := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  have hhi := hok.heapHigh
  have hol : o < H.length := by
    rcases Nat.lt_or_ge o H.length with hh | hh
    · exact hh
    · rw [List.getElem?_eq_none hh] at hg; simp at hg
  have hHN' : H.length ≤ C.HN := hHN
  have hnlt : ¬ C.HB + BitVec.ofNat 64 (8 * o) < BitVec.ofNat 64 (2 ^ 32) := by
    rw [BitVec.lt_def]; simp [BitVec.toNat_add]; omega
  refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt]) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI lQ (vv pLa) (C.HB + BitVec.ofNat 64 (8 * o)) (by decide) (by simp +decide [ctxEnv]) ?_
  exact specR_lvViewI (C := ctxH C H) (ctxOK_H hok H) _ l (by simp) hl (by simp +decide [ctxEnv] <;> rfl)
    (by simp +decide [ctxEnv] <;> rfl) lvScratch_DL (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => hk Γ1 M1 Pc hp1 hx1 hy1 hk1)

theorem internLv_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcZ : C.code.lookup fInternLZero = some ([], internLZeroBody, .one))
    (hcS : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one))
    (hcM : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one))
    (hcI : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one))
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (hcV : C.code.lookup fInternLv = some ([(pLa, .one)], internLvBody, .one)) :
    ∀ (l : ConLeche.Level) (H : List (BitVec 64)) (w : BitVec 64) (s : AState), StoreWF s.store →
      LRep C.HB H s.store.ls w l →
      SpecR (Pre (σ := σ) (ctxH C H) s [(pLa, w)]) internLvBody s (internLevel l) (PostIL (ctxH C H) s l) := by
  have hok' := fun H => ctxOK_H hok H
  intro l
  induction l with
  | zero =>
    intro H w s hwf hl
    refine specR_prologue (postIL_locals _ _ _) (params_noneIL _ _) ?_
    rcases lrep_split hl with ⟨h0, f, rfl, hd⟩ | ⟨o, rfl, hg, -⟩
    · exact internLv_arena _ C H s hwf _ h0 f hd
    refine internLv_heap C hok H s _ o _ hl hg (fun Γ1 M1 Pc hp1 hx1 hy1 hk1 => ?_)
    refine specR_ifEqT lX 0 0 (by decide) (by decide) hx1 (fun _ => ?_) (fun h => absurd rfl h)
    refine specR_congr (m' := internLNode .zero >>= pure) (by simp [internLevel]) ?_
    unfold callRetW
    refine callLN (C := ctxH C H) lW fInternLZero [] [] internLZeroBody [] (by decide) rfl (by decide) hcZ trivial
      .zero (internLZero_body_spec ra (ctxH C H) (hok' H) s) (fun h s2 hr => ?_)
    obtain ⟨wf2, hv2, e2, -⟩ := finishIL hr hwf ⟨fun c hc => by simp [LNodeView.lchildren] at hc,
      fun c hc => by simp [LNodeView.nchildren] at hc⟩
    exact specR_returnI (vv lW) (Enc.idxW h) (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, wf2,
      ⟨_, e2, LGrow.intern _ _⟩, ⟨1, by simp [denoteLAux, hv2]⟩⟩)
  | succ u ih =>
    intro H w s hwf hl
    refine specR_prologue (postIL_locals _ _ _) (params_noneIL _ _) ?_
    rcases lrep_split hl with ⟨h0, f, rfl, hd⟩ | ⟨o, rfl, hg, -⟩
    · exact internLv_arena _ C H s hwf _ h0 f hd
    refine internLv_heap C hok H s _ o _ hl hg (fun Γ1 M1 Pc hp1 hx1 hy1 hk1 => ?_)
    refine specR_ifEqT lX 1 0 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_ifEqT lX 1 1 (by decide) (by decide) hx1 (fun _ => ?_) (fun h => absurd rfl h)
    obtain ⟨wu, mu, ru⟩ := hk1
    refine specR_loadI' lA1 (vv lY) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [hy1])
      (by simp) mu ?_
    refine specR_congr (m' := internLevel u >>= fun hu => internLNode (.succ hu) >>= pure) (by simp [internLevel]) ?_
    refine callIL lA1 (vv lA1) internLvBody wu u (by decide) hcV (by simp) (ih H wu s hwf ru)
      (fun hu s1 hr1 wf1 ⟨ls1, e1, g1⟩ ⟨f1, d1⟩ => ?_)
    subst e1
    unfold callRetW
    refine callLN (C := ctxH C H) lW fInternLSucc [lEu] [vv lA1] internLSuccBody [Enc.idxW hu] (by decide) rfl
      (by decide) hcS ⟨by simp, trivial⟩ (.succ hu) (internLSucc_body_spec ra (ctxH C H) (hok' H) _ hu)
      (fun h s2 hr => ?_)
    obtain ⟨wf2, hv2, e2, g2⟩ := finishIL hr wf1 ⟨fun c hc => by
      simp [LNodeView.lchildren] at hc; subst hc; obtain ⟨v, hv⟩ := lview_of_denote _ _ _ _ d1; simp [hv],
      fun c hc => by simp [LNodeView.nchildren] at hc⟩
    have d2 := denoteLAux_store_mono g2.1 g2.2 f1 hu u d1
    exact specR_returnI (vv lW) (Enc.idxW h) (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, wf2,
      ⟨_, e2, g1.trans (LGrow.intern _ _)⟩, ⟨f1 + 1, by simp [denoteLAux, hv2, d2]⟩⟩)
  | max u v ihu ihv =>
    intro H w s hwf hl
    refine specR_prologue (postIL_locals _ _ _) (params_noneIL _ _) ?_
    rcases lrep_split hl with ⟨h0, f, rfl, hd⟩ | ⟨o, rfl, hg, -⟩
    · exact internLv_arena _ C H s hwf _ h0 f hd
    refine internLv_heap C hok H s _ o _ hl hg (fun Γ1 M1 Pc hp1 hx1 hy1 hk1 => ?_)
    refine specR_ifEqT lX 2 0 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_ifEqT lX 2 1 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_ifEqT lX 2 4 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    obtain ⟨wu, wv, mu, mv, ru, rv⟩ := hk1
    refine specR_loadI' lA1 (vv lY) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [hy1])
      (by simp) mu ?_
    refine specR_loadI' lB (.op .add [vv lY, .const 8]) (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv (by decide)
      (by simp +decide [sev, hy1]) (by simp) mv ?_
    refine specR_congr (m' := internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.max hu hv) >>= pure)
      (by simp [internLevel]) ?_
    refine callIL lA1 (vv lA1) internLvBody wu u (by decide) hcV (by simp +decide) (ihu H wu s hwf ru)
      (fun hu s1 hr1 wf1 ⟨ls1, e1, g1⟩ ⟨f1, d1⟩ => ?_)
    subst e1
    refine callIL lB (vv lB) internLvBody wv v (by decide) hcV (by simp +decide) (ihv H wv _ wf1 (lrep_grow g1 v wv rv))
      (fun hv s2 hr2 wf2 ⟨ls2, e2, g2⟩ ⟨f2, d2⟩ => ?_)
    subst e2
    refine specR_ifEqT lX 2 2 (by decide) (by decide) (by simp +decide [hx1, ltag]) (fun _ => ?_) (fun h => absurd rfl h)
    unfold callRetW
    refine callLN (C := ctxH C H) lW fInternLMax [lEu, lEv] [vv lA1, vv lB] internLMaxBody [Enc.idxW hu, Enc.idxW hv]
      (by decide) rfl (by decide) hcM ⟨by simp +decide, by simp +decide, trivial⟩ (.max hu hv)
      (internLMax_body_spec ra (ctxH C H) (hok' H) _ hu hv) (fun h s3 hr => ?_)
    have d1' := denoteLAux_store_mono g2.1 g2.2 f1 hu u d1
    obtain ⟨wf3, hv3, e3, g3⟩ := finishIL hr wf2 ⟨fun c hc => by
      simp [LNodeView.lchildren] at hc
      rcases hc with rfl | rfl
      · obtain ⟨x, hx⟩ := lview_of_denote _ _ _ _ d1'; simp [withL, EStore.ls] at hx ⊢; simp [hx]
      · obtain ⟨x, hx⟩ := lview_of_denote _ _ _ _ d2; simp [withL, EStore.ls] at hx ⊢; simp [hx],
      fun c hc => by simp [LNodeView.nchildren] at hc⟩
    have a1 := denoteLAux_mono _ f1 (max f1 f2) hu u (by omega) (denoteLAux_store_mono g3.1 g3.2 f1 hu u d1')
    have a2 := denoteLAux_mono _ f2 (max f1 f2) hv v (by omega) (denoteLAux_store_mono g3.1 g3.2 f2 hv v d2)
    exact specR_returnI (vv lW) (Enc.idxW h) (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, wf3,
      ⟨_, e3, (g1.trans g2).trans (LGrow.intern _ _)⟩, ⟨max f1 f2 + 1, by simp [denoteLAux, hv3, a1, a2, opt2]⟩⟩)
  | imax u v ihu ihv =>
    intro H w s hwf hl
    refine specR_prologue (postIL_locals _ _ _) (params_noneIL _ _) ?_
    rcases lrep_split hl with ⟨h0, f, rfl, hd⟩ | ⟨o, rfl, hg, -⟩
    · exact internLv_arena _ C H s hwf _ h0 f hd
    refine internLv_heap C hok H s _ o _ hl hg (fun Γ1 M1 Pc hp1 hx1 hy1 hk1 => ?_)
    refine specR_ifEqT lX 3 0 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_ifEqT lX 3 1 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_ifEqT lX 3 4 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    obtain ⟨wu, wv, mu, mv, ru, rv⟩ := hk1
    refine specR_loadI' lA1 (vv lY) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [hy1])
      (by simp) mu ?_
    refine specR_loadI' lB (.op .add [vv lY, .const 8]) (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv (by decide)
      (by simp +decide [sev, hy1]) (by simp) mv ?_
    refine specR_congr (m' := internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.imax hu hv) >>= pure)
      (by simp [internLevel]) ?_
    refine callIL lA1 (vv lA1) internLvBody wu u (by decide) hcV (by simp +decide) (ihu H wu s hwf ru)
      (fun hu s1 hr1 wf1 ⟨ls1, e1, g1⟩ ⟨f1, d1⟩ => ?_)
    subst e1
    refine callIL lB (vv lB) internLvBody wv v (by decide) hcV (by simp +decide) (ihv H wv _ wf1 (lrep_grow g1 v wv rv))
      (fun hv s2 hr2 wf2 ⟨ls2, e2, g2⟩ ⟨f2, d2⟩ => ?_)
    subst e2
    refine specR_ifEqT lX 3 2 (by decide) (by decide) (by simp +decide [hx1, ltag]) (fun h => absurd h (by decide))
      (fun _ => ?_)
    unfold callRetW
    refine callLN (C := ctxH C H) lW fInternLImax [lEu, lEv] [vv lA1, vv lB] internLImaxBody [Enc.idxW hu, Enc.idxW hv]
      (by decide) rfl (by decide) hcI ⟨by simp +decide, by simp +decide, trivial⟩ (.imax hu hv)
      (internLImax_body_spec ra (ctxH C H) (hok' H) _ hu hv) (fun h s3 hr => ?_)
    have d1' := denoteLAux_store_mono g2.1 g2.2 f1 hu u d1
    obtain ⟨wf3, hv3, e3, g3⟩ := finishIL hr wf2 ⟨fun c hc => by
      simp [LNodeView.lchildren] at hc
      rcases hc with rfl | rfl
      · obtain ⟨x, hx⟩ := lview_of_denote _ _ _ _ d1'; simp [withL, EStore.ls] at hx ⊢; simp [hx]
      · obtain ⟨x, hx⟩ := lview_of_denote _ _ _ _ d2; simp [withL, EStore.ls] at hx ⊢; simp [hx],
      fun c hc => by simp [LNodeView.nchildren] at hc⟩
    have a1 := denoteLAux_mono _ f1 (max f1 f2) hu u (by omega) (denoteLAux_store_mono g3.1 g3.2 f1 hu u d1')
    have a2 := denoteLAux_mono _ f2 (max f1 f2) hv v (by omega) (denoteLAux_store_mono g3.1 g3.2 f2 hv v d2)
    exact specR_returnI (vv lW) (Enc.idxW h) (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, wf3,
      ⟨_, e3, (g1.trans g2).trans (LGrow.intern _ _)⟩, ⟨max f1 f2 + 1, by simp [denoteLAux, hv3, a1, a2, opt2]⟩⟩)
  | param n =>
    intro H w s hwf hl
    refine specR_prologue (postIL_locals _ _ _) (params_noneIL _ _) ?_
    rcases lrep_split hl with ⟨h0, f, rfl, hd⟩ | ⟨o, rfl, hg, -⟩
    · exact internLv_arena _ C H s hwf _ h0 f hd
    refine internLv_heap C hok H s _ o _ hl hg (fun Γ1 M1 Pc hp1 hx1 hy1 hk1 => ?_)
    refine specR_ifEqT lX 4 0 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_ifEqT lX 4 1 (by decide) (by decide) hx1 (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_ifEqT lX 4 4 (by decide) (by decide) hx1 (fun _ => ?_) (fun h => absurd rfl h)
    obtain ⟨nh, f, mn, dn⟩ := hk1
    refine specR_loadI' lA1 (vv lY) Pc (Pc + BitVec.ofNat 64 (8 * 0)) _ (by decide) (by simp +decide [hy1])
      (by simp) mn ?_
    obtain ⟨⟨rkL, hL⟩, ⟨rkN, hN⟩⟩ := wf_parts hwf
    have hrn := internName_denote s rkN hN n f nh dn
    refine specR_congr (m' := internLNode (.param nh) >>= pure) (by
      simp only [internLevel, bind, StateT.bind, Except.bind]; rw [hrn]; simp only
      cases internLNode (LNodeView.param nh) s <;> rfl) ?_
    unfold callRetW
    refine callLN (C := ctxH C H) lW fInternLParam [lEn] [vv lA1] internLParamBody [Enc.idxW nh] (by decide) rfl
      (by decide) hcP ⟨by simp, trivial⟩ (.param nh) (internLParam_body_spec ra (ctxH C H) (hok' H) s nh)
      (fun h s2 hr => ?_)
    obtain ⟨wf2, hv2, e2, g2⟩ := finishIL hr hwf ⟨fun c hc => by simp [LNodeView.lchildren] at hc,
      fun c hc => by
        simp [LNodeView.nchildren] at hc; subst hc; obtain ⟨v, hv⟩ := nview_of_denote _ _ _ _ dn; simp [hv]⟩
    have dN : denoteN s2.store.ls.ns nh = some n := by
      rw [g2.2]; exact denoteN_of_aux _ rkN hN nh f n dn
    exact specR_returnI (vv lW) (Enc.idxW h) (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, wf2,
      ⟨_, e2, LGrow.intern _ _⟩, ⟨1, by simp [denoteLAux, hv2, dN]⟩⟩)

end ConPanqueque.T
