import ConPanqueque.T.Inv
import ConPanqueque.V.EApp2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The twin's monadic interns

`internNodeE v` probes, tests the constructor array's capacity on a miss, and interns; Pancake's
intern code refines `EStore.intern v`. The two agree whenever the new store's tables fit Pancake's
geometry, which the intern's post-state representation gives (a table never exceeds its
geometry's capacity, at most `2^26` rows).
-/

namespace ConPanqueque.T

/-- con-ron's `intern_of_find` (`Refine2/Specs.lean`), restated: a cons hit moves nothing. -/
theorem intern_of_find {st : EStore} {v : ENodeView} {h : EIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  unfold EStore.find? at hf
  unfold EStore.intern
  cases hp : st.persFindMaybe v with
  | some j =>
    simp only [hp, Option.some.injEq] at hf
    simp only [hf]
  | none =>
    simp only [hp] at hf ⊢
    by_cases hon : st.scratchOn = true
    · simp only [hon, ite_true] at hf ⊢
      cases hs : st.scr.find? v with
      | some j =>
        simp only [hs, Option.some.injEq] at hf
        simp only [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp only [hon] at hf; simp at hf

variable {σ : Type}

theorem tabAt_size_le {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] {t : PState σ} {L : Layout}
    {k tier : Nat} {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ} {mkI : Nat → ι}
    (h : TabAt t L k tier enc dW tb mkI) : tb.size ≤ (L.geo k tier).cap := by
  obtain ⟨_, _, rows, ders, slots, hu, hR⟩ := h
  have e := congrArg List.length hR.rel.nodes
  simp only [Array.length_toList] at e
  show tb.nodes.size ≤ _
  rw [e]; exact hR.vt.le


theorem twoTier_miss_size {α ι δ : Type} [BEq α] [Hashable α] (P Sc : Tbl α ι δ) (on sk : Bool) (x : α) (d : δ)
    (mkP mkS : Nat → ι) (h1 : (if on && sk then none else P.find? x) = none) (h2 : on = true → Sc.find? x = none) :
    (on = true → (twoTier P Sc on sk x d mkP mkS).2.1.size = Sc.size + 1) ∧
      (on = false → (twoTier P Sc on sk x d mkP mkS).1.size = P.size + 1) := by
  unfold twoTier
  rw [h1]
  cases on with
  | true =>
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    simp only [ite_true, tierInt, h2 rfl, Tbl.push, Tbl.size, Array.size_push]
  | false =>
    refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    have hp : P.find? x = none := by simpa using h1
    simp only [Bool.false_eq_true, ite_false, tierInt, hp, Tbl.push, Tbl.size, Array.size_push]

/-- The twin's `internNodeE` at an `app` view is `EStore.intern`, when the new store's `app` tables
have at most `2^26` rows each. -/
theorem internNodeE_app (s : AState) (f a : EIdx)
    (hP : (s.store.intern (.app f a)).1.pers.apps.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.app f a)).1.scr.apps.size ≤ 2 ^ 26) :
    internNodeE (.app f a) s = .ok ((s.store.intern (.app f a)).2, { s with store := (s.store.intern (.app f a)).1 }) := by
  show (match s.store.find? (.app f a) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.app f a) else s.store.pers.sizeOf (.app f a)
      if n < (ENodeView.app f a).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.app f a)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.app f a) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.app f a) else s.store.pers.sizeOf (.app f a)) <
        (ENodeView.app f a).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.app f a) then none
          else s.store.pers.apps.find? ⟨f, a⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.app f a) <;> simp <;>
          (cases s.store.pers.apps.find? ⟨f, a⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.apps.find? ⟨f, a⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.app f a) <;> simp <;>
          (cases s.store.pers.apps.find? ⟨f, a⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.apps s.store.scr.apps s.store.scratchOn
        (EStore.eViewHasScratchChild (.app f a)) ⟨f, a⟩ (s.store.derOfView (.app f a)) (mkW 0) (mkW 1) h1 h2
      have hint := estore_app s.store f a
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.apps.nodes.size else s.store.pers.apps.nodes.size) < 1073741824
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl

/-! ## The `internApp` function -/

/-- What the layout must satisfy for the interns (static facts about `C`). -/
structure CtxOK (C : Ctx) : Prop where
  sepApp : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 13
  b0App : C.L.base 13 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824
  b1App : C.L.base 13 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824
  /-- The memo lies apart from the key buffer and the stores. -/
  kbMemo : ∀ j, j < 3 → ¬ inR C.mg (C.KB + BitVec.ofNat 64 (8 * j))
  kbMdesc : ∀ k j, k < 8 → j < 3 → C.mG + BitVec.ofNat 64 (8 * k) ≠ C.KB + BitVec.ofNat 64 (8 * j)
  memoOut : ∀ c, inR C.mg c → ¬ inAny C.L c
  mdescOut : ∀ k, k < 8 → ¬ inAny C.L (C.mG + BitVec.ofNat 64 (8 * k))

def fInternApp := ofString "internApp"

def internAppBody : ProgHOL 64 := prologue bin2Scratch (eBin2With Der.appDataE (eRest 13 2))

theorem kb_ne_kb8 (KB : BitVec 64) : KB ≠ KB + 8 := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add] at this
  have hk := KB.isLt
  have e8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [e8] at this; omega

/-- The post of an expression-building call: the handle, and the new state represented. -/
def PostE (C : Ctx) (h : EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = Enc.idxW h ∧ SR C s' st

theorem postE_locals (C : Ctx) : ∀ (a : EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostE C a w s' st → PostE C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

theorem internApp_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (f a : EIdx) :
    SpecR (Pre (σ := σ) C s [(lEf, Enc.idxW f), (lEa, Enc.idxW a)]) internAppBody s (internAppE f a) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [bin2Scratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases eInternApp2_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store f a ht.sr.rep hok.sepApp
      ⟨by simpa using ht.sr.kbuf 0 (by decide), by simpa using ht.sr.kbuf 1 (by decide)⟩ (kb_ne_kb8 C.KB)
      hok.b0App hok.b1App (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.app f a)).2, { s with store := (s.store.intern (.app f a)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.app f a) s = _
    exact internNodeE_app s f a
      (Nat.le_trans (tabAt_size_le hsr.e.p4) (hok.sepApp.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s4) (hok.sepApp.cap 1 (by decide)))
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      memoAt_frame ht.sr.inst1 (fun c hc => hm c (hok.memoOut c hc) (fun j hj e => hok.kbMemo j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut k hk) (fun j hj => hok.kbMdesc k j hk (by omega))) hd⟩

/-- In a caller: `x := internApp(e₁, e₂); rest` against `internAppE f a >>= k`. -/
theorem specR_internAppI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (f a : EIdx) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW f)) (he2 : sev Γ e2 = some (Enc.idxW a))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternApp [e1, e2]) rest) s
      (internAppE f a >>= k) R :=
  specR_call2I x fInternApp lEf lEa (by decide) e1 e2 internAppBody (Enc.idxW f) (Enc.idxW a) hx hcode he1 he2
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu h1 h2 v hv => by
      subst hv
      exact internApp_body_spec ra C hok s f a _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

/-! ## Writing the key buffer -/

/-- A store into key-buffer word `j < 2` leaves the stores' representation alone. -/
theorem sr_storeKB {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (h : SR C s t) (j : Nat) (hj : j < 2)
    (w : BitVec 64) :
    SR C s { t with memory := fun c => if c = C.KB + BitVec.ofNat 64 (8 * j) then .word w else t.memory c } := by
  have S := hok.sepApp
  have hne : ∀ c, c ≠ C.KB + BitVec.ofNat 64 (8 * j) →
      (fun c => if c = C.KB + BitVec.ofNat 64 (8 * j) then HolWordLab.word w else t.memory c) c = t.memory c :=
    fun c hc => by simp [hc]
  refine ⟨srep_frame h.rep ⟨hne _ ((S.fls _ (Or.inl rfl)).2.2 j hj), ?_, ?_, ?_⟩ rfl (fun k tier hk ht => ⟨fun m hm =>
      hne _ ((S.dsc k tier m hk ht hm).2.2 j hj), fun c hc => hne c (fun e => S.kbo j k tier hj hk ht (e ▸ hc))⟩),
    h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf,
    memoAt_frame h.inst1 (fun c hc => hne c (fun e => hok.kbMemo j (by omega) (e ▸ hc)))
      (fun k hk => hne _ (hok.kbMdesc k j hk (by omega))) rfl⟩
  · exact hne _ ((S.fls _ (Or.inr (Or.inl rfl))).2.2 j hj)
  · exact hne _ ((S.fls _ (Or.inr (Or.inr (Or.inl rfl)))).2.2 j hj)
  · exact hne _ ((S.fls _ (Or.inr (Or.inr (Or.inr rfl)))).2.2 j hj)

/-- `KB[j] := e; rest`: the twin sees nothing; afterwards the word is known (other memory facts dropped). -/
theorem specR_storeKBI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (j : Nat) (hj : j < 2) (e : ExpHOL 64) (w : BitVec 64) (he : sev Γ e = some w) (hkb : Γ.get lKb = some C.KB)
    (h : SpecR (Inv C s Γ [(C.KB + BitVec.ofNat 64 (8 * j), w)] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * j))]) e) rest) s m R := by
  refine specR_seq (fun t ht => ?_) h
  have hdom : t.memaddrs (C.KB + BitVec.ofNat 64 (8 * j)) := ht.sr.kbuf j (by omega)
  rw [store_word t _ e _ w (eval_add2 t _ _ _ _ (eval_vv t lKb _ (ht.env _ _ hkb)) (eval_const t _))
    (inv_ev ht he) hdom]
  refine Or.inr ⟨rfl, sr_storeKB hok ht.sr j hj w, fun y v hy => ht.env y v hy, fun a v ha => ?_, ht.decl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact ⟨hdom, by simp⟩

/-- `KB[0] := e₀; KB[1] := e₁; rest`: both words become known memory. -/
theorem specR_storeKB2I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (e0 e1 : ExpHOL 64) (w0 w1 : BitVec 64) (he0 : sev Γ e0 = some w0) (he1 : sev Γ e1 = some w1)
    (hkb : Γ.get lKb = some C.KB)
    (h : SpecR (Inv C s Γ [(C.KB + BitVec.ofNat 64 (8 * 0), w0), (C.KB + BitVec.ofNat 64 (8 * 1), w1)] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) e0)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) e1) rest)) s m R := by
  refine specR_storeKBI hok 0 (by decide) e0 w0 he0 hkb ?_
  refine specR_seq (fun t ht => ?_) h
  have hdom : t.memaddrs (C.KB + BitVec.ofNat 64 (8 * 1)) := ht.sr.kbuf 1 (by decide)
  rw [store_word t _ e1 _ w1 (eval_add2 t _ _ _ _ (eval_vv t lKb _ (ht.env _ _ hkb)) (eval_const t _))
    (inv_ev ht he1) hdom]
  have hne : C.KB + BitVec.ofNat 64 (8 * 0) ≠ C.KB + BitVec.ofNat 64 (8 * 1) := by
    simpa using kb_ne_kb8 C.KB
  refine Or.inr ⟨rfl, sr_storeKB hok ht.sr 1 (by decide) w1, fun y v hy => ht.env y v hy, fun a v ha => ?_, ht.decl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := ht.mem _ _ (List.mem_singleton_self _)
    exact ⟨h1, by simp only; rw [if_neg hne]; exact h2⟩
  · exact ⟨hdom, by simp⟩

end ConPanqueque.T
