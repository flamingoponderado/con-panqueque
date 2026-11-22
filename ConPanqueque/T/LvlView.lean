import ConPanqueque.T.Lvl
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Viewing a level tree

`lvViewP rest`: for the tree word in `lq`, the tag in `x` and the address of the children words in `y`
(the arena row, or the heap block past its tag), the children as known memory.
-/

namespace ConPanqueque.T
open ConPanqueque.T.Ex ConPanqueque.T.ExS

variable {σ : Type}

theorem specR_lviewPI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (h : LIdx)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ v P, s.store.ls.view h = some v → v.tagN = h.tag.toNat → (encLView v).length < 2 ^ 61 →
      SpecR (Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encLView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encLView v) ++ M) D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq lViewP rest) s m R := by
  intro t ht
  rcases lView_spec t C.L C.FLl s.store.ls ht.sr.rep.l h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl (seq_stop t _ _ hs)
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
  have e : evaluateHOLFiniteState t lViewP = (none, (evaluateHOLFiniteState t lViewP).2) := by rw [← hn]
  rw [seq_normal rest e]
  refine hk v P hv htg hsh _ ⟨sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => ?_, fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hrp
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hrn
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdt
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; rw [htg]; exact hdg
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdi
    rename_i e1 e2 e3 e4 e5
    rw [hfr y e1 e2 e3 e4 e5]; exact ht.env y w hy
  · simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · rw [hm, hd]; exact wordsAt_mem hW b w hb
    · rw [hm, hd]; exact ht.mem b w hb
  · by_cases e1 : y = lRp
    · subst e1; exact ⟨P, hrp⟩
    by_cases e2 : y = lRn
    · subst e2; exact ⟨_, hrn⟩
    by_cases e3 : y = lDt
    · subst e3; exact ⟨_, hdt⟩
    by_cases e4 : y = lDg
    · subst e4; exact ⟨_, hdg⟩
    by_cases e5 : y = lDi
    · subst e5; exact ⟨_, hdi⟩
    obtain ⟨w, hw⟩ := ht.decl y hy; exact ⟨w, by rw [hfr y e1 e2 e3 e4 e5]; exact hw⟩

/-- A denoting level handle's view, and the tree it reads back to. -/
theorem denoteLAux_cases (st : LStore) (f : Nat) (i : LIdx) (l : ConLeche.Level) (v : LNodeView)
    (hd : denoteLAux st f i = some l) (hv : st.view i = some v) :
    (v = .zero ∧ l = .zero) ∨
    (∃ u lu f', v = .succ u ∧ l = .succ lu ∧ denoteLAux st f' u = some lu) ∨
    (∃ u w lu lw f', v = .max u w ∧ l = .max lu lw ∧ denoteLAux st f' u = some lu ∧ denoteLAux st f' w = some lw) ∨
    (∃ u w lu lw f', v = .imax u w ∧ l = .imax lu lw ∧ denoteLAux st f' u = some lu ∧ denoteLAux st f' w = some lw) ∨
    (∃ n x, v = .param n ∧ l = .param x ∧ denoteN st.ns n = some x) := by
  cases f with
  | zero => simp [denoteLAux] at hd
  | succ f =>
    simp only [denoteLAux, hv, Option.bind_some] at hd
    cases v with
    | zero => left; simp at hd; exact ⟨rfl, hd.symm⟩
    | succ u =>
      right; left
      simp only [Option.map_eq_some_iff] at hd
      obtain ⟨q, hq, rfl⟩ := hd
      exact ⟨u, q, f, rfl, rfl, hq⟩
    | max u w =>
      right; right; left
      cases hu : denoteLAux st f u with
      | none => simp [opt2, hu] at hd
      | some lu =>
        cases hw : denoteLAux st f w with
        | none => simp [opt2, hu, hw] at hd
        | some lw =>
          simp only [opt2, hu, hw, Option.some.injEq] at hd
          exact ⟨u, w, lu, lw, f, rfl, hd.symm, hu, hw⟩
    | imax u w =>
      right; right; right; left
      cases hu : denoteLAux st f u with
      | none => simp [opt2, hu] at hd
      | some lu =>
        cases hw : denoteLAux st f w with
        | none => simp [opt2, hu, hw] at hd
        | some lw =>
          simp only [opt2, hu, hw, Option.some.injEq] at hd
          exact ⟨u, w, lu, lw, f, rfl, hd.symm, hu, hw⟩
    | param n =>
      right; right; right; right
      simp only [Option.map_eq_some_iff] at hd
      obtain ⟨q, hq, rfl⟩ := hd
      exact ⟨n, q, rfl, rfl, hq⟩

/-- A heap cell of the image as a known memory word. -/
theorem inv_heapMem {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ}
    (h : Inv C s Γ M D t) (j : Nat) (hj : j < C.H.length) : Inv C s Γ ((cellA C j, C.H[j]) :: M) D t :=
  ⟨h.sr, h.env, fun a v hm => by
    rcases List.mem_cons.mp hm with e | e
    · cases e; exact heap_cell h.sr j hj
    · exact h.mem a v e, h.decl⟩

def lQ := ofString "lq"

def ltag : ConLeche.Level → Nat
  | .zero => 0 | .succ _ => 1 | .max _ _ => 2 | .imax _ _ => 3 | .param _ => 4

/-- The children words of `l` at `Pc`, `Pc + 8`, as known memory. -/
def LKids (HB : BitVec 64) (H : List (BitVec 64)) (ls : LStore) (Pc : BitVec 64) (M : Mem) :
    ConLeche.Level → Prop
  | .zero => True
  | .succ u => ∃ wu, (Pc + BitVec.ofNat 64 (8 * 0), wu) ∈ M ∧ LRep HB H ls wu u
  | .max u v => ∃ wu wv, (Pc + BitVec.ofNat 64 (8 * 0), wu) ∈ M ∧ (Pc + BitVec.ofNat 64 (8 * 1), wv) ∈ M ∧
      LRep HB H ls wu u ∧ LRep HB H ls wv v
  | .imax u v => ∃ wu wv, (Pc + BitVec.ofNat 64 (8 * 0), wu) ∈ M ∧ (Pc + BitVec.ofNat 64 (8 * 1), wv) ∈ M ∧
      LRep HB H ls wu u ∧ LRep HB H ls wv v
  | .param n => ∃ (nh : NIdx) (f : Nat), (Pc + BitVec.ofNat 64 (8 * 0), Enc.idxW nh) ∈ M ∧
      denoteNAux ls.ns f nh = some n

def lvViewOld (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower (vv lQ) (.const (BitVec.ofNat 64 (2 ^ 32))))
    (.seq (.assign .local lDh (vv lQ)) (.seq (.assign .local lFl (vv lFll)) (.seq lViewP
      (.seq (.assign .local lX (vv lDg)) (.seq (.assign .local lY (vv lRp)) rest)))))
    (.seq (.assign .local lX (.load .one (vv lQ))) (.seq (.assign .local lY (.op .add [vv lQ, .const 8])) rest))

def lvScratch : List MlS := [lRp, lRn, lDt, lDg, lDi, lDh, lFl, lX, lY]

theorem idxW_lt32 {k : IdxKind} (i : Idx k) : (Enc.idxW i).toNat < 2 ^ 32 := by
  simp [Enc.idxW]; exact i.word.toNat_lt

theorem cellA_succ_add (C : Ctx) (o i : Nat) :
    (C.HB + BitVec.ofNat 64 (8 * o) + 8) + BitVec.ofNat 64 (8 * i) = cellA C (o + 1 + i) := by
  simp only [cellA, BitVec.add_assoc]
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  congr 2; omega

/-- The heap block's children of `l` at image index `o`. -/
def HKids (HB : BitVec 64) (H : List (BitVec 64)) (ls : LStore) (o : Nat) : ConLeche.Level → Prop
  | .zero => True
  | .succ u => ∃ wu, H[o + 1]? = some wu ∧ LRep HB H ls wu u
  | .max u v => ∃ wu wv, H[o + 1]? = some wu ∧ H[o + 2]? = some wv ∧ LRep HB H ls wu u ∧ LRep HB H ls wv v
  | .imax u v => ∃ wu wv, H[o + 1]? = some wu ∧ H[o + 2]? = some wv ∧ LRep HB H ls wu u ∧ LRep HB H ls wv v
  | .param n => ∃ (nh : NIdx) (f : Nat), H[o + 1]? = some (Enc.idxW nh) ∧ denoteNAux ls.ns f nh = some n

theorem lrep_split {HB : BitVec 64} {H : List (BitVec 64)} {ls : LStore} {w : BitVec 64} {l : ConLeche.Level}
    (h : LRep HB H ls w l) :
    (∃ (h : LIdx) (f : Nat), w = Enc.idxW h ∧ denoteLAux ls f h = some l) ∨
    (∃ o, w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some (BitVec.ofNat 64 (ltag l)) ∧ HKids HB H ls o l) := by
  cases l with
  | zero => rcases h with h | ⟨o, h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨o, h1, h2, trivial⟩
  | succ u => rcases h with h | ⟨o, wu, h1, h2, h3, h4⟩
              · exact Or.inl h
              · exact Or.inr ⟨o, h1, h2, wu, h3, h4⟩
  | max u v => rcases h with h | ⟨o, wu, wv, h1, h2, h3, h4, h5, h6⟩
               · exact Or.inl h
               · exact Or.inr ⟨o, h1, h2, wu, wv, h3, h4, h5, h6⟩
  | imax u v => rcases h with h | ⟨o, wu, wv, h1, h2, h3, h4, h5, h6⟩
                · exact Or.inl h
                · exact Or.inr ⟨o, h1, h2, wu, wv, h3, h4, h5, h6⟩
  | param n => rcases h with h | ⟨o, nh, f, h1, h2, h3, h4⟩
               · exact Or.inl h
               · exact Or.inr ⟨o, h1, h2, nh, f, h3, h4⟩

theorem lrep_arena (HB : BitVec 64) (H : List (BitVec 64)) (ls : LStore) (h : LIdx) (f : Nat) (l : ConLeche.Level)
    (hd : denoteLAux ls f h = some l) : LRep HB H ls (Enc.idxW h) l := by
  cases l <;> exact Or.inl ⟨h, f, rfl, hd⟩

/-- An arena view's children, as the readback of the parent gives them. -/
theorem arenaKids (ls : LStore) (HB : BitVec 64) (H : List (BitVec 64)) (h : LIdx) (f : Nat) (l : ConLeche.Level)
    (v : LNodeView) (P : BitVec 64) (M : Mem) (hd : denoteLAux ls f h = some l) (hv : ls.view h = some v) :
    v.tagN = ltag l ∧ LKids HB H ls P (wordsAt P (encLView v) ++ M) l := by
  rcases denoteLAux_cases ls f h l v hd hv with ⟨rfl, rfl⟩ | ⟨u, lu, f', rfl, rfl, hu⟩ |
    ⟨u, w, lu, lw, f', rfl, rfl, hu, hw⟩ | ⟨u, w, lu, lw, f', rfl, rfl, hu, hw⟩ | ⟨n, x, rfl, rfl, hn⟩
  · exact ⟨rfl, trivial⟩
  · exact ⟨rfl, Enc.idxW u, wordsAt_get P [Enc.idxW u] 0 (by simp) M, lrep_arena HB H ls u f' _ hu⟩
  · exact ⟨rfl, Enc.idxW u, Enc.idxW w, wordsAt_get P [Enc.idxW u, Enc.idxW w] 0 (by simp) M,
      wordsAt_get P [Enc.idxW u, Enc.idxW w] 1 (by simp) M, lrep_arena HB H ls u f' _ hu, lrep_arena HB H ls w f' _ hw⟩
  · exact ⟨rfl, Enc.idxW u, Enc.idxW w, wordsAt_get P [Enc.idxW u, Enc.idxW w] 0 (by simp) M,
      wordsAt_get P [Enc.idxW u, Enc.idxW w] 1 (by simp) M, lrep_arena HB H ls u f' _ hu, lrep_arena HB H ls w f' _ hw⟩
  · exact ⟨rfl, n, ls.ns.nodeCount + 1, wordsAt_get P [Enc.idxW n] 0 (by simp) M, hn⟩

theorem heapKids_mem (C : Ctx) (ls : LStore) (o : Nat) (l : ConLeche.Level) (M : Mem)
    (hk : HKids C.HB C.H ls o l) :
    ∃ M', (∀ a v, (a, v) ∈ M' → (a, v) ∈ M ∨ ∃ j, ∃ hj : j < C.H.length, a = cellA C j ∧ v = C.H[j]) ∧
      (∀ p, p ∈ M → p ∈ M') ∧ LKids C.HB C.H ls (C.HB + BitVec.ofNat 64 (8 * o) + 8) M' l := by
  have get_of : ∀ j x, C.H[j]? = some x → ∃ hj : j < C.H.length, x = C.H[j] := by
    intro j x h
    have hj : j < C.H.length := by
      rcases Nat.lt_or_ge j C.H.length with hl | hl
      · exact hl
      · rw [List.getElem?_eq_none hl] at h; simp at h
    exact ⟨hj, by rw [List.getElem?_eq_getElem hj] at h; exact (Option.some.inj h).symm⟩
  cases l with
  | zero => exact ⟨M, fun a v h => Or.inl h, fun _ h => h, trivial⟩
  | succ u =>
    obtain ⟨wu, h1, h2⟩ := hk
    obtain ⟨hj1, e1⟩ := get_of _ _ h1
    refine ⟨(cellA C (o + 1 + 0), wu) :: M, fun a v h => ?_, fun _ h => List.mem_cons_of_mem _ h, wu,
      by rw [cellA_succ_add]; simp, h2⟩
    rcases List.mem_cons.mp h with e | e
    · cases e; exact Or.inr ⟨o + 1, hj1, rfl, e1⟩
    · exact Or.inl e
  | max u v =>
    obtain ⟨wu, wv, h1, h2, h3, h4⟩ := hk
    obtain ⟨hj1, e1⟩ := get_of _ _ h1
    obtain ⟨hj2, e2⟩ := get_of _ _ h2
    refine ⟨(cellA C (o + 1 + 0), wu) :: (cellA C (o + 1 + 1), wv) :: M, fun a x h => ?_,
      fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h), wu, wv,
      by rw [cellA_succ_add]; simp, by rw [cellA_succ_add]; simp, h3, h4⟩
    rcases List.mem_cons.mp h with e | e
    · cases e; exact Or.inr ⟨o + 1, hj1, rfl, e1⟩
    rcases List.mem_cons.mp e with e | e
    · cases e; exact Or.inr ⟨o + 2, hj2, rfl, e2⟩
    · exact Or.inl e
  | imax u v =>
    obtain ⟨wu, wv, h1, h2, h3, h4⟩ := hk
    obtain ⟨hj1, e1⟩ := get_of _ _ h1
    obtain ⟨hj2, e2⟩ := get_of _ _ h2
    refine ⟨(cellA C (o + 1 + 0), wu) :: (cellA C (o + 1 + 1), wv) :: M, fun a x h => ?_,
      fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h), wu, wv,
      by rw [cellA_succ_add]; simp, by rw [cellA_succ_add]; simp, h3, h4⟩
    rcases List.mem_cons.mp h with e | e
    · cases e; exact Or.inr ⟨o + 1, hj1, rfl, e1⟩
    rcases List.mem_cons.mp e with e | e
    · cases e; exact Or.inr ⟨o + 2, hj2, rfl, e2⟩
    · exact Or.inl e
  | param n =>
    obtain ⟨nh, f, h1, h2⟩ := hk
    obtain ⟨hj1, e1⟩ := get_of _ _ h1
    refine ⟨(cellA C (o + 1 + 0), Enc.idxW nh) :: M, fun a v h => ?_, fun _ h => List.mem_cons_of_mem _ h, nh, f,
      by rw [cellA_succ_add]; simp, h2⟩
    rcases List.mem_cons.mp h with e | e
    · cases e; exact Or.inr ⟨o + 1, hj1, rfl, e1⟩
    · exact Or.inl e

theorem specR_lvViewOld {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (w : BitVec 64) (l : ConLeche.Level) (hw : Γ.get lQ = some w) (hl : LRep C.HB C.H s.store.ls w l)
    (hfl : Γ.get lFll = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR) (hD : ∀ z, z ∈ lvScratch → z ∈ D)
    (hk : ∀ (Γ' : Env) (M' : Mem) (Pc : BitVec 64), (∀ z, z ∉ lvScratch → Γ'.get z = Γ.get z) →
      Γ'.get lX = some (BitVec.ofNat 64 (ltag l)) → Γ'.get lY = some Pc → (∀ p, p ∈ M → p ∈ M') →
      LKids C.HB C.H s.store.ls Pc M' l → SpecR (Inv C s Γ' M' D) rest s m R) :
    SpecR (Inv C s Γ M D) (lvViewOld rest) s m R := by
  have hD' : lRp ∈ D ∧ lRn ∈ D ∧ lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lDh ∈ D ∧ lFl ∈ D ∧ lX ∈ D ∧ lY ∈ D :=
    ⟨hD _ (by decide), hD _ (by decide), hD _ (by decide), hD _ (by decide), hD _ (by decide), hD _ (by decide),
      hD _ (by decide), hD _ (by decide), hD _ (by decide)⟩
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  have hhi := hok.heapHigh
  unfold lvViewOld
  rcases lrep_split hl with ⟨h, f, rfl, hd⟩ | ⟨o, rfl, htg, hkids⟩
  · have hlt : Enc.idxW h < BitVec.ofNat 64 (2 ^ 32) := by
      rw [BitVec.lt_def]; have := idxW_lt32 h; simp; omega
    refine specR_ifI _ 1 (by simp [sev, hw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]) (fun _ => ?_)
      (fun hw' => absurd hw' (by decide))
    refine specR_assignI lDh (vv lQ) (Enc.idxW h) hD'.2.2.2.2.2.1 (by simp [hw]) ?_
    refine specR_assignI lFl (vv lFll) C.FLl hD'.2.2.2.2.2.2.1 (by simp +decide [hfl]) ?_
    refine specR_lviewPI h (by simp +decide) (by simp +decide) (by simp +decide [hdir])
      ⟨hD'.2.2.1, hD'.2.2.2.1, hD'.2.2.2.2.1, hD'.1, hD'.2.1⟩ (fun v P hv _ _ => ?_)
    obtain ⟨htv, hkd⟩ := arenaKids s.store.ls C.HB C.H h f l v P M hd hv
    refine specR_assignI lX (vv lDg) (BitVec.ofNat 64 v.tagN) hD'.2.2.2.2.2.2.2.1 (by simp +decide) ?_
    refine specR_assignI lY (vv lRp) P hD'.2.2.2.2.2.2.2.2 (by simp +decide) ?_
    refine hk _ _ P (fun z hz => ?_) (by simp +decide [htv]) (by simp +decide)
      (fun _ h => List.mem_append_right _ h) hkd
    simp only [lvScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hz
    simp [Env.get_cons, n1, n2, n3, n4, n5, n6, n7, n8, n9]
  · have hol : o < C.H.length := by
      rcases Nat.lt_or_ge o C.H.length with hh | hh
      · exact hh
      · rw [List.getElem?_eq_none hh] at htg; simp at htg
    have hnlt : ¬ C.HB + BitVec.ofNat 64 (8 * o) < BitVec.ofNat 64 (2 ^ 32) := by
      rw [BitVec.lt_def]; simp [BitVec.toNat_add]; omega
    refine specR_ifI _ 0 (by simp [sev, hw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt])
      (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_heapLoadI lX (vv lQ) o hol hD'.2.2.2.2.2.2.2.1 (by simp [hw, cellA]) ?_
    rw [show C.H[o]'hol = BitVec.ofNat 64 (ltag l) by
      rw [List.getElem?_eq_getElem hol] at htg; exact Option.some.inj htg]
    refine specR_assignI lY (.op .add [vv lQ, .const 8]) (C.HB + BitVec.ofNat 64 (8 * o) + 8)
      hD'.2.2.2.2.2.2.2.2 (by simp +decide [sev, hw]) ?_
    obtain ⟨M', hM', hMM, hkd⟩ := heapKids_mem C s.store.ls o l M hkids
    intro t ht
    refine hk _ M' _ (fun z hz => ?_) (by simp +decide) (by simp +decide) hMM hkd t
      ⟨ht.sr, ht.env, fun a v hm => ?_, ht.decl⟩
    · simp only [lvScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hz
      simp [Env.get_cons, n8, n9]
    · rcases hM' a v hm with e | ⟨j, hj, rfl, rfl⟩
      · exact ht.mem a v e
      · exact heap_cell ht.sr j hj

theorem denoteLAux_det (st : LStore) (f f' : Nat) (i : LIdx) (x y : ConLeche.Level)
    (h1 : denoteLAux st f i = some x) (h2 : denoteLAux st f' i = some y) : x = y := by
  have a := denoteLAux_mono st f (max f f') i x (by omega) h1
  have b := denoteLAux_mono st f' (max f f') i y (by omega) h2
  rw [a] at b; exact Option.some.inj b

/-- The view as one step: tag into `x`, children's address into `y`. -/
def lvViewCode : ProgHOL 64 :=
  .ite (.cmp .lower (vv lQ) (.const (BitVec.ofNat 64 (2 ^ 32))))
    (.seq (.assign .local lDh (vv lQ)) (.seq (.assign .local lFl (vv lFll)) (.seq lViewP
      (.seq (.assign .local lX (vv lDg)) (.assign .local lY (vv lRp))))))
    (.seq (.assign .local lX (.load .one (vv lQ))) (.assign .local lY (.op .add [vv lQ, .const 8])))

def lvViewP (rest : ProgHOL 64) : ProgHOL 64 := .seq lvViewCode rest

theorem lvViewP_eval (rest : ProgHOL 64) (t : PState σ) (w : BitVec 64)
    (hw : t.locals.lookup lQ = some (.val (.word w))) :
    evaluateHOLFiniteState t (lvViewP rest) = evaluateHOLFiniteState t (lvViewOld rest) := by
  unfold lvViewP lvViewCode lvViewOld
  have hc := ConsLoop.eval_cmp_of t .lower (vv lQ) (.const (BitVec.ofNat 64 (2 ^ 32))) w _ (eval_vv t lQ _ hw)
    (eval_const t _)
  generalize (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower w (BitVec.ofNat 64 (2 ^ 32)) = true
    then (1 : BitVec 64) else 0) = cw at hc
  rw [seq_ite_distrib t _ _ _ _ _ hc]
  rw [ite_word t _ _ _ _ hc, ite_word t _ _ _ _ hc]
  by_cases hz : cw ≠ 0
  · rw [if_pos hz, if_pos hz]
    rw [seq_assoc]; apply seq_congr_right; intro t1
    rw [seq_assoc]; apply seq_congr_right; intro t2
    rw [seq_assoc]; apply seq_congr_right; intro t3
    rw [seq_assoc]
  · rw [if_neg hz, if_neg hz, seq_assoc]

theorem specR_lvViewI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (w : BitVec 64) (l : ConLeche.Level) (hw : Γ.get lQ = some w) (hl : LRep C.HB C.H s.store.ls w l)
    (hfl : Γ.get lFll = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR) (hD : ∀ z, z ∈ lvScratch → z ∈ D)
    (hk : ∀ (Γ' : Env) (M' : Mem) (Pc : BitVec 64), (∀ z, z ∉ lvScratch → Γ'.get z = Γ.get z) →
      Γ'.get lX = some (BitVec.ofNat 64 (ltag l)) → Γ'.get lY = some Pc → (∀ p, p ∈ M → p ∈ M') →
      LKids C.HB C.H s.store.ls Pc M' l → SpecR (Inv C s Γ' M' D) rest s m R) :
    SpecR (Inv C s Γ M D) (lvViewP rest) s m R := by
  intro t ht
  rw [lvViewP_eval rest t w (ht.env _ _ hw)]
  exact specR_lvViewOld hok w l hw hl hfl hdir hD hk t ht

end ConPanqueque.T
