import ConPanqueque.T.LvlEqQ
import ConPanqueque.T.LsView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `isEquivList` and `lvlsEq?`

`lsGo(a, b, i)` views both level lists and compares position `i` with `isEquiv`, then recurses; at the
end of the shorter list the lengths decide, in con-leche's order (elements first).
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub
open ConLeche (Level)

def fLsGo := ofString "lvlsEqGo"
def pIx := ofString "ix"
def lsParams : List MlS := [pLa, pLb, pIx]

def lsFin : ProgHOL 64 := .ite (.cmp .equal (vv lA2) (vv lRn)) (retK 2) (retK 1)

def lsStep : ProgHOL 64 :=
  .seq (.assign .local lZ (.load .one (.op .add [vv lA1, .shift .lsl (vv pIx) (.const 3)])))
  (.seq (.assign .local lD1 (.load .one (.op .add [vv lRp, .shift .lsl (vv pIx) (.const 3)])))
  (.seq (.call (some (some (.local, lV), none)) fEqv [vv lZ, vv lD1])
  (.ite (eqC lV 0) (retK 0) (.ite (eqC lV 1) (retK 1)
  (.seq (.call (some (some (.local, lV), none)) fLsGo [vv pLa, vv pLb, .op .add [vv pIx, .const 1]])
    (.return (vv lV)))))))

def lsGoBody : ProgHOL 64 :=
  prologue leqLocals
  (.seq (.assign .local lDh (vv pLa)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.seq (.assign .local lA1 (vv lRp)) (.seq (.assign .local lA2 (vv lRn))
  (.seq (.assign .local lDh (vv pLb)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.ite (.cmp .lower (vv pIx) (vv lA2)) (.ite (.cmp .lower (vv pIx) (vv lRn)) lsStep lsFin) lsFin)))))))))

/-! ## Twin facts -/

theorem denoteLList_get (st : LStore) : ∀ (xs : List LIdx) (ys : List Level), denoteLList st xs = some ys →
    ∃ hl : ys.length = xs.length, ∀ j (hj : j < xs.length), denoteL st xs[j] = some (ys[j]'(by omega))
  | [], ys, h => by
    simp [denoteLList] at h; subst h; exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
  | x :: xs, ys, h => by
    simp only [denoteLList, opt2] at h
    split at h
    · rename_i a b ha hb
      simp at h; subst h
      obtain ⟨hl, hg⟩ := denoteLList_get st xs b hb
      refine ⟨by simp [hl], fun j hj => ?_⟩
      cases j with
      | zero => simpa using ha
      | succ j => simpa using hg j (by simp at hj; omega)
    · simp at h

theorem isEquivList_cons (a : Level) (as : List Level) (b : Level) (bs : List Level) :
    Level.isEquivList (a :: as) (b :: bs) = (match Level.isEquiv a b with
      | none => none | some false => some false | some true => Level.isEquivList as bs) := by
  simp only [Level.isEquivList]
  rcases Level.isEquiv a b with _ | _ | _ <;> rfl

theorem isEquivList_fin (us vs : List Level) (i : Nat) (h1 : i ≤ us.length) (h2 : i ≤ vs.length)
    (h : ¬ (i < us.length ∧ i < vs.length)) :
    Level.isEquivList (us.drop i) (vs.drop i) = some (decide (us.length = vs.length)) := by
  rcases Nat.lt_or_ge i us.length with hu | hu
  · have hv : vs.length = i := by omega
    rw [List.drop_eq_nil_of_le (by omega : vs.length ≤ i), List.drop_eq_getElem_cons hu]
    simp [Level.isEquivList]; omega
  · have hu' : us.length = i := by omega
    rw [List.drop_eq_nil_of_le (by omega : us.length ≤ i)]
    rcases Nat.lt_or_ge i vs.length with hv | hv
    · rw [List.drop_eq_getElem_cons hv]; simp [Level.isEquivList]; omega
    · rw [List.drop_eq_nil_of_le (by omega : vs.length ≤ i)]; simp [Level.isEquivList]; omega

section
variable {σ : Type}

theorem params_noneLs (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ leqLocals → (ctxEnv C ++ lsParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ lsParams := by
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

theorem lsGo_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (hcB : C.code.lookup fByC = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody C, .one))
    (hcI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one))
    (hcR : C.code.lookup fImax = some (leqParams.map (fun p => (p, ShapeHOL.one)), imBody C, .one))
    (hcE : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    (hcT : C.code.lookup fRest = some (leqParams.map (fun p => (p, ShapeHOL.one)), restBody, .one))
    (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), leqBody, .one))
    (hcV : C.code.lookup fEqv = some ([(pLa, .one), (pLb, .one)], eqvBody, .one))
    (hcG : C.code.lookup fLsGo = some (lsParams.map (fun p => (p, ShapeHOL.one)), lsGoBody, .one))
    (H : List (BitVec 64)) (a b : LsIdx) (ua ub : List LIdx) (us vs : List Level) (s : AState)
    (ha : s.store.lss.view a = some ua) (hb : s.store.lss.view b = some ub)
    (hus : denoteLList s.store.ls ua = some us) (hvs : denoteLList s.store.ls ub = some vs) :
    ∀ n i, ua.length - i = n → i ≤ ua.length → i ≤ ub.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (lsParams.zip [Enc.idxW a, Enc.idxW b, BitVec.ofNat 64 i])) lsGoBody s
        (pure (Level.isEquivList (us.drop i) (vs.drop i))) (PostOB (ctxH C H)) := by
  obtain ⟨hlu, hgu⟩ := denoteLList_get _ ua us hus
  obtain ⟨hlv, hgv⟩ := denoteLList_get _ ub vs hvs
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hn hi1 hi2
    refine specR_prologue (postOB_locals _) (params_noneLs _ _) ?_
    refine specR_assignI lDh (vv pLa) (Enc.idxW a) (by decide) (by simp +decide [ctxEnv, lsParams]) ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [ctxEnv, lsParams] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) a (by simp +decide) (by simp +decide <;> rfl)
      (by simp +decide [ctxEnv, lsParams] <;> rfl) ⟨by decide, by decide, by decide, by decide, by decide⟩
      (fun v1 P1 hv1 _ hl1 => ?_)
    rw [ha] at hv1; cases hv1
    refine specR_assignI lA1 (vv lRp) P1 (by decide) (by simp) ?_
    refine specR_assignI lA2 (vv lRn) (BitVec.ofNat 64 (ua.map Enc.idxW).length) (by decide) (by simp +decide) ?_
    refine specR_assignI lDh (vv pLb) (Enc.idxW b) (by decide) (by simp +decide [ctxEnv, lsParams]) ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [ctxEnv, lsParams] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) b (by simp +decide) (by simp +decide <;> rfl)
      (by simp +decide [ctxEnv, lsParams] <;> rfl) ⟨by decide, by decide, by decide, by decide, by decide⟩
      (fun v2 P2 hv2 _ hl2 => ?_)
    rw [hb] at hv2; cases hv2
    simp only [List.length_map] at hl1 hl2 ⊢
    have fin : ∀ {Γ' : Env} {M' : Mem}, Env.get Γ' lA2 = some (BitVec.ofNat 64 ua.length) →
        Env.get Γ' lRn = some (BitVec.ofNat 64 ub.length) → ¬ (i < ua.length ∧ i < ub.length) →
        SpecR (Inv (σ := σ) (ctxH C H) s Γ' M' DQ) lsFin s
          (pure (Level.isEquivList (us.drop i) (vs.drop i))) (PostOB (ctxH C H)) := by
      intro Γ' M' g1 g2 hnot
      rw [isEquivList_fin us vs i (by omega) (by omega) (by omega)]
      unfold lsFin
      by_cases el : ua.length = ub.length
      · refine specR_ifI _ 1 (by simp +decide [sev, g1, g2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, el]) (fun _ => specR_retOB 2 _ ?_) (fun h => absurd h (by decide))
        simp [obW, hlu, hlv, el]
      · refine specR_ifI _ 0 (by simp +decide [sev, g1, g2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_eq_iff _ _ (by omega : ua.length < 2 ^ 64)
          (by omega : ub.length < 2 ^ 64), el]) (fun h => absurd rfl h) (fun _ => specR_retOB 1 _ ?_)
        simp [obW, hlu, hlv, el]
    by_cases c1 : i < ua.length
    · refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, lsParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
        (by omega : ua.length < 2 ^ 64), c1]) (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases c2 : i < ub.length
      · refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, lsParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
          (by omega : ub.length < 2 ^ 64), c2]) (fun _ => ?_) (fun h => absurd h (by decide))
        have hiu : i < us.length := by omega
        have hiv : i < vs.length := by omega
        rw [List.drop_eq_getElem_cons hiu, List.drop_eq_getElem_cons hiv, isEquivList_cons]
        unfold lsStep
        have m1 := wordsAt_get P1 (ua.map Enc.idxW) i (by simpa using c1) []
        have m2 := wordsAt_get P2 (ub.map Enc.idxW) i (by simpa using c2) (wordsAt P1 (ua.map Enc.idxW) ++ [])
        simp only [List.getElem_map] at m1 m2
        refine specR_loadI' lZ _ (P1 + BitVec.ofNat 64 (8 * i)) _ (Enc.idxW ua[i]) (by decide)
          (by simp +decide [sev, ctxEnv, lsParams]; rw [shl_ofNat _ _ (by omega)]) rfl
          (List.mem_append_right _ m1) ?_
        refine specR_loadI' lD1 _ (P2 + BitVec.ofNat 64 (8 * i)) _ (Enc.idxW ub[i]) (by decide)
          (by simp +decide [sev, ctxEnv, lsParams]; rw [shl_ofNat _ _ (by omega)]) rfl m2 ?_
        refine specR_congr (m' := pure (Level.isEquiv us[i] vs[i]) >>= fun o => pure (match o with
          | none => none | some false => some false
          | some true => Level.isEquivList (us.drop (i + 1)) (vs.drop (i + 1)))) (by simp) ?_
        refine callOB_spec (C := ctxH C H) lV fEqv [pLa, pLb] [vv lZ, vv lD1] eqvBody [Enc.idxW ua[i], Enc.idxW ub[i]]
          (by decide) rfl (by decide) hcV ⟨by simp +decide, by simp +decide, trivial⟩ _
          (eqv_spec C hok hcS hcN hcM hcC hcB hcI hcR hcE hcT hcL H us[i] vs[i] _ _ s
            (lrep_arena _ _ _ _ _ _ (hgu i c1)) (lrep_arena _ _ _ _ _ _ (hgv i c2))) ?_
        rcases ho : Level.isEquiv us[i] vs[i] with _ | b0
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
        exact callRetOB (C := ctxH C H) fLsGo lsParams [vv pLa, vv pLb, .op .add [vv pIx, .const 1]] lsGoBody
            [Enc.idxW a, Enc.idxW b, BitVec.ofNat 64 (i + 1)] (by decide) rfl (by decide) hcG
            ⟨by simp +decide [ctxEnv, lsParams], by simp +decide [ctxEnv, lsParams],
              by simp +decide [sev, ctxEnv, lsParams]; exact word_add1_eq i, trivial⟩ _
            (ih (n - 1) (by omega) (i + 1) (by omega) (by omega) (by omega))
      · refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, lsParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
          (by omega : ub.length < 2 ^ 64), c2]) (fun h => absurd rfl h) (fun _ => fin (by simp +decide) (by simp +decide) (by omega))
    · refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, lsParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
        (by omega : ua.length < 2 ^ 64), c1]) (fun h => absurd rfl h) (fun _ => fin (by simp +decide) (by simp +decide) (by omega))

end

/-! ## `lvlsEq?` -/

theorem readLevelsM_run (h : LsIdx) (s : AState) (l : List Level) (hrl : ReadLsCacheOK s.caches.readLsC s.store)
    (hd : denoteLs s.store.lss h = some l) :
    ∃ s1, readLevelsM h s = .ok (l, s1) ∧ s1.store = s.store ∧ s1.memos = s.memos ∧
      ReadLsCacheOK s1.caches.readLsC s1.store ∧ s1.caches.lvlsEqC = s.caches.lvlsEqC ∧
      MirrorEq s1.caches s.caches ∧ s1.pins = s.pins := by
  unfold readLevelsM
  rcases hc : s.caches.readLsC[h]? with _ | l'
  · refine ⟨{ s with caches := { s.caches with readLsC := s.caches.readLsC.insert h l } }, ?_, rfl, rfl, ?_, rfl, mirrorEq_refl _, rfl⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
    · intro k u hk
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hrl k u hk
  · have := hrl h l' hc
    rw [hd] at this; cases this
    exact ⟨s, by simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure], rfl, rfl, hrl, rfl, mirrorEq_refl _, rfl⟩

theorem readLevelsM_cok (h : LsIdx) (s : AState) (l : List Level) (hco : CachesOK s)
    (hd : denoteLs s.store.lss h = some l) :
    ∃ s1, readLevelsM h s = .ok (l, s1) ∧ CachesOK s1 ∧ s1.store = s.store := by
  unfold readLevelsM
  rcases hc : s.caches.readLsC[h]? with _ | l'
  · refine ⟨{ s with caches := { s.caches with readLsC := s.caches.readLsC.insert h l } }, ?_, ?_, rfl⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
    · refine ⟨hco.rn, hco.rl, fun k u hk => ?_, hco.le, hco.les⟩
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hco.rls k u hk
  · have := hco.rls h l' hc
    rw [hd] at this; cases this
    exact ⟨s, by simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure], hco, rfl⟩

theorem lvlsEqQ_cok (u v : LsIdx) (s : AState) (lu lv : List Level) (hu : denoteLs s.store.lss u = some lu)
    (hv : denoteLs s.store.lss v = some lv) (hco : CachesOK s) :
    ∃ s', lvlsEq? u v s = .ok (Level.isEquivList lu lv, s') ∧ CachesOK s' := by
  unfold lvlsEq?
  rcases hc : s.caches.lvlsEqC[(u, v)]? with _ | r
  · obtain ⟨s1, h1, ok1, e1⟩ := readLevelsM_cok u s lu hco hu
    obtain ⟨s2, h2, ok2, e2⟩ := readLevelsM_cok v s1 lv ok1 (by rw [e1]; exact hv)
    rcases hq : Level.isEquivList lu lv with _ | r
    · refine ⟨s2, ?_, ok2⟩
      simp [hc, h1, h2, hq, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
        Except.bind, Except.pure]
    · refine ⟨{ s2 with caches := { s2.caches with lvlsEqC := s2.caches.lvlsEqC.insert (u, v) r } }, ?_,
        ⟨ok2.rn, ok2.rl, ok2.rls, ok2.le, fun k b hk => ?_⟩⟩
      · simp [hc, h1, h2, hq, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure,
          StateT.pure, Except.bind, Except.pure]
      · simp only [Std.HashMap.getElem?_insert] at hk
        split at hk
        · rename_i e; simp at e; subst e; simp at hk; subst hk
          exact ⟨lu, lv, by rw [e2, e1]; exact hu, by rw [e2, e1]; exact hv, hq⟩
        · exact ok2.les k b hk
  · obtain ⟨u', v', hu', hv', hq⟩ := hco.les (u, v) r hc
    rw [hu] at hu'; cases hu'
    rw [hv] at hv'; cases hv'
    refine ⟨s, ?_, hco⟩
    simp [hc, hq, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure]

theorem lvlsEqQ_run (u v : LsIdx) (s : AState) (lu lv : List Level) (hu : denoteLs s.store.lss u = some lu)
    (hv : denoteLs s.store.lss v = some lv)
    (hrl : ReadLsCacheOK s.caches.readLsC s.store) (hle : LvlsEqCacheOK s.caches.lvlsEqC s.store) :
    ∃ s', lvlsEq? u v s = .ok (Level.isEquivList lu lv, s') ∧ s'.store = s.store ∧ s'.memos = s.memos ∧
      MirrorEq s'.caches s.caches ∧ s'.pins = s.pins := by
  unfold lvlsEq?
  rcases hc : s.caches.lvlsEqC[(u, v)]? with _ | r
  · obtain ⟨s1, h1, e1, m1, ok1, _, c1, p1⟩ := readLevelsM_run u s lu hrl hu
    obtain ⟨s2, h2, e2, m2, _, _, c2, p2⟩ := readLevelsM_run v s1 lv ok1 (by rw [e1]; exact hv)
    rcases hq : Level.isEquivList lu lv with _ | r
    · refine ⟨s2, ?_, by rw [e2, e1], by rw [m2, m1], mirrorEq_trans c2 c1, p2.trans p1⟩
      simp [hc, h1, h2, hq, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
        Except.bind, Except.pure]
    · refine ⟨{ s2 with caches := { s2.caches with lvlsEqC := s2.caches.lvlsEqC.insert (u, v) r } }, ?_,
        e2.trans e1, m2.trans m1, mirrorEq_trans c2 c1, p2.trans p1⟩
      simp [hc, h1, h2, hq, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure,
        StateT.pure, Except.bind, Except.pure]
  · obtain ⟨u', v', hu', hv', hq⟩ := hle (u, v) r hc
    rw [hu] at hu'; cases hu'
    rw [hv] at hv'; cases hv'
    refine ⟨s, ?_, rfl, rfl, mirrorEq_refl _, rfl⟩
    simp [hc, hq, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure]


section
variable {σ : Type}

theorem lvlsEqQ_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (hcB : C.code.lookup fByC = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody C, .one))
    (hcI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one))
    (hcR : C.code.lookup fImax = some (leqParams.map (fun p => (p, ShapeHOL.one)), imBody C, .one))
    (hcE : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    (hcT : C.code.lookup fRest = some (leqParams.map (fun p => (p, ShapeHOL.one)), restBody, .one))
    (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), leqBody, .one))
    (hcV : C.code.lookup fEqv = some ([(pLa, .one), (pLb, .one)], eqvBody, .one))
    (hcG : C.code.lookup fLsGo = some (lsParams.map (fun p => (p, ShapeHOL.one)), lsGoBody, .one))
    (H : List (BitVec 64)) (u v : LsIdx) (s : AState) (lu lv : List Level)
    (hu : denoteLs s.store.lss u = some lu) (hv : denoteLs s.store.lss v = some lv)
    (hrl : ReadLsCacheOK s.caches.readLsC s.store) (hle : LvlsEqCacheOK s.caches.lvlsEqC s.store) :
    SpecR (Pre (σ := σ) (ctxH C H) s (lsParams.zip [Enc.idxW u, Enc.idxW v, BitVec.ofNat 64 0])) lsGoBody s
      (lvlsEq? u v)
      (fun o w s' st => s'.store = s.store ∧ s'.memos = s.memos ∧ PostOB (ctxH C H) o w s' st) := by
  obtain ⟨s', hrun, e1, e2, e3, e4⟩ := lvlsEqQ_run u v s lu lv hu hv hrl hle
  have hu' := hu; have hv' := hv
  unfold denoteLs at hu' hv'
  split at hu'
  · simp at hu'
  rename_i ua hua
  split at hv'
  · simp at hv'
  rename_i ub hub
  have hsp := lsGo_spec (σ := σ) C hok hcS hcN hcM hcC hcB hcI hcR hcE hcT hcL hcV hcG H u v ua ub lu lv s hua hub
    hu' hv' _ 0 rfl (Nat.zero_le _) (Nat.zero_le _)
  simp only [List.drop_zero] at hsp
  exact specR_ofRun hrun hsp (fun w st ⟨hw, hsr⟩ => ⟨e1, e2, hw, sr_congrS hsr e1 e2 e3 e4 (by
      obtain ⟨s'', hr'', hc''⟩ := lvlsEqQ_cok u v s lu lv hu hv hsr.cok
      rw [hrun] at hr''; simp only [Except.ok.injEq, Prod.mk.injEq] at hr''; rw [hr''.2]; exact hc'')⟩)

end

end ConPanqueque.T.LLeq
