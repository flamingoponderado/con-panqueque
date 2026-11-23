import ConPanqueque.T.LvlEqList
import ConPanqueque.T.Blk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Level substitution at a parameter list

`goM(n, ks, us, i)`: con-leche's `Level.subst.go` from position `i`: the names `ks` are a heap block of
name handles, the levels `us` a level-list handle; names are compared by structure (`nameEq`). The answer
is the matching level's handle word, or `2^32` (no handle word) when no name matches.
-/

namespace ConPanqueque.T.LSub
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LLeq
open ConLeche (Level Name)

/-- The twin's `subst.go` as a search: the matching level, if any. -/
def goIdx : List Name → List Level → Name → Option Level
  | k :: ks, v :: vs, n => if k = n then some v else goIdx ks vs n
  | _, _, _ => none

theorem go_eq (ks : List Name) (vs : List Level) (n : Name) :
    Level.subst.go ks vs n = (goIdx ks vs n).getD (.param n) := by
  induction ks generalizing vs with
  | nil => cases vs <;> rfl
  | cons k ks ih =>
    cases vs with
    | nil => rfl
    | cons v vs => by_cases e : k = n <;> simp [Level.subst.go, goIdx, e, ih]

def fGoM := ofString "substGo"
def pGn := ofString "gn"
def pKp := ofString "kp"
def pUs := ofString "us"
def pGi := ofString "gi"
def goParams : List MlS := [pGn, pKp, pUs, pGi]

def goBody : ProgHOL 64 :=
  prologue lvlLocals
  (.seq (.assign .local lDh (vv pUs)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.seq (.assign .local lW (.load .one (vv pKp)))
  (.ite (.cmp .lower (vv pGi) (vv lW)) (.ite (.cmp .lower (vv pGi) (vv lRn))
    (.seq (.assign .local lA1 (.load .one (.op .add [vv pKp, .op .add [.shift .lsl (vv pGi) (.const 3), .const 8]])))
    (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .shift .lsl (vv pGi) (.const 3)])))
    (.seq (.call (some (some (.local, lZ), none)) fNeq [vv lA1, vv pGn])
    (.ite (eqC lZ 0)
      (.seq (.call (some (some (.local, lA2), none)) fGoM [vv pGn, vv pKp, vv pUs, .op .add [vv pGi, .const 1]])
        (.return (vv lA2)))
      (.return (vv lB))))))
    (.return (.const (BitVec.ofNat 64 (2 ^ 32))))) (.return (.const (BitVec.ofNat 64 (2 ^ 32)))))))))

section
variable {σ : Type}

/-- `goM`'s post: the state kept; a match is an arena word reading back to the level, no match is `2^32`. -/
def PostGo (C : Ctx) (o : Option Level) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  SR C s' st ∧ (o = none → w = BitVec.ofNat 64 (2 ^ 32)) ∧
    ∀ v, o = some v → w.toNat < 2 ^ 32 ∧ LRep C.HB C.H s'.store.ls w v

theorem postGo_locals (C : Ctx) : ∀ (a : Option Level) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostGo C a w s' st → PostGo C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨sr_of_eq h1 rfl rfl rfl rfl, h2, h3⟩

theorem params_noneGo (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ lvlLocals → (ctxEnv C ++ goParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ goParams := by
    simp only [lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
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

theorem denoteNList_get (st : NStore) : ∀ (xs : List NIdx) (ys : List Name), Frontend.denoteNList st xs = some ys →
    ∃ hl : ys.length = xs.length, ∀ j (hj : j < xs.length), denoteN st xs[j] = some (ys[j]'(by omega))
  | [], ys, h => by
    simp [Frontend.denoteNList] at h; subst h; exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
  | x :: xs, ys, h => by
    simp only [Frontend.denoteNList] at h
    split at h
    · rename_i a b ha hb
      simp at h; subst h
      obtain ⟨hl, hg⟩ := denoteNList_get st xs b hb
      refine ⟨by simp [hl], fun j hj => ?_⟩
      cases j with
      | zero => simpa using ha
      | succ j => simpa using hg j (by simp at hj; omega)
    · simp at h

end

theorem goIdx_cons (ks : List Name) (vs : List Level) (n : Name) (i : Nat) (h1 : i < ks.length) (h2 : i < vs.length) :
    goIdx (ks.drop i) (vs.drop i) n = if ks[i] = n then some vs[i] else goIdx (ks.drop (i + 1)) (vs.drop (i + 1)) n := by
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2]; rfl

theorem goIdx_end (ks : List Name) (vs : List Level) (n : Name) (i : Nat) (h : ¬ (i < ks.length ∧ i < vs.length)) :
    goIdx (ks.drop i) (vs.drop i) n = none := by
  rcases Nat.lt_or_ge i ks.length with h1 | h1
  · rw [List.drop_eq_nil_of_le (show vs.length ≤ i by omega)]; cases ks.drop i <;> rfl
  · rw [List.drop_eq_nil_of_le h1]; rfl

theorem cellA_idxH (C : Ctx) (o i : Nat) (h : C.HB.toNat + 8 * (o + 1 + i) < 2 ^ 64) :
    cellA C o + (BitVec.ofNat 64 i <<< 3 + 8#64) = cellA C (o + 1 + i) := by
  apply BitVec.eq_of_toNat_eq
  simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

section
variable {σ : Type}

theorem callGo {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Option Level → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (es : List (ExpHOL 64)) (vs : List (BitVec 64)) (hl : vs.length = goParams.length)
    (hx : x ∈ D) (hC : C.code.lookup fGoM = some (goParams.map (fun p => (p, ShapeHOL.one)), goBody, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs) (o : Option Level)
    (hspec : SpecR (Pre (σ := σ) C s (goParams.zip vs)) goBody s (pure o) (PostGo C))
    (hk : ∀ w, ((o = none → w = BitVec.ofNat 64 (2 ^ 32)) ∧
      ∀ v, o = some v → w.toNat < 2 ^ 32 ∧ LRep C.HB C.H s.store.ls w v) →
      SpecR (Inv C s ((x, w) :: Γ) [] D) rest s (k o) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fGoM es) rest) s (pure o >>= k) R :=
  specR_callNIM x fGoM goParams es goBody vs (by decide) hl hx hC hes
    (fun a w s' st => s' = s ∧ a = o ∧ PostGo C a w s' st) (fun _ _ _ _ hp => hp.2.2.1)
    (fun u hu _ hlk => by
      have H0 : SpecR (· = u) goBody s (pure o : AM (Option Level)) (PostGo C) :=
        fun w hw => by subst hw; exact hspec _ (pre_of_lookups hu goParams vs hl hlk)
      refine specR_mono (specR_run H0) (fun _ h => h) (fun a w s' st hp => ?_)
      obtain ⟨hrun, hp⟩ := hp
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨hrun.2.symm, hrun.1.symm, hp⟩)
    (fun a w s' st ⟨hs, ha, hp⟩ => by subst hs ha; exact hk w hp.2)

theorem goM_spec (C : Ctx) (hok : CtxOK C)
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcG : C.code.lookup fGoM = some (goParams.map (fun p => (p, ShapeHOL.one)), goBody, .one))
    (H : List (BitVec 64)) (ko : Nat) (khs : List NIdx) (ks : List Name) (us : LsIdx) (uh : List LIdx)
    (vs : List Level) (nh : NIdx) (fn : Nat) (nm : Name) (s : AState)
    (hblk : BlkAt H ko (khs.map Enc.idxW)) (hks : Frontend.denoteNList s.store.ns khs = some ks)
    (hu : s.store.lss.view us = some uh) (hvs : denoteLList s.store.ls uh = some vs)
    (hn : denoteNAux s.store.ns fn nh = some nm) :
    ∀ n i, ks.length - i = n → i ≤ ks.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (goParams.zip [Enc.idxW nh, cellA C ko, Enc.idxW us, BitVec.ofNat 64 i]))
        goBody s (pure (goIdx (ks.drop i) (vs.drop i) nm)) (PostGo (ctxH C H)) := by
  obtain ⟨hlk, hgk⟩ := denoteNList_get _ khs ks hks
  obtain ⟨hlv, hgv⟩ := denoteLList_get _ uh vs hvs
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hn' hik0
    refine specR_prologue (postGo_locals _) (params_noneGo _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hlay := hok.heapLay
    have hkl : ko + 1 + khs.length ≤ C.HN := by
      have := blkAt_len hblk; simp only [List.length_map] at this
      simp only [show (ctxH C H).H = H from rfl, show (ctxH C H).HN = C.HN from rfl] at hHN; omega
    refine specR_assignI lDh (vv pUs) (Enc.idxW us) (by decide) (by simp +decide [ctxEnv, goParams]) ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [ctxEnv, goParams] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp +decide) (by simp +decide <;> rfl)
      (by simp +decide [ctxEnv, goParams] <;> rfl) ⟨by decide, by decide, by decide, by decide, by decide⟩
      (fun v1 P1 hv1 _ hl1 => ?_)
    rw [hu] at hv1; cases hv1
    simp only [List.length_map] at hl1 ⊢
    obtain ⟨h0l, h0v⟩ := blkAt_get0 hblk
    refine specR_heapLoadI (C := ctxH C H) lW (vv pKp) ko h0l (by decide)
      (by simp +decide [ctxEnv, goParams] <;> rfl) ?_
    simp only [show (ctxH C H).H = H from rfl, h0v, List.length_map]
    by_cases c : i < khs.length ∧ i < uh.length
    · obtain ⟨c1, c2⟩ := c
      refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, goParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
        (by omega : khs.length < 2 ^ 64), c1]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, goParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
        (by omega : uh.length < 2 ^ 64), c2]) (fun _ => ?_) (fun h => absurd h (by decide))
      obtain ⟨hil, hiv⟩ := blkAt_get hblk i (by simpa using c1)
      refine specR_heapLoadI (C := ctxH C H) lA1 _ (ko + 1 + i) hil (by decide)
        (by simp +decide [sev, ctxEnv, goParams]; exact cellA_idxH C ko i (by omega)) ?_
      have m2 := wordsAt_get P1 (uh.map Enc.idxW) i (by simpa using c2) []
      simp only [List.getElem_map] at m2 hiv
      refine specR_loadI' lB _ (P1 + BitVec.ofNat 64 (8 * i)) _ (Enc.idxW uh[i]) (by decide)
        (by simp +decide [sev, ctxEnv, goParams]; rw [shl_ofNat _ _ (by omega)]) rfl m2 ?_
      have hik : i < ks.length := by omega
      have hiv' : i < vs.length := by omega
      rw [goIdx_cons ks vs nm i hik hiv']
      refine specR_congr (m' := pure (decide (ks[i] = nm)) >>= fun b =>
        if b = true then pure (some vs[i]) else pure (goIdx (ks.drop (i + 1)) (vs.drop (i + 1)) nm))
        (by by_cases e : ks[i] = nm <;> simp [e]) ?_
      refine callNeq_spec (C := ctxH C H) hcN lZ lA1 pGn khs[i] nh ks[i] nm _ fn (hgk i c1) hn (by decide)
        (by simp only [show (ctxH C H).H = H from rfl] at hiv ⊢; simp +decide [hiv]) (by simp +decide [ctxEnv, goParams]) ?_
      by_cases e : ks[i] = nm
      · simp only [e, decide_true, ite_true]
        refine specR_ifI _ 0 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        exact specR_returnI (vv lB) (Enc.idxW uh[i]) (by simp +decide) (fun t ht => ⟨sr_of_eq ht.sr rfl rfl rfl rfl,
          fun h => by simp at h, fun v hv => by
            simp only [Option.some.injEq] at hv; subst hv
            exact ⟨idxW_lt32 _, lrep_arena _ _ _ _ _ _ (hgv i c2)⟩⟩)
      · simp only [e, decide_false]
        refine specR_ifI _ 1 (by simp +decide [eqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_congr (m' := pure (goIdx (ks.drop (i + 1)) (vs.drop (i + 1)) nm) >>= fun o => pure o)
          (by simp) ?_
        refine callGo (C := ctxH C H) lA2 [vv pGn, vv pKp, vv pUs, .op .add [vv pGi, .const 1]]
          [Enc.idxW nh, cellA C ko, Enc.idxW us, BitVec.ofNat 64 (i + 1)] rfl (by decide) hcG
          ⟨by simp +decide [ctxEnv, goParams], by simp +decide [ctxEnv, goParams] <;> rfl,
            by simp +decide [ctxEnv, goParams], by simp +decide [sev, ctxEnv, goParams]; exact word_add1_eq i, trivial⟩ _
          (ih (n - 1) (by omega) (i + 1) (by omega) (by omega)) (fun w hw => ?_)
        exact specR_returnI (vv lA2) w (by simp) (fun t ht => ⟨sr_of_eq ht.sr rfl rfl rfl rfl, hw⟩)
    · rw [goIdx_end ks vs nm i (by omega)]
      have fin : ∀ {Γ' : Env} {M' : Mem}, SpecR (Inv (σ := σ) (ctxH C H) s Γ' M' (ctxLocals ++ lvlLocals))
          (.return (.const (BitVec.ofNat 64 (2 ^ 32)))) s (pure none) (PostGo (ctxH C H)) := fun {Γ' M'} =>
        specR_returnI _ _ rfl (fun t ht => ⟨sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun v hv => by simp at hv⟩)
      by_cases c1 : i < khs.length
      · refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, goParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
          (by omega : khs.length < 2 ^ 64), c1]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, goParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
          (by omega : uh.length < 2 ^ 64), show ¬ i < uh.length by omega]) (fun h => absurd rfl h) (fun _ => fin)
      · refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, goParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : i < 2 ^ 64)
          (by omega : khs.length < 2 ^ 64), c1]) (fun h => absurd rfl h) (fun _ => fin)

end

/-! ## Substitution at a parameter list -/

def fSubstM := ofString "substM"

def substRestM (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lA2) (.const 0)) (.return (vv pLa))
  (.seq (.assign .local lD1 (.load .one (vv lA3)))
  (.ite (.cmp .equal (vv lA2) (.const 4))
    (.seq (.call (some (some (.local, lZ), none)) fGoM [vv lD1, vv pKp, vv pUs, .const 0])
      (.ite (.cmp .equal (vv lZ) (.const (BitVec.ofNat 64 (2 ^ 32)))) (.return (vv pLa)) (.return (vv lZ))))
  (.ite (.cmp .equal (vv lA2) (.const 1))
    (.seq (.call (some (some (.local, lA1), none)) fSubstM [vv lD1, vv pKp, vv pUs])
      (alloc2 C lW (.const 1) (vv lA1) (.return (vv lW))))
    (.seq (.assign .local lB (.load .one (.op .add [vv lA3, .const 8])))
    (.seq (.call (some (some (.local, lA1), none)) fSubstM [vv lD1, vv pKp, vv pUs])
    (.seq (.call (some (some (.local, lZ), none)) fSubstM [vv lB, vv pKp, vv pUs])
      (alloc3 C lW (vv lA2) (vv lA1) (vv lZ) (.return (vv lW)))))))))

def substCoreM (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv pLa)) (lvViewP
    (.seq (.assign .local lA2 (vv lX)) (.seq (.assign .local lA3 (vv lY)) (substRestM C))))

def substBodyM (C : Ctx) : ProgHOL 64 := prologue lvlLocals (substCoreM C)

def substMParams : List MlS := [pLa, pKp, pUs]

section
variable {σ : Type}

theorem params_noneSubM (a b c : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ lvlLocals → (ctxEnv C ++ substMParams.zip [a, b, c]).get x = none := by
  intro x hx
  simp only [lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem substM_view (C : Ctx) (hok : CtxOK C) (H : List (BitVec 64)) (w : BitVec 64) (ko : Nat) (us : LsIdx)
    (l : ConLeche.Level) (s : AState) (hl : LRep C.HB H s.store.ls w l) (m : AM ConLeche.Level)
    (hk : ∀ (Γ1 : Env) (M1 : Mem) (Pc : BitVec 64), Γ1.get lA2 = some (BitVec.ofNat 64 (ltag l)) →
      Γ1.get lA3 = some Pc → Γ1.get pLa = some w → Γ1.get pKp = some (cellA C ko) → Γ1.get pUs = some (Enc.idxW us) →
      Γ1.get lA1 = none → Γ1.get lZ = none → Γ1.get lB = none → Γ1.get lD1 = none → Γ1.get lW = none →
      LKids C.HB H s.store.ls Pc M1 l →
      SpecR (Inv (σ := σ) (ctxH C H) s Γ1 M1 DL) (substRestM C) s m (PostLv (ctxH C H))) :
    SpecR (Pre (σ := σ) (ctxH C H) s (substMParams.zip [w, cellA C ko, Enc.idxW us])) (substBodyM C) s m
      (PostLv (ctxH C H)) := by
  refine specR_prologue (postLv_locals _) (params_noneSubM _ _ _ _) ?_
  unfold substCoreM
  refine specR_assignI lQ (vv pLa) w (by decide) (by simp +decide [ctxEnv, substMParams]) ?_
  refine specR_lvViewI (C := ctxH C H) (ctxOK_H hok H) w l (by simp) hl (by simp +decide [ctxEnv] <;> rfl)
    (by simp +decide [ctxEnv] <;> rfl) lvScratch_DL (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => ?_)
  refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 (ltag l)) (by decide) (by simp [hx1]) ?_
  refine specR_assignI lA3 (vv lY) Pc (by decide) (by simp +decide [hy1]) ?_
  refine hk _ _ Pc (by simp +decide) (by simp +decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hk1 <;>
    (simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, substMParams] <;> rfl)

theorem substM_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubstM = some (substMParams.map (fun p => (p, ShapeHOL.one)), substBodyM C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcG : C.code.lookup fGoM = some (goParams.map (fun p => (p, ShapeHOL.one)), goBody, .one))
    (s : AState) (ko : Nat) (khs : List NIdx) (ks : List Name) (us : LsIdx) (uh : List LIdx) (vs : List Level)
    (hks : Frontend.denoteNList s.store.ns khs = some ks)
    (hu : s.store.lss.view us = some uh) (hvs : denoteLList s.store.ls uh = some vs) :
    ∀ (l : ConLeche.Level) (H : List (BitVec 64)) (w : BitVec 64), BlkAt H ko (khs.map Enc.idxW) →
      LRep C.HB H s.store.ls w l →
      SpecR (Pre (σ := σ) (ctxH C H) s (substMParams.zip [w, cellA C ko, Enc.idxW us])) (substBodyM C) s
        (pure (ConLeche.Level.subst ks vs l)) (PostLv (ctxH C H)) := by
  intro l
  induction l with
  | zero =>
    intro H w hb hl
    refine substM_view C hok H w ko us _ s hl _ (fun Γ1 M1 Pc h2 h3 hw _ _ _ _ _ _ _ _ => ?_)
    unfold substRestM
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    exact specR_returnI (vv pLa) w (by simp [hw]) (fun t ht => ⟨H, List.prefix_refl _, hl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | param n =>
    intro H w hb hl
    refine substM_view C hok H w ko us _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨nhn, fn, m1, d1⟩ := hk1
    unfold substRestM
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) _ (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    rw [show ConLeche.Level.subst ks vs (.param n) = (goIdx (ks.drop 0) (vs.drop 0) n).getD (.param n) by
      simp [ConLeche.Level.subst, go_eq]]
    refine specR_congr (m' := pure (goIdx (ks.drop 0) (vs.drop 0) n) >>= fun o => pure (o.getD (.param n)))
      (by simp) ?_
    refine callGo (C := ctxH C H) lZ [vv lD1, vv pKp, vv pUs, .const 0]
      [Enc.idxW nhn, cellA C ko, Enc.idxW us, BitVec.ofNat 64 0] rfl (by decide) hcG
      ⟨by simp +decide, by simp +decide [hsp] <;> rfl, by simp +decide [hlb], rfl, trivial⟩ _
      (goM_spec C hok hcN hcG H ko khs ks us uh vs nhn fn n s hb hks hu hvs d1 _ 0 rfl (Nat.zero_le _))
      (fun wz hz => ?_)
    rcases ho : goIdx (ks.drop 0) (vs.drop 0) n with _ | v
    · have e := hz.1 ho
      refine specR_ifI _ 1 (by simp +decide [sev, e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
      exact specR_returnI (vv pLa) w (by simp +decide [hw])
        (fun t ht => ⟨H, List.prefix_refl _, hl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · obtain ⟨hlt, hrep⟩ := hz.2 v ho
      have hne : wz ≠ BitVec.ofNat 64 (2 ^ 32) := by
        intro e; rw [e] at hlt; simp at hlt
      refine specR_ifI _ 0 (by simp +decide [sev, hne, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
      exact specR_returnI (vv lZ) wz (by simp +decide)
        (fun t ht => ⟨H, List.prefix_refl _, hrep, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ u ih =>
    intro H w hb hl
    refine substM_view C hok H w ko us _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, m1, r1⟩ := hk1
    unfold substRestM
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    refine specR_congr (m' := pure (ConLeche.Level.subst ks vs u) >>= fun c => pure (ConLeche.Level.succ c))
      (by simp [ConLeche.Level.subst]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSubstM substMParams [vv lD1, vv pKp, vv pUs] (substBodyM C) [wu, cellA C ko, Enc.idxW us]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp] <;> rfl, by simp +decide [hlb], trivial⟩ _
      (ih H wu hb r1) (fun H1 c hp1 hc => ?_)
    refine specR_alloc2I (C := ctxH C H1) (ctxOK_H hok H1) lW (.const 1) (vv lA1) 1 c (by decide) (fun _ => rfl)
      (fun _ => by simp +decide) (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp2' : H1 <+: H2 := hp2
    exact ⟨_, hp1.trans (hp2'.trans (img2_prefix H2 ws _ c hws)),
      lrep_mkSucc (ctxH C H1) s.store.ls H2 ws c _ hws hp2 hc, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | max u v ihu ihv =>
    intro H w hb hl
    refine substM_view C hok H w ko us _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, wv2, m1, m2, r1, r2⟩ := hk1
    unfold substRestM
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lB _ (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv2 (by decide) (by simp +decide [sev, h3])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (ConLeche.Level.subst ks vs u) >>= fun a =>
      pure (ConLeche.Level.subst ks vs v) >>= fun b => pure (ConLeche.Level.max a b))
      (by simp [ConLeche.Level.subst]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSubstM substMParams [vv lD1, vv pKp, vv pUs] (substBodyM C) [wu, cellA C ko, Enc.idxW us]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp] <;> rfl, by simp +decide [hlb], trivial⟩ _
      (ihu H wu hb r1) (fun H1 c1 hp1 hc1 => ?_)
    refine callLv_spec (C := ctxH C H1) lZ fSubstM substMParams [vv lB, vv pKp, vv pUs] (substBodyM C) [wv2, cellA C ko, Enc.idxW us]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp] <;> rfl, by simp +decide [hlb], trivial⟩ _
      (ihv H1 wv2 (blkAt_mono hb hp1) (lrep_mono hp1 v wv2 r2)) (fun H2 c2 hp2 hc2 => ?_)
    have hc1' := lrep_mono hp2 _ c1 hc1
    refine specR_alloc3I (C := ctxH C H2) (ctxOK_H hok H2) lW (vv lA2) (vv lA1) (vv lZ) (BitVec.ofNat 64 2) c1 c2
      (by decide) (fun _ => by simp +decide [h2, ltag]) (fun _ => by simp +decide) (fun _ => by simp +decide)
      (fun H3 ws hp3 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H3.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp3' : H2 <+: H3 := hp3
    exact ⟨_, hp1.trans (hp2.trans (hp3'.trans (img3_prefix H3 ws _ c1 c2 hws))),
      lrep_mkMax (ctxH C H2) s.store.ls H3 ws c1 c2 _ _ hws hp3 hc1' hc2 2 rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | imax u v ihu ihv =>
    intro H w hb hl
    refine substM_view C hok H w ko us _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, wv2, m1, m2, r1, r2⟩ := hk1
    unfold substRestM
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lB _ (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv2 (by decide) (by simp +decide [sev, h3])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (ConLeche.Level.subst ks vs u) >>= fun a =>
      pure (ConLeche.Level.subst ks vs v) >>= fun b => pure (ConLeche.Level.imax a b))
      (by simp [ConLeche.Level.subst]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSubstM substMParams [vv lD1, vv pKp, vv pUs] (substBodyM C) [wu, cellA C ko, Enc.idxW us]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp] <;> rfl, by simp +decide [hlb], trivial⟩ _
      (ihu H wu hb r1) (fun H1 c1 hp1 hc1 => ?_)
    refine callLv_spec (C := ctxH C H1) lZ fSubstM substMParams [vv lB, vv pKp, vv pUs] (substBodyM C) [wv2, cellA C ko, Enc.idxW us]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp] <;> rfl, by simp +decide [hlb], trivial⟩ _
      (ihv H1 wv2 (blkAt_mono hb hp1) (lrep_mono hp1 v wv2 r2)) (fun H2 c2 hp2 hc2 => ?_)
    have hc1' := lrep_mono hp2 _ c1 hc1
    refine specR_alloc3I (C := ctxH C H2) (ctxOK_H hok H2) lW (vv lA2) (vv lA1) (vv lZ) (BitVec.ofNat 64 3) c1 c2
      (by decide) (fun _ => by simp +decide [h2, ltag]) (fun _ => by simp +decide) (fun _ => by simp +decide)
      (fun H3 ws hp3 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H3.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp3' : H2 <+: H3 := hp3
    exact ⟨_, hp1.trans (hp2.trans (hp3'.trans (img3_prefix H3 ws _ c1 c2 hws))),
      lrep_mkImax (ctxH C H2) s.store.ls H3 ws c1 c2 _ _ hws hp3 hc1' hc2, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.LSub
