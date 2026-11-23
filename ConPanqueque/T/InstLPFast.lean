import ConPanqueque.T.InstLP
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `instLPFast`: the top-level entry of `instantiateLevelParams`

The `hasLP` cutoff, then the walk between two clears of its memo. The twin reads the names and levels
back first (through its readback caches) and clears all three per-call memos; the port mirrors only the
expression memo, and the other two are cleared on the twin side alone.
-/

namespace ConPanqueque.T.ILP
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM
open ConPanqueque.T.LEq ConPanqueque.T.LSub ConPanqueque.T.ExG ConPanqueque.T.LLeq ConPanqueque.T.ExA

theorem readNameM_eq (u : NIdx) (s : AState) (x : ConLeche.Name) (hrl : ReadNCacheOK s.caches.readNC s.store)
    (hd : denoteN s.store.ns u = some x) :
    ∃ c1 : Caches, readNameM u s = .ok (x, withC s c1) ∧ c1 = { s.caches with readNC := c1.readNC } ∧
      ReadNCacheOK c1.readNC s.store := by
  unfold readNameM
  rcases hc : s.caches.readNC[u]? with _ | x'
  · refine ⟨{ s.caches with readNC := s.caches.readNC.insert u x }, ?_, rfl, ?_⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure,
        StateT.pure, Except.bind, Except.pure, withC]
    · intro k v hk
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hrl k v hk
  · have := hrl u x' hc
    rw [hd] at this; cases this
    refine ⟨s.caches, ?_, rfl, hrl⟩
    simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, withC]

theorem readNamesM_eq : ∀ (us : List NIdx) (s : AState) (xs : List ConLeche.Name),
    ReadNCacheOK s.caches.readNC s.store → Frontend.denoteNList s.store.ns us = some xs →
    ∃ c1 : Caches, readNamesM us s = .ok (xs, withC s c1) ∧ c1 = { s.caches with readNC := c1.readNC } ∧
      ReadNCacheOK c1.readNC s.store
  | [], s, xs, hrl, hd => by
    simp [Frontend.denoteNList] at hd; subst hd
    exact ⟨s.caches, rfl, rfl, hrl⟩
  | u :: us, s, xs, hrl, hd => by
    simp only [Frontend.denoteNList] at hd
    split at hd
    · rename_i a b ha hb
      simp at hd; subst hd
      obtain ⟨c1, e1, ec1, ok1⟩ := readNameM_eq u s a hrl ha
      obtain ⟨c2, e2, ec2, ok2⟩ := readNamesM_eq us (withC s c1) b ok1 hb
      refine ⟨c2, ?_, ?_, ok2⟩
      · simp only [readNamesM, bind, StateT.bind, Except.bind]
        rw [e1]; simp only; rw [e2]; rfl
      · rw [ec2]; simp only [withC]; rw [ec1]
    · simp at hd

section
variable {σ : Type}

/-- `specR_memoClearI` for a twin clear that may also touch tables the port does not mirror. -/
theorem specR_memoClearIG {β : Type} {C : Ctx} (hok : CtxOK C) (mk : MemoK) (clearOp : AM Unit)
    {s s' : AState} (hclear : clearOp s = .ok ((), s')) (hst : s'.store = s.store)
    (hoE : ∀ k, k ≠ mk → memoSel k s'.memos = memoSel k s.memos)
    (hoN : ∀ k, memoSelN k s'.memos = memoSelN k s.memos) (hsame : memoSel mk s'.memos = ∅)
    (hoC : MirrorEq s'.caches s.caches)
    {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {k : Unit → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (hj : lJ0 ∈ D)
    (hk : SpecR (Inv C s' (Γ.kill [lJ0]) [] D) rest s' (k ()) R) :
    SpecR (Inv C s Γ M D) (clearCode (C.mg (.e mk)) rest) s (clearOp >>= k) R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl lJ0 hj
  rcases clearCode_core t _ _ _ (ht.sr.memo mk) rest w0 hw0 (fun j hj' => hok.mdescMemo (.e mk) (.e mk) j hj') with
    hs | ⟨t4, he, hmem, hout, hd4, hg4, hc4, hl4, hj4⟩
  · exact Or.inl hs
  have hsr' : SR C s' t4 :=
    sr_upd_region hok (.e mk) ht.sr hout hd4 hg4 hc4 hst
      (fun k' e => hoE k' (fun x => e (by rw [x])))
      (fun k' _ => hoN k')
      (fun k' e => by injection e with e; subst e; rw [hsame]; exact hmem)
      (fun k' e => by simp at e)
      (fun _ _ => hoC) (fun _ e => by simp at e) (fun _ _ => by simp) (fun _ => by simp) hoC
  rw [he]
  rcases hk t4 (inv_after_clear ht hsr' hl4 hj4) with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← clearOp s; match r with | (a, s) => k a s) = _
  rw [hclear]; exact hk'

end

def fInstLPF := ofString "instLPFast"
def ilpfLocals : List MlS := inst1Locals ++ [lJ0]

def ilpfBody (C : Ctx) : ProgHOL 64 :=
  prologue ilpfLocals
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
  (.ite (.cmp .equal (.op .and [vv lDo1, .const 1]) (.const 0)) (.return (vv pH))
  (clearCode (C.mg (.e .instLP))
    (.seq (.call (some (some (.local, lW), none)) fInstLP [vv pFu, vv pH, vv pKp, vv pUs])
      (clearCode (C.mg (.e .instLP)) (.return (vv lW)))))))))

/-- The three per-call memos of `instantiateLevelParams`, cleared. -/
def clr3 (s : AState) : AState := { s with memos := { s.memos with instLPC := ∅, instLPLC := ∅, instLPLsC := ∅ } }

theorem instLPClear_run (s : AState) : instLPClear s = .ok ((), clr3 s) := rfl

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem params_noneILPF (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ ilpfLocals → (ctxEnv C ++ ilpParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ ilpParams := by
    simp only [ilpfLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [ilpfLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
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

theorem ilpf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesILP C (ilpBody C))
    (fuel : Nat) (hf : fuel < 2 ^ 64) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (H : List (BitVec 64)) (s : AState) (h : EIdx)
    (hks : Frontend.denoteNList s.store.ns khs = some ks) (hus : denoteLs s.store.lss usH = some vsL)
    (hst : StateOK s) (hcn : ReadNCacheOK s.caches.readNC s.store) (hcl : ReadLCacheOK s.caches.readLC s.store)
    (hcls : ReadLsCacheOK s.caches.readLsC s.store) (hden : (denoteE s.store h).isSome = true)
    (hb : BlkAt H ko (khs.map Enc.idxW)) :
    SpecR (Pre (σ := σ) (ctxH C H) s (ilpParams.zip [BitVec.ofNat 64 fuel, Enc.idxW h, cellA C ko, Enc.idxW usH]))
      (ilpfBody C) s (instLPFast fuel khs usH h) (PostILP (ctxH C H)) := by
  refine specR_prologue (postILP_locals _) (params_noneILPF _ _) ?_
  unfold instLPFast
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv, ilpParams]) ?_
  refine specR_derivedEI h (by simp +decide) (by simp +decide <;> rfl) (by simp +decide [ctxEnv] <;> rfl)
    ⟨by decide, by decide, by decide, by decide, by decide⟩ ?_
  by_cases hlp : ConLeche.lpOfData (s.store.derived h) = false
  · refine specR_ifI _ 1 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact (lp_bit _).mpr hlp) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    simp only [hlp, Bool.not_false, ite_true]
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv, ilpParams])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hlp' : ConLeche.lpOfData (s.store.derived h) = true := by simpa using hlp
  have hne : (s.store.derived h).toBitVec &&& 1 ≠ 0 := fun e => hlp ((lp_bit _).mp e)
  refine specR_ifI _ 0 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun hw => absurd rfl hw) (fun _ => ?_)
  simp only [hlp', Bool.not_true, Bool.false_eq_true, ite_false]
  obtain ⟨c1, e1, ec1, ok1⟩ := readNamesM_eq khs s ks hcn hks
  obtain ⟨c2, e2, ec2, ok2⟩ := readLevelsM_eq usH (withC s c1) vsL (by rw [ec1]; exact hcls) hus
  generalize hs3 : clr3 (withC (withC s c1) c2) = s3
  have hrun : (readNamesM khs >>= fun _ => readLevelsM usH >>= fun _ => instLPClear) s = .ok ((), s3) := by
    rw [← hs3]; simp only [bind, StateT.bind, Except.bind]; rw [e1]; simp only; rw [e2]; rfl
  refine specR_congr (m' := (readNamesM khs >>= fun _ => readLevelsM usH >>= fun _ => instLPClear) >>= fun _ =>
      (do let r ← instLPGo ks vsL fuel h; instLPClear; pure r))
    (by simp only [bind, StateT.bind, Except.bind]; rw [e1]; simp only; rw [e2]) ?_
  have hst3 : s3.store = s.store := by rw [← hs3]; rfl
  refine specR_memoClearIG (C := ctxH C H) (ctxOK_H hok H) .instLP _ hrun hst3
    (fun k hk => by rw [← hs3]; cases k <;> first | rfl | exact absurd rfl hk) (fun k => by rw [← hs3]; cases k <;> rfl)
    (by rw [← hs3]; rfl)
    (by rw [← hs3]; show MirrorEq c2 s.caches; rw [ec2]; simp only [withC]; rw [ec1]; exact mirrorEq_refl _)
    (by decide) ?_
  have hp3 : PInv s3 khs ks usH vsL := by
    rw [← hs3]
    exact ⟨⟨hst.wf⟩, fun k r hk => by simp [clr3] at hk, fun k r hk => by simp [clr3] at hk, fun k r hk => by simp [clr3] at hk,
      by simp only [withC]; rw [ec2]; simp only [withC]; rw [ec1]; exact hcl, ok2, hks, hus⟩
  have hden3 : (denoteE s3.store h).isSome = true := by rw [hst3]; exact hden
  refine specR_callNIH lW fInstLP ilpParams [vv pFu, vv pH, vv pKp, vv pUs] (ilpBody C)
    [BitVec.ofNat 64 fuel, Enc.idxW h, cellA C ko, Enc.idxW usH] (by decide) rfl (by decide) hc.ilp
    ⟨by simp +decide [Env.kill, ctxEnv, ilpParams], by simp +decide [Env.kill, ctxEnv, ilpParams],
      by simp +decide [Env.kill, ctxEnv, ilpParams] <;> rfl, by simp +decide [Env.kill, ctxEnv, ilpParams], trivial⟩
    (PostILP (ctxH C H)) (fun a w s' _ => w = Enc.idxW a)
    (fun a w s' st ⟨H', hpH, hw, hsr⟩ => ⟨H', hpH, hw, hsr⟩)
    (fun u hu _ hlk => fun w hw => by
      subst hw
      exact ilp_spec ra C hok hc ko khs ks usH vsL fuel hf H s3 h hp3 hden3 hb _
        (pre_of_lookups hu ilpParams _ rfl hlk))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  refine specR_memoClearIG (C := ctxH C H4) (ctxOK_H hok H4) .instLP instLPClear (instLPClear_run s4) rfl
    (fun k hk => by cases k <;> first | rfl | exact absurd rfl hk) (fun k => by cases k <;> rfl) rfl (mirrorEq_refl _) (by decide) ?_
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [Env.kill])
    (fun t ht => ⟨H4, hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ILP
