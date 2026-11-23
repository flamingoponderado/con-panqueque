import ConPanqueque.T.Core.NzSubst
import ConPanqueque.T.LvlEqList
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `formerNeverZero`: a stored family's sort, never zero at the use's levels

The sort its stored type ends in (`formerResSort`), then the substituted never-zero walk (`nzS`); a type that
does not end in a sort answers `false`. The twin's reads (`readLevelM`, `readNamesM`, `readLevelsM`) only move
read caches, which the state relation does not see.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def fnQ := ofString "fnq"
def fnU := ofString "fnu"
def fnT := ofString "fnt"
def fnR := ofString "fnr"
def fnP := ofString "fnp"
def fnN := ofString "fnn"
def fnX := ofString "fnx"
def fFnz := ofString "formerNeverZero"

@[simp] theorem fn_fnQ_ne_fnU : fnQ ≠ fnU := by decide
@[simp] theorem fn_fnQ_ne_fnT : fnQ ≠ fnT := by decide
@[simp] theorem fn_fnQ_ne_fnR : fnQ ≠ fnR := by decide
@[simp] theorem fn_fnQ_ne_fnP : fnQ ≠ fnP := by decide
@[simp] theorem fn_fnQ_ne_fnN : fnQ ≠ fnN := by decide
@[simp] theorem fn_fnQ_ne_fnX : fnQ ≠ fnX := by decide
@[simp] theorem fn_fnQ_ne_lKb : fnQ ≠ lKb := by decide
@[simp] theorem fn_lKb_ne_fnQ : lKb ≠ fnQ := by decide
@[simp] theorem fn_fnU_ne_fnQ : fnU ≠ fnQ := by decide
@[simp] theorem fn_fnU_ne_fnT : fnU ≠ fnT := by decide
@[simp] theorem fn_fnU_ne_fnR : fnU ≠ fnR := by decide
@[simp] theorem fn_fnU_ne_fnP : fnU ≠ fnP := by decide
@[simp] theorem fn_fnU_ne_fnN : fnU ≠ fnN := by decide
@[simp] theorem fn_fnU_ne_fnX : fnU ≠ fnX := by decide
@[simp] theorem fn_fnU_ne_lKb : fnU ≠ lKb := by decide
@[simp] theorem fn_lKb_ne_fnU : lKb ≠ fnU := by decide
@[simp] theorem fn_fnT_ne_fnQ : fnT ≠ fnQ := by decide
@[simp] theorem fn_fnT_ne_fnU : fnT ≠ fnU := by decide
@[simp] theorem fn_fnT_ne_fnR : fnT ≠ fnR := by decide
@[simp] theorem fn_fnT_ne_fnP : fnT ≠ fnP := by decide
@[simp] theorem fn_fnT_ne_fnN : fnT ≠ fnN := by decide
@[simp] theorem fn_fnT_ne_fnX : fnT ≠ fnX := by decide
@[simp] theorem fn_fnT_ne_lKb : fnT ≠ lKb := by decide
@[simp] theorem fn_lKb_ne_fnT : lKb ≠ fnT := by decide
@[simp] theorem fn_fnR_ne_fnQ : fnR ≠ fnQ := by decide
@[simp] theorem fn_fnR_ne_fnU : fnR ≠ fnU := by decide
@[simp] theorem fn_fnR_ne_fnT : fnR ≠ fnT := by decide
@[simp] theorem fn_fnR_ne_fnP : fnR ≠ fnP := by decide
@[simp] theorem fn_fnR_ne_fnN : fnR ≠ fnN := by decide
@[simp] theorem fn_fnR_ne_fnX : fnR ≠ fnX := by decide
@[simp] theorem fn_fnR_ne_lKb : fnR ≠ lKb := by decide
@[simp] theorem fn_lKb_ne_fnR : lKb ≠ fnR := by decide
@[simp] theorem fn_fnP_ne_fnQ : fnP ≠ fnQ := by decide
@[simp] theorem fn_fnP_ne_fnU : fnP ≠ fnU := by decide
@[simp] theorem fn_fnP_ne_fnT : fnP ≠ fnT := by decide
@[simp] theorem fn_fnP_ne_fnR : fnP ≠ fnR := by decide
@[simp] theorem fn_fnP_ne_fnN : fnP ≠ fnN := by decide
@[simp] theorem fn_fnP_ne_fnX : fnP ≠ fnX := by decide
@[simp] theorem fn_fnP_ne_lKb : fnP ≠ lKb := by decide
@[simp] theorem fn_lKb_ne_fnP : lKb ≠ fnP := by decide
@[simp] theorem fn_fnN_ne_fnQ : fnN ≠ fnQ := by decide
@[simp] theorem fn_fnN_ne_fnU : fnN ≠ fnU := by decide
@[simp] theorem fn_fnN_ne_fnT : fnN ≠ fnT := by decide
@[simp] theorem fn_fnN_ne_fnR : fnN ≠ fnR := by decide
@[simp] theorem fn_fnN_ne_fnP : fnN ≠ fnP := by decide
@[simp] theorem fn_fnN_ne_fnX : fnN ≠ fnX := by decide
@[simp] theorem fn_fnN_ne_lKb : fnN ≠ lKb := by decide
@[simp] theorem fn_lKb_ne_fnN : lKb ≠ fnN := by decide
@[simp] theorem fn_fnX_ne_fnQ : fnX ≠ fnQ := by decide
@[simp] theorem fn_fnX_ne_fnU : fnX ≠ fnU := by decide
@[simp] theorem fn_fnX_ne_fnT : fnX ≠ fnT := by decide
@[simp] theorem fn_fnX_ne_fnR : fnX ≠ fnR := by decide
@[simp] theorem fn_fnX_ne_fnP : fnX ≠ fnP := by decide
@[simp] theorem fn_fnX_ne_fnN : fnX ≠ fnN := by decide
@[simp] theorem fn_fnX_ne_lKb : fnX ≠ lKb := by decide
@[simp] theorem fn_lKb_ne_fnX : lKb ≠ fnX := by decide

def fnParams : List MlS := [fnQ, fnU]
def fnLocals : List MlS := [fnT, fnR, fnP, fnN, fnX]

def fnBody : ProgHOL 64 := prologue fnLocals
  (.seq (.assign .local fnT (.load .one (.op .add [vv fnQ, .const 24])))
  (.seq (.call (some (some (.local, fnR), none)) fFs [vv fnT])
  (.ite (.cmp .equal (vv fnR) (.const 0)) (.return (.const 0))
  (.seq (.assign .local fnP (.load .one (.op .add [vv fnQ, .const 16])))
  (.seq (.assign .local fnN (.load .one (vv fnP)))
  (.seq (.call (some (some (.local, fnX), none)) fZs
      [.op .sub [vv fnR, .const 1], .op .add [vv fnP, .const 8], vv fnN, vv fnU])
    (.return (vv fnX))))))))

section
variable {σ : Type}
open ConRon.Bridge

theorem fn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fnLocals → (ctxEnv C ++ fnParams.zip vals).get x = none :=
  Knot.params_none C fnLocals fnParams vals (by decide) (by decide)

theorem readLevelM_runC (h : LIdx) (s : AState) (l : ConLeche.Level) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hd : denoteL s.store.ls h = some l) :
    ∃ X, readLevelM h s = .ok (l, { s with caches := { s.caches with readLC := X } }) ∧ ReadLCacheOK X s.store := by
  unfold readLevelM
  rcases hc : s.caches.readLC[h]? with _ | l'
  · refine ⟨s.caches.readLC.insert h l, ?_, ?_⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure, StateT.pure,
        Except.bind, Except.pure]
    · intro k u hk
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hrl k u hk
  · have := hrl h l' hc
    rw [hd] at this; cases this
    exact ⟨s.caches.readLC, by simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure,
      StateT.pure, Except.bind, Except.pure], hrl⟩

theorem readLevelsM_runC (h : LsIdx) (s : AState) (l : List ConLeche.Level)
    (hrl : ReadLsCacheOK s.caches.readLsC s.store) (hd : denoteLs s.store.lss h = some l) :
    ∃ X, readLevelsM h s = .ok (l, { s with caches := { s.caches with readLsC := X } }) := by
  unfold readLevelsM
  rcases hc : s.caches.readLsC[h]? with _ | l'
  · refine ⟨s.caches.readLsC.insert h l, ?_⟩
    simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure, StateT.pure,
      Except.bind, Except.pure]
  · have := hrl h l' hc
    rw [hd] at this; cases this
    exact ⟨s.caches.readLsC, by simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure,
      StateT.pure, Except.bind, Except.pure]⟩

theorem lidxW_add_one_ne (v : LIdx) : Enc.idxW v + 1 ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  have hl : (Enc.idxW v).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact v.word.toNat_lt
  simp [BitVec.toNat_add] at this; omega

theorem fn_ecell8 (C : Ctx) (o : Nat) : ecell C o + 8 = ecell C (o + 1) := by simpa using ecell_add C o 1
theorem fn_ecell16 (C : Ctx) (o : Nat) : ecell C o + 16 = ecell C (o + 2) := by simpa using ecell_add C o 2
theorem fn_ecell24 (C : Ctx) (o : Nat) : ecell C o + 24 = ecell C (o + 3) := by simpa using ecell_add C o 3

theorem am_run_bind {α β : Type} {m : AM α} {k : α → AM β} {s s1 s2 : AState} {a : α} {b : β}
    (h1 : m s = .ok (a, s1)) (h2 : k a s1 = .ok (b, s2)) : (m >>= k) s = .ok (b, s2) := by
  show (do let r ← m s; match r with | (a, s) => k a s) = _
  rw [h1]; exact h2

/-- `formerNeverZero` at a stored constant `[tag, name, levelParams, type, …]` at `o` and the use's levels `us`.
The sort's level denoting is the caller's obligation (`hsd`). -/
theorem fn_spec (C : Ctx) (hcs : C.code.lookup fFs = some ([(fsT, ShapeHOL.one)], fsBody, .one))
    (hcp : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one))
    (hcf : C.code.lookup fZs = some (zsParams.map (fun p => (p, ShapeHOL.one)), zsBody, .one))
    (hcpz : C.code.lookup fZp = some (zpParams.map (fun p => (p, ShapeHOL.one)), zpBody, .one))
    (hcn : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one))
    (hcz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)) (s : AState)
    (hwf : LStoreWF s.store.ls) (cvT : IConstantVal) (o : Nat) (hcv : CVE C.EB C.EH (o + 1) cvT)
    (ks : List ConLeche.Name) (hks : Frontend.denoteNList s.store.ns cvT.levelParams = some ks)
    (us : LsIdx) (vs : List ConLeche.Level) (hus : denoteLs s.store.lss us = some vs)
    (hrn : ReadNCacheOK s.caches.readNC s.store) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hrls : ReadLsCacheOK s.caches.readLsC s.store)
    (hsd : ∀ u, formerResSort cvT.type s = .ok (some u, s) → (denoteL s.store.ls u).isSome = true)
    (hlen : cvT.levelParams.length < 2 ^ 60) :
    SpecR (σ := σ) (Pre C s (fnParams.zip [ecell C o, Enc.idxW us])) fnBody s
      (formerNeverZero cvT us) (PostB C) := by
  obtain ⟨_, ⟨wl, hwl, o', hwl', hblk⟩, hty⟩ := hcv
  subst hwl'
  obtain ⟨hkl, hkd⟩ := LSub.denoteNList_get _ _ _ hks
  have hmir : ∀ (c : Caches), c = { s.caches with readNC := c.readNC } → ∀ X, MirrorEq { c with readLsC := X } s.caches :=
    fun c hc X => by rw [hc]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine specR_prologue (postB_locals C) (fn_none C _) ?_
  refine specR_envLoadI fnT (.op .add [vv fnQ, .const 24]) (o + 3) _ (by decide)
    (by simp +decide [sev, Env.get, fnParams, ctxEnv]; exact fn_ecell24 C o) (by simpa [Nat.add_assoc] using hty) ?_
  refine specR_congr (m' := formerResSort cvT.type >>= fun r =>
      (match r with
        | some s => readLevelM s >>= fun l => pure (ConLeche.Level.zeronessOf l)
        | none => pure (ConLeche.PropWhen.ifAllZero [])) >>= fun z =>
      readNamesM cvT.levelParams >>= fun ks => readLevelsM us >>= fun vs =>
        pure (ConLeche.Level.substPW ks vs z).isNever)
    (by simp only [formerNeverZero, formerZ, bind_assoc] <;> rfl) ?_
  refine specR_callNIH fnR fFs [fsT] [vv fnT] fsBody [Enc.idxW cvT.type] (by decide) rfl (by decide) hcs
    ⟨by simp +decide [sev, Env.get], trivial⟩
    (fun a w s' st => formerResSort cvT.type s = .ok (a, s') ∧ PostOL C s a w s' st)
    (fun a w s' _ => formerResSort cvT.type s = .ok (a, s') ∧ s' = s ∧ w = optWG Enc.idxW a)
    (fun a w s' st ⟨hrun, h1, h2, H', hp, h3⟩ => ⟨H', hp, ⟨hrun, h1, h2⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [fsT] _ rfl hlk) (fs_spec C hcp s cvT.type)))
    (fun r w s1 H1 hp1 ⟨hrun, hs1, hw⟩ => ?_)
  subst s1 hw
  rcases r with _ | u
  · obtain ⟨c1, hn1, hc1, _⟩ := ILP.readNamesM_eq cvT.levelParams s ks hrn hks
    obtain ⟨X, hx⟩ := readLevelsM_runC us (withC s c1) vs (by show ReadLsCacheOK c1.readLsC s.store; rw [hc1]; exact hrls) hus
    refine LLeq.specR_ofRun (R' := PostB C) (am_run_bind rfl (am_run_bind hn1 (am_run_bind hx rfl))) ?_
      (fun w st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, LLeq.sr_congrS hsr rfl rfl (hmir c1 hc1 X) rfl⟩)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hsd u hrun)
    obtain ⟨X1, hx1, _⟩ := readLevelM_runC u s l hrl hl
    obtain ⟨c1, hn1, hc1, _⟩ := ILP.readNamesM_eq cvT.levelParams
      { s with caches := { s.caches with readLC := X1 } } ks hrn hks
    obtain ⟨X, hx⟩ := readLevelsM_runC us (withC { s with caches := { s.caches with readLC := X1 } } c1) vs
      (by show ReadLsCacheOK c1.readLsC s.store; rw [hc1]; exact hrls) hus
    have hmir2 : MirrorEq { c1 with readLsC := X } s.caches := by rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine LLeq.specR_ofRun (R' := PostB C) (am_run_bind (am_run_bind hx1 rfl) (am_run_bind hn1 (am_run_bind hx rfl))) ?_
      (fun w st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, LLeq.sr_congrS hsr rfl rfl hmir2 rfl⟩)
    have hne : ¬ Enc.idxW u + 1 = 0 := lidxW_add_one_ne u
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_envLoadI (C := ctxH C H1) fnP (.op .add [vv fnQ, .const 16]) (o + 2) _ (by decide)
      (by simp +decide [sev, Env.get, fnParams, ctxEnv]; exact fn_ecell16 C o) (by simpa [Nat.add_assoc] using hwl : C.EH[o + 2]? = _) ?_
    refine specR_envLoadI (C := ctxH C H1) fnN (vv fnP) o' (BitVec.ofNat 64 cvT.levelParams.length) (by decide)
      (by simp +decide [Env.get]; rfl) (by simpa using hblk.1 : C.EH[o']? = _) ?_
    rw [substPW_isNever]
    rcases hv : s.store.lss.view us with _ | uh
    · simp [denoteLs, hv] at hus
    simp only [denoteLs, hv] at hus
    obtain ⟨hvl, hvd⟩ := LLeq.denoteLList_get _ _ _ hus
    refine specR_bindPure ?_
    refine specR_callNIH (C := ctxH C H1) fnX fZs zsParams
      [.op .sub [vv fnR, .const 1], .op .add [vv fnP, .const 8], vv fnN, vv fnU] zsBody
      [Enc.idxW u, ecell C (o' + 1), BitVec.ofNat 64 cvT.levelParams.length, Enc.idxW us] (by decide) rfl (by decide) hcf
      ⟨by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _, by simp +decide [sev, Env.get]; exact fn_ecell8 C o',
        by simp +decide [sev, Env.get], by simp +decide [sev, Env.get, fnParams, ctxEnv], trivial⟩
      (PostBS (ctxH C H1) s) (fun a w s' _ => s' = s ∧ w = boolW a)
      (fun a w s' st ⟨h1, h2, h3⟩ => ⟨H1, List.prefix_refl _, ⟨h1, h2⟩, by subst h1; exact h3⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu zsParams _ rfl hlk)
        (zs_spec (ctxH C H1) hcf hcpz hcn hcz s hwf cvT.levelParams ks (o' + 1)
          (fun j hj => by have h := hblk.2 j (by simpa using hj); rw [List.getElem_map] at h; exact h) hkl
          (fun j hj => ⟨_, hkd j hj⟩) hlen us uh vs hv hvl hvd l u hl))
      (fun b w s3 H3 hp3 ⟨hs3, hw⟩ => ?_)
    subst hs3 hw
    exact specR_returnI _ (boolW b) (by simp [Env.get]) (fun t ht => ⟨H3, hp1.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
