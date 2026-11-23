import ConPanqueque.T.Core.IotaCase3
import ConPanqueque.T.Core.IotaCerts
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `recFireLevels`' element loop: substitute and re-intern each comparand

A run of environment cells, each a level handle (`.nested`/`.levels`: `substLevelsAt`) or a name handle (`.plain`:
`substParamLevels`, the name wrapped as a `param` level block). Each is substituted at the recursor's
instantiation and re-interned (`substLHBody`, the memo-free `substLH_core`), then appended to an accumulator
block. The twin's reads (`readLevelM`, `readNameM`) move read caches only (`specR_quiet`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.T.LSub ConPanqueque.T.LEq
open ConPanqueque.V.Enc

def rgPl := ofString "rgpl"
def rgS := ofString "rgs"
def rgN := ofString "rgn"
def rgK := ofString "rgk"
def rgU := ofString "rgu"
def rgA := ofString "rga"
def rgX := ofString "rgx"
def rgB := ofString "rgb"
def rgW := ofString "rgw"
def rgH := ofString "rgh"
def rgA2 := ofString "rga2"
def rgR := ofString "rgr"
def fRg := ofString "recFireGo"

@[simp] theorem rg_rgPl_ne_rgS : rgPl ≠ rgS := by decide
@[simp] theorem rg_rgPl_ne_rgN : rgPl ≠ rgN := by decide
@[simp] theorem rg_rgPl_ne_rgK : rgPl ≠ rgK := by decide
@[simp] theorem rg_rgPl_ne_rgU : rgPl ≠ rgU := by decide
@[simp] theorem rg_rgPl_ne_rgA : rgPl ≠ rgA := by decide
@[simp] theorem rg_rgPl_ne_rgX : rgPl ≠ rgX := by decide
@[simp] theorem rg_rgPl_ne_rgB : rgPl ≠ rgB := by decide
@[simp] theorem rg_rgPl_ne_rgW : rgPl ≠ rgW := by decide
@[simp] theorem rg_rgPl_ne_rgH : rgPl ≠ rgH := by decide
@[simp] theorem rg_rgPl_ne_rgA2 : rgPl ≠ rgA2 := by decide
@[simp] theorem rg_rgPl_ne_rgR : rgPl ≠ rgR := by decide
@[simp] theorem rg_rgPl_ne_lKb : rgPl ≠ lKb := by decide
@[simp] theorem rg_rgS_ne_rgPl : rgS ≠ rgPl := by decide
@[simp] theorem rg_rgS_ne_rgN : rgS ≠ rgN := by decide
@[simp] theorem rg_rgS_ne_rgK : rgS ≠ rgK := by decide
@[simp] theorem rg_rgS_ne_rgU : rgS ≠ rgU := by decide
@[simp] theorem rg_rgS_ne_rgA : rgS ≠ rgA := by decide
@[simp] theorem rg_rgS_ne_rgX : rgS ≠ rgX := by decide
@[simp] theorem rg_rgS_ne_rgB : rgS ≠ rgB := by decide
@[simp] theorem rg_rgS_ne_rgW : rgS ≠ rgW := by decide
@[simp] theorem rg_rgS_ne_rgH : rgS ≠ rgH := by decide
@[simp] theorem rg_rgS_ne_rgA2 : rgS ≠ rgA2 := by decide
@[simp] theorem rg_rgS_ne_rgR : rgS ≠ rgR := by decide
@[simp] theorem rg_rgS_ne_lKb : rgS ≠ lKb := by decide
@[simp] theorem rg_rgN_ne_rgPl : rgN ≠ rgPl := by decide
@[simp] theorem rg_rgN_ne_rgS : rgN ≠ rgS := by decide
@[simp] theorem rg_rgN_ne_rgK : rgN ≠ rgK := by decide
@[simp] theorem rg_rgN_ne_rgU : rgN ≠ rgU := by decide
@[simp] theorem rg_rgN_ne_rgA : rgN ≠ rgA := by decide
@[simp] theorem rg_rgN_ne_rgX : rgN ≠ rgX := by decide
@[simp] theorem rg_rgN_ne_rgB : rgN ≠ rgB := by decide
@[simp] theorem rg_rgN_ne_rgW : rgN ≠ rgW := by decide
@[simp] theorem rg_rgN_ne_rgH : rgN ≠ rgH := by decide
@[simp] theorem rg_rgN_ne_rgA2 : rgN ≠ rgA2 := by decide
@[simp] theorem rg_rgN_ne_rgR : rgN ≠ rgR := by decide
@[simp] theorem rg_rgN_ne_lKb : rgN ≠ lKb := by decide
@[simp] theorem rg_rgK_ne_rgPl : rgK ≠ rgPl := by decide
@[simp] theorem rg_rgK_ne_rgS : rgK ≠ rgS := by decide
@[simp] theorem rg_rgK_ne_rgN : rgK ≠ rgN := by decide
@[simp] theorem rg_rgK_ne_rgU : rgK ≠ rgU := by decide
@[simp] theorem rg_rgK_ne_rgA : rgK ≠ rgA := by decide
@[simp] theorem rg_rgK_ne_rgX : rgK ≠ rgX := by decide
@[simp] theorem rg_rgK_ne_rgB : rgK ≠ rgB := by decide
@[simp] theorem rg_rgK_ne_rgW : rgK ≠ rgW := by decide
@[simp] theorem rg_rgK_ne_rgH : rgK ≠ rgH := by decide
@[simp] theorem rg_rgK_ne_rgA2 : rgK ≠ rgA2 := by decide
@[simp] theorem rg_rgK_ne_rgR : rgK ≠ rgR := by decide
@[simp] theorem rg_rgK_ne_lKb : rgK ≠ lKb := by decide
@[simp] theorem rg_rgU_ne_rgPl : rgU ≠ rgPl := by decide
@[simp] theorem rg_rgU_ne_rgS : rgU ≠ rgS := by decide
@[simp] theorem rg_rgU_ne_rgN : rgU ≠ rgN := by decide
@[simp] theorem rg_rgU_ne_rgK : rgU ≠ rgK := by decide
@[simp] theorem rg_rgU_ne_rgA : rgU ≠ rgA := by decide
@[simp] theorem rg_rgU_ne_rgX : rgU ≠ rgX := by decide
@[simp] theorem rg_rgU_ne_rgB : rgU ≠ rgB := by decide
@[simp] theorem rg_rgU_ne_rgW : rgU ≠ rgW := by decide
@[simp] theorem rg_rgU_ne_rgH : rgU ≠ rgH := by decide
@[simp] theorem rg_rgU_ne_rgA2 : rgU ≠ rgA2 := by decide
@[simp] theorem rg_rgU_ne_rgR : rgU ≠ rgR := by decide
@[simp] theorem rg_rgU_ne_lKb : rgU ≠ lKb := by decide
@[simp] theorem rg_rgA_ne_rgPl : rgA ≠ rgPl := by decide
@[simp] theorem rg_rgA_ne_rgS : rgA ≠ rgS := by decide
@[simp] theorem rg_rgA_ne_rgN : rgA ≠ rgN := by decide
@[simp] theorem rg_rgA_ne_rgK : rgA ≠ rgK := by decide
@[simp] theorem rg_rgA_ne_rgU : rgA ≠ rgU := by decide
@[simp] theorem rg_rgA_ne_rgX : rgA ≠ rgX := by decide
@[simp] theorem rg_rgA_ne_rgB : rgA ≠ rgB := by decide
@[simp] theorem rg_rgA_ne_rgW : rgA ≠ rgW := by decide
@[simp] theorem rg_rgA_ne_rgH : rgA ≠ rgH := by decide
@[simp] theorem rg_rgA_ne_rgA2 : rgA ≠ rgA2 := by decide
@[simp] theorem rg_rgA_ne_rgR : rgA ≠ rgR := by decide
@[simp] theorem rg_rgA_ne_lKb : rgA ≠ lKb := by decide
@[simp] theorem rg_rgX_ne_rgPl : rgX ≠ rgPl := by decide
@[simp] theorem rg_rgX_ne_rgS : rgX ≠ rgS := by decide
@[simp] theorem rg_rgX_ne_rgN : rgX ≠ rgN := by decide
@[simp] theorem rg_rgX_ne_rgK : rgX ≠ rgK := by decide
@[simp] theorem rg_rgX_ne_rgU : rgX ≠ rgU := by decide
@[simp] theorem rg_rgX_ne_rgA : rgX ≠ rgA := by decide
@[simp] theorem rg_rgX_ne_rgB : rgX ≠ rgB := by decide
@[simp] theorem rg_rgX_ne_rgW : rgX ≠ rgW := by decide
@[simp] theorem rg_rgX_ne_rgH : rgX ≠ rgH := by decide
@[simp] theorem rg_rgX_ne_rgA2 : rgX ≠ rgA2 := by decide
@[simp] theorem rg_rgX_ne_rgR : rgX ≠ rgR := by decide
@[simp] theorem rg_rgX_ne_lKb : rgX ≠ lKb := by decide
@[simp] theorem rg_rgB_ne_rgPl : rgB ≠ rgPl := by decide
@[simp] theorem rg_rgB_ne_rgS : rgB ≠ rgS := by decide
@[simp] theorem rg_rgB_ne_rgN : rgB ≠ rgN := by decide
@[simp] theorem rg_rgB_ne_rgK : rgB ≠ rgK := by decide
@[simp] theorem rg_rgB_ne_rgU : rgB ≠ rgU := by decide
@[simp] theorem rg_rgB_ne_rgA : rgB ≠ rgA := by decide
@[simp] theorem rg_rgB_ne_rgX : rgB ≠ rgX := by decide
@[simp] theorem rg_rgB_ne_rgW : rgB ≠ rgW := by decide
@[simp] theorem rg_rgB_ne_rgH : rgB ≠ rgH := by decide
@[simp] theorem rg_rgB_ne_rgA2 : rgB ≠ rgA2 := by decide
@[simp] theorem rg_rgB_ne_rgR : rgB ≠ rgR := by decide
@[simp] theorem rg_rgB_ne_lKb : rgB ≠ lKb := by decide
@[simp] theorem rg_rgW_ne_rgPl : rgW ≠ rgPl := by decide
@[simp] theorem rg_rgW_ne_rgS : rgW ≠ rgS := by decide
@[simp] theorem rg_rgW_ne_rgN : rgW ≠ rgN := by decide
@[simp] theorem rg_rgW_ne_rgK : rgW ≠ rgK := by decide
@[simp] theorem rg_rgW_ne_rgU : rgW ≠ rgU := by decide
@[simp] theorem rg_rgW_ne_rgA : rgW ≠ rgA := by decide
@[simp] theorem rg_rgW_ne_rgX : rgW ≠ rgX := by decide
@[simp] theorem rg_rgW_ne_rgB : rgW ≠ rgB := by decide
@[simp] theorem rg_rgW_ne_rgH : rgW ≠ rgH := by decide
@[simp] theorem rg_rgW_ne_rgA2 : rgW ≠ rgA2 := by decide
@[simp] theorem rg_rgW_ne_rgR : rgW ≠ rgR := by decide
@[simp] theorem rg_rgW_ne_lKb : rgW ≠ lKb := by decide
@[simp] theorem rg_rgH_ne_rgPl : rgH ≠ rgPl := by decide
@[simp] theorem rg_rgH_ne_rgS : rgH ≠ rgS := by decide
@[simp] theorem rg_rgH_ne_rgN : rgH ≠ rgN := by decide
@[simp] theorem rg_rgH_ne_rgK : rgH ≠ rgK := by decide
@[simp] theorem rg_rgH_ne_rgU : rgH ≠ rgU := by decide
@[simp] theorem rg_rgH_ne_rgA : rgH ≠ rgA := by decide
@[simp] theorem rg_rgH_ne_rgX : rgH ≠ rgX := by decide
@[simp] theorem rg_rgH_ne_rgB : rgH ≠ rgB := by decide
@[simp] theorem rg_rgH_ne_rgW : rgH ≠ rgW := by decide
@[simp] theorem rg_rgH_ne_rgA2 : rgH ≠ rgA2 := by decide
@[simp] theorem rg_rgH_ne_rgR : rgH ≠ rgR := by decide
@[simp] theorem rg_rgH_ne_lKb : rgH ≠ lKb := by decide
@[simp] theorem rg_rgA2_ne_rgPl : rgA2 ≠ rgPl := by decide
@[simp] theorem rg_rgA2_ne_rgS : rgA2 ≠ rgS := by decide
@[simp] theorem rg_rgA2_ne_rgN : rgA2 ≠ rgN := by decide
@[simp] theorem rg_rgA2_ne_rgK : rgA2 ≠ rgK := by decide
@[simp] theorem rg_rgA2_ne_rgU : rgA2 ≠ rgU := by decide
@[simp] theorem rg_rgA2_ne_rgA : rgA2 ≠ rgA := by decide
@[simp] theorem rg_rgA2_ne_rgX : rgA2 ≠ rgX := by decide
@[simp] theorem rg_rgA2_ne_rgB : rgA2 ≠ rgB := by decide
@[simp] theorem rg_rgA2_ne_rgW : rgA2 ≠ rgW := by decide
@[simp] theorem rg_rgA2_ne_rgH : rgA2 ≠ rgH := by decide
@[simp] theorem rg_rgA2_ne_rgR : rgA2 ≠ rgR := by decide
@[simp] theorem rg_rgA2_ne_lKb : rgA2 ≠ lKb := by decide
@[simp] theorem rg_rgR_ne_rgPl : rgR ≠ rgPl := by decide
@[simp] theorem rg_rgR_ne_rgS : rgR ≠ rgS := by decide
@[simp] theorem rg_rgR_ne_rgN : rgR ≠ rgN := by decide
@[simp] theorem rg_rgR_ne_rgK : rgR ≠ rgK := by decide
@[simp] theorem rg_rgR_ne_rgU : rgR ≠ rgU := by decide
@[simp] theorem rg_rgR_ne_rgA : rgR ≠ rgA := by decide
@[simp] theorem rg_rgR_ne_rgX : rgR ≠ rgX := by decide
@[simp] theorem rg_rgR_ne_rgB : rgR ≠ rgB := by decide
@[simp] theorem rg_rgR_ne_rgW : rgR ≠ rgW := by decide
@[simp] theorem rg_rgR_ne_rgH : rgR ≠ rgH := by decide
@[simp] theorem rg_rgR_ne_rgA2 : rgR ≠ rgA2 := by decide
@[simp] theorem rg_rgR_ne_lKb : rgR ≠ lKb := by decide
@[simp] theorem rg_lKb_ne_rgPl : lKb ≠ rgPl := by decide
@[simp] theorem rg_lKb_ne_rgS : lKb ≠ rgS := by decide
@[simp] theorem rg_lKb_ne_rgN : lKb ≠ rgN := by decide
@[simp] theorem rg_lKb_ne_rgK : lKb ≠ rgK := by decide
@[simp] theorem rg_lKb_ne_rgU : lKb ≠ rgU := by decide
@[simp] theorem rg_lKb_ne_rgA : lKb ≠ rgA := by decide
@[simp] theorem rg_lKb_ne_rgX : lKb ≠ rgX := by decide
@[simp] theorem rg_lKb_ne_rgB : lKb ≠ rgB := by decide
@[simp] theorem rg_lKb_ne_rgW : lKb ≠ rgW := by decide
@[simp] theorem rg_lKb_ne_rgH : lKb ≠ rgH := by decide
@[simp] theorem rg_lKb_ne_rgA2 : lKb ≠ rgA2 := by decide
@[simp] theorem rg_lKb_ne_rgR : lKb ≠ rgR := by decide

def rgParams : List MlS := [rgPl, rgS, rgN, rgK, rgU, rgA]
def rgLocals : List MlS := [rgX, rgB, rgW, rgH, rgA2, rgR]

def rgRest : ProgHOL 64 :=
  .seq (.call (some (some (.local, rgH), none)) fSubstLH [vv rgW, vv rgK, vv rgU])
  (.seq (.call (some (some (.local, rgA2), none)) ExPre.fAppend [vv rgA, vv rgH])
  (.seq (.call (some (some (.local, rgR), none)) fRg
      [vv rgPl, .op .add [vv rgS, .const 8], .op .sub [vv rgN, .const 1], vv rgK, vv rgU, vv rgA2])
    (.return (vv rgR))))

def rgCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv rgN) (.const 0)) (.return (vv rgA))
  (.seq (.assign .local rgX (.load .one (vv rgS)))
  (.ite (vv rgPl)
    (allocP C rgB (.const 16) (.seq (.store (vv rgB) (.const 4))
      (.seq (.store (.op .add [vv rgB, .const 8]) (vv rgX)) (.seq (.assign .local rgW (vv rgB)) rgRest))))
    (.seq (.assign .local rgW (vv rgX)) rgRest)))

def rgBody (C : Ctx) : ProgHOL 64 := prologue rgLocals (rgCore C)

structure RgCodes (C : Ctx) : Prop where
  sm : C.code.lookup fSubstM = some (substMParams.map (fun p => (p, ShapeHOL.one)), substBodyM C, .one)
  neq : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  go : C.code.lookup fGoM = some (goParams.map (fun p => (p, ShapeHOL.one)), goBody, .one)
  z : C.code.lookup fInternLZero = some ([], internLZeroBody, .one)
  su : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  mx : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one)
  im : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one)
  pa : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  lv : C.code.lookup fInternLv = some ([(pLa, .one)], internLvBody, .one)
  slh : C.code.lookup fSubstLH = some (substMParams.map (fun p => (p, ShapeHOL.one)), substLHBody C, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fRg = some (rgParams.map (fun p => (p, ShapeHOL.one)), rgBody C, .one)

section
variable {σ : Type}

/-- A fresh level-handle block, the heap extended, any final state. -/
def PostAL (C : Ctx) (L : Nat) (xs : List LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ L ≤ o ∧ w = cellA C o ∧ BlkAt H' o (xs.map Enc.idxW) ∧ SR (ctxH C H') s' st

theorem postAL_locals (C : Ctx) (L0 : Nat) : ∀ (a : List LIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostAL C L0 a w s' st → PostAL C L0 a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, h0, hw, hb, hsr⟩ => ⟨H', o, hp, h0, hw, hb, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem rg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rgLocals → (ctxEnv C ++ rgParams.zip vals).get x = none :=
  Knot.params_none C rgLocals rgParams vals (by decide) (by decide)

theorem rgL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RgCodes C)
    (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (L : Nat) :
    ∀ (src : List LIdx) (qs : Nat) (H : List (BitVec 64)) (acc : List LIdx) (oa : Nat) (s : AState), C.H <+: H →
      (∀ j (hj : j < src.length), C.EH[qs + j]? = some (Enc.idxW src[j])) → BlkAt H oa (acc.map Enc.idxW) →
      BlkAt H ko (khs.map Enc.idxW) → Frontend.denoteNList s.store.ns khs = some ks →
      s.store.lss.view us = some uh → denoteLList s.store.ls uh = some vs → StoreWF s.store →
      ReadLCacheOK s.caches.readLC s.store → (∀ j (hj : j < src.length), (denoteL s.store.ls src[j]).isSome = true) →
      src.length < 2 ^ 60 → L ≤ oa → L ≤ H.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (rgParams.zip [boolW false, ecell C qs, BitVec.ofNat 64 src.length, cellA C ko,
        Enc.idxW us, cellA C oa])) (rgBody C) s (substLevelsAt ks vs src >>= fun hs => pure (acc ++ hs))
        (PostAL (ctxH C H) L) := by
  intro src
  induction src with
  | nil =>
    intro qs H acc oa s hp hsrc hb hko hks hu hvs hwf hrl hden hlen hLo hLH
    refine specR_prologue (postAL_locals _ _) (rg_none _ _) ?_
    unfold rgCore
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [substLevelsAt, pure_bind, List.append_nil]
    exact specR_returnI _ (cellA C oa) (by simp +decide [Env.get, rgParams, ctxEnv] <;> rfl)
      (fun t ht => ⟨H, oa, List.prefix_refl _, hLo, rfl, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons u src ih =>
    intro qs H acc oa s hp hsrc hb hko hks hu hvs hwf hrl hden hlen hLo hLH
    have hok1 := ctxOK_H hok H
    refine specR_prologue (postAL_locals _ _) (rg_none _ _) ?_
    unfold rgCore
    have hne := ofNat_succ_ne src.length (by simp at hlen; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_envLoadI rgX (vv rgS) qs (Enc.idxW u) (by decide) (by simp +decide [Env.get, rgParams, ctxEnv]; rfl)
      (hsrc 0 (by simp) : C.EH[qs]? = _) ?_
    refine specR_ifI _ (boolW false) (by simp +decide [sev, Env.get, rgParams, ctxEnv])
      (fun h => absurd h (by decide)) (fun _ => ?_)
    refine specR_assignI rgW (vv rgX) (Enc.idxW u) (by decide) (by simp) ?_
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hden 0 (by simp))
    obtain ⟨X, hx, hX⟩ := readLevelM_runC u s l hrl hl
    simp only [substLevelsAt, bind_assoc, pure_bind]
    refine specR_quiet hx rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl ?_
    refine specR_callNIH (C := ctxH C H) rgH fSubstLH substMParams [vv rgW, vv rgK, vv rgU] (substLHBody C)
      [Enc.idxW u, cellA C ko, Enc.idxW us] (by decide) rfl (by decide) hc.slh
      ⟨by simp, by simp +decide [Env.get, rgParams, ctxEnv] <;> rfl, by simp +decide [Env.get, rgParams, ctxEnv], trivial⟩
      _ (fun h w s'' H' => w = Enc.idxW h ∧ StoreWF s''.store ∧
        (∃ ls', s'' = { ({ s with caches := { s.caches with readLC := X } } : AState) with
          store := withL s.store ls' } ∧ LGrow s.store.ls ls') ∧ Ext s.store s''.store)
      (fun h w s'' st ⟨H', hp', hw, hsr, wf, g, _, x⟩ => ⟨H', hp', ⟨hw, wf, g, x⟩, hsr⟩)
      (fun u' hu' _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu' substMParams _ rfl hlk)
        (substLH_core ra C hok hc.sm hc.neq hc.go hc.z hc.su hc.mx hc.im hc.pa hc.lv
          { s with caches := { s.caches with readLC := X } } ko khs ks us uh vs hks hu hvs hwf H hko (Enc.idxW u) l
          (lrep_arena _ _ _ u _ l hl)))
      (fun h w s2 H2 hp2 ⟨hw, wf2, ⟨ls2, es2, g2⟩, x2⟩ => ?_)
    subst hw es2
    refine ExPre.specR_callAppF (C := ctxH C H2) (ctxOK_H hok H2) hc.app rgA2 (vv rgA) (vv rgH) oa
      (acc.map Enc.idxW) (Enc.idxW h) (by decide) (blkAt_mono hb hp2)
      (by simp +decide [Env.get, rgParams, ctxEnv]; rfl) (by simp) (fun H3 o3 hp3 h03 hb3 => ?_)
    have hb3' : BlkAt H3 o3 ((acc ++ [h]).map Enc.idxW) := by simpa using hb3
    refine specR_congr (m' := (substLevelsAt ks vs src >>= fun hs => pure ((acc ++ [h]) ++ hs)) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) rgR fRg rgParams
      [vv rgPl, .op .add [vv rgS, .const 8], .op .sub [vv rgN, .const 1], vv rgK, vv rgU, vv rgA2] (rgBody C)
      [boolW false, ecell C (qs + 1), BitVec.ofNat 64 src.length, cellA C ko, Enc.idxW us, cellA C o3]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [Env.get, rgParams, ctxEnv],
        by simp +decide [sev, Env.get, rgParams, ctxEnv]; exact ecell_add8 C qs,
        by simp +decide [sev, Env.get, rgParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
        by simp +decide [Env.get, rgParams, ctxEnv] <;> rfl, by simp +decide [Env.get, rgParams, ctxEnv],
        by simp <;> rfl, trivial⟩
      (PostAL (ctxH C H3) L) (fun a w _ H4 => ∃ o4, L ≤ o4 ∧ w = cellA C o4 ∧ BlkAt H4 o4 (a.map Enc.idxW))
      (fun a w s' st ⟨H4, o4, hp4, hL4, hw, hb4, hsr⟩ => ⟨H4, hp4, ⟨o4, hL4, hw, hb4⟩, hsr⟩)
      (fun u' hu' _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu' rgParams _ rfl hlk)
        (ih (qs + 1) H3 (acc ++ [h]) o3 _ (hp.trans (hp2.trans hp3))
          (fun j hj => by have h' := hsrc (j + 1) (by simp; omega); rw [show qs + (j + 1) = qs + 1 + j by omega] at h'; simpa using h')
          hb3' (blkAt_mono hko (hp2.trans hp3))
          (by show Frontend.denoteNList ls2.ns khs = some ks; rw [g2.2]; exact hks)
          hu (denoteLList_ext x2.lss.ls uh vs hvs) wf2 (ReadLCacheOK.mono hX x2)
          (fun j hj => by
            obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp (hden (j + 1) (by simp; omega))
            simp only [List.getElem_cons_succ] at hl'
            rw [denoteL_ext hl' x2]; rfl)
          (by simp at hlen; omega) (by have e1 := hp2.length_le; simp only [ctxH] at e1 h03; omega)
          (by have e1 := hp2.length_le; have e2 := hp3.length_le; simp only [ctxH] at e1 e2; omega)))
      (fun r w s4 H4 hp4 ⟨o4, hL4, hw, hb4⟩ => ?_)
    subst hw
    exact specR_returnI _ (cellA C o4) (by simp)
      (fun t ht => ⟨H4, o4, hp2.trans (hp3.trans hp4), hL4, rfl, by simpa using hb4, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem rgP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RgCodes C)
    (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (L : Nat) :
    ∀ (src : List NIdx) (pns : List ConLeche.Name) (qs : Nat) (H : List (BitVec 64)) (acc : List LIdx) (oa : Nat)
      (s : AState), C.H <+: H →
      (∀ j (hj : j < src.length), C.EH[qs + j]? = some (Enc.idxW src[j])) → BlkAt H oa (acc.map Enc.idxW) →
      BlkAt H ko (khs.map Enc.idxW) → Frontend.denoteNList s.store.ns khs = some ks →
      s.store.lss.view us = some uh → denoteLList s.store.ls uh = some vs → StoreWF s.store →
      ReadNCacheOK s.caches.readNC s.store → Frontend.denoteNList s.store.ns src = some pns →
      src.length < 2 ^ 60 → L ≤ oa → L ≤ H.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (rgParams.zip [boolW true, ecell C qs, BitVec.ofNat 64 src.length, cellA C ko,
        Enc.idxW us, cellA C oa])) (rgBody C) s (substParamLevels ks vs src >>= fun hs => pure (acc ++ hs))
        (PostAL (ctxH C H) L) := by
  intro src
  induction src with
  | nil =>
    intro pns qs H acc oa s hp hsrc hb hko hks hu hvs hwf hrn hsn hlen hLo hLH
    refine specR_prologue (postAL_locals _ _) (rg_none _ _) ?_
    unfold rgCore
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [substParamLevels, pure_bind, List.append_nil]
    exact specR_returnI _ (cellA C oa) (by simp +decide [Env.get, rgParams, ctxEnv] <;> rfl)
      (fun t ht => ⟨H, oa, List.prefix_refl _, hLo, rfl, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons p src ih =>
    intro pns qs H acc oa s hp hsrc hb hko hks hu hvs hwf hrn hsn hlen hLo hLH
    rcases hq1 : denoteN s.store.ns p with _ | pn
    · simp [Frontend.denoteNList, hq1] at hsn
    rcases hq2 : Frontend.denoteNList s.store.ns src with _ | pns'
    · simp [Frontend.denoteNList, hq1, hq2] at hsn
    refine specR_prologue (postAL_locals _ _) (rg_none _ _) ?_
    unfold rgCore
    have hne := ofNat_succ_ne src.length (by simp at hlen; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_envLoadI rgX (vv rgS) qs (Enc.idxW p) (by decide) (by simp +decide [Env.get, rgParams, ctxEnv]; rfl)
      (hsrc 0 (by simp) : C.EH[qs]? = _) ?_
    refine specR_ifI _ (boolW true) (by simp +decide [sev, Env.get, rgParams, ctxEnv]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    obtain ⟨c1, hn1, hc1, hN1⟩ := ILP.readNameM_eq p s pn hrn hq1
    simp only [substParamLevels, bind_assoc, pure_bind]
    refine specR_quiet hn1 rfl rfl (by show MirrorEq c1 s.caches; rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl ?_
    refine specR_allocI (C := ctxH C H) rgB (.const 16) 2 (by decide) (by decide) (fun _ => rfl)
      (fun H1 ws hpa hws hroom => ?_)
    have hj1 : H1.length < (ctxH (ctxH C H) (H1 ++ ws)).H.length := by
      show H1.length < (H1 ++ ws).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv rgB) (.const 4) H1.length hj1 4 (by simp <;> rfl) rfl ?_
    have hj2 : H1.length + 1 < (ctxH (ctxH (ctxH C H) (H1 ++ ws)) ((H1 ++ ws).set H1.length 4)).H.length := by
      show H1.length + 1 < ((H1 ++ ws).set H1.length 4).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv rgB, .const 8]) (vv rgX) (H1.length + 1) hj2 (Enc.idxW p)
      (by simp +decide [sev, Env.get]; exact cellA_add8 C H1.length) (by simp +decide [Env.get]) ?_
    refine specR_assignI rgW (vv rgB) (cellA C H1.length) (by decide) (by simp +decide [Env.get] <;> rfl) ?_
    change SpecR (Inv (ctxH C (((H1 ++ ws).set H1.length 4).set (H1.length + 1) (Enc.idxW p))) _ _ _ _) _ _ _ _
    generalize hH' : ((H1 ++ ws).set H1.length 4).set (H1.length + 1) (Enc.idxW p) = H'
    have hpH : H <+: H' := by
      rw [← hH']
      exact prefix_set_ge (prefix_set_ge (hpa.trans (List.prefix_append _ _)) _ hpa.length_le _) _
        (by have := hpa.length_le; simp only [ctxH, List.length_set] at this ⊢; omega) _
    have hg4 : H'[H1.length]? = some 4 := by
      rw [← hH', List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    have hgp : H'[H1.length + 1]? = some (Enc.idxW p) := by
      rw [← hH', List.getElem?_set_self (by simp; omega)]
    have hrep : LRep C.HB H' (withC s c1).store.ls (cellA C H1.length) (.param pn) :=
      Or.inr ⟨H1.length, p, _, rfl, hg4, hgp, hq1⟩
    refine specR_callNIH (C := ctxH C H') rgH fSubstLH substMParams [vv rgW, vv rgK, vv rgU] (substLHBody C)
      [cellA C H1.length, cellA C ko, Enc.idxW us] (by decide) rfl (by decide) hc.slh
      ⟨by simp, by simp +decide [Env.get, rgParams, ctxEnv] <;> rfl, by simp +decide [Env.get, rgParams, ctxEnv], trivial⟩
      _ (fun h w s'' H'' => w = Enc.idxW h ∧ StoreWF s''.store ∧
        (∃ ls', s'' = { withC s c1 with store := withL s.store ls' } ∧ LGrow s.store.ls ls') ∧ Ext s.store s''.store)
      (fun h w s'' st ⟨H'', hp', hw, hsr, wf, g, _, x⟩ => ⟨H'', hp', ⟨hw, wf, g, x⟩, hsr⟩)
      (fun u' hu' _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu' substMParams _ rfl hlk)
        (substLH_core ra C hok hc.sm hc.neq hc.go hc.z hc.su hc.mx hc.im hc.pa hc.lv
          (withC s c1) ko khs ks us uh vs hks hu hvs hwf H' (blkAt_mono hko hpH) (cellA C H1.length) (.param pn) hrep))
      (fun h w s2 H2 hp2 ⟨hw, wf2, ⟨ls2, es2, g2⟩, x2⟩ => ?_)
    subst hw es2
    have hp2' : H <+: H2 := hpH.trans hp2
    refine ExPre.specR_callAppF (C := ctxH C H2) (ctxOK_H hok H2) hc.app rgA2 (vv rgA) (vv rgH) oa
      (acc.map Enc.idxW) (Enc.idxW h) (by decide) (blkAt_mono hb hp2')
      (by simp +decide [Env.get, rgParams, ctxEnv]; rfl) (by simp) (fun H3 o3 hp3 h03 hb3 => ?_)
    have hb3' : BlkAt H3 o3 ((acc ++ [h]).map Enc.idxW) := by simpa using hb3
    refine specR_congr (m' := (substParamLevels ks vs src >>= fun hs => pure ((acc ++ [h]) ++ hs)) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) rgR fRg rgParams
      [vv rgPl, .op .add [vv rgS, .const 8], .op .sub [vv rgN, .const 1], vv rgK, vv rgU, vv rgA2] (rgBody C)
      [boolW true, ecell C (qs + 1), BitVec.ofNat 64 src.length, cellA C ko, Enc.idxW us, cellA C o3]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [Env.get, rgParams, ctxEnv],
        by simp +decide [sev, Env.get, rgParams, ctxEnv]; exact ecell_add8 C qs,
        by simp +decide [sev, Env.get, rgParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
        by simp +decide [Env.get, rgParams, ctxEnv] <;> rfl, by simp +decide [Env.get, rgParams, ctxEnv],
        by simp <;> rfl, trivial⟩
      (PostAL (ctxH C H3) L) (fun a w _ H4 => ∃ o4, L ≤ o4 ∧ w = cellA C o4 ∧ BlkAt H4 o4 (a.map Enc.idxW))
      (fun a w s' st ⟨H4, o4, hp4, hL4, hw, hb4, hsr⟩ => ⟨H4, hp4, ⟨o4, hL4, hw, hb4⟩, hsr⟩)
      (fun u' hu' _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu' rgParams _ rfl hlk)
        (ih pns' (qs + 1) H3 (acc ++ [h]) o3 _ (hp.trans (hp2'.trans hp3))
          (fun j hj => by have h' := hsrc (j + 1) (by simp; omega); rw [show qs + (j + 1) = qs + 1 + j by omega] at h'; simpa using h')
          hb3' (blkAt_mono hko (hp2'.trans hp3))
          (by show Frontend.denoteNList ls2.ns khs = some ks; rw [g2.2]; exact hks)
          hu (denoteLList_ext x2.lss.ls uh vs hvs) wf2 (ReadNCacheOK.mono hN1 x2)
          (by show Frontend.denoteNList ls2.ns src = some pns'; rw [g2.2]; exact hq2)
          (by simp at hlen; omega) (by have e1 := hp2'.length_le; simp only [ctxH] at e1 h03; omega)
          (by have e1 := hp2'.length_le; have e2 := hp3.length_le; simp only [ctxH] at e1 e2; omega)))
      (fun r w s4 H4 hp4 ⟨o4, hL4, hw, hb4⟩ => ?_)
    subst hw
    simp [Frontend.denoteNList, hq1, hq2] at hsn
    exact specR_returnI _ (cellA C o4) (by simp)
      (fun t ht => ⟨H4, o4, hp2'.trans (hp3.trans hp4), hL4, rfl, by simpa using hb4, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
