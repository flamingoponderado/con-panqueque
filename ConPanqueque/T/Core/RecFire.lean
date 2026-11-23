import ConPanqueque.T.Core.IotaCase3
import ConPanqueque.T.Core.IotaCerts
import ConPanqueque.T.LsView
import ConPanqueque.T.SRFacts
import ConPanqueque.T.PinRead
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
open ConPanqueque.T.CV (prefix_fillI blk_of_fillI mul8_eq)

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
    refine specR_quiet hx rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl (fun hc => cachesOK_readLC hc X hX) ?_
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
    refine specR_quiet hn1 rfl rfl (by show MirrorEq c1 s.caches; rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl (fun hc => cachesOK_caches hc c1 hc1 hN1) ?_
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


def rfR := ofString "rfr"
def rfKs := ofString "rfks"
def rfU := ofString "rfu"
def rfJs := ofString "rfjs"
def rfKl := ofString "rfkl"
def rfKb := ofString "rfkb"
def rfA := ofString "rfa"
def rfT := ofString "rft"
def rfS := ofString "rfs"
def rfN := ofString "rfn"
def rfB := ofString "rfb"
def rfL := ofString "rfl"
def rfZ := ofString "rfz"
def fRf := ofString "recFireLevels"

@[simp] theorem rf_rfR_ne_rfKs : rfR ≠ rfKs := by decide
@[simp] theorem rf_rfR_ne_rfU : rfR ≠ rfU := by decide
@[simp] theorem rf_rfR_ne_rfJs : rfR ≠ rfJs := by decide
@[simp] theorem rf_rfR_ne_rfKl : rfR ≠ rfKl := by decide
@[simp] theorem rf_rfR_ne_rfKb : rfR ≠ rfKb := by decide
@[simp] theorem rf_rfR_ne_rfA : rfR ≠ rfA := by decide
@[simp] theorem rf_rfR_ne_rfT : rfR ≠ rfT := by decide
@[simp] theorem rf_rfR_ne_rfS : rfR ≠ rfS := by decide
@[simp] theorem rf_rfR_ne_rfN : rfR ≠ rfN := by decide
@[simp] theorem rf_rfR_ne_rfB : rfR ≠ rfB := by decide
@[simp] theorem rf_rfR_ne_rfL : rfR ≠ rfL := by decide
@[simp] theorem rf_rfR_ne_rfZ : rfR ≠ rfZ := by decide
@[simp] theorem rf_rfR_ne_lKb : rfR ≠ lKb := by decide
@[simp] theorem rf_rfR_ne_lCn : rfR ≠ lCn := by decide
@[simp] theorem rf_rfR_ne_lSrc : rfR ≠ lSrc := by decide
@[simp] theorem rf_rfR_ne_lDst : rfR ≠ lDst := by decide
@[simp] theorem rf_rfR_ne_lCi : rfR ≠ lCi := by decide
@[simp] theorem rf_rfR_ne_lCz : rfR ≠ lCz := by decide
@[simp] theorem rf_rfKs_ne_rfR : rfKs ≠ rfR := by decide
@[simp] theorem rf_rfKs_ne_rfU : rfKs ≠ rfU := by decide
@[simp] theorem rf_rfKs_ne_rfJs : rfKs ≠ rfJs := by decide
@[simp] theorem rf_rfKs_ne_rfKl : rfKs ≠ rfKl := by decide
@[simp] theorem rf_rfKs_ne_rfKb : rfKs ≠ rfKb := by decide
@[simp] theorem rf_rfKs_ne_rfA : rfKs ≠ rfA := by decide
@[simp] theorem rf_rfKs_ne_rfT : rfKs ≠ rfT := by decide
@[simp] theorem rf_rfKs_ne_rfS : rfKs ≠ rfS := by decide
@[simp] theorem rf_rfKs_ne_rfN : rfKs ≠ rfN := by decide
@[simp] theorem rf_rfKs_ne_rfB : rfKs ≠ rfB := by decide
@[simp] theorem rf_rfKs_ne_rfL : rfKs ≠ rfL := by decide
@[simp] theorem rf_rfKs_ne_rfZ : rfKs ≠ rfZ := by decide
@[simp] theorem rf_rfKs_ne_lKb : rfKs ≠ lKb := by decide
@[simp] theorem rf_rfKs_ne_lCn : rfKs ≠ lCn := by decide
@[simp] theorem rf_rfKs_ne_lSrc : rfKs ≠ lSrc := by decide
@[simp] theorem rf_rfKs_ne_lDst : rfKs ≠ lDst := by decide
@[simp] theorem rf_rfKs_ne_lCi : rfKs ≠ lCi := by decide
@[simp] theorem rf_rfKs_ne_lCz : rfKs ≠ lCz := by decide
@[simp] theorem rf_rfU_ne_rfR : rfU ≠ rfR := by decide
@[simp] theorem rf_rfU_ne_rfKs : rfU ≠ rfKs := by decide
@[simp] theorem rf_rfU_ne_rfJs : rfU ≠ rfJs := by decide
@[simp] theorem rf_rfU_ne_rfKl : rfU ≠ rfKl := by decide
@[simp] theorem rf_rfU_ne_rfKb : rfU ≠ rfKb := by decide
@[simp] theorem rf_rfU_ne_rfA : rfU ≠ rfA := by decide
@[simp] theorem rf_rfU_ne_rfT : rfU ≠ rfT := by decide
@[simp] theorem rf_rfU_ne_rfS : rfU ≠ rfS := by decide
@[simp] theorem rf_rfU_ne_rfN : rfU ≠ rfN := by decide
@[simp] theorem rf_rfU_ne_rfB : rfU ≠ rfB := by decide
@[simp] theorem rf_rfU_ne_rfL : rfU ≠ rfL := by decide
@[simp] theorem rf_rfU_ne_rfZ : rfU ≠ rfZ := by decide
@[simp] theorem rf_rfU_ne_lKb : rfU ≠ lKb := by decide
@[simp] theorem rf_rfU_ne_lCn : rfU ≠ lCn := by decide
@[simp] theorem rf_rfU_ne_lSrc : rfU ≠ lSrc := by decide
@[simp] theorem rf_rfU_ne_lDst : rfU ≠ lDst := by decide
@[simp] theorem rf_rfU_ne_lCi : rfU ≠ lCi := by decide
@[simp] theorem rf_rfU_ne_lCz : rfU ≠ lCz := by decide
@[simp] theorem rf_rfJs_ne_rfR : rfJs ≠ rfR := by decide
@[simp] theorem rf_rfJs_ne_rfKs : rfJs ≠ rfKs := by decide
@[simp] theorem rf_rfJs_ne_rfU : rfJs ≠ rfU := by decide
@[simp] theorem rf_rfJs_ne_rfKl : rfJs ≠ rfKl := by decide
@[simp] theorem rf_rfJs_ne_rfKb : rfJs ≠ rfKb := by decide
@[simp] theorem rf_rfJs_ne_rfA : rfJs ≠ rfA := by decide
@[simp] theorem rf_rfJs_ne_rfT : rfJs ≠ rfT := by decide
@[simp] theorem rf_rfJs_ne_rfS : rfJs ≠ rfS := by decide
@[simp] theorem rf_rfJs_ne_rfN : rfJs ≠ rfN := by decide
@[simp] theorem rf_rfJs_ne_rfB : rfJs ≠ rfB := by decide
@[simp] theorem rf_rfJs_ne_rfL : rfJs ≠ rfL := by decide
@[simp] theorem rf_rfJs_ne_rfZ : rfJs ≠ rfZ := by decide
@[simp] theorem rf_rfJs_ne_lKb : rfJs ≠ lKb := by decide
@[simp] theorem rf_rfJs_ne_lCn : rfJs ≠ lCn := by decide
@[simp] theorem rf_rfJs_ne_lSrc : rfJs ≠ lSrc := by decide
@[simp] theorem rf_rfJs_ne_lDst : rfJs ≠ lDst := by decide
@[simp] theorem rf_rfJs_ne_lCi : rfJs ≠ lCi := by decide
@[simp] theorem rf_rfJs_ne_lCz : rfJs ≠ lCz := by decide
@[simp] theorem rf_rfKl_ne_rfR : rfKl ≠ rfR := by decide
@[simp] theorem rf_rfKl_ne_rfKs : rfKl ≠ rfKs := by decide
@[simp] theorem rf_rfKl_ne_rfU : rfKl ≠ rfU := by decide
@[simp] theorem rf_rfKl_ne_rfJs : rfKl ≠ rfJs := by decide
@[simp] theorem rf_rfKl_ne_rfKb : rfKl ≠ rfKb := by decide
@[simp] theorem rf_rfKl_ne_rfA : rfKl ≠ rfA := by decide
@[simp] theorem rf_rfKl_ne_rfT : rfKl ≠ rfT := by decide
@[simp] theorem rf_rfKl_ne_rfS : rfKl ≠ rfS := by decide
@[simp] theorem rf_rfKl_ne_rfN : rfKl ≠ rfN := by decide
@[simp] theorem rf_rfKl_ne_rfB : rfKl ≠ rfB := by decide
@[simp] theorem rf_rfKl_ne_rfL : rfKl ≠ rfL := by decide
@[simp] theorem rf_rfKl_ne_rfZ : rfKl ≠ rfZ := by decide
@[simp] theorem rf_rfKl_ne_lKb : rfKl ≠ lKb := by decide
@[simp] theorem rf_rfKl_ne_lCn : rfKl ≠ lCn := by decide
@[simp] theorem rf_rfKl_ne_lSrc : rfKl ≠ lSrc := by decide
@[simp] theorem rf_rfKl_ne_lDst : rfKl ≠ lDst := by decide
@[simp] theorem rf_rfKl_ne_lCi : rfKl ≠ lCi := by decide
@[simp] theorem rf_rfKl_ne_lCz : rfKl ≠ lCz := by decide
@[simp] theorem rf_rfKb_ne_rfR : rfKb ≠ rfR := by decide
@[simp] theorem rf_rfKb_ne_rfKs : rfKb ≠ rfKs := by decide
@[simp] theorem rf_rfKb_ne_rfU : rfKb ≠ rfU := by decide
@[simp] theorem rf_rfKb_ne_rfJs : rfKb ≠ rfJs := by decide
@[simp] theorem rf_rfKb_ne_rfKl : rfKb ≠ rfKl := by decide
@[simp] theorem rf_rfKb_ne_rfA : rfKb ≠ rfA := by decide
@[simp] theorem rf_rfKb_ne_rfT : rfKb ≠ rfT := by decide
@[simp] theorem rf_rfKb_ne_rfS : rfKb ≠ rfS := by decide
@[simp] theorem rf_rfKb_ne_rfN : rfKb ≠ rfN := by decide
@[simp] theorem rf_rfKb_ne_rfB : rfKb ≠ rfB := by decide
@[simp] theorem rf_rfKb_ne_rfL : rfKb ≠ rfL := by decide
@[simp] theorem rf_rfKb_ne_rfZ : rfKb ≠ rfZ := by decide
@[simp] theorem rf_rfKb_ne_lKb : rfKb ≠ lKb := by decide
@[simp] theorem rf_rfKb_ne_lCn : rfKb ≠ lCn := by decide
@[simp] theorem rf_rfKb_ne_lSrc : rfKb ≠ lSrc := by decide
@[simp] theorem rf_rfKb_ne_lDst : rfKb ≠ lDst := by decide
@[simp] theorem rf_rfKb_ne_lCi : rfKb ≠ lCi := by decide
@[simp] theorem rf_rfKb_ne_lCz : rfKb ≠ lCz := by decide
@[simp] theorem rf_rfA_ne_rfR : rfA ≠ rfR := by decide
@[simp] theorem rf_rfA_ne_rfKs : rfA ≠ rfKs := by decide
@[simp] theorem rf_rfA_ne_rfU : rfA ≠ rfU := by decide
@[simp] theorem rf_rfA_ne_rfJs : rfA ≠ rfJs := by decide
@[simp] theorem rf_rfA_ne_rfKl : rfA ≠ rfKl := by decide
@[simp] theorem rf_rfA_ne_rfKb : rfA ≠ rfKb := by decide
@[simp] theorem rf_rfA_ne_rfT : rfA ≠ rfT := by decide
@[simp] theorem rf_rfA_ne_rfS : rfA ≠ rfS := by decide
@[simp] theorem rf_rfA_ne_rfN : rfA ≠ rfN := by decide
@[simp] theorem rf_rfA_ne_rfB : rfA ≠ rfB := by decide
@[simp] theorem rf_rfA_ne_rfL : rfA ≠ rfL := by decide
@[simp] theorem rf_rfA_ne_rfZ : rfA ≠ rfZ := by decide
@[simp] theorem rf_rfA_ne_lKb : rfA ≠ lKb := by decide
@[simp] theorem rf_rfA_ne_lCn : rfA ≠ lCn := by decide
@[simp] theorem rf_rfA_ne_lSrc : rfA ≠ lSrc := by decide
@[simp] theorem rf_rfA_ne_lDst : rfA ≠ lDst := by decide
@[simp] theorem rf_rfA_ne_lCi : rfA ≠ lCi := by decide
@[simp] theorem rf_rfA_ne_lCz : rfA ≠ lCz := by decide
@[simp] theorem rf_rfT_ne_rfR : rfT ≠ rfR := by decide
@[simp] theorem rf_rfT_ne_rfKs : rfT ≠ rfKs := by decide
@[simp] theorem rf_rfT_ne_rfU : rfT ≠ rfU := by decide
@[simp] theorem rf_rfT_ne_rfJs : rfT ≠ rfJs := by decide
@[simp] theorem rf_rfT_ne_rfKl : rfT ≠ rfKl := by decide
@[simp] theorem rf_rfT_ne_rfKb : rfT ≠ rfKb := by decide
@[simp] theorem rf_rfT_ne_rfA : rfT ≠ rfA := by decide
@[simp] theorem rf_rfT_ne_rfS : rfT ≠ rfS := by decide
@[simp] theorem rf_rfT_ne_rfN : rfT ≠ rfN := by decide
@[simp] theorem rf_rfT_ne_rfB : rfT ≠ rfB := by decide
@[simp] theorem rf_rfT_ne_rfL : rfT ≠ rfL := by decide
@[simp] theorem rf_rfT_ne_rfZ : rfT ≠ rfZ := by decide
@[simp] theorem rf_rfT_ne_lKb : rfT ≠ lKb := by decide
@[simp] theorem rf_rfT_ne_lCn : rfT ≠ lCn := by decide
@[simp] theorem rf_rfT_ne_lSrc : rfT ≠ lSrc := by decide
@[simp] theorem rf_rfT_ne_lDst : rfT ≠ lDst := by decide
@[simp] theorem rf_rfT_ne_lCi : rfT ≠ lCi := by decide
@[simp] theorem rf_rfT_ne_lCz : rfT ≠ lCz := by decide
@[simp] theorem rf_rfS_ne_rfR : rfS ≠ rfR := by decide
@[simp] theorem rf_rfS_ne_rfKs : rfS ≠ rfKs := by decide
@[simp] theorem rf_rfS_ne_rfU : rfS ≠ rfU := by decide
@[simp] theorem rf_rfS_ne_rfJs : rfS ≠ rfJs := by decide
@[simp] theorem rf_rfS_ne_rfKl : rfS ≠ rfKl := by decide
@[simp] theorem rf_rfS_ne_rfKb : rfS ≠ rfKb := by decide
@[simp] theorem rf_rfS_ne_rfA : rfS ≠ rfA := by decide
@[simp] theorem rf_rfS_ne_rfT : rfS ≠ rfT := by decide
@[simp] theorem rf_rfS_ne_rfN : rfS ≠ rfN := by decide
@[simp] theorem rf_rfS_ne_rfB : rfS ≠ rfB := by decide
@[simp] theorem rf_rfS_ne_rfL : rfS ≠ rfL := by decide
@[simp] theorem rf_rfS_ne_rfZ : rfS ≠ rfZ := by decide
@[simp] theorem rf_rfS_ne_lKb : rfS ≠ lKb := by decide
@[simp] theorem rf_rfS_ne_lCn : rfS ≠ lCn := by decide
@[simp] theorem rf_rfS_ne_lSrc : rfS ≠ lSrc := by decide
@[simp] theorem rf_rfS_ne_lDst : rfS ≠ lDst := by decide
@[simp] theorem rf_rfS_ne_lCi : rfS ≠ lCi := by decide
@[simp] theorem rf_rfS_ne_lCz : rfS ≠ lCz := by decide
@[simp] theorem rf_rfN_ne_rfR : rfN ≠ rfR := by decide
@[simp] theorem rf_rfN_ne_rfKs : rfN ≠ rfKs := by decide
@[simp] theorem rf_rfN_ne_rfU : rfN ≠ rfU := by decide
@[simp] theorem rf_rfN_ne_rfJs : rfN ≠ rfJs := by decide
@[simp] theorem rf_rfN_ne_rfKl : rfN ≠ rfKl := by decide
@[simp] theorem rf_rfN_ne_rfKb : rfN ≠ rfKb := by decide
@[simp] theorem rf_rfN_ne_rfA : rfN ≠ rfA := by decide
@[simp] theorem rf_rfN_ne_rfT : rfN ≠ rfT := by decide
@[simp] theorem rf_rfN_ne_rfS : rfN ≠ rfS := by decide
@[simp] theorem rf_rfN_ne_rfB : rfN ≠ rfB := by decide
@[simp] theorem rf_rfN_ne_rfL : rfN ≠ rfL := by decide
@[simp] theorem rf_rfN_ne_rfZ : rfN ≠ rfZ := by decide
@[simp] theorem rf_rfN_ne_lKb : rfN ≠ lKb := by decide
@[simp] theorem rf_rfN_ne_lCn : rfN ≠ lCn := by decide
@[simp] theorem rf_rfN_ne_lSrc : rfN ≠ lSrc := by decide
@[simp] theorem rf_rfN_ne_lDst : rfN ≠ lDst := by decide
@[simp] theorem rf_rfN_ne_lCi : rfN ≠ lCi := by decide
@[simp] theorem rf_rfN_ne_lCz : rfN ≠ lCz := by decide
@[simp] theorem rf_rfB_ne_rfR : rfB ≠ rfR := by decide
@[simp] theorem rf_rfB_ne_rfKs : rfB ≠ rfKs := by decide
@[simp] theorem rf_rfB_ne_rfU : rfB ≠ rfU := by decide
@[simp] theorem rf_rfB_ne_rfJs : rfB ≠ rfJs := by decide
@[simp] theorem rf_rfB_ne_rfKl : rfB ≠ rfKl := by decide
@[simp] theorem rf_rfB_ne_rfKb : rfB ≠ rfKb := by decide
@[simp] theorem rf_rfB_ne_rfA : rfB ≠ rfA := by decide
@[simp] theorem rf_rfB_ne_rfT : rfB ≠ rfT := by decide
@[simp] theorem rf_rfB_ne_rfS : rfB ≠ rfS := by decide
@[simp] theorem rf_rfB_ne_rfN : rfB ≠ rfN := by decide
@[simp] theorem rf_rfB_ne_rfL : rfB ≠ rfL := by decide
@[simp] theorem rf_rfB_ne_rfZ : rfB ≠ rfZ := by decide
@[simp] theorem rf_rfB_ne_lKb : rfB ≠ lKb := by decide
@[simp] theorem rf_rfB_ne_lCn : rfB ≠ lCn := by decide
@[simp] theorem rf_rfB_ne_lSrc : rfB ≠ lSrc := by decide
@[simp] theorem rf_rfB_ne_lDst : rfB ≠ lDst := by decide
@[simp] theorem rf_rfB_ne_lCi : rfB ≠ lCi := by decide
@[simp] theorem rf_rfB_ne_lCz : rfB ≠ lCz := by decide
@[simp] theorem rf_rfL_ne_rfR : rfL ≠ rfR := by decide
@[simp] theorem rf_rfL_ne_rfKs : rfL ≠ rfKs := by decide
@[simp] theorem rf_rfL_ne_rfU : rfL ≠ rfU := by decide
@[simp] theorem rf_rfL_ne_rfJs : rfL ≠ rfJs := by decide
@[simp] theorem rf_rfL_ne_rfKl : rfL ≠ rfKl := by decide
@[simp] theorem rf_rfL_ne_rfKb : rfL ≠ rfKb := by decide
@[simp] theorem rf_rfL_ne_rfA : rfL ≠ rfA := by decide
@[simp] theorem rf_rfL_ne_rfT : rfL ≠ rfT := by decide
@[simp] theorem rf_rfL_ne_rfS : rfL ≠ rfS := by decide
@[simp] theorem rf_rfL_ne_rfN : rfL ≠ rfN := by decide
@[simp] theorem rf_rfL_ne_rfB : rfL ≠ rfB := by decide
@[simp] theorem rf_rfL_ne_rfZ : rfL ≠ rfZ := by decide
@[simp] theorem rf_rfL_ne_lKb : rfL ≠ lKb := by decide
@[simp] theorem rf_rfL_ne_lCn : rfL ≠ lCn := by decide
@[simp] theorem rf_rfL_ne_lSrc : rfL ≠ lSrc := by decide
@[simp] theorem rf_rfL_ne_lDst : rfL ≠ lDst := by decide
@[simp] theorem rf_rfL_ne_lCi : rfL ≠ lCi := by decide
@[simp] theorem rf_rfL_ne_lCz : rfL ≠ lCz := by decide
@[simp] theorem rf_rfZ_ne_rfR : rfZ ≠ rfR := by decide
@[simp] theorem rf_rfZ_ne_rfKs : rfZ ≠ rfKs := by decide
@[simp] theorem rf_rfZ_ne_rfU : rfZ ≠ rfU := by decide
@[simp] theorem rf_rfZ_ne_rfJs : rfZ ≠ rfJs := by decide
@[simp] theorem rf_rfZ_ne_rfKl : rfZ ≠ rfKl := by decide
@[simp] theorem rf_rfZ_ne_rfKb : rfZ ≠ rfKb := by decide
@[simp] theorem rf_rfZ_ne_rfA : rfZ ≠ rfA := by decide
@[simp] theorem rf_rfZ_ne_rfT : rfZ ≠ rfT := by decide
@[simp] theorem rf_rfZ_ne_rfS : rfZ ≠ rfS := by decide
@[simp] theorem rf_rfZ_ne_rfN : rfZ ≠ rfN := by decide
@[simp] theorem rf_rfZ_ne_rfB : rfZ ≠ rfB := by decide
@[simp] theorem rf_rfZ_ne_rfL : rfZ ≠ rfL := by decide
@[simp] theorem rf_rfZ_ne_lKb : rfZ ≠ lKb := by decide
@[simp] theorem rf_rfZ_ne_lCn : rfZ ≠ lCn := by decide
@[simp] theorem rf_rfZ_ne_lSrc : rfZ ≠ lSrc := by decide
@[simp] theorem rf_rfZ_ne_lDst : rfZ ≠ lDst := by decide
@[simp] theorem rf_rfZ_ne_lCi : rfZ ≠ lCi := by decide
@[simp] theorem rf_rfZ_ne_lCz : rfZ ≠ lCz := by decide
@[simp] theorem rf_lKb_ne_rfR : lKb ≠ rfR := by decide
@[simp] theorem rf_lKb_ne_rfKs : lKb ≠ rfKs := by decide
@[simp] theorem rf_lKb_ne_rfU : lKb ≠ rfU := by decide
@[simp] theorem rf_lKb_ne_rfJs : lKb ≠ rfJs := by decide
@[simp] theorem rf_lKb_ne_rfKl : lKb ≠ rfKl := by decide
@[simp] theorem rf_lKb_ne_rfKb : lKb ≠ rfKb := by decide
@[simp] theorem rf_lKb_ne_rfA : lKb ≠ rfA := by decide
@[simp] theorem rf_lKb_ne_rfT : lKb ≠ rfT := by decide
@[simp] theorem rf_lKb_ne_rfS : lKb ≠ rfS := by decide
@[simp] theorem rf_lKb_ne_rfN : lKb ≠ rfN := by decide
@[simp] theorem rf_lKb_ne_rfB : lKb ≠ rfB := by decide
@[simp] theorem rf_lKb_ne_rfL : lKb ≠ rfL := by decide
@[simp] theorem rf_lKb_ne_rfZ : lKb ≠ rfZ := by decide
@[simp] theorem rf_lCn_ne_rfR : lCn ≠ rfR := by decide
@[simp] theorem rf_lCn_ne_rfKs : lCn ≠ rfKs := by decide
@[simp] theorem rf_lCn_ne_rfU : lCn ≠ rfU := by decide
@[simp] theorem rf_lCn_ne_rfJs : lCn ≠ rfJs := by decide
@[simp] theorem rf_lCn_ne_rfKl : lCn ≠ rfKl := by decide
@[simp] theorem rf_lCn_ne_rfKb : lCn ≠ rfKb := by decide
@[simp] theorem rf_lCn_ne_rfA : lCn ≠ rfA := by decide
@[simp] theorem rf_lCn_ne_rfT : lCn ≠ rfT := by decide
@[simp] theorem rf_lCn_ne_rfS : lCn ≠ rfS := by decide
@[simp] theorem rf_lCn_ne_rfN : lCn ≠ rfN := by decide
@[simp] theorem rf_lCn_ne_rfB : lCn ≠ rfB := by decide
@[simp] theorem rf_lCn_ne_rfL : lCn ≠ rfL := by decide
@[simp] theorem rf_lCn_ne_rfZ : lCn ≠ rfZ := by decide
@[simp] theorem rf_lSrc_ne_rfR : lSrc ≠ rfR := by decide
@[simp] theorem rf_lSrc_ne_rfKs : lSrc ≠ rfKs := by decide
@[simp] theorem rf_lSrc_ne_rfU : lSrc ≠ rfU := by decide
@[simp] theorem rf_lSrc_ne_rfJs : lSrc ≠ rfJs := by decide
@[simp] theorem rf_lSrc_ne_rfKl : lSrc ≠ rfKl := by decide
@[simp] theorem rf_lSrc_ne_rfKb : lSrc ≠ rfKb := by decide
@[simp] theorem rf_lSrc_ne_rfA : lSrc ≠ rfA := by decide
@[simp] theorem rf_lSrc_ne_rfT : lSrc ≠ rfT := by decide
@[simp] theorem rf_lSrc_ne_rfS : lSrc ≠ rfS := by decide
@[simp] theorem rf_lSrc_ne_rfN : lSrc ≠ rfN := by decide
@[simp] theorem rf_lSrc_ne_rfB : lSrc ≠ rfB := by decide
@[simp] theorem rf_lSrc_ne_rfL : lSrc ≠ rfL := by decide
@[simp] theorem rf_lSrc_ne_rfZ : lSrc ≠ rfZ := by decide
@[simp] theorem rf_lDst_ne_rfR : lDst ≠ rfR := by decide
@[simp] theorem rf_lDst_ne_rfKs : lDst ≠ rfKs := by decide
@[simp] theorem rf_lDst_ne_rfU : lDst ≠ rfU := by decide
@[simp] theorem rf_lDst_ne_rfJs : lDst ≠ rfJs := by decide
@[simp] theorem rf_lDst_ne_rfKl : lDst ≠ rfKl := by decide
@[simp] theorem rf_lDst_ne_rfKb : lDst ≠ rfKb := by decide
@[simp] theorem rf_lDst_ne_rfA : lDst ≠ rfA := by decide
@[simp] theorem rf_lDst_ne_rfT : lDst ≠ rfT := by decide
@[simp] theorem rf_lDst_ne_rfS : lDst ≠ rfS := by decide
@[simp] theorem rf_lDst_ne_rfN : lDst ≠ rfN := by decide
@[simp] theorem rf_lDst_ne_rfB : lDst ≠ rfB := by decide
@[simp] theorem rf_lDst_ne_rfL : lDst ≠ rfL := by decide
@[simp] theorem rf_lDst_ne_rfZ : lDst ≠ rfZ := by decide
@[simp] theorem rf_lCi_ne_rfR : lCi ≠ rfR := by decide
@[simp] theorem rf_lCi_ne_rfKs : lCi ≠ rfKs := by decide
@[simp] theorem rf_lCi_ne_rfU : lCi ≠ rfU := by decide
@[simp] theorem rf_lCi_ne_rfJs : lCi ≠ rfJs := by decide
@[simp] theorem rf_lCi_ne_rfKl : lCi ≠ rfKl := by decide
@[simp] theorem rf_lCi_ne_rfKb : lCi ≠ rfKb := by decide
@[simp] theorem rf_lCi_ne_rfA : lCi ≠ rfA := by decide
@[simp] theorem rf_lCi_ne_rfT : lCi ≠ rfT := by decide
@[simp] theorem rf_lCi_ne_rfS : lCi ≠ rfS := by decide
@[simp] theorem rf_lCi_ne_rfN : lCi ≠ rfN := by decide
@[simp] theorem rf_lCi_ne_rfB : lCi ≠ rfB := by decide
@[simp] theorem rf_lCi_ne_rfL : lCi ≠ rfL := by decide
@[simp] theorem rf_lCi_ne_rfZ : lCi ≠ rfZ := by decide
@[simp] theorem rf_lCz_ne_rfR : lCz ≠ rfR := by decide
@[simp] theorem rf_lCz_ne_rfKs : lCz ≠ rfKs := by decide
@[simp] theorem rf_lCz_ne_rfU : lCz ≠ rfU := by decide
@[simp] theorem rf_lCz_ne_rfJs : lCz ≠ rfJs := by decide
@[simp] theorem rf_lCz_ne_rfKl : lCz ≠ rfKl := by decide
@[simp] theorem rf_lCz_ne_rfKb : lCz ≠ rfKb := by decide
@[simp] theorem rf_lCz_ne_rfA : lCz ≠ rfA := by decide
@[simp] theorem rf_lCz_ne_rfT : lCz ≠ rfT := by decide
@[simp] theorem rf_lCz_ne_rfS : lCz ≠ rfS := by decide
@[simp] theorem rf_lCz_ne_rfN : lCz ≠ rfN := by decide
@[simp] theorem rf_lCz_ne_rfB : lCz ≠ rfB := by decide
@[simp] theorem rf_lCz_ne_rfL : lCz ≠ rfL := by decide
@[simp] theorem rf_lCz_ne_rfZ : lCz ≠ rfZ := by decide

def rfParams : List MlS := [rfR, rfKs, rfU, rfJs]
def rfLocals : List MlS := [rfKl, rfKb, rfA, rfT, rfS, rfN, rfB, rfL, rfZ, lCn, lSrc, lDst, lCi, lCz,
  lDh, lFl, lDt, lDg, lDi, lRp, lRn]

def rfCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rfKl (.load .one (vv rfKs)))
  (.seq (.assign .local lCn (.op .add [vv rfKl, .const 1]))
  (allocP C rfKb (.panop .mul [vv lCn, .const 8])
  (.seq (.assign .local lSrc (vv rfKs)) (.seq (.assign .local lDst (vv rfKb)) (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop
  (allocP C rfA (.const 8) (.seq (.store (vv rfA) (.const 0))
  (.seq (.assign .local rfT (.load .one (.op .add [vv rfR, .const 16])))
  (.ite (.cmp .equal (vv rfT) (.const 0))
    (.seq (.assign .local rfN (.load .one (vv rfJs)))
    (.seq (.call (some (some (.local, rfB), none)) fRg [.const 1, .op .add [vv rfJs, .const 8], vv rfN, vv rfKb, vv rfU, vv rfA])
    (.seq (.assign .local rfL (.load .one (vv rfB)))
    (.seq (.call (some (some (.local, rfZ), none)) fInternLs [.op .add [vv rfB, .const 8], vv rfL])
      (.return (vv rfZ))))))
    (.seq (.assign .local rfS (.load .one (.op .add [vv rfR, .const 24])))
    (.seq (.assign .local rfN (.load .one (vv rfS)))
    (.seq (.call (some (some (.local, rfB), none)) fRg [.const 0, .op .add [vv rfS, .const 8], vv rfN, vv rfKb, vv rfU, vv rfA])
    (.seq (.assign .local rfL (.load .one (vv rfB)))
    (.seq (.call (some (some (.local, rfZ), none)) fInternLs [.op .add [vv rfB, .const 8], vv rfL])
      (.return (vv rfZ)))))))))))))))))

/-- `recFireLevels`, after checking its level list's view (halting on an invalid handle). -/
def rfBody (C : Ctx) : ProgHOL 64 :=
  prologue rfLocals (.seq (.assign .local lDh (vv rfU)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP (rfCore C))))

section
variable {σ : Type}

structure RfCodes (C : Ctx) : Prop where
  rg : RgCodes C
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)

/-- A level-list handle, the heap extended, any final state. -/
def PostLI (C : Ctx) (h : LsIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW h ∧ SR (ctxH C H') s' st

theorem postLI_locals (C : Ctx) : ∀ (a : LsIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLI C a w s' st → PostLI C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem rf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rfLocals → (ctxEnv C ++ rfParams.zip vals).get x = none :=
  Knot.params_none C rfLocals rfParams vals (by decide) (by decide)

theorem rf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : RfCodes C) (s : AState)
    (rl : IRecRule) (qr : Nat) (hrule : RuleE C.EB C.EH qr rl) (lps cvjLps : List NIdx) (ok oj : Nat)
    (hks0 : EBlk C.EH ok (lps.map Enc.idxW)) (hjs : EBlk C.EH oj (cvjLps.map Enc.idxW)) (us : LsIdx)
    (ks : List ConLeche.Name) (hks : Frontend.denoteNList s.store.ns lps = some ks)
    (hwf : StoreWF s.store)
    (hrn : ReadNCacheOK s.caches.readNC s.store) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hrls : ReadLsCacheOK s.caches.readLsC s.store)
    (hpl : rl.fire = .plain → ∃ pns, Frontend.denoteNList s.store.ns cvjLps = some pns)
    (hlv : ∀ lv, (∃ pins, rl.fire = .nested lv pins) ∨ rl.fire = .levels lv →
      ∀ j (hj : j < lv.length), (denoteL s.store.ls lv[j]).isSome = true)
    (hlvl : ∀ lv, (∃ pins, rl.fire = .nested lv pins) ∨ rl.fire = .levels lv → lv.length < 2 ^ 60)
    (hll : lps.length + 1 < 2 ^ 60) (hjl : cvjLps.length < 2 ^ 60) (H : List (BitVec 64)) (hp : C.H <+: H) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rfParams.zip [ecell C qr, ecell C ok, Enc.idxW us, ecell C oj])) (rfBody C) s
      (recFireLevels rl lps us cvjLps) (PostLI (ctxH C H)) := by
  refine specR_prologue (postLI_locals _) (rf_none _ _) ?_
  refine specR_assignI lDh (vv rfU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, rfParams, ctxEnv]) ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, rfParams, ctxEnv] <;> rfl) ?_
  refine specR_lsviewPI (C := ctxH C H) us (by simp +decide) (by simp +decide <;> rfl)
    (by simp +decide [Env.get, rfParams, ctxEnv] <;> rfl) ⟨by decide, by decide, by decide, by decide, by decide⟩
    (fun v0 P0 hv0 _ _ => ?_)
  obtain ⟨vs, hus⟩ := Option.isSome_iff_exists.mp (denoteLs_total' (by obtain ⟨rk, w⟩ := hwf; exact w.lss) (by rw [hv0]; rfl))
  refine specR_dropMem ?_
  unfold rfCore
  have hl0 : C.EH[ok]? = some (BitVec.ofNat 64 lps.length) := by simpa using hks0.1
  rcases hv : s.store.lss.view us with _ | uh
  · simp [denoteLs, hv] at hus
  have hvs : denoteLList s.store.ls uh = some vs := by have := hus; simp only [denoteLs, hv] at this; exact this
  have hu : s.store.lss.view us = some uh := hv
  obtain ⟨c1, hn1, hc1, hN1⟩ := ILP.readNamesM_eq lps s ks hrn hks
  obtain ⟨X, hx, hXo⟩ := readLevelsM_runCok us (withC s c1) vs
    (by show ReadLsCacheOK c1.readLsC s.store; rw [hc1]; exact hrls) hus
  rcases hf : rl.fire with _ | ⟨lv, pins⟩ | lv
  · -- plain
    obtain ⟨pns, hpns⟩ := hpl hf
    have hft : C.EH[qr + 2]? = some 0 := by have := hrule.2.2.1; rw [hf] at this; exact this
    simp only [recFireLevels, hf]
    refine specR_quiet hn1 rfl rfl (by show MirrorEq c1 s.caches; rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl (fun hc => cachesOK_caches hc c1 hc1 hN1) ?_
    refine specR_quiet hx rfl rfl
      (by show MirrorEq { c1 with readLsC := X } c1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl (fun hc => cachesOK_readLsC hc X hXo) ?_
    refine specR_envLoadI (C := ctxH C H) rfKl (vv rfKs) ok _ (by decide)
      (by simp +decide [Env.get, rfParams, ctxEnv]; rfl) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (lps.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI (C := ctxH C H) rfKb (.panop .mul [vv lCn, .const 8]) (lps.length + 1) (by omega) (by decide)
      (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _) (fun H1 ws hpa hwl2 hcap => ?_)
    refine specR_assignI lSrc (vv rfKs) (ecell C ok) (by decide) (by simp +decide [sev, Env.get, rfParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDst (vv rfKb) (cellA C H1.length) (by decide) (by simp +decide [sev, Env.get] <;> rfl) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = lps.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) ok H1.length
      (by decide) (fun j hj => ?_) (by simp [hwl2]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, rfParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hks0.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show ok + (j + 1) = ok + 1 + j by omega]; simpa using this
    generalize hF : fillI (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H1.length
      (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = F
    have hblkK : BlkAt F H1.length (lps.map Enc.idxW) := by
      rw [← hF]; exact blk_of_fillI _ _ H1.length _ (by simp) (by simp [hwl2])
    have hpF : H <+: F := by
      rw [← hF]; exact prefix_fillI _ _ _ H hpa.length_le (hpa.trans (List.prefix_append _ _)) _
    refine specR_allocI (C := ctxH C F) rfA (.const 8) 1 (by decide) (by decide) (fun _ => rfl)
      (fun H2 ws2 hpb hws2 hroom2 => ?_)
    have hj0 : H2.length < (ctxH (ctxH C F) (H2 ++ ws2)).H.length := by
      show H2.length < (H2 ++ ws2).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv rfA) (.const 0) H2.length hj0 0 (by simp <;> rfl) rfl ?_
    change SpecR (Inv (ctxH C ((H2 ++ ws2).set H2.length 0)) _ _ _ _) _ _ _ _
    generalize hG : (H2 ++ ws2).set H2.length 0 = G
    have hpG : F <+: G := by
      rw [← hG]; exact prefix_set_ge (hpb.trans (List.prefix_append _ _)) _ hpb.length_le _
    have hbA : BlkAt G H2.length (([] : List LIdx).map Enc.idxW) :=
      ⟨by rw [← hG, List.getElem?_set_self (by simp; omega)]; rfl, fun i hi => absurd hi (by simp)⟩
    have hLA : H.length ≤ H2.length := (hpF.trans hpb).length_le
    refine specR_envLoadI (C := ctxH C G) rfT (.op .add [vv rfR, .const 16]) (qr + 2) _ (by decide)
      (by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_envLoadI (C := ctxH C G) rfN (vv rfJs) oj _ (by decide)
      (by simp +decide [Env.get, rfParams, ctxEnv]; rfl) (by simpa using hjs.1 : C.EH[oj]? = _) ?_
    refine specR_congr (m' := (substParamLevels ks vs cvjLps >>= fun hs => pure (([] : List LIdx) ++ hs)) >>= fun ls => internLsNode ls)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C G) rfB fRg rgParams
      [.const 1, .op .add [vv rfJs, .const 8], vv rfN, vv rfKb, vv rfU, vv rfA] (rgBody C)
      [boolW true, ecell C (oj + 1), BitVec.ofNat 64 cvjLps.length, cellA C H1.length, Enc.idxW us, cellA C H2.length]
      (by decide) rfl (by decide) hc.rg.self
      ⟨rfl, by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact ecell_add8 C oj,
        by simp +decide [Env.get], by simp +decide [Env.get] <;> rfl, by simp +decide [Env.get, rfParams, ctxEnv],
        by simp +decide [Env.get] <;> rfl, trivial⟩
      (PostAL (ctxH C G) H.length) (fun a w _ H4 => ∃ o4, H.length ≤ o4 ∧ w = cellA C o4 ∧ BlkAt H4 o4 (a.map Enc.idxW))
      (fun a w s' st ⟨H4, o4, hp4, hL4, hw, hb4, hsr⟩ => ⟨H4, hp4, ⟨o4, hL4, hw, hb4⟩, hsr⟩)
      (fun u' hu' _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu' rgParams _ rfl hlk)
        (rgP_spec ra C hok hc.rg H1.length lps ks us uh vs H.length cvjLps pns (oj + 1) G [] H2.length _
                (hp.trans (hpF.trans hpG)) (fun j hj => by have h' := hjs.2 j (by simpa using hj); simpa using h')
                hbA (blkAt_mono hblkK hpG) hks hu hvs hwf (by show ReadNCacheOK c1.readNC s.store; exact hN1) hpns
                hjl hLA ((hpF.trans hpG).length_le)))
      (fun hs w s4 H4 hp4 ⟨o4, hL4, hw, hb4⟩ => ?_)
    subst hw
    try simp only [List.nil_append]
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hb4
    refine UD.specR_heapLoadI' (C := ctxH C H4) rfL (vv rfB) o4 (BitVec.ofNat 64 hs.length)
      (by show H4[o4]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get]; rfl) ?_
    refine specR_atEntry fun t ht => ?_
    have hsz := blk_small0 (ctxOK_H hok H4) ht.sr hb4
    simp only [List.length_map] at hsz
    have hbl := blkAt_len hb4
    simp only [List.length_map] at hbl
    have hHH4 : H <+: H4 := hpF.trans (hpG.trans hp4)
    refine specR_bindPure ?_
    refine specR_callNIA (C := ctxH C H4) rfZ fInternLs [pKey, lEc] [.op .add [vv rfB, .const 8], vv rfL] internLsBody
      [cellA C (o4 + 1), BitVec.ofNat 64 hs.length] (by decide) rfl (by decide) hc.ls
      ⟨by simp +decide [sev, Env.get]; exact cellA_add8 C o4, by simp +decide [Env.get], trivial⟩
      (fun a w s' st => PostLs (ctxH (ctxH C H4) H) a w s' st)
      (fun a w s' H' => H' = H ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hw, hsr⟩ => ⟨H, ⟨rfl, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pKey, lEc] _ rfl hlk)
        (internLs_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s4 hs (o4 + 1) H hHH4 (by omega)
          (by show o4 + 1 + hs.length ≤ H4.length; omega) (by omega)
          (fun j hj => by have := hb4.2 j (by simpa using hj); simp only [List.getElem_map] at this; exact this)))
      (fun h w s5 H5 ⟨e, hw⟩ => ?_)
    subst H5; subst hw
    exact specR_returnI _ (Enc.idxW h) (by simp)
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · -- nested
    have hfe := hrule.2.2.1; rw [hf] at hfe
    obtain ⟨hft, ⟨w3, hw3, olv, hw3', hblv⟩, -⟩ := hfe
    subst hw3'
    simp only [recFireLevels, hf]
    refine specR_quiet hn1 rfl rfl (by show MirrorEq c1 s.caches; rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl (fun hc => cachesOK_caches hc c1 hc1 hN1) ?_
    refine specR_quiet hx rfl rfl
      (by show MirrorEq { c1 with readLsC := X } c1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl (fun hc => cachesOK_readLsC hc X hXo) ?_
    refine specR_envLoadI (C := ctxH C H) rfKl (vv rfKs) ok _ (by decide)
      (by simp +decide [Env.get, rfParams, ctxEnv]; rfl) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (lps.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI (C := ctxH C H) rfKb (.panop .mul [vv lCn, .const 8]) (lps.length + 1) (by omega) (by decide)
      (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _) (fun H1 ws hpa hwl2 hcap => ?_)
    refine specR_assignI lSrc (vv rfKs) (ecell C ok) (by decide) (by simp +decide [sev, Env.get, rfParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDst (vv rfKb) (cellA C H1.length) (by decide) (by simp +decide [sev, Env.get] <;> rfl) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = lps.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) ok H1.length
      (by decide) (fun j hj => ?_) (by simp [hwl2]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, rfParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hks0.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show ok + (j + 1) = ok + 1 + j by omega]; simpa using this
    generalize hF : fillI (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H1.length
      (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = F
    have hblkK : BlkAt F H1.length (lps.map Enc.idxW) := by
      rw [← hF]; exact blk_of_fillI _ _ H1.length _ (by simp) (by simp [hwl2])
    have hpF : H <+: F := by
      rw [← hF]; exact prefix_fillI _ _ _ H hpa.length_le (hpa.trans (List.prefix_append _ _)) _
    refine specR_allocI (C := ctxH C F) rfA (.const 8) 1 (by decide) (by decide) (fun _ => rfl)
      (fun H2 ws2 hpb hws2 hroom2 => ?_)
    have hj0 : H2.length < (ctxH (ctxH C F) (H2 ++ ws2)).H.length := by
      show H2.length < (H2 ++ ws2).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv rfA) (.const 0) H2.length hj0 0 (by simp <;> rfl) rfl ?_
    change SpecR (Inv (ctxH C ((H2 ++ ws2).set H2.length 0)) _ _ _ _) _ _ _ _
    generalize hG : (H2 ++ ws2).set H2.length 0 = G
    have hpG : F <+: G := by
      rw [← hG]; exact prefix_set_ge (hpb.trans (List.prefix_append _ _)) _ hpb.length_le _
    have hbA : BlkAt G H2.length (([] : List LIdx).map Enc.idxW) :=
      ⟨by rw [← hG, List.getElem?_set_self (by simp; omega)]; rfl, fun i hi => absurd hi (by simp)⟩
    have hLA : H.length ≤ H2.length := (hpF.trans hpb).length_le
    refine specR_envLoadI (C := ctxH C G) rfT (.op .add [vv rfR, .const 16]) (qr + 2) _ (by decide)
      (by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
    have hne0 : (BitVec.ofNat 64 1 : BitVec 64) ≠ 0 := by decide
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_envLoadI (C := ctxH C G) rfS (.op .add [vv rfR, .const 24]) (qr + 3) _ (by decide)
      (by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact ecell_add24 C qr) (by simpa using hw3 : C.EH[qr + 3]? = _) ?_
    refine specR_envLoadI (C := ctxH C G) rfN (vv rfS) olv _ (by decide)
      (by simp +decide [Env.get, rfParams, ctxEnv]; rfl) (by simpa using hblv.1 : C.EH[olv]? = _) ?_
    refine specR_congr (m' := (substLevelsAt ks vs lv >>= fun hs => pure (([] : List LIdx) ++ hs)) >>= fun ls => internLsNode ls)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C G) rfB fRg rgParams
      [.const 0, .op .add [vv rfS, .const 8], vv rfN, vv rfKb, vv rfU, vv rfA] (rgBody C)
      [boolW false, ecell C (olv + 1), BitVec.ofNat 64 lv.length, cellA C H1.length, Enc.idxW us, cellA C H2.length]
      (by decide) rfl (by decide) hc.rg.self
      ⟨rfl, by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact ecell_add8 C olv,
        by simp +decide [Env.get], by simp +decide [Env.get] <;> rfl, by simp +decide [Env.get, rfParams, ctxEnv],
        by simp +decide [Env.get] <;> rfl, trivial⟩
      (PostAL (ctxH C G) H.length) (fun a w _ H4 => ∃ o4, H.length ≤ o4 ∧ w = cellA C o4 ∧ BlkAt H4 o4 (a.map Enc.idxW))
      (fun a w s' st ⟨H4, o4, hp4, hL4, hw, hb4, hsr⟩ => ⟨H4, hp4, ⟨o4, hL4, hw, hb4⟩, hsr⟩)
      (fun u' hu' _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu' rgParams _ rfl hlk)
        (rgL_spec ra C hok hc.rg H1.length lps ks us uh vs H.length lv (olv + 1) G [] H2.length _
                (hp.trans (hpF.trans hpG)) (fun j hj => by have h' := hblv.2 j (by simpa using hj); simpa using h')
                hbA (blkAt_mono hblkK hpG) hks hu hvs hwf (by show ReadLCacheOK c1.readLC s.store; rw [hc1]; exact hrl)
                (hlv lv (Or.inl ⟨pins, hf⟩)) (hlvl lv (Or.inl ⟨pins, hf⟩)) hLA ((hpF.trans hpG).length_le)))
      (fun hs w s4 H4 hp4 ⟨o4, hL4, hw, hb4⟩ => ?_)
    subst hw
    try simp only [List.nil_append]
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hb4
    refine UD.specR_heapLoadI' (C := ctxH C H4) rfL (vv rfB) o4 (BitVec.ofNat 64 hs.length)
      (by show H4[o4]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get]; rfl) ?_
    refine specR_atEntry fun t ht => ?_
    have hsz := blk_small0 (ctxOK_H hok H4) ht.sr hb4
    simp only [List.length_map] at hsz
    have hbl := blkAt_len hb4
    simp only [List.length_map] at hbl
    have hHH4 : H <+: H4 := hpF.trans (hpG.trans hp4)
    refine specR_bindPure ?_
    refine specR_callNIA (C := ctxH C H4) rfZ fInternLs [pKey, lEc] [.op .add [vv rfB, .const 8], vv rfL] internLsBody
      [cellA C (o4 + 1), BitVec.ofNat 64 hs.length] (by decide) rfl (by decide) hc.ls
      ⟨by simp +decide [sev, Env.get]; exact cellA_add8 C o4, by simp +decide [Env.get], trivial⟩
      (fun a w s' st => PostLs (ctxH (ctxH C H4) H) a w s' st)
      (fun a w s' H' => H' = H ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hw, hsr⟩ => ⟨H, ⟨rfl, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pKey, lEc] _ rfl hlk)
        (internLs_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s4 hs (o4 + 1) H hHH4 (by omega)
          (by show o4 + 1 + hs.length ≤ H4.length; omega) (by omega)
          (fun j hj => by have := hb4.2 j (by simpa using hj); simp only [List.getElem_map] at this; exact this)))
      (fun h w s5 H5 ⟨e, hw⟩ => ?_)
    subst H5; subst hw
    exact specR_returnI _ (Enc.idxW h) (by simp)
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · -- levels
    have hfe := hrule.2.2.1; rw [hf] at hfe
    obtain ⟨hft, w3, hw3, olv, hw3', hblv⟩ := hfe
    subst hw3'
    simp only [recFireLevels, hf]
    refine specR_quiet hn1 rfl rfl (by show MirrorEq c1 s.caches; rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl (fun hc => cachesOK_caches hc c1 hc1 hN1) ?_
    refine specR_quiet hx rfl rfl
      (by show MirrorEq { c1 with readLsC := X } c1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl (fun hc => cachesOK_readLsC hc X hXo) ?_
    refine specR_envLoadI (C := ctxH C H) rfKl (vv rfKs) ok _ (by decide)
      (by simp +decide [Env.get, rfParams, ctxEnv]; rfl) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (lps.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI (C := ctxH C H) rfKb (.panop .mul [vv lCn, .const 8]) (lps.length + 1) (by omega) (by decide)
      (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _) (fun H1 ws hpa hwl2 hcap => ?_)
    refine specR_assignI lSrc (vv rfKs) (ecell C ok) (by decide) (by simp +decide [sev, Env.get, rfParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDst (vv rfKb) (cellA C H1.length) (by decide) (by simp +decide [sev, Env.get] <;> rfl) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = lps.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) ok H1.length
      (by decide) (fun j hj => ?_) (by simp [hwl2]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, rfParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hks0.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show ok + (j + 1) = ok + 1 + j by omega]; simpa using this
    generalize hF : fillI (H1 ++ ws) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H1.length
      (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = F
    have hblkK : BlkAt F H1.length (lps.map Enc.idxW) := by
      rw [← hF]; exact blk_of_fillI _ _ H1.length _ (by simp) (by simp [hwl2])
    have hpF : H <+: F := by
      rw [← hF]; exact prefix_fillI _ _ _ H hpa.length_le (hpa.trans (List.prefix_append _ _)) _
    refine specR_allocI (C := ctxH C F) rfA (.const 8) 1 (by decide) (by decide) (fun _ => rfl)
      (fun H2 ws2 hpb hws2 hroom2 => ?_)
    have hj0 : H2.length < (ctxH (ctxH C F) (H2 ++ ws2)).H.length := by
      show H2.length < (H2 ++ ws2).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv rfA) (.const 0) H2.length hj0 0 (by simp <;> rfl) rfl ?_
    change SpecR (Inv (ctxH C ((H2 ++ ws2).set H2.length 0)) _ _ _ _) _ _ _ _
    generalize hG : (H2 ++ ws2).set H2.length 0 = G
    have hpG : F <+: G := by
      rw [← hG]; exact prefix_set_ge (hpb.trans (List.prefix_append _ _)) _ hpb.length_le _
    have hbA : BlkAt G H2.length (([] : List LIdx).map Enc.idxW) :=
      ⟨by rw [← hG, List.getElem?_set_self (by simp; omega)]; rfl, fun i hi => absurd hi (by simp)⟩
    have hLA : H.length ≤ H2.length := (hpF.trans hpb).length_le
    refine specR_envLoadI (C := ctxH C G) rfT (.op .add [vv rfR, .const 16]) (qr + 2) _ (by decide)
      (by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact UD.ecell_add16 C qr) hft ?_
    have hne0 : (BitVec.ofNat 64 2 : BitVec 64) ≠ 0 := by decide
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_envLoadI (C := ctxH C G) rfS (.op .add [vv rfR, .const 24]) (qr + 3) _ (by decide)
      (by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact ecell_add24 C qr) (by simpa using hw3 : C.EH[qr + 3]? = _) ?_
    refine specR_envLoadI (C := ctxH C G) rfN (vv rfS) olv _ (by decide)
      (by simp +decide [Env.get, rfParams, ctxEnv]; rfl) (by simpa using hblv.1 : C.EH[olv]? = _) ?_
    refine specR_congr (m' := (substLevelsAt ks vs lv >>= fun hs => pure (([] : List LIdx) ++ hs)) >>= fun ls => internLsNode ls)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C G) rfB fRg rgParams
      [.const 0, .op .add [vv rfS, .const 8], vv rfN, vv rfKb, vv rfU, vv rfA] (rgBody C)
      [boolW false, ecell C (olv + 1), BitVec.ofNat 64 lv.length, cellA C H1.length, Enc.idxW us, cellA C H2.length]
      (by decide) rfl (by decide) hc.rg.self
      ⟨rfl, by simp +decide [sev, Env.get, rfParams, ctxEnv]; exact ecell_add8 C olv,
        by simp +decide [Env.get], by simp +decide [Env.get] <;> rfl, by simp +decide [Env.get, rfParams, ctxEnv],
        by simp +decide [Env.get] <;> rfl, trivial⟩
      (PostAL (ctxH C G) H.length) (fun a w _ H4 => ∃ o4, H.length ≤ o4 ∧ w = cellA C o4 ∧ BlkAt H4 o4 (a.map Enc.idxW))
      (fun a w s' st ⟨H4, o4, hp4, hL4, hw, hb4, hsr⟩ => ⟨H4, hp4, ⟨o4, hL4, hw, hb4⟩, hsr⟩)
      (fun u' hu' _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu' rgParams _ rfl hlk)
        (rgL_spec ra C hok hc.rg H1.length lps ks us uh vs H.length lv (olv + 1) G [] H2.length _
                (hp.trans (hpF.trans hpG)) (fun j hj => by have h' := hblv.2 j (by simpa using hj); simpa using h')
                hbA (blkAt_mono hblkK hpG) hks hu hvs hwf (by show ReadLCacheOK c1.readLC s.store; rw [hc1]; exact hrl)
                (hlv lv (Or.inr hf)) (hlvl lv (Or.inr hf)) hLA ((hpF.trans hpG).length_le)))
      (fun hs w s4 H4 hp4 ⟨o4, hL4, hw, hb4⟩ => ?_)
    subst hw
    try simp only [List.nil_append]
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hb4
    refine UD.specR_heapLoadI' (C := ctxH C H4) rfL (vv rfB) o4 (BitVec.ofNat 64 hs.length)
      (by show H4[o4]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get]; rfl) ?_
    refine specR_atEntry fun t ht => ?_
    have hsz := blk_small0 (ctxOK_H hok H4) ht.sr hb4
    simp only [List.length_map] at hsz
    have hbl := blkAt_len hb4
    simp only [List.length_map] at hbl
    have hHH4 : H <+: H4 := hpF.trans (hpG.trans hp4)
    refine specR_bindPure ?_
    refine specR_callNIA (C := ctxH C H4) rfZ fInternLs [pKey, lEc] [.op .add [vv rfB, .const 8], vv rfL] internLsBody
      [cellA C (o4 + 1), BitVec.ofNat 64 hs.length] (by decide) rfl (by decide) hc.ls
      ⟨by simp +decide [sev, Env.get]; exact cellA_add8 C o4, by simp +decide [Env.get], trivial⟩
      (fun a w s' st => PostLs (ctxH (ctxH C H4) H) a w s' st)
      (fun a w s' H' => H' = H ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hw, hsr⟩ => ⟨H, ⟨rfl, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pKey, lEc] _ rfl hlk)
        (internLs_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s4 hs (o4 + 1) H hHH4 (by omega)
          (by show o4 + 1 + hs.length ≤ H4.length; omega) (by omega)
          (fun j hj => by have := hb4.2 j (by simpa using hj); simp only [List.getElem_map] at this; exact this)))
      (fun h w s5 H5 ⟨e, hw⟩ => ?_)
    subst H5; subst hw
    exact specR_returnI _ (Enc.idxW h) (by simp)
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
