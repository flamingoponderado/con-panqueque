import ConPanqueque.T.DefeqMemo
import ConPanqueque.T.Heap
import ConPanqueque.T.CallN
import ConPanqueque.T.Ex.GetAppFn
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The Core knot

The twin ties `whnfCore`, `whnf`, `infer`, `defeq`, `defeqE` and `inferIO` by fuel (`coreKnot`). The port
has one Pancake function per entry point, each taking the fuel as its first parameter, and one per body.
An entry point checks the fuel (zero hangs, where the twin fails), probes its mode memo, and on a miss
calls its body at one fuel level down and stores the answer.

This file proves the entry points from the bodies' specs; the bodies are proved separately against
the entry points one level down.
-/

namespace ConPanqueque.T.Knot

def kFu := ofString "kfu"
def kD := ofString "kd"
def kE := ofString "ke"
def lX := ofString "kx"
def lY := ofString "ky"
def lZ := ofString "kz"

def kParams : List MlS := [kFu, kD, kE]

section
variable {σ : Type}

/-- The post of a Core entry returning a handle: the callee may grow the heap. -/
def PostK (C : Ctx) (a : EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW a ∧ SR (ctxH C H') s' st

theorem postK_locals (C : Ctx) : ∀ (a : EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostK C a w s' st → PostK C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

/-- The memoized part of an entry point: probe mode memo `k` at `e`; on a miss call body `fB` at
`fuel - 1` and record its answer. -/
def memoEntry (C : Ctx) (k : CacheK) (fB : MlS) : ProgHOL 64 :=
  modeGetP C k lX (vv kE)
    (.ite (.cmp .notEqual (vv lX) (.const 0)) (.return (.op .sub [vv lX, .const 1]))
      (.seq (.call (some (some (.local, lY), none)) fB [.op .sub [vv kFu, .const 1], vv kD, vv kE])
        (modeSetP C k lZ (vv kE) (vv lY) (.return (vv lY)))))

/-- The twin's memoized entry, written as the port reads it. -/
def memoTwin (k : ModeKE) (e : EIdx) (body : AM EIdx) (setOp : EIdx → EIdx → AM Unit) : AM EIdx :=
  (fun st => .ok ((k.sel st.caches.modeMemos)[e]?, st) : AM (Option EIdx)) >>= fun r =>
    match r with
    | some x => pure x
    | none => body >>= fun x => setOp e x >>= fun _ => pure x

theorem optW_some_ne (x : EIdx) : optW (some x) ≠ 0 := idxW_add_one_ne x

theorem memoEntry_spec {C : Ctx} (hok : CtxOK C) (k : ModeKE)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (fB : MlS) (B : ProgHOL 64) (hcB : C.code.lookup fB = some (kParams.map (fun p => (p, ShapeHOL.one)), B, .one))
    (setOp : EIdx → EIdx → AM Unit) (hset : ∀ e r s, setOp e r s = .ok ((), modeSetS k s e r))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (n d : Nat) (e : EIdx) (body : AM EIdx)
    (hbody : ∀ u : PState σ, SR C s u → u.locals.lookup kFu = some (.val (.word (BitVec.ofNat 64 n))) →
      u.locals.lookup kD = some (.val (.word (BitVec.ofNat 64 d))) →
      u.locals.lookup kE = some (.val (.word (Enc.idxW e))) → SpecR (· = u) B s body (PostK C))
    (hfu : Γ.get kFu = some (BitVec.ofNat 64 (n + 1))) (hd : Γ.get kD = some (BitVec.ofNat 64 d))
    (he : Γ.get kE = some (Enc.idxW e)) (hkb : Γ.get lKb = some C.KB)
    (hD : lEo ∈ D ∧ lX ∈ D ∧ lY ∈ D ∧ lZ ∈ D) :
    SpecR (σ := σ) (Inv C s Γ M D) (memoEntry C k.toK fB) s (memoTwin k e body setOp) (PostK C) := by
  obtain ⟨heo, hx, hy, hz⟩ := hD
  have hE1 : sev ((lEo, C.eo) :: Γ) (vv kE) = some (Enc.idxW e) := by simp +decide [sev, Env.get, he]
  refine specR_modeGetI hok k _ (fun _ _ => rfl) hcodeG hcodeP lX (vv kE) e hx heo hE1 hkb (fun r => ?_)
  cases r with
  | some x =>
    refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact optW_some_ne x)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_returnI _ (Enc.idxW x) (by simp [sev, Env.get, optW, optWG]; exact BitVec.add_sub_cancel _ _) (fun t ht => ?_)
    exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | none =>
    refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optW, optWG])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callNIH lY fB kParams [.op .sub [vv kFu, .const 1], vv kD, vv kE] B
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (by decide) rfl hy hcB
      ⟨by simp +decide [sev, Env.get, hfu]; exact Ex.ofNat_succ_sub_one n, by simp +decide [sev, Env.get, hd],
        by simp +decide [sev, Env.get, he], trivial⟩
      (PostK C) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => hbody u hu (hlk 0 (by decide)) (hlk 1 (by decide)) (hlk 2 (by decide)))
      (fun a w s' H' hp hw => ?_)
    subst hw
    refine specR_modeSetI (C := ctxH C H') (ctxOK_H hok H') k setOp hset hcodeS hcodeI lZ (vv kE) (vv lY) e a hz heo
      (by simp +decide [sev, Env.get, he]) (by simp +decide [sev, Env.get]) (by simp +decide [Env.get, hkb]; rfl)
      (fun w => ?_)
    refine specR_returnI _ (Enc.idxW a) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
    exact ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.Knot
