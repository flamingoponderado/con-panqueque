import ConPanqueque.T.DefeqMemo
import ConPanqueque.T.Heap
import ConPanqueque.T.CallN
import ConPanqueque.T.Ex.GetAppFn
import ConPanqueque.T.Proj
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
def kA := ofString "ka"
def kB := ofString "kb"
def lSv := ofString "ksv"
def dParams : List MlS := [kFu, kD, kA, kB]

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

/-! ## Prologue bookkeeping -/

theorem env_get_zip_none (x : MlS) : ∀ (ps : List MlS) (vs : List (BitVec 64)), x ∉ ps → Env.get (ps.zip vs) x = none
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: ps, v :: vs, hp => by
    simp only [List.mem_cons, not_or] at hp
    simp only [List.zip_cons_cons, Env.get, hp.1, ite_false]; exact env_get_zip_none x ps vs hp.2

theorem env_get_append_none (x : MlS) (A B : Env) (hA : A.get x = none) (hB : B.get x = none) :
    (A ++ B).get x = none := by
  induction A with
  | nil => exact hB
  | cons a A ih =>
    obtain ⟨y, v⟩ := a
    simp only [Env.get] at hA ⊢
    split at hA
    · simp at hA
    · rename_i hne; simp only [List.cons_append, Env.get, hne, ite_false]; exact ih hA

theorem ctxEnv_get_none (C : Ctx) (x : MlS) (hx : x ∉ ctxLocals) : (ctxEnv C).get x = none := by
  simp only [ctxLocals, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  simp [ctxEnv, Env.get, h1, h2, h3, h4, h5, h6]

theorem params_none (C : Ctx) (L ps : List MlS) (vals : List (BitVec 64)) (h1 : ∀ x ∈ L, x ∉ ps)
    (h2 : ∀ x ∈ L, x ∉ ctxLocals) : ∀ x, x ∈ L → (ctxEnv C ++ ps.zip vals).get x = none :=
  fun x hx => env_get_append_none x _ _ (ctxEnv_get_none C x (h2 x hx)) (env_get_zip_none x ps vals (h1 x hx))

/-! ## Tag tests on a variable -/

theorem specR_tagIteV {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (h : EIdx) (k : Nat) (hk : k < 16)
    (hk4 : k ≠ 4) (hh : Γ.get x = some (Enc.idxW h))
    (h1 : h.tag = UInt32.ofNat k → SpecR (Inv C s Γ M D) c1 s m R)
    (h2 : h.tag ≠ UInt32.ofNat k → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite (tagIsE x k) c1 c2) s m R := by
  obtain ⟨w, hw, hiff⟩ := sev_tagIs Γ x h hh k hk hk4
  exact specR_ifI _ w hw (fun e => h1 (hiff.mp e)) (fun e => h2 (fun t => (hiff.mpr t) e))

/-! ## The `whnf`, `infer` and `inferIO` entry points -/

def kLocals : List MlS := [lEo, lX, lY, lZ, lSv]

/-- `whnf`'s shortcut: `sort`, `fvar`, `lam`, `forallE` and `lit` are their own head normal forms. -/
def stuckChain (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (tagIsE kE 2) (.return (vv kE)) (.ite (tagIsE kE 1) (.return (vv kE)) (.ite (tagIsE kE 5) (.return (vv kE))
    (.ite (tagIsE kE 6) (.return (vv kE)) (.ite (tagIsE kE 8) (.return (vv kE)) rest))))

def fuelCheck (rest : ProgHOL 64) : ProgHOL 64 := .ite (.cmp .equal (vv kFu) (.const 0)) hang rest

def whnfE (C : Ctx) (fB : MlS) : ProgHOL 64 := prologue kLocals (fuelCheck (stuckChain (memoEntry C .whnf fB)))
def inferE (C : Ctx) (fB : MlS) : ProgHOL 64 := prologue kLocals (fuelCheck (memoEntry C .infer fB))
def inferIOE (C : Ctx) (fB : MlS) : ProgHOL 64 := prologue kLocals (fuelCheck (memoEntry C .inferIO fB))

theorem kParams_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kLocals → (ctxEnv C ++ kParams.zip vals).get x = none :=
  params_none C kLocals kParams vals (by decide) (by decide)

theorem pre_kparams {C : Ctx} {s : AState} {u : PState σ} (hu : SR C s u) (v1 v2 v3 : BitVec 64)
    (h1 : u.locals.lookup kFu = some (.val (.word v1))) (h2 : u.locals.lookup kD = some (.val (.word v2)))
    (h3 : u.locals.lookup kE = some (.val (.word v3))) : Pre C s (kParams.zip [v1, v2, v3]) u :=
  pre_of_lookups hu kParams [v1, v2, v3] rfl (fun i hi => by
    have : i < 3 := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3)

/-- The callee form of a spec: from any entry state with the parameters bound. -/
def CalleeSpec (C : Ctx) (B : ProgHOL 64) (s : AState) (vals : List (BitVec 64)) {α : Type} (m : AM α)
    (R : α → BitVec 64 → AState → PState σ → Prop) : Prop :=
  ∀ u : PState σ, SR C s u → (∀ i (hi : i < kParams.length), u.locals.lookup kParams[i] =
    some (.val (.word (vals[i]?.getD 0)))) → SpecR (· = u) B s m R

theorem specR_of_pre {α : Type} {C : Ctx} {s : AState} {Γ : Env} {B : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (u : PState σ) (hu : Pre C s Γ u)
    (h : SpecR (Pre C s Γ) B s m R) : SpecR (· = u) B s m R := by
  intro t ht; subst ht; exact h t hu

/-- A memoized entry at fuel `n + 1`, as a callee. -/
theorem entry_succ {C : Ctx} (hok : CtxOK C) (k : ModeKE)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (fB : MlS) (B : ProgHOL 64) (hcB : C.code.lookup fB = some (kParams.map (fun p => (p, ShapeHOL.one)), B, .one))
    (setOp : EIdx → EIdx → AM Unit) (hset : ∀ e r s, setOp e r s = .ok ((), modeSetS k s e r))
    {s : AState} (n d : Nat) (hn : n + 1 < 2 ^ 64) (e : EIdx) (body : AM EIdx)
    (hbody : ∀ u : PState σ, SR C s u → u.locals.lookup kFu = some (.val (.word (BitVec.ofNat 64 n))) →
      u.locals.lookup kD = some (.val (.word (BitVec.ofNat 64 d))) →
      u.locals.lookup kE = some (.val (.word (Enc.idxW e))) → SpecR (· = u) B s body (PostK C)) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d, Enc.idxW e]))
      (prologue kLocals (fuelCheck (memoEntry C k.toK fB))) s (memoTwin k e body setOp) (PostK C) := by
  refine specR_prologue (postK_locals C) (kParams_none C _) ?_
  have hne : BitVec.ofNat 64 (n + 1) ≠ 0 := Ex.ofNat_ne_zero (n + 1) (by omega) hn
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, kParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  exact memoEntry_spec hok k hcodeG hcodeP hcodeS hcodeI fB B hcB setOp hset n d e body hbody
    (by simp +decide [Env.get, kParams, ctxEnv]) (by simp +decide [Env.get, kParams, ctxEnv])
    (by simp +decide [Env.get, kParams, ctxEnv]) (by simp +decide [Env.get, kParams, ctxEnv]) (by decide)

/-- Any entry at fuel `0` hangs. -/
theorem entry_zero {α : Type} {C : Ctx} {s : AState} (vs : List (BitVec 64)) (core : ProgHOL 64) (m : AM α)
    (R : α → BitVec 64 → AState → PState σ → Prop)
    (hR : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)), R a w s' st → R a w s' { st with locals := L })
    (d e : BitVec 64) :
    SpecR (σ := σ) (Pre C s (kParams.zip [0, d, e])) (prologue kLocals (fuelCheck core)) s m R := by
  refine specR_prologue hR (kParams_none C _) ?_
  exact specR_ifI _ 1 (by simp +decide [sev, Env.get, kParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => specR_hangI) (fun h => absurd h (by decide))

theorem uofNat_eq (k : Nat) : UInt32.ofNat k = (UInt32.ofNat k) := rfl

/-- `whnf` at fuel `n + 1`, as a callee: the stuck-tag shortcut, then the memoized entry. -/
theorem whnf_succ {C : Ctx} (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (fB : MlS) (B : ProgHOL 64) (hcB : C.code.lookup fB = some (kParams.map (fun p => (p, ShapeHOL.one)), B, .one))
    {s : AState} (n d : Nat) (hn : n + 1 < 2 ^ 64) (e : EIdx) (body : AM EIdx)
    (hbody : ∀ u : PState σ, SR C s u → u.locals.lookup kFu = some (.val (.word (BitVec.ofNat 64 n))) →
      u.locals.lookup kD = some (.val (.word (BitVec.ofNat 64 d))) →
      u.locals.lookup kE = some (.val (.word (Enc.idxW e))) → SpecR (· = u) B s body (PostK C)) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d, Enc.idxW e]))
      (whnfE C fB) s (if whnfStuckTag e then pure e else memoTwin .whnf e body whnfSet) (PostK C) := by
  refine specR_prologue (postK_locals C) (kParams_none C _) ?_
  have hne : BitVec.ofNat 64 (n + 1) ≠ 0 := Ex.ofNat_ne_zero (n + 1) (by omega) hn
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, kParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hE : (ctxEnv C ++ kParams.zip [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d, Enc.idxW e]).get kE =
      some (Enc.idxW e) := by simp +decide [Env.get, kParams, ctxEnv]
  have stuckRet : SpecR (σ := σ) (Inv C s (ctxEnv C ++ kParams.zip [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d,
      Enc.idxW e]) [] (ctxLocals ++ kLocals)) (.return (vv kE)) s (pure e) (PostK C) :=
    specR_returnI _ (Enc.idxW e) (by simp [sev_vv, hE]) (fun t ht => ⟨C.H, List.prefix_refl _, rfl,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  unfold stuckChain
  refine specR_tagIteV kE e 2 (by decide) (by decide) hE (fun ht => ?_) (fun h2 => ?_)
  · have : whnfStuckTag e = true := by simp [whnfStuckTag, ht, ETag.sort]
    rw [if_pos this]; exact stuckRet
  refine specR_tagIteV kE e 1 (by decide) (by decide) hE (fun ht => ?_) (fun h1 => ?_)
  · have : whnfStuckTag e = true := by simp [whnfStuckTag, ht, ETag.sort, ETag.fvar]
    rw [if_pos this]; exact stuckRet
  refine specR_tagIteV kE e 5 (by decide) (by decide) hE (fun ht => ?_) (fun h5 => ?_)
  · have : whnfStuckTag e = true := by simp [whnfStuckTag, ht, ETag.sort, ETag.fvar, ETag.lam]
    rw [if_pos this]; exact stuckRet
  refine specR_tagIteV kE e 6 (by decide) (by decide) hE (fun ht => ?_) (fun h6 => ?_)
  · have : whnfStuckTag e = true := by simp [whnfStuckTag, ht, ETag.sort, ETag.fvar, ETag.lam, ETag.forallE]
    rw [if_pos this]; exact stuckRet
  refine specR_tagIteV kE e 8 (by decide) (by decide) hE (fun ht => ?_) (fun h8 => ?_)
  · have : whnfStuckTag e = true := by
      simp [whnfStuckTag, ht, ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit]
    rw [if_pos this]; exact stuckRet
  have : whnfStuckTag e = false := by
    simp only [whnfStuckTag, ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit, beq_iff_eq]
    rw [if_neg (by simpa using h2), if_neg (by simpa using h1), if_neg (by simpa using h5),
      if_neg (by simpa using h6), if_neg (by simpa using h8)]
  rw [if_neg (by rw [this]; decide)]
  exact memoEntry_spec hok .whnf hcodeG hcodeP hcodeS hcodeI fB B hcB whnfSet (fun _ _ _ => rfl) n d e body hbody
    (by simp +decide [Env.get, kParams, ctxEnv]) (by simp +decide [Env.get, kParams, ctxEnv]) hE
    (by simp +decide [Env.get, kParams, ctxEnv]) (by decide)

/-! ## The `defeq` and `defeqE` entry points -/

/-- The post of a Core entry returning a verdict. -/
def PostB (C : Ctx) (a : Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = boolW a ∧ SR (ctxH C H') s' st

theorem postB_locals (C : Ctx) : ∀ (a : Bool) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostB C a w s' st → PostB C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

/-- The twin's memoized `defeq` entry. -/
def defeqTwin (a b : EIdx) (body : AM Bool) : AM Bool :=
  (fun st => .ok (st.caches.defeqC[(a, b)]?, st) : AM (Option Bool)) >>= fun r =>
    match r with
    | some x => pure x
    | none => body >>= fun x => defeqSet a b x >>= fun _ => pure x

/-- The twin's eager slot. -/
def defeqETwin (eager : Bool) (a b : EIdx) (body : AM Bool) : AM Bool :=
  enterEager eager >>= fun saved =>
  (fun st => .ok (st.caches.defeqC[(a, b)]?, st) : AM (Option Bool)) >>= fun r =>
    match r with
    | some x => leaveEager saved >>= fun _ => pure x
    | none => body >>= fun x => defeqSet a b x >>= fun _ => leaveEager saved >>= fun _ => pure x

def callDB (fB : MlS) : ProgHOL 64 →  ProgHOL 64 :=
  .seq (.call (some (some (.local, lY), none)) fB [.op .sub [vv kFu, .const 1], vv kD, vv kA, vv kB])

def defeqCore (C : Ctx) (fB : MlS) : ProgHOL 64 :=
  defeqGetP C lX (vv kA) (vv kB)
    (.ite (.cmp .notEqual (vv lX) (.const 0)) (.return (.op .sub [vv lX, .const 1]))
      (callDB fB (defeqSetP C lZ (vv kA) (vv kB) (vv lY) (.return (vv lY)))))

def defeqECore (C : Ctx) (fB : MlS) : ProgHOL 64 :=
  .seq (enterBlk C lSv) (defeqGetP C lX (vv kA) (vv kB)
    (.ite (.cmp .notEqual (vv lX) (.const 0)) (.seq (leaveBlk (vv lSv)) (.return (.op .sub [vv lX, .const 1])))
      (callDB fB (defeqSetP C lZ (vv kA) (vv kB) (vv lY) (.seq (leaveBlk (vv lSv)) (.return (vv lY)))))))

theorem boolW_add_one_ne (b : Bool) : boolW b + 1 ≠ 0 := by cases b <;> decide

theorem optWB_some_sub (b : Bool) : optWG boolW (some b) - 1 = boolW b := by
  simp only [optWG]; exact BitVec.add_sub_cancel _ _

/-- The body's spec for `defeq`, as a callee. -/
def DBodySpec (C : Ctx) (B : ProgHOL 64) (s : AState) (n d : Nat) (a b : EIdx) (body : AM Bool) : Prop :=
  ∀ u : PState σ, SR C s u → u.locals.lookup kFu = some (.val (.word (BitVec.ofNat 64 n))) →
    u.locals.lookup kD = some (.val (.word (BitVec.ofNat 64 d))) →
    u.locals.lookup kA = some (.val (.word (Enc.idxW a))) →
    u.locals.lookup kB = some (.val (.word (Enc.idxW b))) → SpecR (· = u) B s body (PostB C)

structure DCodes (C : Ctx) (fB : MlS) (B : ProgHOL 64) : Prop where
  g : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  p : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  s : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  i : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)
  b : C.code.lookup fB = some (dParams.map (fun p => (p, ShapeHOL.one)), B, .one)

/-- The memoized `defeq` after the probe's key is known: at any context. -/
theorem defeqMiss {C : Ctx} (hok : CtxOK C) {fB : MlS} {B : ProgHOL 64} (hc : DCodes C fB B)
    {s : AState} {Γ : Env} {D : List MlS} (n d : Nat) (a b : EIdx) (body : AM Bool) {β : Type}
    {k : Bool → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (hbody : DBodySpec (σ := σ) C B s n d a b body)
    (hfu : Γ.get kFu = some (BitVec.ofNat 64 (n + 1))) (hd : Γ.get kD = some (BitVec.ofNat 64 d))
    (ha : Γ.get kA = some (Enc.idxW a)) (hb : Γ.get kB = some (Enc.idxW b)) (hkb : Γ.get lKb = some C.KB)
    (hD : lEo ∈ D ∧ lY ∈ D ∧ lZ ∈ D)
    (hk : ∀ x s' H' w, C.H <+: H' → SpecR (Inv (ctxH C H') (defeqSetS s' a b x)
      ((lZ, w) :: (lEo, C.eo) :: (lY, boolW x) :: Γ) [] D) rest (defeqSetS s' a b x) (k x) R) :
    SpecR (Inv C s Γ [] D) (callDB fB (defeqSetP C lZ (vv kA) (vv kB) (vv lY) rest)) s
      (body >>= fun x => defeqSet a b x >>= fun _ => k x) R := by
  obtain ⟨heo, hy, hz⟩ := hD
  refine specR_callNIH lY fB dParams [.op .sub [vv kFu, .const 1], vv kD, vv kA, vv kB] B
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl hy hc.b
    ⟨by simp +decide [sev, Env.get, hfu]; exact Ex.ofNat_succ_sub_one n, by simp +decide [sev, Env.get, hd],
      by simp +decide [sev, Env.get, ha], by simp +decide [sev, Env.get, hb], trivial⟩
    (PostB C) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => hbody u hu (hlk 0 (by decide)) (hlk 1 (by decide)) (hlk 2 (by decide)) (hlk 3 (by decide)))
    (fun x w s' H' hp hw => ?_)
  subst hw
  refine specR_defeqSetI (C := ctxH C H') (ctxOK_H hok H') hc.s hc.i lZ (vv kA) (vv kB) (vv lY) a b x hz heo
    (by simp +decide [sev, Env.get, ha]) (by simp +decide [sev, Env.get, hb]) (by simp +decide [sev, Env.get])
    (by simp +decide [Env.get, hkb]; rfl) (fun w => ?_)
  exact hk x s' H' w hp

theorem dParams_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kLocals → (ctxEnv C ++ dParams.zip vals).get x = none :=
  params_none C kLocals dParams vals (by decide) (by decide)

theorem dcodes_saved {C : Ctx} {fB : MlS} {B : ProgHOL 64} (hc : DCodes C fB B) (sv : Option ModeMemos) :
    DCodes { C with saved := sv } fB B := ⟨hc.g, hc.p, hc.s, hc.i, hc.b⟩

theorem dcodes_H {C : Ctx} {fB : MlS} {B : ProgHOL 64} (hc : DCodes C fB B) (H : List (BitVec 64)) :
    DCodes (ctxH C H) fB B := ⟨hc.g, hc.p, hc.s, hc.i, hc.b⟩

theorem ctxOK_saved {C : Ctx} (hok : CtxOK C) (sv : Option ModeMemos) : CtxOK { C with saved := sv } := by
  cases hok; constructor <;> assumption

theorem ctx_back {C : Ctx} (hsv : C.saved = none) (mm : ModeMemos) (H : List (BitVec 64)) :
    { ctxH { C with saved := some mm } H with saved := none } = ctxH C H := by
  cases C; cases hsv; rfl

theorem defeq_succ {C : Ctx} (hok : CtxOK C) {fB : MlS} {B : ProgHOL 64} (hc : DCodes C fB B)
    {s : AState} (n d : Nat) (hn : n + 1 < 2 ^ 64) (a b : EIdx) (body : AM Bool)
    (hbody : DBodySpec (σ := σ) C B s n d a b body) :
    SpecR (σ := σ) (Pre C s (dParams.zip [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
      (prologue kLocals (fuelCheck (defeqCore C fB))) s (defeqTwin a b body) (PostB C) := by
  refine specR_prologue (postB_locals C) (dParams_none C _) ?_
  have hne : BitVec.ofNat 64 (n + 1) ≠ 0 := Ex.ofNat_ne_zero (n + 1) (by omega) hn
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_defeqGetI hok hc.g hc.p lX (vv kA) (vv kB) a b (by decide) (by decide)
    (by simp +decide [sev, Env.get, dParams, ctxEnv]) (by simp +decide [sev, Env.get, dParams, ctxEnv])
    (by simp +decide [Env.get, dParams, ctxEnv]) (fun r => ?_)
  cases r with
  | some v =>
    refine specR_ifI _ 1
      (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optWG]; exact boolW_add_one_ne v)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_returnI _ (boolW v) (by simp [sev, Env.get]; exact optWB_some_sub v) (fun t ht => ?_)
    exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | none =>
    refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optWG])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine defeqMiss hok hc n d a b body (k := fun x => pure x) hbody
      (by simp +decide [Env.get, dParams, ctxEnv]) (by simp +decide [Env.get, dParams, ctxEnv])
      (by simp +decide [Env.get, dParams, ctxEnv]) (by simp +decide [Env.get, dParams, ctxEnv])
      (by simp +decide [Env.get, dParams, ctxEnv]) (by decide) (fun x s' H' w hp => ?_)
    refine specR_returnI _ (boolW x) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
    exact ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

theorem defeqE_succ {C : Ctx} (hok : CtxOK C) {fB : MlS} {B : ProgHOL 64} (hc : DCodes C fB B)
    {s : AState} (n d : Nat) (hn : n + 1 < 2 ^ 64) (a b : EIdx) (body : AM Bool)
    (hbN : C.saved = none → DBodySpec (σ := σ) { C with saved := some s.caches.modeMemos } B (eagerIn s) n d a b body)
    (hbS : C.saved.isSome = true → DBodySpec (σ := σ) C B s n d a b body) :
    SpecR (σ := σ) (Pre C s (dParams.zip [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
      (prologue kLocals (fuelCheck (defeqECore C fB))) s (defeqETwin C.side a b body) (PostB C) := by
  refine specR_prologue (postB_locals C) (dParams_none C _) ?_
  have hne : BitVec.ofNat 64 (n + 1) ≠ 0 := Ex.ofNat_ne_zero (n + 1) (by omega) hn
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  unfold defeqECore defeqETwin
  rcases hsv : C.saved with _ | mm0
  · -- plain: enter the eager tower
    have hside : C.side = false := by simp [Ctx.side, hsv]
    rw [hside]
    refine specR_enterPlainI hok hsv lSv (by decide) (by decide) ?_
    have hok' := ctxOK_saved hok (some s.caches.modeMemos)
    have hc' := dcodes_saved hc (some s.caches.modeMemos)
    refine specR_defeqGetI hok' hc'.g hc'.p lX (vv kA) (vv kB) a b (by decide) (by decide)
      (by simp +decide [sev, Env.get, dParams, ctxEnv]) (by simp +decide [sev, Env.get, dParams, ctxEnv])
      (by simp +decide [Env.get, dParams, ctxEnv]) (fun r => ?_)
    cases r with
    | some v =>
      refine specR_ifI _ 1
        (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optWG]; exact boolW_add_one_ne v)
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_leaveSomeI hok' rfl (vv lSv) 1 (by simp +decide [sev, Env.get]) (by decide) ?_
      refine specR_returnI _ (boolW v) (by simp [sev, Env.get]; exact optWB_some_sub v) (fun t ht => ?_)
      refine ⟨C.H, List.prefix_refl _, rfl, ?_⟩
      have e := ctx_back hsv s.caches.modeMemos C.H
      have h1 := sr_of_eq ht.sr rfl rfl rfl rfl (u := emptyLocalsHOLFinite t)
      exact e ▸ h1
    | none =>
      refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optWG])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine defeqMiss hok' hc' n d a b body (hbN hsv)
        (by simp +decide [Env.get, dParams, ctxEnv]) (by simp +decide [Env.get, dParams, ctxEnv])
        (by simp +decide [Env.get, dParams, ctxEnv]) (by simp +decide [Env.get, dParams, ctxEnv])
        (by simp +decide [Env.get, dParams, ctxEnv]) (by decide) (fun x s' H' w hp => ?_)
      refine specR_leaveSomeI (ctxOK_H hok' H') rfl (vv lSv) 1 (by simp +decide [sev, Env.get]) (by decide) ?_
      refine specR_returnI _ (boolW x) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
      refine ⟨H', hp, rfl, ?_⟩
      have e := ctx_back hsv s.caches.modeMemos H'
      have h1 := sr_of_eq ht.sr rfl rfl rfl rfl (u := emptyLocalsHOLFinite t)
      exact e ▸ h1
  · -- eager already: nothing moves
    have hside : C.side = true := by simp [Ctx.side, hsv]
    rw [hside]
    refine specR_enterEagerI hok hsv lSv (by decide) (by decide) ?_
    refine specR_defeqGetI hok hc.g hc.p lX (vv kA) (vv kB) a b (by decide) (by decide)
      (by simp +decide [sev, Env.get, dParams, ctxEnv]) (by simp +decide [sev, Env.get, dParams, ctxEnv])
      (by simp +decide [Env.get, dParams, ctxEnv]) (fun r => ?_)
    cases r with
    | some v =>
      refine specR_ifI _ 1
        (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optWG]; exact boolW_add_one_ne v)
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_leaveNoneI (vv lSv) (by simp +decide [sev, Env.get]) ?_
      refine specR_returnI _ (boolW v) (by simp [sev, Env.get]; exact optWB_some_sub v) (fun t ht => ?_)
      exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
    | none =>
      refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optWG])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine defeqMiss hok hc n d a b body (hbS (by simp [hsv]))
        (by simp +decide [Env.get, dParams, ctxEnv]) (by simp +decide [Env.get, dParams, ctxEnv])
        (by simp +decide [Env.get, dParams, ctxEnv]) (by simp +decide [Env.get, dParams, ctxEnv])
        (by simp +decide [Env.get, dParams, ctxEnv]) (by decide) (fun x s' H' w hp => ?_)
      refine specR_leaveNoneI (vv lSv) (by simp +decide [sev, Env.get]) ?_
      refine specR_returnI _ (boolW x) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
      exact ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.Knot
