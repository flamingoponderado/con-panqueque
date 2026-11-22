import ConPanqueque.T.Ex.AppArgs
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `mkAppN`, `mkAppNFrom`

Apply a head to the arguments of a block, from index `i` on: `mka(f, p, i, n)`. One Pancake function
refines both twins (the list one at `xs.drop i`, the array one at `args`, `i`).
-/

namespace ConPanqueque.T.ExK
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM

def fMka := ofString "mkAppN"
def pF := ofString "mf"
def pP := ofString "mp"
def pI := ofString "mi"
def pN := ofString "mn"

def mkaLocals : List MlS := [lA1, lW, lY]

def mkaCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pI) (vv pN)) (.return (vv pF))
    (.seq (.assign .local lA1 (.load .one (.op .add [vv pP, .shift .lsl (.op .add [vv pI, .const 1]) (.const 3)])))
      (.seq (.call (some (some (.local, lW), none)) fInternApp [vv pF, vv lA1])
        (.seq (.call (some (some (.local, lY), none)) fMka [vv lW, vv pP, .op .add [vv pI, .const 1], vv pN])
          (.return (vv lY)))))

def mkaBody : ProgHOL 64 := prologue mkaLocals mkaCore

section
variable {σ : Type}

theorem params_noneK (a b c d : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ mkaLocals → (ctxEnv C ++ [(pF, a), (pP, b), (pI, c), (pN, d)]).get x = none := by
  intro x hx
  simp only [mkaLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl <;> rfl

theorem pre4 {C : Ctx} {s : AState} {u : PState σ} (hu : SR C s u) (x y z w : MlS) (vx vy vz vw : BitVec 64)
    (h1 : u.locals.lookup x = some (.val (.word vx))) (h2 : u.locals.lookup y = some (.val (.word vy)))
    (h3 : u.locals.lookup z = some (.val (.word vz))) (h4 : u.locals.lookup w = some (.val (.word vw))) :
    Pre C s [(x, vx), (y, vy), (z, vz), (w, vw)] u := ⟨hu, fun q v hq => by
  simp only [Env.get] at hq
  split at hq
  · rename_i e; subst e; simp at hq; subst hq; exact h1
  · split at hq
    · rename_i e; subst e; simp at hq; subst hq; exact h2
    · split at hq
      · rename_i e; subst e; simp at hq; subst hq; exact h3
      · split at hq
        · rename_i e; subst e; simp at hq; subst hq; exact h4
        · simp at hq⟩

theorem cellA_idx (C : Ctx) (o i : Nat) (hi : i + 1 < 2 ^ 60) :
    cellA C o + BitVec.ofNat 64 (i + 1) <<< (3 : BitVec 64).toNat = cellA C (o + 1 + i) := by
  rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
  simp only [cellA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

theorem cellA_idx' (C : Ctx) (o i : Nat) (hi : i + 1 < 2 ^ 60) :
    cellA C o + (BitVec.ofNat 64 i <<< 3 + 8#64) = cellA C (o + 1 + i) := by
  apply BitVec.eq_of_toNat_eq
  simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The common induction: from index `i`, the walk answers the twin `T i f`. -/
theorem mka_gen (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fMka = some ([(pF, .one), (pP, .one), (pI, .one), (pN, .one)], mkaBody, .one))
    (hcI : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (o : Nat) (xs : List EIdx) (hblk : BlkAt C.H o (xs.map Enc.idxW)) (hn : xs.length < 2 ^ 59)
    (T : Nat → EIdx → AM EIdx)
    (hT0 : ∀ f, T xs.length f = pure f)
    (hT1 : ∀ i f (hi : i < xs.length), T i f = (internAppE f xs[i] >>= fun g => T (i + 1) g)) :
    ∀ k i f s, i + k = xs.length →
      SpecR (Pre (σ := σ) C s [(pF, Enc.idxW f), (pP, cellA C o), (pI, BitVec.ofNat 64 i),
        (pN, BitVec.ofNat 64 xs.length)]) mkaBody s (T i f) (PostE C) := by
  intro k
  induction k with
  | zero =>
    intro i f s hik
    simp only [Nat.add_zero] at hik; subst hik
    refine specR_prologue (postE_locals C) (params_noneK _ _ _ _ C) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    rw [show T xs.length f = pure f from hT0 f]
    exact specR_returnI (vv pF) (Enc.idxW f) (by simp +decide [ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i f s hik
    have hi : i < xs.length := by omega
    refine specR_prologue (postE_locals C) (params_noneK _ _ _ _ C) ?_
    have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 xs.length := fun e =>
      absurd ((word_eq_iff i xs.length (by omega) (by omega)).mp e) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    obtain ⟨hl, hv⟩ := blkAt_get hblk i (by simpa using hi)
    refine specR_heapLoadI lA1 _ (o + 1 + i) hl (by decide)
      (by simp +decide [sev, ctxEnv]; exact cellA_idx' C o i (by omega)) ?_
    rw [show C.H[o + 1 + i]'hl = Enc.idxW xs[i] by rw [hv]; simp]
    rw [show T i f = (internAppE f xs[i] >>= fun g => T (i + 1) g) from hT1 i f hi]
    refine specR_internAppI ra hok hcI lW (vv pF) (vv lA1) f xs[i] (by decide) (by simp +decide [ctxEnv])
      (by simp +decide) (fun g s1 => ?_)
    refine specR_congr (m' := T (i + 1) g >>= fun a => pure a) (by simp) ?_
    refine specR_call4IM lY fMka pF pP pI pN (by decide) _ _ _ _ mkaBody (Enc.idxW g) (cellA C o)
      (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 xs.length) (by decide) hcode (by simp +decide)
      (by simp +decide [ctxEnv]) (by simp +decide [sev, ctxEnv]; exact word_add1_eq i) (by simp +decide [ctxEnv])
      (PostE C) (fun _ _ _ _ hp => hp.2)
      (fun u hu _ h1 h2 h3 h4 w hw => by subst hw; exact ih (i + 1) g s1 (by omega) _ (pre4 hu _ _ _ _ _ _ _ _ h1 h2 h3 h4))
      (fun a w s' st hp => ?_)
    obtain ⟨rfl, _⟩ := hp
    exact specR_returnI (vv lY) (Enc.idxW a) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- `mkAppN f (xs.drop i)`. -/
theorem mkAppN_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fMka = some ([(pF, .one), (pP, .one), (pI, .one), (pN, .one)], mkaBody, .one))
    (hcI : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (o : Nat) (xs : List EIdx) (hblk : BlkAt C.H o (xs.map Enc.idxW)) (hn : xs.length < 2 ^ 59)
    (i : Nat) (hi : i ≤ xs.length) (f : EIdx) (s : AState) :
    SpecR (Pre (σ := σ) C s [(pF, Enc.idxW f), (pP, cellA C o), (pI, BitVec.ofNat 64 i),
      (pN, BitVec.ofNat 64 xs.length)]) mkaBody s (mkAppN f (xs.drop i)) (PostE C) :=
  mka_gen ra C hok hcode hcI o xs hblk hn (fun i f => mkAppN f (xs.drop i))
    (fun f => by simp [mkAppN])
    (fun i f hi => by rw [List.drop_eq_getElem_cons hi]; rfl)
    (xs.length - i) i f s (by omega)

/-- `mkAppNFrom f args i`. -/
theorem mkAppNFrom_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fMka = some ([(pF, .one), (pP, .one), (pI, .one), (pN, .one)], mkaBody, .one))
    (hcI : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (o : Nat) (args : Array EIdx) (hblk : BlkAt C.H o (args.toList.map Enc.idxW)) (hn : args.size < 2 ^ 59)
    (i : Nat) (hi : i ≤ args.size) (f : EIdx) (s : AState) :
    SpecR (Pre (σ := σ) C s [(pF, Enc.idxW f), (pP, cellA C o), (pI, BitVec.ofNat 64 i),
      (pN, BitVec.ofNat 64 args.toList.length)]) mkaBody s (mkAppNFrom f args i) (PostE C) :=
  mka_gen ra C hok hcode hcI o args.toList hblk (by simpa using hn) (fun i f => mkAppNFrom f args i)
    (fun f => by rw [mkAppNFrom]; simp)
    (fun i f hi => by rw [mkAppNFrom]; simp at hi; simp [hi])
    (args.toList.length - i) i f s (by simp; omega)

end

end ConPanqueque.T.ExK
