import ConPanqueque.Front.IndLineB
import ConPanqueque.Front.IndTwin

/-! # The inductive line: the stored constants as robust facts

From the words an `allocWr` wrote, the `CIE` encodings of the block's type former, constructors and
recursor (with its rules), robust above a bound `X` below every cell they read. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

set_option autoImplicit false

macro "envg" : tactic => `(tactic| simp +decide only [ConPanqueque.T.Env.get_cons, ite_false, ite_true])

theorem cve_keep {X : Nat} {C : Ctx} {H H' : List (BitVec 64)} (hk : KeepsAbove X H H') {o ol : Nat}
    {cv : IConstantVal} (hX : X ≤ o) (hXl : X ≤ ol)
    (h1 : H[o + 1]? = some (Enc.idxW cv.name)) (h2 : H[o + 2]? = some (cellA C ol))
    (h3 : H[o + 3]? = some (Enc.idxW cv.type)) (hb : BlkAt H ol (cv.levelParams.map Enc.idxW)) :
    CVE C.HB H' (o + 1) cv :=
  ⟨keep_get hk (by omega) h1, ⟨_, keep_get hk (by omega) h2, ol, rfl, blkAt_keep hk hb hXl⟩,
    by rw [show o + 1 + 2 = o + 3 by omega]; exact keep_get hk (by omega) h3⟩

theorem natE_keep {X : Nat} {H H' : List (BitVec 64)} (hk : KeepsAbove X H H') {i n : Nat} (hX : X ≤ i)
    (h : H[i]? = some (BitVec.ofNat 64 n)) (hn : n < 2 ^ 63) : NatE H' i n :=
  ⟨keep_get hk hX h, hn⟩

/-- An empty block at `oe`. -/
theorem enlist_nil {X : Nat} {C : Ctx} {H H' : List (BitVec 64)} (hk : KeepsAbove X H H') {oe : Nat}
    (hX : X ≤ oe) (h : H[oe]? = some 0) : ENList C.HB H' (cellA C oe) ([] : List NIdx) :=
  ⟨oe, rfl, ⟨by simpa using keep_get hk hX h, fun i hi => absurd hi (by simp)⟩⟩

/-- The type former's record `[3, name, lps, type, 0, ∅, 0, 0, ∅, 0]`. -/
theorem rcie_ind (X : Nat) (C : Ctx) (H : List (BitVec 64)) (o ol oe : Nat) (cv : IConstantVal)
    (hX : X ≤ o) (hXl : X ≤ ol) (hXe : X ≤ oe)
    (hr : ∀ i (hi : i < 10), H[o + i]? = some ([BitVec.ofNat 64 3, Enc.idxW cv.name, cellA C ol, Enc.idxW cv.type,
      0, cellA C oe, 0, 0, cellA C oe, 0][i]'(by simpa using hi)))
    (hb : BlkAt H ol (cv.levelParams.map Enc.idxW)) (he : H[oe]? = some 0) :
    RCIE X C H o (.indInfo cv {}) := by
  intro H' hk
  have g : ∀ i (hi : i < 10), H'[o + i]? = some ([BitVec.ofNat 64 3, Enc.idxW cv.name, cellA C ol, Enc.idxW cv.type,
      0, cellA C oe, 0, 0, cellA C oe, 0][i]'(by simpa using hi)) := fun i hi => keep_get hk (by omega) (hr i hi)
  refine ⟨cve_keep (cv := cv) hk hX hXl (by simpa using hr 1 (by decide)) (by simpa using hr 2 (by decide))
    (by simpa using hr 3 (by decide)) hb, ?_⟩
  refine ⟨by simpa using g 0 (by decide), by simpa [boolW] using g 4 (by decide),
    ⟨_, by simpa using g 5 (by decide), enlist_nil hk hXe he⟩, ⟨by simpa using g 6 (by decide), by decide⟩,
    ⟨by simpa using g 7 (by decide), by decide⟩, ⟨_, by simpa using g 8 (by decide), enlist_nil hk hXe he⟩,
    by simpa [boolW] using g 9 (by decide)⟩

/-- A constructor's record `[4, name, lps, type, np, nf, T]`. -/
theorem rcie_ctor (X : Nat) (C : Ctx) (H : List (BitVec 64)) (o ol : Nat) (cv : IConstantVal) (np nf : Nat)
    (T : NIdx) (hX : X ≤ o) (hXl : X ≤ ol) (hnp : np < 2 ^ 63) (hnf : nf < 2 ^ 63)
    (hr : ∀ i (hi : i < 7), H[o + i]? = some ([BitVec.ofNat 64 4, Enc.idxW cv.name, cellA C ol, Enc.idxW cv.type,
      BitVec.ofNat 64 np, BitVec.ofNat 64 nf, Enc.idxW T][i]'(by simpa using hi)))
    (hb : BlkAt H ol (cv.levelParams.map Enc.idxW)) :
    RCIE X C H o (.ctorInfo cv np nf T) := by
  intro H' hk
  have g : ∀ i (hi : i < 7), H'[o + i]? = some ([BitVec.ofNat 64 4, Enc.idxW cv.name, cellA C ol, Enc.idxW cv.type,
      BitVec.ofNat 64 np, BitVec.ofNat 64 nf, Enc.idxW T][i]'(by simpa using hi)) :=
    fun i hi => keep_get hk (by omega) (hr i hi)
  refine ⟨cve_keep (cv := cv) hk hX hXl (by simpa using hr 1 (by decide)) (by simpa using hr 2 (by decide))
    (by simpa using hr 3 (by decide)) hb, ?_⟩
  exact ⟨by simpa using g 0 (by decide), ⟨by simpa using g 4 (by decide), hnp⟩, ⟨by simpa using g 5 (by decide), hnf⟩,
    by simpa using g 6 (by decide)⟩

/-- A rule's record `[ctor, nfields, 0, 0, 0, rhs]`, robust. -/
def RRule (X : Nat) (C : Ctx) (H : List (BitVec 64)) (o : Nat) (ru : IRecRule) : Prop :=
  ∀ H', KeepsAbove X H H' → RuleE C.HB H' o ru

theorem rrule_of (X : Nat) (C : Ctx) (H : List (BitVec 64)) (o : Nat) (ru : IRecRule) (hX : X ≤ o)
    (hf : ru.fire = .plain) (hn : ru.nfields < 2 ^ 63)
    (hr : ∀ i (hi : i < 6), H[o + i]? = some ([Enc.idxW ru.ctor, BitVec.ofNat 64 ru.nfields, 0, 0, 0,
      Enc.idxW ru.rhs][i]'(by simpa using hi))) : RRule X C H o ru := by
  intro H' hk
  have g : ∀ i (hi : i < 6), H'[o + i]? = some ([Enc.idxW ru.ctor, BitVec.ofNat 64 ru.nfields, 0, 0, 0,
      Enc.idxW ru.rhs][i]'(by simpa using hi)) := fun i hi => keep_get hk (by omega) (hr i hi)
  refine ⟨by simpa using g 0 (by decide), ⟨by simpa using g 1 (by decide), hn⟩, ?_, by simpa using g 5 (by decide)⟩
  rw [hf]; show H'[o + 2]? = some 0; simpa using g 2 (by decide)

theorem rrule_keep {X : Nat} {C : Ctx} {H H' : List (BitVec 64)} {o : Nat} {ru : IRecRule}
    (h : RRule X C H o ru) (hk : KeepsAbove X H H') : RRule X C H' o ru :=
  fun H'' hk' => h H'' (keepsAbove_trans hk hk')

/-- A recursor's record `[5, name, lps, type, mi, rp, k, rules]`, its rules block at `orb` (`[n, ptrs]`). -/
theorem rcie_rec (X : Nat) (C : Ctx) (H : List (BitVec 64)) (o ol orb : Nat) (cv : IConstantVal) (mi rp : Nat)
    (k : Bool) (rules : List IRecRule) (ors : List Nat) (hX : X ≤ o) (hXl : X ≤ ol) (hXr : X ≤ orb)
    (hmi : mi < 2 ^ 63) (hrp : rp < 2 ^ 63)
    (hr : ∀ i (hi : i < 8), H[o + i]? = some ([BitVec.ofNat 64 5, Enc.idxW cv.name, cellA C ol, Enc.idxW cv.type,
      BitVec.ofNat 64 mi, BitVec.ofNat 64 rp, boolW k, cellA C orb][i]'(by simpa using hi)))
    (hb : BlkAt H ol (cv.levelParams.map Enc.idxW)) (hlo : ors.length = rules.length)
    (hrb : BlkAt H orb (ors.map (cellA C))) (hru : ∀ i (hi : i < rules.length) (ho : i < ors.length),
      RRule X C H ors[i] rules[i]) :
    RCIE X C H o (.recInfo cv mi rp k rules) := by
  intro H' hk
  have g : ∀ i (hi : i < 8), H'[o + i]? = some ([BitVec.ofNat 64 5, Enc.idxW cv.name, cellA C ol, Enc.idxW cv.type,
      BitVec.ofNat 64 mi, BitVec.ofNat 64 rp, boolW k, cellA C orb][i]'(by simpa using hi)) :=
    fun i hi => keep_get hk (by omega) (hr i hi)
  refine ⟨cve_keep (cv := cv) hk hX hXl (by simpa using hr 1 (by decide)) (by simpa using hr 2 (by decide))
    (by simpa using hr 3 (by decide)) hb, ?_⟩
  refine ⟨by simpa using g 0 (by decide), ⟨by simpa using g 4 (by decide), hmi⟩, ⟨by simpa using g 5 (by decide), hrp⟩,
    by simpa using g 6 (by decide), _, by simpa [cellA] using g 7 (by decide), orb, rfl, ?_, fun i hi => ?_⟩
  · have := (blkAt_keep hk hrb hXr).1; simpa [hlo] using this
  · have hio : i < ors.length := by omega
    refine ⟨ors[i], ?_, hru i hi hio H' hk⟩
    have := (blkAt_keep hk hrb hXr).2 i (by simpa using hio)
    simpa [cellA] using this

/-- The block's pointer block and records give `IndBlk`. -/
theorem indBlk_of {X : Nat} {C : Ctx} {H : List (BitVec 64)} {ob : Nat} {blk : List IConstantInfo} {os : List Nat}
    (hl : os.length = blk.length) (hb : BlkAt H ob (os.map (cellA C)))
    (hc : ∀ i (hi : i < blk.length) (ho : i < os.length), RCIE X C H os[i] blk[i])
    (H' : List (BitVec 64)) (hk : KeepsAbove X H H') (hob : X ≤ ob) : T.Ind.IndBlk C H' ob blk :=
  ⟨os, hl, blkAt_keep hk hb hob, fun i hi ho => hc i hi ho H' hk⟩

end ConPanqueque.Front
