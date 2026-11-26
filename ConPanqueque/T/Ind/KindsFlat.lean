import ConPanqueque.T.Ind.Seeds

/-!
# The positivity walk's field kinds are flat (else hang)

`kf1Body`: a kinds block (`kindW` words) has no `inProgress`/`nested` word (`w &&& 3 = 3`); `kf2Body`: every
constructor output of a member; `kf3Body`: every member.  The answer gates `blockNestedBit = false`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

theorem kindW_and3 (k : NestFieldKind) : (kindW k &&& 3#64 = 3#64) ↔ k.flat = false := by
  have key : ∀ t r : Nat, r < 4 → BitVec.ofNat 64 (4 * t + r) &&& 3#64 = BitVec.ofNat 64 r := by
    intro t r hr
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (3 : Nat) % 2 ^ 64 = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  cases k with
  | ordinary => simp [kindW, NestFieldKind.flat]
  | recursive t => simp only [kindW, NestFieldKind.flat, key t 1 (by omega)]; decide
  | reflexive t => simp only [kindW, NestFieldKind.flat, key t 2 (by omega)]; decide
  | inProgress => simp [kindW, NestFieldKind.flat]
  | nested b => cases b <;> simp [kindW, NestFieldKind.flat] <;> decide

def kf1B := ofString "kf1_b"
def kf1I := ofString "kf1_i"
def kf1N := ofString "kf1_n"
def kf1W := ofString "kf1_w"
def kf1R := ofString "kf1_r"
def fKf1 := ofString "kindsFlat"

def kf1Params : List MlS := [kf1B, kf1I, kf1N]
def kf1Locals : List MlS := [kf1W, kf1R]

def kf1Body : ProgHOL 64 := prologue kf1Locals
  (.ite (.cmp .lower (vv kf1I) (vv kf1N))
    (.seq (.assign .local kf1W (.load .one (.op .add [vv kf1B, .op .add [.panop .mul [vv kf1I, .const 8], .const 8]])))
    (.ite (.cmp .equal (.op .and [vv kf1W, .const 3]) (.const 3)) hang
    (.seq (.call (some (some (.local, kf1R), none)) fKf1 [vv kf1B, .op .add [vv kf1I, .const 1], vv kf1N])
      (.return (.const 0)))))
    (.return (.const 0)))

def kf2B := ofString "kf2_b"
def kf2I := ofString "kf2_i"
def kf2N := ofString "kf2_n"
def kf2X := ofString "kf2_x"
def kf2K := ofString "kf2_k"
def kf2L := ofString "kf2_l"
def kf2R := ofString "kf2_r"
def fKf2 := ofString "outsFlat"

def kf2Params : List MlS := [kf2B, kf2I, kf2N]
def kf2Locals : List MlS := [kf2X, kf2K, kf2L, kf2R]

def kf2Body : ProgHOL 64 := prologue kf2Locals
  (.ite (.cmp .lower (vv kf2I) (vv kf2N))
    (.seq (.assign .local kf2X (.load .one (.op .add [vv kf2B, .op .add [.panop .mul [vv kf2I, .const 8], .const 8]])))
    (.seq (.assign .local kf2K (.load .one (vv kf2X)))
    (.seq (.assign .local kf2L (.load .one (vv kf2K)))
    (.seq (.call (some (some (.local, kf2R), none)) fKf1 [vv kf2K, .const 0, vv kf2L])
    (.seq (.call (some (some (.local, kf2R), none)) fKf2 [vv kf2B, .op .add [vv kf2I, .const 1], vv kf2N])
      (.return (.const 0)))))))
    (.return (.const 0)))

def kf3B := ofString "kf3_b"
def kf3I := ofString "kf3_i"
def kf3N := ofString "kf3_n"
def kf3X := ofString "kf3_x"
def kf3K := ofString "kf3_k"
def kf3L := ofString "kf3_l"
def kf3R := ofString "kf3_r"
def fKf3 := ofString "outssFlat"

def kf3Params : List MlS := [kf3B, kf3I, kf3N]
def kf3Locals : List MlS := [kf3X, kf3K, kf3L, kf3R]

def kf3Body : ProgHOL 64 := prologue kf3Locals
  (.ite (.cmp .lower (vv kf3I) (vv kf3N))
    (.seq (.assign .local kf3X (.load .one (.op .add [vv kf3B, .op .add [.panop .mul [vv kf3I, .const 8], .const 8]])))
    (.seq (.assign .local kf3K (vv kf3X))
    (.seq (.assign .local kf3L (.load .one (vv kf3K)))
    (.seq (.call (some (some (.local, kf3R), none)) fKf2 [vv kf3K, .const 0, vv kf3L])
    (.seq (.call (some (some (.local, kf3R), none)) fKf3 [vv kf3B, .op .add [vv kf3I, .const 1], vv kf3N])
      (.return (.const 0)))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- The state unchanged, a fact learned. -/
def PostKF (C : Ctx) (s : AState) (P : Prop) (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ P ∧ SR C s' st

theorem postKF_locals (C : Ctx) (s : AState) (P : Prop) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostKF C s P a w s' st → PostKF C s P a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, h1, h2⟩ => ⟨h0, h1, sr_of_eq h2 rfl rfl rfl rfl⟩

theorem kf1_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kf1Locals → (ctxEnv C ++ kf1Params.zip vals).get x = none :=
  Knot.params_none C kf1Locals kf1Params vals (by decide) (by decide)

/-- A block in the heap is shorter than the heap's capacity. -/
theorem blkAt_len {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} (hH : H.length ≤ C.HN) {o : Nat}
    {xs : List (BitVec 64)} (hb : BlkAt H o xs) : o + xs.length < 2 ^ 61 := by
  have hlay := hok.heapLay
  have h0 := (List.getElem?_eq_some_iff.mp hb.1).1
  rcases Nat.eq_zero_or_pos xs.length with h | h
  · omega
  · have := (List.getElem?_eq_some_iff.mp (hb.2 (xs.length - 1) (by omega))).1; omega

/-- **The kinds from position `i` on are flat** (a non-flat one hangs). -/
theorem kf1_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fKf1 = some (kf1Params.map (fun p => (p, ShapeHOL.one)), kf1Body, .one))
    (ks : List NestFieldKind) (ob : Nat) (hb : BlkAt C.H ob (ks.map kindW)) :
    ∀ f i (s : AState), ks.length - i = f → i ≤ ks.length →
      SpecR (σ := σ) (Pre C s (kf1Params.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 ks.length])) kf1Body s
        (pure ()) (PostKF C s (∀ k ∈ ks.drop i, k.flat = true)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hil : i = ks.length := by omega
    subst hil
    refine specR_prologue (postKF_locals _ _ _) (kf1_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len hok hHN hb
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ks.length ks.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, kf1Params, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hil : i < ks.length := by omega
    refine specR_prologue (postKF_locals _ _ _) (kf1_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len hok hHN hb
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ks.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, kf1Params, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h1 := hb.2 i (by simpa using hil)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := C) kf1W _ (ob + 1 + i) _ h1 (by decide)
      (by simp +decide [sev, Env.get, kf1Params, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    by_cases hfl : ks[i].flat = true
    swap
    · have e := (kindW_and3 ks[i]).mpr (by simpa using hfl)
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    have hne : ¬ (kindW ks[i] &&& 3#64 = 3#64) := fun h => by rw [(kindW_and3 _).mp h] at hfl; exact absurd hfl (by decide)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM kf1R fKf1 kf1Params [vv kf1B, .op .add [vv kf1I, .const 1], vv kf1N] kf1Body
      [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ks.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, kf1Params, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, kf1Params, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, kf1Params, ctxEnv], trivial⟩
      (PostKF C s (∀ k ∈ ks.drop (i + 1), k.flat = true)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kf1Params _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s1 st ⟨hs1, hall, _⟩ => ?_)
    subst s1
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by
      rw [List.drop_eq_getElem_cons hil]
      intro k hk
      rcases List.mem_cons.mp hk with e | e
      · subst e; exact hfl
      · exact hall k e, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem kf2_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kf2Locals → (ctxEnv C ++ kf2Params.zip vals).get x = none :=
  Knot.params_none C kf2Locals kf2Params vals (by decide) (by decide)

/-- **Every constructor output from position `i` on has flat kinds.** -/
theorem kf2_spec (C : Ctx) (hok : CtxOK C)
    (hc1 : C.code.lookup fKf1 = some (kf1Params.map (fun p => (p, ShapeHOL.one)), kf1Body, .one))
    (hc : C.code.lookup fKf2 = some (kf2Params.map (fun p => (p, ShapeHOL.one)), kf2Body, .one))
    (xs : List (List NestFieldKind × EIdx)) (o : Nat) (hx : PRep C C.H o (OutRep C) xs) :
    ∀ f i (s : AState), xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre C s (kf2Params.zip [cellA C o, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length])) kf2Body s
        (pure ()) (PostKF C s (∀ x ∈ xs.drop i, ∀ k ∈ x.1, k.flat = true)) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := hx
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hil : i = xs.length := by omega
    subst hil
    refine specR_prologue (postKF_locals _ _ _) (kf2_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len hok hHN hosb
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, kf2Params, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hil : i < xs.length := by omega
    refine specR_prologue (postKF_locals _ _ _) (kf2_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len hok hHN hosb
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, kf2Params, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : i < os.length := by omega
    have h1 := hosb.2 i (by simpa using hio)
    rw [List.getElem_map] at h1
    obtain ⟨⟨ok, hok1, hkb⟩, -⟩ := hosr i hil hio
    refine UD.specR_heapLoadI' (C := C) kf2X _ (o + 1 + i) _ h1 (by decide)
      (by simp +decide [sev, Env.get, kf2Params, ctxEnv]; exact cellA_mulIdx C o i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := C) kf2K (vv kf2X) os[i] _ hok1 (by decide) (by simp [sev, Env.get_cons]) ?_
    have hkl : C.H[ok]? = some (BitVec.ofNat 64 xs[i].1.length) := by simpa using hkb.1
    refine UD.specR_heapLoadI' (C := C) kf2L (vv kf2K) ok _ hkl (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM kf2R fKf1 kf1Params [vv kf2K, .const 0, vv kf2L] kf1Body
      [cellA C ok, BitVec.ofNat 64 0, BitVec.ofNat 64 xs[i].1.length] (by decide) rfl (by decide) hc1
      ⟨by simp +decide [sev, Env.get_cons], by simp [sev], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostKF C s (∀ k ∈ xs[i].1.drop 0, k.flat = true)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kf1Params _ rfl hlk)
        (kf1_spec C hok hc1 xs[i].1 ok hkb _ 0 s rfl (Nat.zero_le _)))
      (fun _ w s1 st ⟨hs1, hk1, _⟩ => ?_)
    subst s1
    refine specR_callNIM kf2R fKf2 kf2Params [vv kf2B, .op .add [vv kf2I, .const 1], vv kf2N] kf2Body
      [cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, kf2Params, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, kf2Params, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, kf2Params, ctxEnv], trivial⟩
      (PostKF C s (∀ x ∈ xs.drop (i + 1), ∀ k ∈ x.1, k.flat = true)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kf2Params _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s2 st ⟨hs2, hall, _⟩ => ?_)
    subst s2
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by
      rw [List.drop_eq_getElem_cons hil]
      intro x hx
      rcases List.mem_cons.mp hx with e | e
      · subst e; simpa using hk1
      · exact hall x e, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem kf3_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kf3Locals → (ctxEnv C ++ kf3Params.zip vals).get x = none :=
  Knot.params_none C kf3Locals kf3Params vals (by decide) (by decide)

/-- **Every member's outputs from position `i` on have flat kinds.** -/
theorem kf3_spec (C : Ctx) (hok : CtxOK C)
    (hc0 : C.code.lookup fKf1 = some (kf1Params.map (fun p => (p, ShapeHOL.one)), kf1Body, .one))
    (hc1 : C.code.lookup fKf2 = some (kf2Params.map (fun p => (p, ShapeHOL.one)), kf2Body, .one))
    (hc : C.code.lookup fKf3 = some (kf3Params.map (fun p => (p, ShapeHOL.one)), kf3Body, .one))
    (xs : List (List (List NestFieldKind × EIdx))) (o : Nat) (hx : PRep C C.H o (OutsRep C) xs) :
    ∀ f i (s : AState), xs.length - i = f → i ≤ xs.length →
      SpecR (σ := σ) (Pre C s (kf3Params.zip [cellA C o, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length])) kf3Body s
        (pure ()) (PostKF C s (∀ x ∈ xs.drop i, ∀ y ∈ x, ∀ k ∈ y.1, k.flat = true)) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := hx
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hil : i = xs.length := by omega
    subst hil
    refine specR_prologue (postKF_locals _ _ _) (kf3_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len hok hHN hosb
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, kf3Params, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hil : i < xs.length := by omega
    refine specR_prologue (postKF_locals _ _ _) (kf3_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hbl := blkAt_len hok hHN hosb
    simp only [List.length_map] at hbl
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, kf3Params, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : i < os.length := by omega
    have h1 := hosb.2 i (by simpa using hio)
    rw [List.getElem_map] at h1
    have hrep := hosr i hil hio
    refine UD.specR_heapLoadI' (C := C) kf3X _ (o + 1 + i) _ h1 (by decide)
      (by simp +decide [sev, Env.get, kf3Params, ctxEnv]; exact cellA_mulIdx C o i (by omega)) ?_
    refine specR_assignI kf3K _ (cellA C os[i]) (by decide) (by simp [sev, Env.get_cons]) ?_
    obtain ⟨os2, hos2l, hos2b, -⟩ := hrep
    have hkl : C.H[os[i]]? = some (BitVec.ofNat 64 xs[i].length) := by simpa [hos2l] using hos2b.1
    refine UD.specR_heapLoadI' (C := C) kf3L (vv kf3K) os[i] _ hkl (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM kf3R fKf2 kf2Params [vv kf3K, .const 0, vv kf3L] kf2Body
      [cellA C os[i], BitVec.ofNat 64 0, BitVec.ofNat 64 xs[i].length] (by decide) rfl (by decide) hc1
      ⟨by simp +decide [sev, Env.get_cons], by simp [sev], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostKF C s (∀ x ∈ xs[i].drop 0, ∀ k ∈ x.1, k.flat = true)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kf2Params _ rfl hlk)
        (kf2_spec C hok hc0 hc1 xs[i] os[i] (hosr i hil hio) _ 0 s rfl (Nat.zero_le _)))
      (fun _ w s1 st ⟨hs1, hk1, _⟩ => ?_)
    subst s1
    refine specR_callNIM kf3R fKf3 kf3Params [vv kf3B, .op .add [vv kf3I, .const 1], vv kf3N] kf3Body
      [cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, kf3Params, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, kf3Params, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, kf3Params, ctxEnv], trivial⟩
      (PostKF C s (∀ x ∈ xs.drop (i + 1), ∀ y ∈ x, ∀ k ∈ y.1, k.flat = true)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kf3Params _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s2 st ⟨hs2, hall, _⟩ => ?_)
    subst s2
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by
      rw [List.drop_eq_getElem_cons hil]
      intro x hx
      rcases List.mem_cons.mp hx with e | e
      · subst e; simpa using hk1
      · exact hall x e, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
