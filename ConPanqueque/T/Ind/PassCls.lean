import ConPanqueque.T.Ind.ReadBlock
import ConPanqueque.T.Ind.PiBinders
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Pers

/-! # The pass's member classes carry the member's constructors

`checkBlockPass_cls`: every class of an accepting pass that is a member's (`member = some t`) carries that
member's constructors (con-ron's `targetMajorOf`, member arm). -/

open ConRon.Arena

namespace ConPanqueque.T.Ind

set_option autoImplicit false

theorem pure_ok' {α : Type} {a b : α} {s s' : AState} (h : (pure a : AM α) s = .ok (b, s')) : a = b ∧ s = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h

theorem targetMajorOf_member {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {pfvs fvs : List EIdx}
    {mty : EIdx} {s s' : AState} {m : TargetMajor} (h : targetMajorOf mode fe p pfvs fvs mty s = .ok (m, s')) :
    ∀ t, m.member = some t → ∃ ms, p.members[t]? = some ms ∧ m.ctors = ms.ctors := by
  intro t ht
  unfold targetMajorOf at h
  obtain ⟨args, s1, -, h⟩ := bind_ok_inv' h
  obtain ⟨hd, s2, -, h⟩ := bind_ok_inv' h
  split at h
  swap
  · exact absurd h (fun hc => ConRon.Bridge.AM.fail_ok hc)
  obtain ⟨vc, s3, -, h⟩ := bind_ok_inv' h
  have kf : ∀ {β : Type} {e : CheckError} {s0 s1 : AState} {b : β}, (fail e : AM β) s0 = .ok (b, s1) → False :=
    fun hc => ConRon.Bridge.AM.fail_ok hc
  rcases vc with _ | ⟨I, us⟩
  · exact (kf (by simpa [failDanglingE] using h)).elim
  simp only at h
  cases hfi : List.findIdx? (fun x => x == I) p.memberNames with
  | some t' =>
    rw [hfi] at h
    obtain ⟨ms, s4, h4, h⟩ := bind_ok_inv' h
    obtain ⟨hms, -⟩ := ConRon.Bridge.Inductives.unwrapOr_ok h4
    obtain ⟨_, s5, -, h⟩ := bind_ok_inv' h
    split at h
    · obtain ⟨rfl, -⟩ := pure_ok' h
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨ms, hms, rfl⟩
    · exact (kf h).elim
  | none =>
    rw [hfi] at h
    obtain ⟨_, s4, -, h⟩ := bind_ok_inv' h
    split at h
    · exact (kf h).elim
    obtain ⟨tc, s5, -, h⟩ := bind_ok_inv' h
    rcases tc with _ | ⟨nPc, ctors⟩
    · exact (kf h).elim
    simp only at h
    split at h
    · exact (kf h).elim
    obtain ⟨_, s6, -, h⟩ := bind_ok_inv' h
    split at h
    · exact (kf h).elim
    obtain ⟨b, s7, -, h⟩ := bind_ok_inv' h
    split at h
    · obtain ⟨_, s8, -, h⟩ := bind_ok_inv' h
      obtain ⟨_, s9, -, h⟩ := bind_ok_inv' h
      obtain ⟨_, s10, -, h⟩ := bind_ok_inv' h
      obtain ⟨_, s11, -, h⟩ := bind_ok_inv' h
      split at h
      · obtain ⟨_, s12, -, h⟩ := bind_ok_inv' h
        obtain ⟨rfl, -⟩ := pure_ok' h
        simp at ht
      · obtain ⟨_, s12, h12, -⟩ := bind_ok_inv' h
        exact (kf h12).elim
    · obtain ⟨_, s8, h8, -⟩ := bind_ok_inv' h
      exact (kf h8).elim

/-- A member class's constructors. -/
def ClsCtors (p : BlockShape) (m : TargetMajor) : Prop :=
  ∀ t, m.member = some t → ∃ ms, p.members[t]? = some ms ∧ m.ctors = ms.ctors

theorem classMajors_member {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {pfvs : List EIdx} :
    ∀ (keys : List ClassKey) (s s' : AState) (ms : List TargetMajor),
      classMajors mode fe p pfvs keys s = .ok (ms, s') → ∀ m ∈ ms, ClsCtors p m
  | [], s, s', ms, h, m, hm => by
    simp only [classMajors] at h
    obtain ⟨rfl, -⟩ := pure_ok' h
    exact absurd hm List.not_mem_nil
  | key :: keys, s, s', ms, h, m, hm => by
    simp only [classMajors] at h
    obtain ⟨_, s1, -, h⟩ := bind_ok_inv' h
    obtain ⟨_, s2, -, h⟩ := bind_ok_inv' h
    obtain ⟨m0, s3, h3, h⟩ := bind_ok_inv' h
    obtain ⟨_, s4, -, h⟩ := bind_ok_inv' h
    obtain ⟨ms', s5, h5, h⟩ := bind_ok_inv' h
    obtain ⟨rfl, -⟩ := pure_ok' h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact targetMajorOf_member h3
    · exact classMajors_member keys s4 s5 ms' h5 m hm

theorem checkBlockClasses_member {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {params : List EIdx}
    {s s' : AState} {rd : ClassRead} {ms : List TargetMajor}
    (h : checkBlockClasses mode fe p params s = .ok ((rd, ms), s')) : ∀ m ∈ ms, ClsCtors p m := by
  have kf : ∀ {β : Type} {e : CheckError} {s0 s1 : AState} {b : β}, (fail e : AM β) s0 = .ok (b, s1) → False :=
    fun hc => ConRon.Bridge.AM.fail_ok hc
  unfold checkBlockClasses at h
  obtain ⟨o, s1, -, h⟩ := bind_ok_inv' h
  rcases o with _ | rd'
  · exact (kf h).elim
  simp only at h
  obtain ⟨keys, s2, -, h⟩ := bind_ok_inv' h
  obtain ⟨ms', s3, h3, h⟩ := bind_ok_inv' h
  split at h
  · obtain ⟨e, -⟩ := pure_ok' h
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact classMajors_member keys s2 s3 ms' h3
  · exact (kf h).elim

/-- **The pass's member classes** carry the pass's block's members' constructors. -/
theorem checkBlockPass_cls {mode : ConLeche.CheckMode} {fe : IFEnv} {p₀ : BlockShape} {isRec : Bool}
    {s s' : AState} {q : BlockPass} (h : checkBlockPass mode fe p₀ isRec s = .ok (q, s')) :
    ∀ m ∈ q.cls, ClsCtors q.p m := by
  unfold checkBlockPass at h
  obtain ⟨⟨fe₁, p₁⟩, s1, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s2, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s3, -, h⟩ := bind_ok_inv' h
  obtain ⟨⟨ctx, holes⟩, s4, -, h⟩ := bind_ok_inv' h
  obtain ⟨⟨rd, ms⟩, s5, h5, h⟩ := bind_ok_inv' h
  obtain ⟨⟨outs, pos⟩, s6, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s7, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s8, -, h⟩ := bind_ok_inv' h
  obtain ⟨rfl, -⟩ := pure_ok' h
  exact checkBlockClasses_member h5

/-! ## The class read's indices -/

theorem classOfMotiveVar_lt {nP : Nat} {motPos : List Nat} {v c : Nat} (h : classOfMotiveVar nP motPos v = some c) :
    c < motPos.length := by
  unfold classOfMotiveVar at h
  split at h
  · exact (List.findIdx?_eq_some_iff_getElem.mp h).1
  · cases h

theorem classReadMinor_c {nP : Nat} {motPos : List Nat} {d : Nat} {dom : EIdx} {s s' : AState} {sl : ClassSlot}
    (h : classReadMinor nP motPos d dom s = .ok (some sl, s')) : ∀ c cn ihs, sl = .minor c cn ihs → c < motPos.length := by
  intro c cn ihs hsl
  subst hsl
  unfold classReadMinor at h
  obtain ⟨⟨bs, _⟩, s1, -, h⟩ := bind_ok_inv' h
  obtain ⟨o, s2, -, h⟩ := bind_ok_inv' h
  rcases o with _ | ⟨fvs, concl⟩
  · obtain ⟨e, -⟩ := pure_ok' h; cases e
  simp only at h
  obtain ⟨o2, s3, -, h⟩ := bind_ok_inv' h
  rcases o2 with _ | v
  · obtain ⟨e, -⟩ := pure_ok' h; cases e
  simp only at h
  cases hcv : classOfMotiveVar nP motPos v with
  | none => rw [hcv] at h; obtain ⟨e, -⟩ := pure_ok' h; cases e
  | some c' =>
  rw [hcv] at h
  have kf : ∀ {β : Type} {e : CheckError} {s0 s1 : AState} {b : β}, (fail e : AM β) s0 = .ok (b, s1) → False :=
    fun hc => ConRon.Bridge.AM.fail_ok hc
  simp only at h
  obtain ⟨args, s4, -, h⟩ := bind_ok_inv' h
  cases hla : args.getLast? with
  | none => rw [hla] at h; obtain ⟨e, -⟩ := pure_ok' h; cases e
  | some last =>
  rw [hla] at h
  simp only at h
  obtain ⟨hd, s5, -, h⟩ := bind_ok_inv' h
  split at h
  swap
  · obtain ⟨e, -⟩ := pure_ok' h; cases e
  obtain ⟨vc, s6, -, h⟩ := bind_ok_inv' h
  rcases vc with _ | ⟨cn', _⟩
  · exact (kf (by simpa [failDanglingE] using h)).elim
  simp only at h
  obtain ⟨ihs', s7, -, h⟩ := bind_ok_inv' h
  obtain ⟨e, -⟩ := pure_ok' h
  simp only [Option.some.injEq, ClassSlot.minor.injEq] at e
  obtain ⟨rfl, -, -⟩ := e
  exact classOfMotiveVar_lt hcv

theorem classReadSlot_c {p : BlockShape} {fe : IFEnv} {np : Nat} {motPos : List Nat} {d : Nat} {dom : EIdx}
    {s s' : AState} {sl : ClassSlot} (h : classReadSlot p fe np motPos d dom s = .ok (some sl, s')) :
    ∀ c cn ihs, sl = .minor c cn ihs → c < motPos.length := by
  have kf : ∀ {β : Type} {e : CheckError} {s0 s1 : AState} {b : β}, (fail e : AM β) s0 = .ok (b, s1) → False :=
    fun hc => ConRon.Bridge.AM.fail_ok hc
  intro c cn ihs hsl
  unfold classReadSlot at h
  obtain ⟨r, s1, -, h⟩ := bind_ok_inv' h
  split at h
  · obtain ⟨⟨bs, _⟩, s2, -, h⟩ := bind_ok_inv' h
    simp only at h
    cases hl : bs.getLast? with
    | none => rw [hl] at h; obtain ⟨e, -⟩ := pure_ok' h; cases e
    | some mdom =>
    rw [hl] at h
    simp only at h
    obtain ⟨hd, s3, -, h⟩ := bind_ok_inv' h
    split at h
    · obtain ⟨vc, s4, -, h⟩ := bind_ok_inv' h
      rcases vc with _ | ⟨i, us⟩
      · exact (kf (by simpa [failDanglingE] using h)).elim
      simp only at h
      obtain ⟨args, s5, -, h⟩ := bind_ok_inv' h
      obtain ⟨e, -⟩ := pure_ok' h
      subst hsl
      simp at e
    · obtain ⟨e, -⟩ := pure_ok' h; cases e
  · exact classReadMinor_c h c cn ihs hsl

theorem classReadSlots_c {p : BlockShape} {fe : IFEnv} {np : Nat} :
    ∀ (n : Nat) (motPos : List Nat) (d : Nat) (e : EIdx) (s s' : AState) (sls : List ClassSlot),
      classReadSlots p fe np n motPos d e s = .ok (some sls, s') →
      sls.length = n ∧ ∀ sl ∈ sls, ∀ c cn ihs, sl = .minor c cn ihs → c < motPos.length + n
  | 0, motPos, d, e, s, s', sls, h => by
    simp only [classReadSlots] at h
    obtain ⟨e, -⟩ := pure_ok' h
    simp only [Option.some.injEq] at e; subst e
    exact ⟨rfl, fun sl hsl => absurd hsl List.not_mem_nil⟩
  | n + 1, motPos, d, e, s, s', sls, h => by
    have kf : ∀ {β : Type} {e : CheckError} {s0 s1 : AState} {b : β}, (fail e : AM β) s0 = .ok (b, s1) → False :=
      fun hc => ConRon.Bridge.AM.fail_ok hc
    simp only [classReadSlots] at h
    split at h
    swap
    · obtain ⟨e, -⟩ := pure_ok' h; cases e
    obtain ⟨vb, s1, -, h⟩ := bind_ok_inv' h
    rcases vb with _ | ⟨dom, body⟩
    · exact (kf (by simpa [failDanglingE] using h)).elim
    simp only at h
    obtain ⟨os, s2, h2, h⟩ := bind_ok_inv' h
    rcases os with _ | slot
    · obtain ⟨e, -⟩ := pure_ok' h; cases e
    simp only at h
    obtain ⟨fv, s3, -, h⟩ := bind_ok_inv' h
    obtain ⟨b2, s4, -, h⟩ := bind_ok_inv' h
    obtain ⟨orr, s5, h5, h⟩ := bind_ok_inv' h
    rcases orr with _ | rest
    · obtain ⟨e, -⟩ := pure_ok' h; cases e
    simp only at h
    obtain ⟨e, -⟩ := pure_ok' h
    simp only [Option.some.injEq] at e; subst e
    have hc0 := classReadSlot_c h2
    cases slot with
    | motive k =>
      obtain ⟨hl, hc⟩ := classReadSlots_c n (motPos ++ [d - np]) (d + 1) b2 s4 s5 rest h5
      refine ⟨by simp [hl], fun sl hsl c cn ihs hm => ?_⟩
      rcases List.mem_cons.mp hsl with rfl | hsl
      · cases hm
      · have := hc sl hsl c cn ihs hm; simp at this; omega
    | minor c0 cn0 ihs0 =>
      obtain ⟨hl, hc⟩ := classReadSlots_c n motPos (d + 1) b2 s4 s5 rest h5
      refine ⟨by simp [hl], fun sl hsl c cn ihs hm => ?_⟩
      rcases List.mem_cons.mp hsl with rfl | hsl
      · have := hc0 c cn ihs hm; omega
      · have := hc sl hsl c cn ihs hm; omega

theorem classReadRecCls_c {nP : Nat} {motPos : List Nat} :
    ∀ (recs : List RecShape) (s s' : AState) (cs : List Nat),
      classReadRecCls nP motPos recs s = .ok (some cs, s') → ∀ c ∈ cs, c < motPos.length
  | [], s, s', cs, h, c, hc => by
    simp only [classReadRecCls] at h
    obtain ⟨e, -⟩ := pure_ok' h
    simp only [Option.some.injEq] at e; subst e
    exact absurd hc List.not_mem_nil
  | rc :: rest, s, s', cs, h, c, hc => by
    simp only [classReadRecCls] at h
    obtain ⟨o, s1, -, h⟩ := bind_ok_inv' h
    rcases o with _ | ⟨fvs, concl⟩
    · obtain ⟨e, -⟩ := pure_ok' h; cases e
    simp only at h
    obtain ⟨o2, s2, -, h⟩ := bind_ok_inv' h
    rcases o2 with _ | v
    · obtain ⟨e, -⟩ := pure_ok' h; cases e
    simp only at h
    cases hcv : classOfMotiveVar nP motPos v with
    | none => rw [hcv] at h; obtain ⟨e, -⟩ := pure_ok' h; cases e
    | some c0 =>
    rw [hcv] at h
    simp only at h
    obtain ⟨o3, s3, h3, h⟩ := bind_ok_inv' h
    rcases o3 with _ | cs'
    · obtain ⟨e, -⟩ := pure_ok' h; cases e
    simp only at h
    obtain ⟨e, -⟩ := pure_ok' h
    simp only [Option.some.injEq] at e; subst e
    rcases List.mem_cons.mp hc with rfl | hc
    · exact classOfMotiveVar_lt hcv
    · exact classReadRecCls_c rest s2 s3 cs' h3 c hc

/-- The class read's indices are below the first recursor's rule prefix. -/
def RdBound (p : BlockShape) (rd : ClassRead) : Prop :=
  ∀ rc0, p.recs.head? = some rc0 → (∀ c ∈ rd.recCls, c < rc0.rP) ∧
    ∀ sl ∈ rd.slots, ∀ c cn ihs, sl = .minor c cn ihs → c < rc0.rP

theorem classRead_bound {p : BlockShape} {fe : IFEnv} {s s' : AState} {rd : ClassRead}
    (h : classRead p fe p.nP p.recs s = .ok (some rd, s')) : RdBound p rd := by
  intro rc0 hrc0
  unfold classRead at h
  cases hr : p.recs with
  | nil => rw [hr] at hrc0; cases hrc0
  | cons r rest =>
  rw [hr] at h hrc0
  simp only [List.head?_cons, Option.some.injEq] at hrc0
  subst hrc0
  simp only at h
  obtain ⟨o, s1, -, h⟩ := bind_ok_inv' h
  rcases o with _ | ⟨fvs, body⟩
  · obtain ⟨e, -⟩ := pure_ok' h; cases e
  simp only at h
  obtain ⟨o2, s2, h2, h⟩ := bind_ok_inv' h
  rcases o2 with _ | slots
  · obtain ⟨e, -⟩ := pure_ok' h; cases e
  simp only at h
  obtain ⟨o3, s3, h3, h⟩ := bind_ok_inv' h
  rcases o3 with _ | recCls
  · obtain ⟨e, -⟩ := pure_ok' h; cases e
  simp only at h
  obtain ⟨e, -⟩ := pure_ok' h
  simp only [Option.some.injEq] at e; subst e
  obtain ⟨hl, hc⟩ := classReadSlots_c _ [] _ body s1 s2 slots h2
  have hmot := classReadRecCls_c _ s2 s3 recCls h3
  refine ⟨fun c hc' => ?_, fun sl hsl c cn ihs hm => ?_⟩
  · have h1 := hmot c hc'
    have h2 := Nat.lt_of_lt_of_le h1 ((List.length_filter_le _ _).trans (Nat.le_of_eq List.length_range))
    omega
  · have := hc sl hsl c cn ihs hm; simp at this; omega

theorem checkBlockClasses_rd {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {params : List EIdx}
    {s s' : AState} {rd : ClassRead} {ms : List TargetMajor}
    (h : checkBlockClasses mode fe p params s = .ok ((rd, ms), s')) : RdBound p rd := by
  have kf : ∀ {β : Type} {e : CheckError} {s0 s1 : AState} {b : β}, (fail e : AM β) s0 = .ok (b, s1) → False :=
    fun hc => ConRon.Bridge.AM.fail_ok hc
  unfold checkBlockClasses at h
  obtain ⟨o, s1, h1, h⟩ := bind_ok_inv' h
  rcases o with _ | rd'
  · exact (kf h).elim
  simp only at h
  obtain ⟨keys, s2, -, h⟩ := bind_ok_inv' h
  obtain ⟨ms', s3, -, h⟩ := bind_ok_inv' h
  split at h
  · obtain ⟨e, -⟩ := pure_ok' h
    obtain ⟨rfl, -⟩ := Prod.mk.inj e
    exact classRead_bound h1
  · exact (kf h).elim

theorem checkBlockPass_rd {mode : ConLeche.CheckMode} {fe : IFEnv} {p₀ : BlockShape} {isRec : Bool}
    {s s' : AState} {q : BlockPass} (h : checkBlockPass mode fe p₀ isRec s = .ok (q, s')) : RdBound q.p q.rd := by
  unfold checkBlockPass at h
  obtain ⟨⟨fe₁, p₁⟩, s1, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s2, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s3, -, h⟩ := bind_ok_inv' h
  obtain ⟨⟨ctx, holes⟩, s4, -, h⟩ := bind_ok_inv' h
  obtain ⟨⟨rd, ms⟩, s5, h5, h⟩ := bind_ok_inv' h
  obtain ⟨⟨outs, pos⟩, s6, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s7, -, h⟩ := bind_ok_inv' h
  obtain ⟨_, s8, -, h⟩ := bind_ok_inv' h
  obtain ⟨rfl, -⟩ := pure_ok' h
  exact checkBlockClasses_rd h5

end ConPanqueque.T.Ind
