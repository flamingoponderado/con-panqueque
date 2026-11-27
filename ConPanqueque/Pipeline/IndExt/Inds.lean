import ConPanqueque.Pipeline.IndExt.Tail
import ConPanqueque.Pipeline.IndExt.ResOps

/-! # The block's formers at an extension of the environment

`reduceMembers` (each former at its telescope) and `checkBlockInds` (stage 1: the formers checked,
agreed and consed) carry over from `X₁` to an extension `X₂`.  Every comparison they make is on
terms resolving in `X₁`: the declared types (checked by `checkConstantVal` at `X₁`), the reducts
(`whnfTelescope`'s outputs, closed back) and the free variables opened off resolved types. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

/-! ## Resolution of telescopes and free variables -/

theorem bind_ok_of {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} {b : β}
    (hx : x = .ok a) (hf : f a = .ok b) : (x >>= f) = .ok b := by
  rw [hx]; exact hf

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem err_bind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

theorem unwrapOr_none {α : Type} (e : CheckError) : (unwrapOr none e : CheckM α) = .error e := rfl

theorem unwrapOr_some {α : Type} (a : α) (e : CheckError) : (unwrapOr (some a) e : CheckM α) = .ok a := rfl

/-- A free variable's annotation resolves where the variable does. -/
theorem res_fvarTypeD {env : Env} {e : Expr} (h : Res env e) : Res env e.fvarTypeD := by
  cases e <;> simp only [Expr.fvarTypeD] <;> first | exact res_fvar.mp h | exact h

/-- `whnfTelescope`'s domains resolve (the knot's reducts of resolved terms resolve). -/
theorem whnfTelescope_res {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) (F : Nat) :
    ∀ (n i : Nat) {e : Expr} {bs : List Expr} {s : Level}, Res X₁ e →
      whnfTelescope (fueledOps .verified F) X₁ i n e = .ok (bs, s) → ∀ b ∈ bs, Res X₁ b
  | 0, i, e, bs, s, he, h => by
    unfold whnfTelescope at h
    obtain ⟨w, -, h⟩ := exceptBind_ok h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      intro b hb; rw [← h.1] at hb; exact nomatch hb
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  | n + 1, i, e, bs, s, he, h => by
    unfold whnfTelescope at h
    obtain ⟨w, hw, h⟩ := exceptBind_ok h
    have hres : Res X₁ w := ((knot_ext .verified hx F false).whnf i he).2 w hw
    split at h
    · rename_i dom body
      obtain ⟨hd, hb⟩ := res_forall.mp hres
      obtain ⟨⟨bs', s'⟩, h1, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro b hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hd
      · exact whnfTelescope_res hx F n (i + 1) (res_open hd hb) h1 b hm
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- A former's reduct resolves. -/
theorem reducedFormer_res {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) {F n : Nat} {cv f : ConstantVal}
    (hr : Res X₁ cv.type) (h : reducedFormer (fueledOps .verified F) X₁ cv n = .ok f) :
    Res X₁ f.type := by
  unfold reducedFormer at h
  obtain ⟨⟨bs, s⟩, ht, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact res_closeTelescope bs 0 (whnfTelescope_res hx F n 0 hr ht) res_sort

/-! ## The members at their telescopes -/

theorem reduceMember_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) {F nP : Nat} {ms r : MemberShape}
    (hfr : X₂.find? ms.cvT.name = none)
    (h : reduceMember (m := CheckM) (fueledOps .verified F) X₁ ms nP = .ok r) :
    reduceMember (m := CheckM) (fueledOps .verified F) X₂ ms nP = .ok r := by
  unfold reduceMember at h ⊢
  by_cases hd : formerDefHeaded ms.cvT = true
  · rw [ite_eq_left hd] at h ⊢
    by_cases hg : declinedAtDefinition.contains ms.cvT.name = true
    · rw [ite_eq_left hg] at h; exact nomatch h
    rw [ite_eq_right hg] at h ⊢
    obtain ⟨u, hc, h⟩ := exceptBind_ok h
    cases u
    obtain ⟨cvR, hR, h⟩ := exceptBind_ok h
    have hres := (checkConstantVal_res F X₁ ms.cvT false false false hc).1
    have hresR := reducedFormer_res hx hres hR
    refine bind_ok_of (checkConstantVal_ext hx F ms.cvT false false false hfr hc) ?_
    refine bind_ok_of (reducedFormer_ext hx hres hR) ?_
    dsimp only
    rw [ops_defeq hx F 0 hres hresR]
    exact h
  · rw [ite_eq_right hd] at h ⊢
    exact h

theorem reduceMembers_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) {F nP : Nat} :
    ∀ {mss r : List MemberShape}, (∀ ms ∈ mss, X₂.find? ms.cvT.name = none) →
      reduceMembers (m := CheckM) (fueledOps .verified F) X₁ nP mss = .ok r →
      reduceMembers (m := CheckM) (fueledOps .verified F) X₂ nP mss = .ok r
  | [], _, _, h => h
  | ms :: rest, r, hfr, h => by
    unfold reduceMembers at h ⊢
    obtain ⟨m', hm', h⟩ := exceptBind_ok h
    obtain ⟨r', hr', h⟩ := exceptBind_ok h
    rw [reduceMember_ext hx (hfr ms List.mem_cons_self) hm',
      reduceMembers_ext hx (fun m hm => hfr m (List.mem_cons_of_mem _ hm)) hr']
    exact h

/-! ## Stage 1: the formers -/

theorem checkBlockTele_res {env : Env} {F nP : Nat} {ms : MemberShape} {c : ConstantVal} {s : Level}
    (h : checkBlockTele (fueledOps .verified F) env nP ms = .ok (c, s)) : Res env c.type := by
  obtain ⟨cvT, -, -, hcv, hc, -⟩ := checkBlockTele_shape h
  rw [hcv]
  exact (checkConstantVal_res F env cvT false false false hc).1

theorem checkBlockTele_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) {F nP : Nat} {ms : MemberShape}
    {q : ConstantVal × Level} (hfr : X₂.find? ms.cvT.name = none)
    (h : checkBlockTele (m := CheckM) (fueledOps .verified F) X₁ nP ms = .ok q) :
    checkBlockTele (m := CheckM) (fueledOps .verified F) X₂ nP ms = .ok q := by
  unfold checkBlockTele at h ⊢
  obtain ⟨u, hc, h⟩ := exceptBind_ok h
  cases u
  exact bind_ok_of (checkConstantVal_ext hx F ms.cvT false false false hfr hc) h

theorem checkBlockTeles_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) {F nP : Nat} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      (∀ ms ∈ mss, X₂.find? ms.cvT.name = none) →
      checkBlockTeles (m := CheckM) (fueledOps .verified F) X₁ nP mss = .ok cvs →
      checkBlockTeles (m := CheckM) (fueledOps .verified F) X₂ nP mss = .ok cvs ∧
        ∀ q ∈ cvs, Res X₁ q.1.type
  | [], cvs, _, h => by
    simp only [checkBlockTeles, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun q hq => nomatch hq⟩
  | ms :: rest, cvs, hfr, h => by
    unfold checkBlockTeles at h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨qs, hqs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨h2, hr⟩ := checkBlockTeles_ext hx (fun m hm => hfr m (List.mem_cons_of_mem _ hm)) hqs
    refine ⟨?_, ?_⟩
    · unfold checkBlockTeles
      rw [checkBlockTele_ext hx (hfr ms List.mem_cons_self) hq, h2]
      rfl
    · intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · obtain ⟨c, s⟩ := q'
        exact checkBlockTele_res hq
      · exact hr q' hq'

theorem checkBlockDomsAt_eq {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) (F off : Nat) {fvs doms : List Expr}
    (hf : ∀ a ∈ fvs, Res X₁ a) (hd : ∀ b ∈ doms, Res X₁ b) :
    ∀ (j : Nat), checkBlockDomsAt (m := CheckM) (fueledOps .verified F) X₂ off fvs doms j =
      checkBlockDomsAt (m := CheckM) (fueledOps .verified F) X₁ off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkBlockDomsAt
    cases ha : fvs[j]? with
    | none => simp only [unwrapOr_none, err_bind]
    | some a =>
      cases hb : doms[j]? with
      | none => simp only [unwrapOr_some, ok_bind, unwrapOr_none, err_bind]
      | some b =>
        simp only [unwrapOr_some, ok_bind]
        rw [ops_defeq hx F (off + j) (res_fvarTypeD (hf a (List.mem_of_getElem? ha)))
          (hd b (List.mem_of_getElem? hb)), checkBlockDomsAt_eq hx F off hf hd j]

theorem checkBlockAgree_eq {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) (F nP : Nat) {cvTa0 : ConstantVal}
    {s0 : Level} (h0 : Res X₁ cvTa0.type) :
    ∀ {cvs : List (ConstantVal × Level)}, (∀ q ∈ cvs, Res X₁ q.1.type) →
      checkBlockAgree (m := CheckM) (fueledOps .verified F) X₂ nP cvTa0 s0 cvs =
        checkBlockAgree (m := CheckM) (fueledOps .verified F) X₁ nP cvTa0 s0 cvs
  | [], _ => rfl
  | (cvTa, s) :: rest, hr => by
    unfold checkBlockAgree
    have h1 : Res X₁ cvTa.type := hr (cvTa, s) List.mem_cons_self
    cases h0' : openPisAtFvars nP cvTa0.type 0 with
    | none => simp only [unwrapOr_none, err_bind]
    | some q0 =>
      cases h1' : openPisAtFvars nP cvTa.type 0 with
      | none => simp only [unwrapOr_some, ok_bind, unwrapOr_none, err_bind]
      | some q1 =>
        obtain ⟨tfvs0, trest0⟩ := q0
        obtain ⟨tfvs, trest⟩ := q1
        simp only [unwrapOr_some, ok_bind]
        have hdoms : ∀ b ∈ tfvs0.map Expr.fvarTypeD, Res X₁ b := by
          intro b hb
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
          exact res_fvarTypeD (res_openPisAtFvars nP 0 h0 h0' a ha)
        rw [checkBlockDomsAt_eq hx F 0 (res_openPisAtFvars nP 0 h1 h1') hdoms nP,
          checkBlockAgree_eq hx F nP h0 (fun q hq => hr q (List.mem_cons_of_mem _ hq))]

theorem checkBlockInds_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) {F : Nat} {p : BlockShape}
    {isRec : Bool} {A₁ : Env} {p₁ : BlockShape}
    (hfr : ∀ ms ∈ p.members, X₂.find? ms.cvT.name = none)
    (h : checkBlockInds (m := CheckM) (fueledOps .verified F) X₁ p isRec = .ok (A₁, p₁)) :
    checkBlockInds (m := CheckM) (fueledOps .verified F) X₂ p isRec =
        .ok (consBlockInds p₁ isRec (p.members.map (·.declared)) 0 X₂, p₁) ∧
      A₁ = consBlockInds p₁ isRec (p.members.map (·.declared)) 0 X₁ := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, rfl, hq, hcvs, hag⟩ := checkBlockInds_shape h
  refine ⟨?_, rfl⟩
  have hfr0 : X₂.find? ms0.cvT.name = none := hfr ms0 (by rw [hm]; exact List.mem_cons_self)
  have hfrr : ∀ ms ∈ rest, X₂.find? ms.cvT.name = none :=
    fun ms h' => hfr ms (by rw [hm]; exact List.mem_cons_of_mem _ h')
  have hq2 := checkBlockTele_ext hx hfr0 hq
  obtain ⟨hcvs2, hres⟩ := checkBlockTeles_ext hx hfrr hcvs
  have hag2 : checkBlockAgree (m := CheckM) (fueledOps .verified F) X₂ p.nP cvTa0 s0 cvs = .ok () := by
    rw [checkBlockAgree_eq hx F p.nP (checkBlockTele_res hq) hres]; exact hag
  unfold checkBlockInds
  simp only [hm, hq2, hcvs2, ok_bind, hag2]
  rfl

end ConPanqueque.Pipeline.IndExt
