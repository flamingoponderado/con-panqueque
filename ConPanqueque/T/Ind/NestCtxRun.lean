import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.Positivity
import ConLeche.Verify.Denote.IndFrame

/-! # The walk's context at a well-formed store

`blockNestCtx_facts`: con-ron's `blockNestCtx_spec` at the pure grade (it reads no cache, calls no
knot): from a well-formed store at which the block denotes, the context's levels denote, it has one
parameter per declared parameter and one hole per member.  `CBKRun.bn` asks exactly this. -/

open ConRon.Arena ConRon.Bridge ConRon.Bridge.Inductives

namespace ConPanqueque.T.Ind

set_option autoImplicit false

theorem dShape_at {st : EStore} {p : BlockShape} {pP : ConLeche.BlockShape} (hp : dShape st p = some pP)
    (s0 : LIdx) (ip : Bool) (l : ConLeche.Level) (hl : denoteL st.ls s0 = some l) :
    dShape st { p with resSort := s0, isProp := ip } = some { pP with resSort := l, isProp := ip } := by
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := dShape_inv hp
  simp only [dShape, h1, h2, h4, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, h3, h6]

theorem denoteEList_len {st : EStore} : ∀ {xs : List EIdx} {ys : List ConLeche.Expr},
    Frontend.denoteEList st xs = some ys → xs.length = ys.length
  | [], ys, h => by simp only [Frontend.denoteEList, Option.some.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [Frontend.denoteEList] at h
    cases h1 : denoteE st x with
    | none => rw [h1] at h; exact nomatch h
    | some y =>
    cases h2 : Frontend.denoteEList st xs with
    | none => rw [h1, h2] at h; exact nomatch h
    | some ys' =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    simp [denoteEList_len h2]

/-- **The walk's context, at the pure grade.** -/
theorem blockNestCtx_facts {p : BlockShape} {pP : ConLeche.BlockShape} {s s1 : AState} {ctx : NestCtx}
    {holes : List EIdx} (hok : StateOK s) (hp : dShape s.store p = some pP)
    (hrun : blockNestCtx p s = .ok ((ctx, holes), s1)) :
    (∃ vs, denoteLs s1.store.lss ctx.lvls = some vs) ∧ ctx.params.length = p.nP ∧
      holes.length = p.members.length := by
  have hcvs : p.formers.mapM (Frontend.denoteCV s.store) = some pP.formers := by
    obtain ⟨hms, -⟩ := dShape_inv hp
    simp only [BlockShape.formers, ConLeche.BlockShape.formers]
    clear hrun
    generalize pP.members = ys at hms ⊢
    generalize p.members = xs at hms
    induction xs generalizing ys with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
      subst hms; rfl
    | cons x xs ih =>
      obtain ⟨y, ys', rfl, hy, hys⟩ := mapM_option_cons_inv hms
      exact mapM_option_cons (dMember_inv hy).1 (ih ys' hys)
  have hnP : p.nP = pP.nP := (dShape_inv hp).2.2.1
  have hml : p.members.length = pP.members.length :=
    (ConLeche.option_mapM_length (dShape_inv hp).1).symm
  simp only [blockNestCtx] at hrun
  generalize hfm : p.formers = cvs at hrun hcvs
  cases cvs with
  | nil => exact absurd hrun (fun h => AM.fail_ok h)
  | cons cv0 rest =>
  obtain ⟨cv0P, restP, hfP, hcv0, -⟩ := mapM_option_cons_inv hcvs
  dsimp only at hrun
  obtain ⟨o, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, ho⟩ := openPisAtFvarsF_run hok (denoteCV_type hcv0) k1
  obtain ⟨pq, s₂, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨rfl, hs2⟩ := unwrapOr_ok k2
  subst s₂
  obtain ⟨fvs, b⟩ := pq
  obtain ⟨xs, x, hpq, hxs, -⟩ := denoteOpen_some_inv ho
  obtain ⟨ctx', s₃, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨p3, hctx⟩ := BlockShape.nestCtx_spec p pP fvs xs ConLeche.Env.empty.find? s₁ s₃ ctx' p1.ok
    ⟨dShape_ext p1.ext _ _ hp, hxs⟩ k3
  have p13 := p1.trans p3
  obtain ⟨oh, s₄, k4, z4⟩ := AM.bind_ok z3
  obtain ⟨p4, hoh⟩ := nestHoles_spec (env := ConLeche.Env.empty) ctx' _ s₃ s₄ oh p13.ok hctx k4
  obtain ⟨holes', s₅, k5, z5⟩ := AM.bind_ok z4
  obtain ⟨rfl, hs5⟩ := unwrapOr_ok k5
  subst s₅
  obtain ⟨he, rfl⟩ := AM.pure_ok z5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨holesP, hnh, hholes⟩ := hoh
  have hctx4 := dCtx_ext _ p4.ext _ _ hctx
  obtain ⟨namesP, lpsP, paramsP, sortP, formersP, hcP, -, -, hpar, -, hlv, -⟩ := dCtx_inv hctx4
  refine ⟨⟨_, hlv⟩, ?_, ?_⟩
  · have e := congrArg ConLeche.NestCtx.params hcP
    simp only [ConLeche.BlockShape.nestCtx] at e
    rw [denoteEList_len hpar, ← e, ConLeche.Verify.openPisAtFvars_length _ hpq, hnP]
  · rw [denoteEList_len hholes]
    unfold ConLeche.nestHoles at hnh
    rw [ConLeche.option_mapM_length hnh, List.length_range]
    simp only [ConLeche.BlockShape.nestCtx, ConLeche.BlockShape.memberNames, List.length_map, hml]

end ConPanqueque.T.Ind
