import ConPanqueque.T.LvlSimp
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# One-parameter substitution

`subst1(l, p, v)`: con-leche's `Level.subst [p] [v] l` (the shape `byCases` uses): `param n` becomes
`v` when `p = n` (names compared by structure), the other leaves stay, nodes are rebuilt.
-/

namespace ConPanqueque.T.LSub
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq

def fSubst := ofString "subst1"
def pSp := ofString "sp"

def substRest (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lA2) (.const 0)) (.return (vv pLa))
  (.seq (.assign .local lD1 (.load .one (vv lA3)))
  (.ite (.cmp .equal (vv lA2) (.const 4))
    (.seq (.call (some (some (.local, lZ), none)) fNeq [vv pSp, vv lD1])
      (.ite (.cmp .equal (vv lZ) (.const 0)) (.return (vv pLa)) (.return (vv pLb))))
  (.ite (.cmp .equal (vv lA2) (.const 1))
    (.seq (.call (some (some (.local, lA1), none)) fSubst [vv lD1, vv pSp, vv pLb])
      (alloc2 C lW (.const 1) (vv lA1) (.return (vv lW))))
    (.seq (.assign .local lB (.load .one (.op .add [vv lA3, .const 8])))
    (.seq (.call (some (some (.local, lA1), none)) fSubst [vv lD1, vv pSp, vv pLb])
    (.seq (.call (some (some (.local, lZ), none)) fSubst [vv lB, vv pSp, vv pLb])
      (alloc3 C lW (vv lA2) (vv lA1) (vv lZ) (.return (vv lW)))))))))

def substCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv pLa)) (lvViewP
    (.seq (.assign .local lA2 (vv lX)) (.seq (.assign .local lA3 (vv lY)) (substRest C))))

def substBody (C : Ctx) : ProgHOL 64 := prologue lvlLocals (substCore C)

def substParams : List MlS := [pLa, pSp, pLb]

section
variable {σ : Type}

theorem params_noneSub (a b c : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ lvlLocals → (ctxEnv C ++ substParams.zip [a, b, c]).get x = none := by
  intro x hx
  simp only [lvlLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem subst_view (C : Ctx) (hok : CtxOK C) (H : List (BitVec 64)) (w : BitVec 64) (nh : NIdx) (wv : BitVec 64)
    (l : ConLeche.Level) (s : AState) (hl : LRep C.HB H s.store.ls w l) (m : AM ConLeche.Level)
    (hk : ∀ (Γ1 : Env) (M1 : Mem) (Pc : BitVec 64), Γ1.get lA2 = some (BitVec.ofNat 64 (ltag l)) →
      Γ1.get lA3 = some Pc → Γ1.get pLa = some w → Γ1.get pSp = some (Enc.idxW nh) → Γ1.get pLb = some wv →
      Γ1.get lA1 = none → Γ1.get lZ = none → Γ1.get lB = none → Γ1.get lD1 = none → Γ1.get lW = none →
      LKids C.HB H s.store.ls Pc M1 l →
      SpecR (Inv (σ := σ) (ctxH C H) s Γ1 M1 DL) (substRest C) s m (PostLv (ctxH C H))) :
    SpecR (Pre (σ := σ) (ctxH C H) s (substParams.zip [w, Enc.idxW nh, wv])) (substBody C) s m
      (PostLv (ctxH C H)) := by
  refine specR_prologue (postLv_locals _) (params_noneSub _ _ _ _) ?_
  unfold substCore
  refine specR_assignI lQ (vv pLa) w (by decide) (by simp +decide [ctxEnv, substParams]) ?_
  refine specR_lvViewI (C := ctxH C H) (ctxOK_H hok H) w l (by simp) hl (by simp +decide [ctxEnv] <;> rfl)
    (by simp +decide [ctxEnv] <;> rfl) lvScratch_DL (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => ?_)
  refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 (ltag l)) (by decide) (by simp [hx1]) ?_
  refine specR_assignI lA3 (vv lY) Pc (by decide) (by simp +decide [hy1]) ?_
  refine hk _ _ Pc (by simp +decide) (by simp +decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hk1 <;>
    (simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, substParams])

theorem subst_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one)) :
    ∀ (l : ConLeche.Level) (H : List (BitVec 64)) (w : BitVec 64) (nh : NIdx) (f : Nat) (pn : ConLeche.Name)
      (vl : ConLeche.Level) (wv : BitVec 64) (s : AState),
      LRep C.HB H s.store.ls w l → denoteNAux s.store.ns f nh = some pn → LRep C.HB H s.store.ls wv vl →
      SpecR (Pre (σ := σ) (ctxH C H) s (substParams.zip [w, Enc.idxW nh, wv])) (substBody C) s
        (pure (ConLeche.Level.subst [pn] [vl] l)) (PostLv (ctxH C H)) := by
  intro l
  induction l with
  | zero =>
    intro H w nh f pn vl wv s hl hn hv
    refine subst_view C hok H w nh wv _ s hl _ (fun Γ1 M1 Pc h2 h3 hw _ _ _ _ _ _ _ _ => ?_)
    unfold substRest
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    exact specR_returnI (vv pLa) w (by simp [hw]) (fun t ht => ⟨H, List.prefix_refl _, hl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | param n =>
    intro H w nh f pn vl wv s hl hn hv
    refine subst_view C hok H w nh wv _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨nhn, fn, m1, d1⟩ := hk1
    unfold substRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) _ (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    refine specR_congr (m' := pure (decide (pn = n)) >>= fun b =>
      if b = true then pure vl else pure (ConLeche.Level.param n))
      (by by_cases e : pn = n <;> simp [ConLeche.Level.subst, ConLeche.Level.subst.go, e]) ?_
    refine callNeq_spec (C := ctxH C H) hcN lZ pSp lD1 nh nhn pn n f fn hn d1 (by decide) (by simp +decide [hsp])
      (by simp +decide) ?_
    by_cases e : pn = n
    · refine specR_ifI _ 0 (by simp +decide [sev, e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
      simp only [e, decide_true, ite_true]
      exact specR_returnI (vv pLb) wv (by simp +decide [hlb])
        (fun t ht => ⟨H, List.prefix_refl _, hv, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp +decide [sev, e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
      simp only [e, decide_false]
      exact specR_returnI (vv pLa) w (by simp +decide [hw])
        (fun t ht => ⟨H, List.prefix_refl _, hl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ u ih =>
    intro H w nh f pn vl wv s hl hn hv
    refine subst_view C hok H w nh wv _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, m1, r1⟩ := hk1
    unfold substRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw' => absurd hw' (by decide))
    refine specR_congr (m' := pure (ConLeche.Level.subst [pn] [vl] u) >>= fun c => pure (ConLeche.Level.succ c))
      (by simp [ConLeche.Level.subst]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSubst substParams [vv lD1, vv pSp, vv pLb] (substBody C) [wu, Enc.idxW nh, wv]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp], by simp +decide [hlb], trivial⟩ _
      (ih H wu nh f pn vl wv s r1 hn hv) (fun H1 c hp1 hc => ?_)
    refine specR_alloc2I (C := ctxH C H1) (ctxOK_H hok H1) lW (.const 1) (vv lA1) 1 c (by decide) (fun _ => rfl)
      (fun _ => by simp +decide) (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp2' : H1 <+: H2 := hp2
    exact ⟨_, hp1.trans (hp2'.trans (img2_prefix H2 ws _ c hws)),
      lrep_mkSucc (ctxH C H1) s.store.ls H2 ws c _ hws hp2 hc, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | max u v ihu ihv =>
    intro H w nh f pn vl wv s hl hn hv
    refine subst_view C hok H w nh wv _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, wv2, m1, m2, r1, r2⟩ := hk1
    unfold substRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lB _ (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv2 (by decide) (by simp +decide [sev, h3])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (ConLeche.Level.subst [pn] [vl] u) >>= fun a =>
      pure (ConLeche.Level.subst [pn] [vl] v) >>= fun b => pure (ConLeche.Level.max a b))
      (by simp [ConLeche.Level.subst]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSubst substParams [vv lD1, vv pSp, vv pLb] (substBody C) [wu, Enc.idxW nh, wv]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp], by simp +decide [hlb], trivial⟩ _
      (ihu H wu nh f pn vl wv s r1 hn hv) (fun H1 c1 hp1 hc1 => ?_)
    refine callLv_spec (C := ctxH C H1) lZ fSubst substParams [vv lB, vv pSp, vv pLb] (substBody C) [wv2, Enc.idxW nh, wv]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp], by simp +decide [hlb], trivial⟩ _
      (ihv H1 wv2 nh f pn vl wv s (lrep_mono hp1 v wv2 r2) hn (lrep_mono hp1 vl wv hv)) (fun H2 c2 hp2 hc2 => ?_)
    have hc1' := lrep_mono hp2 _ c1 hc1
    refine specR_alloc3I (C := ctxH C H2) (ctxOK_H hok H2) lW (vv lA2) (vv lA1) (vv lZ) (BitVec.ofNat 64 2) c1 c2
      (by decide) (fun _ => by simp +decide [h2, ltag]) (fun _ => by simp +decide) (fun _ => by simp +decide)
      (fun H3 ws hp3 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H3.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp3' : H2 <+: H3 := hp3
    exact ⟨_, hp1.trans (hp2.trans (hp3'.trans (img3_prefix H3 ws _ c1 c2 hws))),
      lrep_mkMax (ctxH C H2) s.store.ls H3 ws c1 c2 _ _ hws hp3 hc1' hc2 2 rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | imax u v ihu ihv =>
    intro H w nh f pn vl wv s hl hn hv
    refine subst_view C hok H w nh wv _ s hl _ (fun Γ1 M1 Pc h2 h3 hw hsp hlb n1 nz nb nd nw hk1 => ?_)
    obtain ⟨wu, wv2, m1, m2, r1, r2⟩ := hk1
    unfold substRest
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lD1 (vv lA3) Pc (Pc + BitVec.ofNat 64 (8 * 0)) wu (by decide) (by simp +decide [h3])
      (by simp) m1 ?_
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, h2, ltag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw' => absurd rfl hw') (fun _ => ?_)
    refine specR_loadI' lB _ (Pc + 8) (Pc + BitVec.ofNat 64 (8 * 1)) wv2 (by decide) (by simp +decide [sev, h3])
      (by simp) m2 ?_
    refine specR_congr (m' := pure (ConLeche.Level.subst [pn] [vl] u) >>= fun a =>
      pure (ConLeche.Level.subst [pn] [vl] v) >>= fun b => pure (ConLeche.Level.imax a b))
      (by simp [ConLeche.Level.subst]) ?_
    refine callLv_spec (C := ctxH C H) lA1 fSubst substParams [vv lD1, vv pSp, vv pLb] (substBody C) [wu, Enc.idxW nh, wv]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp], by simp +decide [hlb], trivial⟩ _
      (ihu H wu nh f pn vl wv s r1 hn hv) (fun H1 c1 hp1 hc1 => ?_)
    refine callLv_spec (C := ctxH C H1) lZ fSubst substParams [vv lB, vv pSp, vv pLb] (substBody C) [wv2, Enc.idxW nh, wv]
      (by decide) rfl (by decide) hcS ⟨by simp +decide, by simp +decide [hsp], by simp +decide [hlb], trivial⟩ _
      (ihv H1 wv2 nh f pn vl wv s (lrep_mono hp1 v wv2 r2) hn (lrep_mono hp1 vl wv hv)) (fun H2 c2 hp2 hc2 => ?_)
    have hc1' := lrep_mono hp2 _ c1 hc1
    refine specR_alloc3I (C := ctxH C H2) (ctxOK_H hok H2) lW (vv lA2) (vv lA1) (vv lZ) (BitVec.ofNat 64 3) c1 c2
      (by decide) (fun _ => by simp +decide [h2, ltag]) (fun _ => by simp +decide) (fun _ => by simp +decide)
      (fun H3 ws hp3 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H3.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp3' : H2 <+: H3 := hp3
    exact ⟨_, hp1.trans (hp2.trans (hp3'.trans (img3_prefix H3 ws _ c1 c2 hws))),
      lrep_mkImax (ctxH C H2) s.store.ls H3 ws c1 c2 _ _ hws hp3 hc1' hc2, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.LSub
