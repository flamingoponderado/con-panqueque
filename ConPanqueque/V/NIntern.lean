import ConPanqueque.V.LsIntern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning names

The name store sits under the level store. `anonymous`: the empty key and
the constant derived word 1723. (`str`, `num` follow.)
-/

namespace ConPanqueque.V

/-- The four stores with the name store replaced. -/
def withN (st : EStore) (ns : NStore) : EStore := { st with lss := { st.lss with ls := { st.lss.ls with ns := ns } } }

section
variable {σ : Type}

theorem srep_withN {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FLn FLl FLs FLe : BitVec 64} {st : EStore}
    (h : SRep t L FLn FLl FLs FLe st) (k : Nat) (ns' : NStore) (hn : NRep u L FLn ns')
    (hfl : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → u.memory F = t.memory F) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k' tier, k' < 19 → tier < 2 → k' ≠ k → Agree L FLe t u k' tier) (hk : k < 3) :
    SRep u L FLn FLl FLs FLe (withN st ns') := by
  have A : ∀ k' tier, k' < 19 → tier < 2 → k' ≠ k → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k' tier enc dW tb mkI → TabAt u L k' tier enc dW tb mkI :=
    fun k' tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k' tier h2 h3 h4).1 (hag k' tier h2 h3 h4).2 hd
  have he : ERep t L FLe (withN st ns') :=
    ⟨h.e.fl, h.e.p0, h.e.p1, h.e.p2, h.e.p3, h.e.p4, h.e.p5, h.e.p6, h.e.p7, h.e.p8, h.e.p9,
      h.e.s0, h.e.s1, h.e.s2, h.e.s3, h.e.s4, h.e.s5, h.e.s6, h.e.s7, h.e.s8, h.e.s9⟩
  refine ⟨erep_frame he (hfl _ (Or.inr (Or.inr (Or.inr rfl)))) hd (fun k' tier h1 h2 h3 => hag k' tier h2 h3 (by omega)),
    ⟨⟨by rw [hd]; exact h.ls.fl.1, by rw [hfl _ (Or.inr (Or.inr (Or.inl rfl)))]; exact h.ls.fl.2⟩,
      A 8 0 (by decide) (by decide) (by omega) h.ls.pl, A 8 1 (by decide) (by decide) (by omega) h.ls.sl⟩, ?_, hn⟩
  exact ⟨⟨by rw [hd]; exact h.l.fl.1, by rw [hfl _ (Or.inr (Or.inl rfl))]; exact h.l.fl.2⟩,
    A 3 0 (by decide) (by decide) (by omega) h.l.pz, A 4 0 (by decide) (by decide) (by omega) h.l.ps,
    A 5 0 (by decide) (by decide) (by omega) h.l.pm, A 6 0 (by decide) (by decide) (by omega) h.l.pi,
    A 7 0 (by decide) (by decide) (by omega) h.l.pp, A 3 1 (by decide) (by decide) (by omega) h.l.sz,
    A 4 1 (by decide) (by decide) (by omega) h.l.ss, A 5 1 (by decide) (by decide) (by omega) h.l.sm,
    A 6 1 (by decide) (by decide) (by omega) h.l.si, A 7 1 (by decide) (by decide) (by omega) h.l.sp⟩

theorem nrep_anons {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ns : NStore}
    (h : NRep t L FL ns) (P' Sc' : Tbl AnonNode NIdx UInt64)
    (hP : TabAt u L 0 0 Enc.encAnon dWN P' (mkN NTag.anonymous 0)) (hS : TabAt u L 0 1 Enc.encAnon dWN Sc' (mkN NTag.anonymous 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 0 → Agree L FL t u k tier) :
    NRep u L FL { ns with pers := { ns.pers with anons := P' }, scr := { ns.scr with anons := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 0 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩, hP, A 1 0 (by decide) (by decide) (by decide) h.ps,
    A 2 0 (by decide) (by decide) (by decide) h.pn, hS, A 1 1 (by decide) (by decide) (by decide) h.ss,
    A 2 1 (by decide) (by decide) (by decide) h.sn⟩

end

def nAnonWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lDv (.const 1723)) (.seq (.assign .local lDv2 (.const 0)) (.seq (.assign .local lSk (.const 0)) rest))

section
variable {σ : Type}

theorem nInternAnon_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 0 0)
    (hb0 : L.base 0 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.anonymous.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 0 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.anonymous.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfln : t.locals.lookup lFln = some (.val (.word FLn)))
    (hw : ∀ y, y ∈ zeroScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    XRes t L FLn FLl FLs FLe KB 0 (withN st (st.lss.ls.ns.intern .anonymous).1) (st.lss.ls.ns.intern .anonymous).2
      (evaluateHOLFiniteState t (nAnonWith (rRest 0 0 lFln))) := by
  have W : ∀ y, y ∈ zeroScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  let dd := st.lss.ls.ns.derOfView .anonymous
  unfold nAnonWith
  obtain ⟨w1, hw1⟩ := W lDv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lDv (.const 1723) (dWN dd).1 w1 (eval_const t 1723) hw1)]
  let t1 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) t
  obtain ⟨w2, hw2⟩ := W lDv2 (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lDv2 (.const 0) (dWN dd).2 w2 (eval_const t1 0) (by lk [t1]; exact hw2))]
  let t2 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) t1
  obtain ⟨w3, hw3⟩ := W lSk (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lSk (.const 0) (if false then 1 else 0) w3 (eval_const t2 0)
    (by lk [t2, t1]; exact hw3))]
  let t3 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) t2
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have hint := nstore_anon st.lss.ls.ns
  simp only at hint
  have R := rRest_spec t t3 L FLn FLl FLs FLe KB FLn 0 0 lFln (by decide) st.lss.ls.ns.scratchOn Enc.encAnon dWN Enc.idxW
    Enc.encAnon_inj (mkN NTag.anonymous 0) (mkN NTag.anonymous 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN NTag.anonymous 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN NTag.anonymous 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.ns.pers.anons st.lss.ls.ns.scr.anons false AnonNode.mk dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withN st (st.lss.ls.ns.intern .anonymous).1))
    (fun v' hP hS' hf hd' hag => by
      rw [hint]
      exact srep_withN hR3 0 _ (nrep_anons hR3.n _ _ hP hS' (hf _ (Or.inl rfl)) hd'
        (fun k tier h1 h2 h3 => hag k tier h1 h2 h3)) hf hd' hag (by decide))
    hS (by decide) rfl (by decide) (Or.inl rfl) hR3.n.fl hR3.n.pa hR3.n.sa (fun k hk => absurd hk (by simp [Enc.encAnon]))
    (by lk [t3, t2, t1]) (by lk [t3, t2]) (by lk [t3]) (by lk [t3, t2, t1]; exact lfln) (by lk [t3, t2, t1]; exact ldir)
    (by lk [t3, t2, t1]; exact lkb)
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨w, hw⟩ := W lFl (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lOn (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lPg (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lSg (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lK (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lL (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩)
  rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  refine Or.inr ⟨by rw [hr, hint], hQ, c3, g3, d3, ta3, fun c h1 _ => ?_⟩
  have n0 : ¬ inR (L.geo 0 0) c := fun hc => h1 ⟨0, 0, by decide, by decide, hc⟩
  have n1 : ¬ inR (L.geo 0 1) c := fun hc => h1 ⟨0, 1, by decide, by decide, hc⟩
  exact fr3 c n0 n1

end

end ConPanqueque.V
