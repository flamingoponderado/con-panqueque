import ConPanqueque.V.LsIntern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena
open ConPanqueque.Hash (leanStringHash)

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

theorem nrep_nums {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ns : NStore}
    (h : NRep t L FL ns) (P' Sc' : Tbl NumNode NIdx UInt64)
    (hP : TabAt u L 2 0 Enc.encNum dWN P' (mkN NTag.num 0)) (hS : TabAt u L 2 1 Enc.encNum dWN Sc' (mkN NTag.num 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 2 → Agree L FL t u k tier) :
    NRep u L FL { ns with pers := { ns.pers with nums := P' }, scr := { ns.scr with nums := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 2 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩, A 0 0 (by decide) (by decide) (by decide) h.pa,
    A 1 0 (by decide) (by decide) (by decide) h.ps, hP, A 0 1 (by decide) (by decide) (by decide) h.sa,
    A 1 1 (by decide) (by decide) (by decide) h.ss, hS⟩


theorem nrep_strs {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ns : NStore}
    (h : NRep t L FL ns) (P' Sc' : Tbl StrNode NIdx UInt64)
    (hP : TabAt u L 1 0 Enc.encStr dWN P' (mkN NTag.str 0)) (hS : TabAt u L 1 1 Enc.encStr dWN Sc' (mkN NTag.str 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 1 → Agree L FL t u k tier) :
    NRep u L FL { ns with pers := { ns.pers with strs := P' }, scr := { ns.scr with strs := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 1 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩, A 0 0 (by decide) (by decide) (by decide) h.pa,
    hP, A 2 0 (by decide) (by decide) (by decide) h.pn, A 0 1 (by decide) (by decide) (by decide) h.sa,
    hS, A 2 1 (by decide) (by decide) (by decide) h.sn⟩

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

def lDp := ofString "dp"
def lNw := ofString "nw"
def lEp := ofString "ep"

/-- `num p n`: the caller has put the key `idxW p :: limbs n` at `ekb`, its length in `en`, the
prefix handle in `ep` and the number's low word in `nw`. -/
def nNumWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFln))
  (.seq (.assign .local lDh (vv lEp))
  (.seq (storeDerivedC 0 3 badN)
  (.seq (.assign .local lDp (vv lDo1))
  (.seq (.assign .local lDv Der.numDerE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.const 0)) rest))))))

def numScratch : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lDp, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

section
variable {σ : Type}

theorem nInternNum_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (p : NIdx) (n : Nat)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encNum ⟨p, n⟩).length 2)
    (hK : Words t KB (Enc.encNum ⟨p, n⟩)) (hwl : (Enc.encNum ⟨p, n⟩).length < 2 ^ 61)
    (hb0 : L.base 2 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.num.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 2 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.num.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encNum ⟨p, n⟩).length))))
    (lep : t.locals.lookup lEp = some (.val (.word (Enc.idxW p))))
    (lnw : t.locals.lookup lNw = some (.val (.word (UInt64.ofNat n).toBitVec)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfln : t.locals.lookup lFln = some (.val (.word FLn)))
    (hw : ∀ y, y ∈ numScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (XRes t L FLn FLl FLs FLe KB (Enc.encNum ⟨p, n⟩).length (withN st (st.lss.ls.ns.intern (.num p n)).1)
      (st.lss.ls.ns.intern (.num p n)).2 (evaluateHOLFiniteState t (nNumWith (rRestE 2 (vv lEn) lFln)))) ∧
      (Stop (evaluateHOLFiniteState t (nNumWith (rRestE 2 (vv lEn) lFln))).1 ∨ ((st.lss.ls.ns.view p).isSome = true)) := by
  have W : ∀ y, y ∈ numScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  unfold nNumWith
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lFl _ FLn wf (eval_vv t lFln _ lfln) hwf)]
  let t2 := setVarHOLFinite lFl (.val (.word FLn)) t
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lDh _ (Enc.idxW p) wh (eval_vv t2 lEp _ (by lk [t2]; exact lep))
    (by lk [t2]; exact hwh))]
  let t3 := setVarHOLFinite lDh (.val (.word (Enc.idxW p))) t2
  have W3 : ∀ y, y ∈ numScratch → y ≠ lFl → y ≠ lDh → ∃ w, t3.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t3, t2]; exact hw⟩
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  rcases nDerivedC_spec t3 L FLn st.lss.ls.ns hR3.n p (lookup_setVar_same _ _ _) (by lk [t3, t2]; exact ldir)
    (by lk [t3, t2]) (W3 lDt (by decide) (by decide) (by decide)) (W3 lDg (by decide) (by decide) (by decide))
    (W3 lDi (by decide) (by decide) (by decide)) (W3 lDo1 (by decide) (by decide) (by decide))
    (W3 lDo2 (by decide) (by decide) (by decide))
    with hSD | ⟨hvD, D⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD), Or.inl (seq_stop _ _ _ hSD)⟩
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D
  generalize hs1 : evaluateHOLFiniteState t3 (storeDerivedC 0 3 badN) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u4⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  refine ⟨?_, Or.inr hvD⟩
  have back : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u4.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t3, t2]
  have wv : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ∈ numScratch →
      ∃ w, u4.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  let dpd := st.lss.ls.ns.derived p
  obtain ⟨wdp, hwdp⟩ := wv lDp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lDp _ _ wdp (eval_vv u4 lDo1 _ o1) hwdp)]
  let u5 := setVarHOLFinite lDp (.val (.word (dWN dpd).1)) u4
  let dd := st.lss.ls.ns.derOfView (.num p n)
  have hdd : dd = Der.numDerW dpd (UInt64.ofNat n) := Der.nnum_eq ra st.lss.ls.ns p n
  have nw5 : u5.locals.lookup lNw = some (.val (.word (UInt64.ofNat n).toBitVec)) := by
    lk [u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lnw
  obtain ⟨wv1, hwv1⟩ := wv lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDv _ (dWN dd).1 wv1
    (by rw [hdd]; exact Der.numDerE.eval u5 dpd _ (by show u5.locals.lookup lDp = _; lk [u5]; rfl) nw5)
    (by lk [u5]; exact hwv1))]
  let u6 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u5
  obtain ⟨wv2, hwv2⟩ := wv lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u6 0) (by lk [u6, u5]; exact hwv2))]
  let u7 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u6
  obtain ⟨wsk, hwsk⟩ := wv lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u7 lSk (.const 0) (if false then 1 else 0) wsk (eval_const u7 0)
    (by lk [u7, u6, u5]; exact hwsk))]
  let u8 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) u7
  have mem8 : u8.memory = t.memory := by show u4.memory = _; rw [m1']; rfl
  have md8 : u8.memaddrs = t.memaddrs := by show u4.memaddrs = _; rw [d1]; rfl
  have hc8 : u8.code = t.code := by show u4.code = _; rw [c1]; rfl
  have hg8 : u8.globals = t.globals := by show u4.globals = _; rw [g1]; rfl
  have ht8 : u8.topAddr = t.topAddr := by show u4.topAddr = _; rw [ta1]; rfl
  have hR8 : SRep u8 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [mem8], by rw [mem8], by rw [mem8], by rw [mem8]⟩ md8
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem8], fun _ _ => by rw [mem8]⟩)
  have g : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDp → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → y ∈ numScratch → ∃ w, u8.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 hy
    obtain ⟨w, hw⟩ := wv y a1 a2 a3 a4 a5 a6 a7 hy; exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
  have b8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDp → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → u8.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; lk [u8, u7, u6, u5]; exact back y a1 a2 a3 a4 a5 a6 a7
  have hint := nstore_num st.lss.ls.ns p n
  simp only at hint
  have R := rRestE_spec t u8 L FLn FLl FLs FLe KB FLn (Enc.encNum ⟨p, n⟩).length 2 lFln (vv lEn) (by decide)
    st.lss.ls.ns.scratchOn Enc.encNum dWN Enc.idxW
    Enc.encNum_inj (mkN NTag.num 0) (mkN NTag.num 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN NTag.num 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN NTag.num 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.ns.pers.nums st.lss.ls.ns.scr.nums false ⟨p, n⟩ dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withN st (st.lss.ls.ns.intern (.num p n)).1))
    (fun v' hP hS' hf hd' hag => by
      rw [hint]
      exact srep_withN hR8 2 _ (nrep_nums hR8.n _ _ hP hS' (hf _ (Or.inl rfl)) hd'
        (fun k tier h1 h2 h3 => hag k tier h1 h2 h3)) hf hd' hag (by decide))
    hS (by decide) rfl hwl (Or.inl rfl) hR8.n.fl hR8.n.pn hR8.n.sn
    (fun j hj => by rw [md8, mem8]; exact hK j hj)
    (by lk [u8, u7, u6]) (by lk [u8, u7]) (by lk [u8])
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lfln)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact ldir)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lkb)
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨FLn, by lk [u8, u7, u6, u5]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3, t2]⟩
      · obtain ⟨w, hw⟩ := g lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩)
    (fun x hx => by
      have : x.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encNum ⟨p, n⟩).length))) := by
        rw [hx _ (by decide), b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact len
      exact eval_vv x lEn _ this)
  rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  refine Or.inr ⟨by rw [hr, hint], hQ, c3.trans hc8, g3.trans hg8, d3.trans md8, ta3.trans ht8, fun c h1 _ => ?_⟩
  have n0 : ¬ inR (L.geo 2 0) c := fun hc => h1 ⟨2, 0, by decide, by decide, hc⟩
  have n1 : ¬ inR (L.geo 2 1) c := fun hc => h1 ⟨2, 1, by decide, by decide, hc⟩
  rw [fr3 c n0 n1, mem8]


end

def nStrTail (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFln))
  (.seq (.assign .local lDh (vv lEp))
  (.seq (storeDerivedC 0 3 badN)
  (.seq (.assign .local lDp (vv lDo1))
  (.seq (.assign .local lDv Der.strDerE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.const 0)) rest))))))


section
variable {σ : Type}

theorem nStrTail_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (p : NIdx) (s : String)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encStr ⟨p, s⟩).length 1)
    (hK : Words t KB (Enc.encStr ⟨p, s⟩)) (hwl : (Enc.encStr ⟨p, s⟩).length < 2 ^ 61)
    (hb0 : L.base 1 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.str.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 1 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.str.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encStr ⟨p, s⟩).length))))
    (lep : t.locals.lookup lEp = some (.val (.word (Enc.idxW p))))
    (lhs : t.locals.lookup lHs = some (.val (.word (leanStringHash s.toByteArray.data.toList).toBitVec)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfln : t.locals.lookup lFln = some (.val (.word FLn)))
    (hw : ∀ y, y ∈ numScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (XRes t L FLn FLl FLs FLe KB (Enc.encStr ⟨p, s⟩).length (withN st (st.lss.ls.ns.intern (.str p s)).1)
      (st.lss.ls.ns.intern (.str p s)).2 (evaluateHOLFiniteState t (nStrTail (rRestE 1 (vv lEn) lFln)))) ∧
      (Stop (evaluateHOLFiniteState t (nStrTail (rRestE 1 (vv lEn) lFln))).1 ∨ ((st.lss.ls.ns.view p).isSome = true)) := by
  have W : ∀ y, y ∈ numScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  unfold nStrTail
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lFl _ FLn wf (eval_vv t lFln _ lfln) hwf)]
  let t2 := setVarHOLFinite lFl (.val (.word FLn)) t
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lDh _ (Enc.idxW p) wh (eval_vv t2 lEp _ (by lk [t2]; exact lep))
    (by lk [t2]; exact hwh))]
  let t3 := setVarHOLFinite lDh (.val (.word (Enc.idxW p))) t2
  have W3 : ∀ y, y ∈ numScratch → y ≠ lFl → y ≠ lDh → ∃ w, t3.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t3, t2]; exact hw⟩
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  rcases nDerivedC_spec t3 L FLn st.lss.ls.ns hR3.n p (lookup_setVar_same _ _ _) (by lk [t3, t2]; exact ldir)
    (by lk [t3, t2]) (W3 lDt (by decide) (by decide) (by decide)) (W3 lDg (by decide) (by decide) (by decide))
    (W3 lDi (by decide) (by decide) (by decide)) (W3 lDo1 (by decide) (by decide) (by decide))
    (W3 lDo2 (by decide) (by decide) (by decide))
    with hSD | ⟨hvD, D⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD), Or.inl (seq_stop _ _ _ hSD)⟩
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D
  generalize hs1 : evaluateHOLFiniteState t3 (storeDerivedC 0 3 badN) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u4⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  refine ⟨?_, Or.inr hvD⟩
  have back : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u4.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t3, t2]
  have wv : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ∈ numScratch →
      ∃ w, u4.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  let dpd := st.lss.ls.ns.derived p
  obtain ⟨wdp, hwdp⟩ := wv lDp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lDp _ _ wdp (eval_vv u4 lDo1 _ o1) hwdp)]
  let u5 := setVarHOLFinite lDp (.val (.word (dWN dpd).1)) u4
  let dd := st.lss.ls.ns.derOfView (.str p s)
  have hdd : dd = Der.strDerW dpd (leanStringHash s.toByteArray.data.toList) := Der.nstr_eq ra st.lss.ls.ns p s
  have nw5 : u5.locals.lookup lHs = some (.val (.word (leanStringHash s.toByteArray.data.toList).toBitVec)) := by
    lk [u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lhs
  obtain ⟨wv1, hwv1⟩ := wv lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDv _ (dWN dd).1 wv1
    (by rw [hdd]; exact Der.strDerE.eval u5 dpd _ (by show u5.locals.lookup lDp = _; lk [u5]; rfl) nw5)
    (by lk [u5]; exact hwv1))]
  let u6 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u5
  obtain ⟨wv2, hwv2⟩ := wv lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u6 0) (by lk [u6, u5]; exact hwv2))]
  let u7 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u6
  obtain ⟨wsk, hwsk⟩ := wv lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u7 lSk (.const 0) (if false then 1 else 0) wsk (eval_const u7 0)
    (by lk [u7, u6, u5]; exact hwsk))]
  let u8 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) u7
  have mem8 : u8.memory = t.memory := by show u4.memory = _; rw [m1']; rfl
  have md8 : u8.memaddrs = t.memaddrs := by show u4.memaddrs = _; rw [d1]; rfl
  have hc8 : u8.code = t.code := by show u4.code = _; rw [c1]; rfl
  have hg8 : u8.globals = t.globals := by show u4.globals = _; rw [g1]; rfl
  have ht8 : u8.topAddr = t.topAddr := by show u4.topAddr = _; rw [ta1]; rfl
  have hR8 : SRep u8 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [mem8], by rw [mem8], by rw [mem8], by rw [mem8]⟩ md8
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem8], fun _ _ => by rw [mem8]⟩)
  have g : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDp → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → y ∈ numScratch → ∃ w, u8.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 hy
    obtain ⟨w, hw⟩ := wv y a1 a2 a3 a4 a5 a6 a7 hy; exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
  have b8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDp → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → u8.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; lk [u8, u7, u6, u5]; exact back y a1 a2 a3 a4 a5 a6 a7
  have hint := nstore_str st.lss.ls.ns p s
  simp only at hint
  have R := rRestE_spec t u8 L FLn FLl FLs FLe KB FLn (Enc.encStr ⟨p, s⟩).length 1 lFln (vv lEn) (by decide)
    st.lss.ls.ns.scratchOn Enc.encStr dWN Enc.idxW
    Enc.encStr_inj (mkN NTag.str 0) (mkN NTag.str 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN NTag.str 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN NTag.str 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.ns.pers.strs st.lss.ls.ns.scr.strs false ⟨p, s⟩ dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withN st (st.lss.ls.ns.intern (.str p s)).1))
    (fun v' hP hS' hf hd' hag => by
      rw [hint]
      exact srep_withN hR8 1 _ (nrep_strs hR8.n _ _ hP hS' (hf _ (Or.inl rfl)) hd'
        (fun k tier h1 h2 h3 => hag k tier h1 h2 h3)) hf hd' hag (by decide))
    hS (by decide) rfl hwl (Or.inl rfl) hR8.n.fl hR8.n.ps hR8.n.ss
    (fun j hj => by rw [md8, mem8]; exact hK j hj)
    (by lk [u8, u7, u6]) (by lk [u8, u7]) (by lk [u8])
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lfln)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact ldir)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lkb)
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨FLn, by lk [u8, u7, u6, u5]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3, t2]⟩
      · obtain ⟨w, hw⟩ := g lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩
      · obtain ⟨w, hw⟩ := g lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, hw⟩)
    (fun x hx => by
      have : x.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encStr ⟨p, s⟩).length))) := by
        rw [hx _ (by decide), b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact len
      exact eval_vv x lEn _ this)
  rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  refine Or.inr ⟨by rw [hr, hint], hQ, c3.trans hc8, g3.trans hg8, d3.trans md8, ta3.trans ht8, fun c h1 _ => ?_⟩
  have n0 : ¬ inR (L.geo 1 0) c := fun hc => h1 ⟨1, 0, by decide, by decide, hc⟩
  have n1 : ¬ inR (L.geo 1 1) c := fun hc => h1 ⟨1, 1, by decide, by decide, hc⟩
  rw [fr3 c n0 n1, mem8]


/-- `str p s`: the caller has put the key `idxW p :: strW s` at `ekb`, its length in `en`, the prefix
handle in `ep`, the byte count in `hn` and the bytes' address `ekb + 8` in `ha`. -/
def nStrWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq strHash (.seq (.assign .local lHs (vv lHh)) (nStrTail rest))

def strScratch : List MlS := lHh :: lHk :: lHs :: numScratch

theorem words_tail {t : PanSemStateFiniteExact 64 σ} {KB w : BitVec 64} {ws : List (BitVec 64)}
    (h : Words t KB (w :: ws)) : Words t (KB + 8) ws := by
  intro j hj
  have e : KB + 8 + BitVec.ofNat 64 (8 * j) = KB + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
    congr 2; omega
  rw [e]; exact h (j + 1) (by simp; omega)

theorem nInternStr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (p : NIdx) (s : String)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encStr ⟨p, s⟩).length 1)
    (hK : Words t KB (Enc.encStr ⟨p, s⟩)) (hwl : (Enc.encStr ⟨p, s⟩).length < 2 ^ 61)
    (hb0 : L.base 1 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.str.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 1 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + NTag.str.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encStr ⟨p, s⟩).length))))
    (lep : t.locals.lookup lEp = some (.val (.word (Enc.idxW p))))
    (lha : t.locals.lookup lHa = some (.val (.word (KB + 8))))
    (lhn : t.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 s.toByteArray.data.toList.length))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfln : t.locals.lookup lFln = some (.val (.word FLn)))
    (hw : ∀ y, y ∈ strScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (XRes t L FLn FLl FLs FLe KB (Enc.encStr ⟨p, s⟩).length (withN st (st.lss.ls.ns.intern (.str p s)).1)
      (st.lss.ls.ns.intern (.str p s)).2 (evaluateHOLFiniteState t (nStrWith (rRestE 1 (vv lEn) lFln)))) ∧
      (Stop (evaluateHOLFiniteState t (nStrWith (rRestE 1 (vv lEn) lFln))).1 ∨ ((st.lss.ls.ns.view p).isSome = true)) := by
  have W : ∀ y, y ∈ strScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  let bs := s.toByteArray.data.toList
  have hbl : (Enc.encStr ⟨p, s⟩).length = bs.length + 1 := by simp [Enc.encStr, Enc.strW, bs]
  unfold nStrWith
  have H := strHash_spec t (KB + 8) bs (by omega) (words_tail hK) lha lhn (W lHh (by decide)) (W lHk (by decide))
  simp only at H
  rcases H with hs | ⟨hn, yp⟩
  · have ⟨res, hres⟩ : ∃ res, (evaluateHOLFiniteState t strHash).1 = some res := by
      rcases hs with h | ⟨ev, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    rw [seq_abort _ _ _ _ hres]; exact ⟨Or.inl hs, Or.inl hs⟩
  generalize hy : evaluateHOLFiniteState t strHash = q at hn yp
  obtain ⟨qr, y⟩ := q
  simp only at hn yp; subst hn
  rw [seq_normal _ hy]
  obtain ⟨ym, yd, yc, yg, yt, yfr, yh⟩ := yp
  obtain ⟨ws, hws⟩ := W lHs (by decide)
  rw [seq_normal _ (ConsLoop.assign_local y lHs _ _ ws (eval_vv y lHh _ yh)
    (by rw [yfr _ (by decide) (by decide) (by decide) (by decide)]; exact hws))]
  let y1 := setVarHOLFinite lHs (.val (.word (leanStringHash bs).toBitVec)) y
  have yb : ∀ z, z ≠ lHa → z ≠ lHn → z ≠ lHh → z ≠ lHk → z ≠ lHs → y1.locals.lookup z = t.locals.lookup z := by
    intro z a b c d e; lk [y1]; exact yfr z a b c d
  have nd : ∀ z ∈ numScratch, z ≠ lHa ∧ z ≠ lHn ∧ z ≠ lHh ∧ z ≠ lHk ∧ z ≠ lHs := by decide
  have m1 : y1.memory = t.memory := ym
  have hR1 : SRep y1 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [m1], by rw [m1], by rw [m1], by rw [m1]⟩ yd
    (fun _ _ _ _ => ⟨fun _ _ => by rw [m1], fun _ _ => by rw [m1]⟩)
  have T := nStrTail_spec ra y1 L FLn FLl FLs FLe KB st p s hR1 hS (fun j hj => by rw [m1]; exact ⟨yd ▸ (hK j hj).1, (hK j hj).2⟩)
    hwl hb0 hb1 (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lkb)
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact len)
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lep)
    (lookup_setVar_same _ _ _)
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lfln)
    (fun z hz => by
      obtain ⟨a, b, c, d, e⟩ := nd z hz
      obtain ⟨w, hw⟩ := W z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
      exact ⟨w, by rw [yb z a b c d e]; exact hw⟩)
  obtain ⟨T, TV⟩ := T
  refine ⟨?_, TV⟩
  rcases T with hs | ⟨a, b, c, d, e, f, g⟩
  · exact Or.inl hs
  exact Or.inr ⟨a, b, c.trans yc, d.trans yg, e.trans yd, f.trans yt, fun c h1 h2 => by rw [g c h1 h2]; exact congrFun ym c⟩

end

end ConPanqueque.V
