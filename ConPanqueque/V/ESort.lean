import ConPanqueque.V.EIntern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The four stores together, and interning `sort u`

`SRep`: the expression store and the three below it (level lists, levels,
names) represented, each with its scratch flag word. `eInternSort`: the key
`[u]`, the level's derived record through the level store, `sortDataE`, then
the intern tail at kind 11.
-/

namespace ConPanqueque.V

structure SRep {σ : Type} (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe : BitVec 64)
    (st : EStore) : Prop where
  e : ERep t L FLe st
  ls : LsRep t L FLs st.lss
  l : LRep t L FLl st.lss.ls
  n : NRep t L FLn st.lss.ls.ns

def lEu := ofString "eu"
def lFll := ofString "fll"
def lFle := ofString "fle"
def lLh := ofString "lh"
def lLpv := ofString "lp"

def eInternSort : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEu))
  (.seq (.assign .local lFl (vv lFll))
  (.seq (.assign .local lDh (vv lEu))
  (.seq (storeDerivedC 3 5 badL)
  (.seq (.assign .local lLh (vv lDo1))
  (.seq (.assign .local lLpv (vv lDo2))
  (.seq (.assign .local lDv ExprData.sortDataE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual (.shift .lsr (vv lEu) (.const 31)) (.const 0)))
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lOn (.load .one (vv lFl)))
  (.seq (.assign .local lPg (descK 11 0))
  (.seq (.assign .local lSg (descK 11 1))
  (.seq (.assign .local lK (vv lKb))
  (.seq (.assign .local lL (.const 1))
    internTwo))))))))))))))

/-- What an intern at kind `k`, with a `w`-word key buffer at `KB`, needs of the layout. -/
structure SepK (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (w k : Nat) : Prop where
  pow : ∀ tier, tier < 2 → (L.geo k tier).n = 2 ^ (L.geo k tier).b ∧ (L.geo k tier).b ≤ 56
  cap : ∀ tier, tier < 2 → (L.geo k tier).cap ≤ 2 ^ 26
  dis : ∀ c, inR (L.geo k 0) c → ¬ inR (L.geo k 1) c
  oth : ∀ k' tier c, k' < 19 → tier < 2 → k' ≠ k → inR (L.geo k' tier) c → ¬ inR (L.geo k 0) c ∧ ¬ inR (L.geo k 1) c
  dsc : ∀ k' tier m, k' < 19 → tier < 2 → m < 8 →
    ¬ inR (L.geo k 0) (descAddr L k' tier + BitVec.ofNat 64 (8 * m)) ∧
    ¬ inR (L.geo k 1) (descAddr L k' tier + BitVec.ofNat 64 (8 * m)) ∧
    ∀ j, j < w → descAddr L k' tier + BitVec.ofNat 64 (8 * m) ≠ KB + BitVec.ofNat 64 (8 * j)
  fls : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) →
    ¬ inR (L.geo k 0) F ∧ ¬ inR (L.geo k 1) F ∧ ∀ j, j < w → F ≠ KB + BitVec.ofNat 64 (8 * j)
  kbo : ∀ j k' tier, j < w → k' < 19 → tier < 2 → ¬ inR (L.geo k' tier) (KB + BitVec.ofNat 64 (8 * j))

section
variable {σ : Type}

theorem erep_sorts {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl SortNode EIdx UInt64)
    (hP : TabAt u L 11 0 Enc.encSort dWN P' (mkN ETag.sort 0)) (hS : TabAt u L 11 1 Enc.encSort dWN Sc' (mkN ETag.sort 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 11 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with sorts := P' }, scr := { st.scr with sorts := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 11 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0, A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    hP, A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4, A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6, A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8, A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0, A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    hS, A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4, A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6, A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8, A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

end

section
variable {σ : Type}

theorem srep_frame {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FLn FLl FLs FLe : BitVec 64} {st : EStore}
    (h : SRep t L FLn FLl FLs FLe st)
    (hfl : u.memory FLn = t.memory FLn ∧ u.memory FLl = t.memory FLl ∧ u.memory FLs = t.memory FLs ∧
      u.memory FLe = t.memory FLe)
    (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → Agree L FLe t u k tier) : SRep u L FLn FLl FLs FLe st := by
  have A : ∀ k tier, k < 19 → tier < 2 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3).1 (hag k tier h2 h3).2 hd
  refine ⟨erep_frame h.e hfl.2.2.2 hd (fun k tier _ h2 h3 => hag k tier h2 h3), ?_, ?_, ?_⟩
  · exact ⟨⟨by rw [hd]; exact h.ls.fl.1, by rw [hfl.2.2.1]; exact h.ls.fl.2⟩,
      A 8 0 (by decide) (by decide) h.ls.pl, A 8 1 (by decide) (by decide) h.ls.sl⟩
  · exact ⟨⟨by rw [hd]; exact h.l.fl.1, by rw [hfl.2.1]; exact h.l.fl.2⟩,
      A 3 0 (by decide) (by decide) h.l.pz, A 4 0 (by decide) (by decide) h.l.ps, A 5 0 (by decide) (by decide) h.l.pm,
      A 6 0 (by decide) (by decide) h.l.pi, A 7 0 (by decide) (by decide) h.l.pp,
      A 3 1 (by decide) (by decide) h.l.sz, A 4 1 (by decide) (by decide) h.l.ss, A 5 1 (by decide) (by decide) h.l.sm,
      A 6 1 (by decide) (by decide) h.l.si, A 7 1 (by decide) (by decide) h.l.sp⟩
  · exact ⟨⟨by rw [hd]; exact h.n.fl.1, by rw [hfl.1]; exact h.n.fl.2⟩,
      A 0 0 (by decide) (by decide) h.n.pa, A 1 0 (by decide) (by decide) h.n.ps, A 2 0 (by decide) (by decide) h.n.pn,
      A 0 1 (by decide) (by decide) h.n.sa, A 1 1 (by decide) (by decide) h.n.ss, A 2 1 (by decide) (by decide) h.n.sn⟩

end

section
variable {σ : Type}

theorem low_frame {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FLn FLl FLs FLe : BitVec 64} {st : EStore}
    (h : SRep t L FLn FLl FLs FLe st)
    (hfl : u.memory FLn = t.memory FLn ∧ u.memory FLl = t.memory FLl ∧ u.memory FLs = t.memory FLs)
    (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 9 → tier < 2 → Agree L FLe t u k tier) (st' : EStore) (hst : st'.lss = st.lss)
    (he : ERep u L FLe st') : SRep u L FLn FLl FLs FLe st' := by
  have A : ∀ k tier, k < 9 → tier < 2 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3).1 (hag k tier h2 h3).2 hd
  refine ⟨he, ?_, ?_, ?_⟩ <;> rw [hst]
  · exact ⟨⟨by rw [hd]; exact h.ls.fl.1, by rw [hfl.2.2]; exact h.ls.fl.2⟩,
      A 8 0 (by decide) (by decide) h.ls.pl, A 8 1 (by decide) (by decide) h.ls.sl⟩
  · exact ⟨⟨by rw [hd]; exact h.l.fl.1, by rw [hfl.2.1]; exact h.l.fl.2⟩,
      A 3 0 (by decide) (by decide) h.l.pz, A 4 0 (by decide) (by decide) h.l.ps, A 5 0 (by decide) (by decide) h.l.pm,
      A 6 0 (by decide) (by decide) h.l.pi, A 7 0 (by decide) (by decide) h.l.pp,
      A 3 1 (by decide) (by decide) h.l.sz, A 4 1 (by decide) (by decide) h.l.ss, A 5 1 (by decide) (by decide) h.l.sm,
      A 6 1 (by decide) (by decide) h.l.si, A 7 1 (by decide) (by decide) h.l.sp⟩
  · exact ⟨⟨by rw [hd]; exact h.n.fl.1, by rw [hfl.1]; exact h.n.fl.2⟩,
      A 0 0 (by decide) (by decide) h.n.pa, A 1 0 (by decide) (by decide) h.n.ps, A 2 0 (by decide) (by decide) h.n.pn,
      A 0 1 (by decide) (by decide) h.n.sa, A 1 1 (by decide) (by decide) h.n.ss, A 2 1 (by decide) (by decide) h.n.sn⟩

def sortScratch : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lLh, lLpv, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

theorem bitU (b : Bool) : ((if b then (1 : UInt64) else 0)).toBitVec = if b then 1 else 0 := by cases b <;> rfl

theorem eInternSort_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (u : LIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 1 11)
    (hkbd : t.memaddrs KB)
    (hb0 : L.base 11 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.sort.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 11 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.sort.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (leu : t.locals.lookup lEu = some (.val (.word (Enc.idxW u))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfll : t.locals.lookup lFll = some (.val (.word FLl))) (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ sortScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (Stop (evaluateHOLFiniteState t eInternSort).1 ∨
      ((evaluateHOLFiniteState t eInternSort).1 =
          some (.returned (.val (.word (Enc.idxW (st.intern (.sort u)).2)))) ∧
        SRep (evaluateHOLFiniteState t eInternSort).2 L FLn FLl FLs FLe (st.intern (.sort u)).1 ∧
        (evaluateHOLFiniteState t eInternSort).2.code = t.code ∧
        (evaluateHOLFiniteState t eInternSort).2.globals = t.globals ∧
        (evaluateHOLFiniteState t eInternSort).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t eInternSort).2.topAddr = t.topAddr ∧
        ∀ c, ¬ inAny L c → c ≠ KB → (evaluateHOLFiniteState t eInternSort).2.memory c = t.memory c)) ∧
      (Stop (evaluateHOLFiniteState t eInternSort).1 ∨ ((st.lss.ls.view u).isSome = true)) := by
  have KB0 : KB + BitVec.ofNat 64 (8 * 0) = KB := by simp
  unfold eInternSort
  rw [seq_normal _ (store_word t (vv lKb) (vv lEu) KB (Enc.idxW u) (eval_vv t lKb _ lkb) (eval_vv t lEu _ leu) hkbd)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW u) else t.memory c }
  have m1 : ∀ c, c ≠ KB → t1.memory c = t.memory c := fun c h => by show (if c = KB then _ else _) = _; rw [if_neg h]
  have flne : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → F ≠ KB := fun F hF => by
    have := (hS.fls F hF).2.2 0 (by decide); rwa [KB0] at this
  have dscne : ∀ k tier m, k < 19 → tier < 2 → m < 8 → descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB :=
    fun k tier m h1 h2 h3 => by have := (hS.dsc k tier m h1 h2 h3).2.2 0 (by decide); rwa [KB0] at this
  have kbo : ∀ k tier, k < 19 → tier < 2 → ¬ inR (L.geo k tier) KB := fun k tier h1 h2 => by
    have := hS.kbo 0 k tier (by decide) h1 h2; rwa [KB0] at this
  have hR1 : SRep t1 L FLn FLl FLs FLe st := srep_frame hR
    ⟨m1 _ (flne _ (Or.inl rfl)), m1 _ (flne _ (Or.inr (Or.inl rfl))), m1 _ (flne _ (Or.inr (Or.inr (Or.inl rfl)))),
      m1 _ (flne _ (Or.inr (Or.inr (Or.inr rfl))))⟩ rfl
    (fun k tier h1 h2 => ⟨fun m hm => m1 _ (dscne k tier m h1 h2 hm), fun c hc => m1 c (fun e => kbo k tier h1 h2 (e ▸ hc))⟩)
  have W : ∀ y, y ∈ sortScratch → ∃ w, t1.locals.lookup y = some (.val (.word w)) := hw
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lFl _ FLl wf (eval_vv t1 lFll _ lfll) hwf)]
  let t2 := setVarHOLFinite lFl (.val (.word FLl)) t1
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lDh _ (Enc.idxW u) wh (eval_vv t2 lEu _ (by lk [t2]; exact leu))
    (by lk [t2]; exact hwh))]
  let t3 := setVarHOLFinite lDh (.val (.word (Enc.idxW u))) t2
  have W3 : ∀ y, y ∈ sortScratch → y ≠ lFl → y ≠ lDh → ∃ w, t3.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t3, t2]; exact hw⟩
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR1 ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  rcases lDerivedC_spec t3 L FLl st.lss.ls hR3.l u (lookup_setVar_same _ _ _) (by lk [t3, t2]; exact ldir)
    (by lk [t3, t2]) (W3 lDt (by decide) (by decide) (by decide)) (W3 lDg (by decide) (by decide) (by decide))
    (W3 lDi (by decide) (by decide) (by decide)) (W3 lDo1 (by decide) (by decide) (by decide))
    (W3 lDo2 (by decide) (by decide) (by decide))
    with hSD | ⟨hvD, D⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD), Or.inl (seq_stop _ _ _ hSD)⟩
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D
  generalize hs1 : evaluateHOLFiniteState t3 (storeDerivedC 3 5 badL) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u4⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  refine ⟨?_, Or.inr hvD⟩
  have back : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u4.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t3, t2]; rfl
  have wv : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ∈ sortScratch →
      ∃ w, u4.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  let ld := st.lss.ls.derived u
  obtain ⟨wlh, hwlh⟩ := wv lLh (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lLh _ _ wlh (eval_vv u4 lDo1 _ o1) hwlh)]
  let u5 := setVarHOLFinite lLh (.val (.word (dWL ld).1)) u4
  obtain ⟨wlp, hwlp⟩ := wv lLpv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lLpv _ _ wlp (eval_vv u5 lDo2 _ (by lk [u5]; exact o2)) (by lk [u5]; exact hwlp))]
  let u6 := setVarHOLFinite lLpv (.val (.word (dWL ld).2)) u5
  let dd := st.derOfView (.sort u)
  have hdd : (dWN dd).1 = (ExprData.sortDataW ld.hash (if ld.hasParam then 1 else 0)).toBitVec := by
    show (st.derOfSort u).toBitVec = _; rw [Der.derOfSort_eq ra]; rfl
  obtain ⟨wv1, hwv1⟩ := wv lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lh6 : u6.locals.lookup (ofString "lh") = some (.val (.word ld.hash.toBitVec)) := by
    show u6.locals.lookup lLh = _; lk [u6, u5]; rfl
  have lp6 : u6.locals.lookup (ofString "lp") =
      some (.val (.word (if ld.hasParam then (1 : UInt64) else 0).toBitVec)) := by
    show u6.locals.lookup lLpv = _; lk [u6]; rw [bitU]; rfl
  have ev6 := ExprData.sortDataE.eval u6 _ _ lh6 lp6
  rw [seq_normal _ (ConsLoop.assign_local u6 lDv _ (dWN dd).1 wv1 (by rw [hdd]; exact ev6) (by lk [u6, u5]; exact hwv1))]
  let u7 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u6
  have g7 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lLh → y ≠ lLpv →
      y ≠ lDv → y ∈ sortScratch → ∃ w, u7.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hy
    obtain ⟨w, hw⟩ := wv y a1 a2 a3 a4 a5 a6 a7 hy; exact ⟨w, by lk [u7, u6, u5]; exact hw⟩
  have b7 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lLh → y ≠ lLpv →
      y ≠ lDv → u7.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10; lk [u7, u6, u5]; exact back y a1 a2 a3 a4 a5 a6 a7
  obtain ⟨wv2, hwv2⟩ := g7 lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u7 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u7 0) hwv2)]
  let u8 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u7
  have eu8 : u8.locals.lookup lEu = some (.val (.word (Enc.idxW u))) := by
    lk [u8]; rw [b7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact leu
  have hskv : @evalHOLExact 64 σ _ u8.toExact (fun x => Classical.propDecidable (u8.memaddrs x))
      (.cmp .notEqual (.shift .lsr (vv lEu) (.const 31)) (.const 0)) =
      some (.val (.word (if EStore.eViewHasScratchChild (.sort u) then 1 else 0))) := by
    rw [ConsLoop.eval_cmp_of u8 .notEqual _ _ _ 0 (eval_shr u8 _ _ _ (eval_vv u8 lEu _ eu8) (by decide)) (eval_const u8 0)]
    simp only [show (31 : BitVec 64).toNat = 31 from rfl, EStore.eViewHasScratchChild]
    have e := ConsGeo.shr31_zero u.word
    have e2 : u.isPersistent = true ↔ u.word.toNat / 2147483648 = 0 := by
      simp only [Idx.isPersistent, Idx.tier, beq_iff_eq]
      constructor
      · intro h; have := congrArg UInt32.toNat h; simpa [UInt32.toNat_div] using this
      · intro h; apply UInt32.toNat_inj.mp; simpa [UInt32.toNat_div] using h
    by_cases hp : u.isPersistent = true
    · have h0 : Enc.idxW u >>> (31 : Nat) = 0 := e.mpr (e2.mp hp)
      have hb : ((Enc.idxW u >>> (31 : Nat)) == 0) = true := beq_iff_eq.mpr h0
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb, hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · have h0 : ¬ (Enc.idxW u >>> (31 : Nat) = 0) := fun x => hp (e2.mpr (e.mp x))
      have hb : ((Enc.idxW u >>> (31 : Nat)) == 0) = false := by simpa using h0
      have hp' : u.isPersistent = false := by simpa using hp
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb, hp', Bool.not_false, ↓reduceIte]
  have g8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lLh → y ≠ lLpv →
      y ≠ lDv → y ≠ lDv2 → y ∈ sortScratch → ∃ w, u8.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 hy
    by_cases e7 : y = lFl
    · subst e7; exact ⟨FLl, by lk [u8, u7, u6, u5]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3, t2]⟩
    · obtain ⟨w, hw⟩ := g7 y a1 a2 a3 a4 a5 a6 e7 a8 a9 a10 hy; exact ⟨w, by lk [u8]; exact hw⟩
  have b8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lLh → y ≠ lLpv →
      y ≠ lDv → y ≠ lDv2 → u8.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; lk [u8]; exact b7 y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  obtain ⟨ws1, hws1⟩ := g8 lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u8 lSk _ _ ws1 hskv hws1)]
  let u9 := setVarHOLFinite lSk (.val (.word (if EStore.eViewHasScratchChild (.sort u) then 1 else 0))) u8
  obtain ⟨wfl, hwfl⟩ := g8 lFl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u9 lFl _ FLe wfl (eval_vv u9 lFle _ (by
      lk [u9]; rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact lfle)) (by lk [u9]; exact hwfl))]
  let u10 := setVarHOLFinite lFl (.val (.word FLe)) u9
  have mem10 : u10.memory = t1.memory := by
    show u4.memory = _; rw [m1']; rfl
  have md10 : u10.memaddrs = t.memaddrs := by show u4.memaddrs = _; rw [d1]; rfl
  have hld : @evalHOLExact 64 σ _ u10.toExact (fun x => Classical.propDecidable (u10.memaddrs x)) (.load .one (vv lFl)) =
      some (.val (.word (if st.scratchOn then 1 else 0))) := by
    rw [eval_load_word u10 _ _ (eval_vv u10 lFl _ (lookup_setVar_same _ _ _)) (by rw [md10]; exact hR.e.fl.1)]
    show some (ValueHOL.val (u10.memory FLe)) = _
    rw [mem10, m1 _ (flne _ (Or.inr (Or.inr (Or.inr rfl)))), hR.e.fl.2]
  obtain ⟨wo, hwo⟩ := g8 lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u10 lOn _ _ wo hld (by lk [u10, u9]; exact hwo))]
  let u11 := setVarHOLFinite lOn (.val (.word (if st.scratchOn then 1 else 0))) u10
  have dir11 : u11.locals.lookup lDir = some (.val (.word L.DIR)) := by
    lk [u11, u10, u9]; rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact ldir
  obtain ⟨wp, hwp⟩ := g8 lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u11 lPg (descK 11 0) (descAddr L 11 0) wp
    (by unfold descK; exact eval_add2 u11 _ _ _ _ (eval_vv u11 lDir _ dir11) (eval_const u11 _)) (by lk [u11, u10, u9]; exact hwp))]
  let u12 := setVarHOLFinite lPg (.val (.word (descAddr L 11 0))) u11
  obtain ⟨wg', hwg'⟩ := g8 lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u12 lSg (descK 11 1) (descAddr L 11 1) wg'
    (by unfold descK; exact eval_add2 u12 _ _ _ _ (eval_vv u12 lDir _ (by lk [u12]; exact dir11)) (eval_const u12 _))
    (by lk [u12, u11, u10, u9]; exact hwg'))]
  let u13 := setVarHOLFinite lSg (.val (.word (descAddr L 11 1))) u12
  obtain ⟨wk, hwk⟩ := g8 lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u13 lK _ KB wk (eval_vv u13 lKb _ (by
      lk [u13, u12, u11, u10, u9]; rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lkb)) (by lk [u13, u12, u11, u10, u9]; exact hwk))]
  let u14 := setVarHOLFinite lK (.val (.word KB)) u13
  obtain ⟨wl, hwl⟩ := g8 lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u14 lL (.const 1) _ wl (eval_const u14 1) (by lk [u14, u13, u12, u11, u10, u9]; exact hwl))]
  let u15 := setVarHOLFinite lL (.val (.word 1)) u14
  have mem15 : u15.memory = t1.memory := mem10
  have md15 : u15.memaddrs = t.memaddrs := md10
  have hR15 : SRep u15 L FLn FLl FLs FLe st := srep_frame hR1 ⟨by rw [mem15], by rw [mem15], by rw [mem15], by rw [mem15]⟩
    md15 (fun _ _ _ _ => ⟨fun _ _ => by rw [mem15], fun _ _ => by rw [mem15]⟩)
  have hK : Words u15 KB (Enc.encSort ⟨u⟩) := by
    intro k hk
    have hk1 : k < 1 := by simpa [Enc.encSort] using hk
    rcases (by omega : k = 0) with rfl
    refine ⟨by rw [md15, KB0]; exact hkbd, ?_⟩
    rw [mem15, KB0]; show (if KB = KB then _ else _) = _; simp [Enc.encSort]
  have hc15 : u15.code = t.code := by show u4.code = _; rw [c1]; rfl
  have hg15 : u15.globals = t.globals := by show u4.globals = _; rw [g1]; rfl
  have ht15 : u15.topAddr = t.topAddr := by show u4.topAddr = _; rw [ta1]; rfl
  have T := tail_spec u15 L 11 Enc.encSort dWN Enc.idxW (mkN ETag.sort 0) (mkN ETag.sort 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN ETag.sort 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.sort 1 (by decide) (by decide) i hi) Enc.encSort_inj hS.cap
    st.pers.sorts st.scr.sorts st.scratchOn (EStore.eViewHasScratchChild (.sort u)) ⟨u⟩ dd KB hR15.e.p2 hR15.e.s2
    hS.pow hS.dis (fun tier m ht hm => ⟨(hS.dsc 11 tier m (by decide) ht hm).1, (hS.dsc 11 tier m (by decide) ht hm).2.1⟩)
    hK (by simp [Enc.encSort])
    (fun i hi => by
      have hi1 : i < 1 := by simpa [Enc.encSort] using hi
      rcases (by omega : i = 0) with rfl
      exact ⟨hS.kbo 0 11 0 (by decide) (by decide) (by decide), hS.kbo 0 11 1 (by decide) (by decide) (by decide)⟩)
    ⟨by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7], by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7]; rfl, by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7], by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7]⟩
    (by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7]) (by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7]) (by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7]) (by lk [u15, u14, u13, u12, u11, u10, u9, u8, u7])
  rcases T with hs | ⟨hr, hP', hS', c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  have hint := estore_sort st u
  simp only at hint
  rw [hint]
  have agO : ∀ k tier, k < 19 → tier < 2 → k ≠ 11 → Agree L FLe u15 (evaluateHOLFiniteState u15 internTwo).2 k tier :=
    fun k tier h1 h2 h4 => ⟨fun m hm => fr3 _ (hS.dsc k tier m h1 h2 hm).1 (hS.dsc k tier m h1 h2 hm).2.1,
      fun c hc => fr3 c (hS.oth k tier c h1 h2 h4 hc).1 (hS.oth k tier c h1 h2 h4 hc).2⟩
  have flF : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) →
      (evaluateHOLFiniteState u15 internTwo).2.memory F = u15.memory F := fun F hF =>
    fr3 F (hS.fls F hF).1 (hS.fls F hF).2.1
  refine Or.inr ⟨hr, ?_, c3.trans hc15, g3.trans hg15, d3.trans md15, ta3.trans ht15, fun c h1 h2 => ?_⟩
  · refine low_frame hR15 ⟨flF _ (Or.inl rfl), flF _ (Or.inr (Or.inl rfl)), flF _ (Or.inr (Or.inr (Or.inl rfl)))⟩ d3
      (fun k tier h1 h2 => agO k tier (by omega) h2 (by omega)) _ rfl ?_
    exact erep_sorts hR15.e _ _ hP' hS' (flF _ (Or.inr (Or.inr (Or.inr rfl)))) d3
      (fun k tier _ h2 h3 h4 => agO k tier h2 h3 h4)
  · have n0 : ¬ inR (L.geo 11 0) c := fun hc => h1 ⟨11, 0, by decide, by decide, hc⟩
    have n1 : ¬ inR (L.geo 11 1) c := fun hc => h1 ⟨11, 1, by decide, by decide, hc⟩
    rw [fr3 c n0 n1, mem15]; exact m1 c h2

end

end ConPanqueque.V
