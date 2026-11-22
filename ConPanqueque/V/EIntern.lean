import ConPanqueque.V.Layout
import ConPanqueque.V.Der
import ConPanqueque.ConsApp2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning an expression node into the whole store

The layout's well-formedness (`LayoutOK`): every table's geometry within
bounds, its handle base the one `Idx.mk`/`Idx.mkWide` gives, table regions
pairwise disjoint, and the directory, the flag words and the key buffer
outside every table. Then a change confined to one table's region keeps
every other table represented (`erep_frame`).
-/

namespace ConPanqueque.V

/-- All table regions of the layout (19 kinds × 2 tiers). -/
def inAny (L : Layout) (a : BitVec 64) : Prop := ∃ k tier, k < 19 ∧ tier < 2 ∧ inR (L.geo k tier) a

structure LayoutOK (L : Layout) (FLs KB : BitVec 64) (kbW : Nat) : Prop where
  pow : ∀ k tier, k < 19 → tier < 2 → (L.geo k tier).n = 2 ^ (L.geo k tier).b
  b56 : ∀ k tier, k < 19 → tier < 2 → (L.geo k tier).b ≤ 56
  cap : ∀ k tier, k < 19 → tier < 2 → (L.geo k tier).cap < 2 ^ 26
  disj : ∀ k1 t1 k2 t2 a, k1 < 19 → t1 < 2 → k2 < 19 → t2 < 2 → (k1 ≠ k2 ∨ t1 ≠ t2) →
    inR (L.geo k1 t1) a → ¬ inR (L.geo k2 t2) a
  dirOut : ∀ m, m < 8 * 38 → ¬ inAny L (L.DIR + BitVec.ofNat 64 (8 * m))
  flOut : ∀ m, m < 4 → ¬ inAny L (FLs + BitVec.ofNat 64 (8 * m))
  kbOut : ∀ m, m < kbW → ¬ inAny L (KB + BitVec.ofNat 64 (8 * m))

section
variable {σ : Type}

/-- A change outside every table region keeps a table represented at its own place. -/
theorem tabAt_frame {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]
    {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {k tier : Nat} {enc : α → List (BitVec 64)}
    {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ} {mkI : Nat → ι} (h : TabAt t L k tier enc dW tb mkI)
    (hdesc : ∀ m, m < 8 → u.memory (descAddr L k tier + BitVec.ofNat 64 (8 * m)) =
      t.memory (descAddr L k tier + BitVec.ofNat 64 (8 * m)))
    (hm : ∀ c, inR (L.geo k tier) c → u.memory c = t.memory c) (hd : u.memaddrs = t.memaddrs) :
    TabAt u L k tier enc dW tb mkI := by
  obtain ⟨hD, hc, rows, ders, slots, hu, hR⟩ := h
  exact ⟨fun m hm' => by rw [hd, hdesc m hm']; exact hD m hm', hc, rows, ders, slots, hu, tierRepV_frame hR hm hd⟩

end

def lEf := ofString "ef"
def lEa := ofString "ea"
def lKb := ofString "ekb"
def lDfv := ofString "df"
def lDav := ofString "da"

/-- The descriptor pointer for kind `k` at a tier, from the directory local. -/
def descK (k tier : Nat) : ExpHOL 64 := .op .add [vv lDir, .const (BitVec.ofNat 64 (64 * (19 * tier + k)))]

/-- `app f a` into the expression store: key words to the buffer, the children's derived words,
the node's, the scratch-child bit, the two tiers' descriptors and the flag, then `internTwo`. -/
def eInternApp : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEf))
  (.seq (.store (.op .add [vv lKb, .const 8]) (vv lEa))
  (.seq (.assign .local lDh (vv lEf))
  (.seq (storeDerived 9 10)
  (.seq (.assign .local lDfv (vv lDo1))
  (.seq (.assign .local lDh (vv lEa))
  (.seq (storeDerived 9 10)
  (.seq (.assign .local lDav (vv lDo1))
  (.seq (.assign .local lDv Der.appDataE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual
      (.op .or [.shift .lsr (vv lEf) (.const 31), .shift .lsr (vv lEa) (.const 31)]) (.const 0)))
  (.seq (.assign .local lOn (.load .one (vv lFl)))
  (.seq (.assign .local lPg (descK 13 0))
  (.seq (.assign .local lSg (descK 13 1))
  (.seq (.assign .local lK (vv lKb))
  (.seq (.assign .local lL (.const 2))
    internTwo)))))))))))))))

section
variable {σ : Type}

/-- Memory agrees on everything the store representation reads. -/
def Agree (L : Layout) (FL : BitVec 64) (t u : PanSemStateFiniteExact 64 σ) (k tier : Nat) : Prop :=
  (∀ m, m < 8 → u.memory (descAddr L k tier + BitVec.ofNat 64 (8 * m)) =
    t.memory (descAddr L k tier + BitVec.ofNat 64 (8 * m))) ∧
  (∀ c, inR (L.geo k tier) c → u.memory c = t.memory c)

theorem erep_frame {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → Agree L FL t u k tier) : ERep u L FL st := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h1 h2 h3).1 (hag k tier h1 h2 h3).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) h.p0, A 10 0 (by decide) (by decide) (by decide) h.p1,
    A 11 0 (by decide) (by decide) (by decide) h.p2, A 12 0 (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) h.p4, A 14 0 (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) h.p6, A 16 0 (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) h.p8, A 18 0 (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) h.s0, A 10 1 (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) h.s2, A 12 1 (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) h.s4, A 14 1 (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) h.s6, A 16 1 (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) h.s8, A 18 1 (by decide) (by decide) (by decide) h.s9⟩

end

section
variable {σ : Type}

theorem erep_apps {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl AppNode EIdx UInt64)
    (hP : TabAt u L 13 0 Enc.encApp dWN P' (mkW 0)) (hS : TabAt u L 13 1 Enc.encApp dWN Sc' (mkW 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 13 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with apps := P' }, scr := { st.scr with apps := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 13 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0, A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    A 11 0 (by decide) (by decide) (by decide) (by decide) h.p2, A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    hP, A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6, A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8, A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0, A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2, A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    hS, A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6, A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8, A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

theorem idxW_mkW (r : UInt32) (hr : r ≤ 1) (i : Nat) (hi : i < 2 ^ 30) :
    Enc.idxW (mkW (k := .expr) r i) = r.toUInt64.toBitVec * 2147483648 + 1073741824 + BitVec.ofNat 64 i :=
  ConsIntern.mkWide_word r i hr hi

/-- Everything `eInternApp` writes to or needs as words. -/
def scratchW : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lDfv, lDav, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL]

/-- What `eInternApp` guarantees. -/
def EIRes (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL KB : BitVec 64) (st : EStore) (f a : EIdx)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨ (r.1 = some (.returned (.val (.word (Enc.idxW (st.intern (.app f a)).2)))) ∧
    ERep r.2 L FL (st.intern (.app f a)).1 ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
    ∀ c, ¬ inAny L c → c ≠ KB → c ≠ KB + 8 → r.2.memory c = t.memory c)

theorem eInternApp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FL KB : BitVec 64) (st : EStore) (f a : EIdx)
    (hR : ERep t L FL st)
    (hpow : ∀ tier, tier < 2 → (L.geo 13 tier).n = 2 ^ (L.geo 13 tier).b ∧ (L.geo 13 tier).b ≤ 56)
    (hdis : ∀ c, inR (L.geo 13 0) c → ¬ inR (L.geo 13 1) c)
    (hdisO : ∀ k tier c, 9 ≤ k → k < 19 → tier < 2 → k ≠ 13 → inR (L.geo k tier) c →
      ¬ inR (L.geo 13 0) c ∧ ¬ inR (L.geo 13 1) c)
    (hdirO : ∀ k tier m, 9 ≤ k → k < 19 → tier < 2 → m < 8 →
      ¬ inR (L.geo 13 0) (descAddr L k tier + BitVec.ofNat 64 (8 * m)) ∧
      ¬ inR (L.geo 13 1) (descAddr L k tier + BitVec.ofNat 64 (8 * m)) ∧
      descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB ∧ descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB + 8)
    (hflO : ¬ inR (L.geo 13 0) FL ∧ ¬ inR (L.geo 13 1) FL ∧ FL ≠ KB ∧ FL ≠ KB + 8)
    (hkbO : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → ¬ inR (L.geo k tier) KB ∧ ¬ inR (L.geo k tier) (KB + 8))
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (hb0 : L.base 13 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824)
    (hb1 : L.base 13 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (lef : t.locals.lookup lEf = some (.val (.word (Enc.idxW f))))
    (lea : t.locals.lookup lEa = some (.val (.word (Enc.idxW a))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR))) (lfl : t.locals.lookup lFl = some (.val (.word FL)))
    (hw : ∀ y, y ∈ scratchW → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    EIRes t L FL KB st f a (evaluateHOLFiniteState t eInternApp) := by
  have W : ∀ y, y ∈ scratchW → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  unfold eInternApp
  -- the key
  rw [seq_normal _ (store_word t (vv lKb) (vv lEf) KB (Enc.idxW f) (eval_vv t lKb _ lkb) (eval_vv t lEf _ lef) hkbd.1)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW f) else t.memory c }
  rw [seq_normal _ (store_word t1 _ (vv lEa) (KB + 8) (Enc.idxW a)
    (eval_add2 t1 _ _ _ _ (eval_vv t1 lKb _ lkb) (eval_const t1 8)) (eval_vv t1 lEa _ lea) hkbd.2)]
  let t2 : PanSemStateFiniteExact 64 σ :=
    { t1 with memory := fun c => if c = KB + 8 then .word (Enc.idxW a) else t1.memory c }
  have m2 : ∀ c, c ≠ KB → c ≠ KB + 8 → t2.memory c = t.memory c := by
    intro c h1 h2; show (if c = KB + 8 then _ else if c = KB then _ else _) = _; rw [if_neg h2, if_neg h1]
  have hR2 : ERep t2 L FL st := erep_frame hR (m2 _ hflO.2.2.1 hflO.2.2.2) rfl (fun k tier h1 h2 h3 =>
    ⟨fun m hm => m2 _ (hdirO k tier m h1 h2 h3 hm).2.2.1 (hdirO k tier m h1 h2 h3 hm).2.2.2,
     fun c hc => m2 c (fun e => (hkbO k tier h1 h2 h3).1 (e ▸ hc)) (fun e => (hkbO k tier h1 h2 h3).2 (e ▸ hc))⟩)
  -- the children's derived words
  obtain ⟨w0, hw0⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lDh _ _ w0 (eval_vv t2 lEf _ lef) hw0)]
  let t3 := setVarHOLFinite lDh (.val (.word (Enc.idxW f))) t2
  have hR3 : ERep t3 L FL st := erep_frame hR2 rfl rfl (fun _ _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have W3 : ∀ y, y ∈ scratchW → ∃ w, t3.locals.lookup y = some (.val (.word w)) := by
    intro y hy; by_cases e : y = lDh
    · subst e; exact ⟨_, lookup_setVar_same _ _ _⟩
    · obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t3]; exact hw⟩
  have D1 := eDerived_spec t3 L FL st hR3 f (lookup_setVar_same _ _ _) (by lk [t3]; exact ldir) (by lk [t3]; exact lfl)
    (W3 lDt (by decide)) (W3 lDg (by decide)) (W3 lDi (by decide)) (W3 lDo1 (by decide)) (W3 lDo2 (by decide))
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D1
  generalize hs1 : evaluateHOLFiniteState t3 (storeDerived 9 10) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u4⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  have k4 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → u4.locals.lookup y = t3.locals.lookup y := fr1
  obtain ⟨wf, hwf⟩ := W3 lDfv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lDfv _ _ wf (eval_vv u4 lDo1 _ o1)
    (by rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwf))]
  let u5 := setVarHOLFinite lDfv (.val (.word (dWN (st.derived f)).1)) u4
  obtain ⟨wh, hwh⟩ := W3 lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDh _ _ (Enc.idxW f) (eval_vv u5 lEa _ (by
      lk [u5]; rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3]; exact lea))
    (by lk [u5]; rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3]))]
  let u6 := setVarHOLFinite lDh (.val (.word (Enc.idxW a))) u5
  have hR6 : ERep u6 L FL st := erep_frame hR3 (by show u4.memory FL = _; rw [m1']) d1
    (fun _ _ _ _ _ => ⟨fun _ _ => by show u4.memory _ = _; rw [m1'], fun _ _ => by show u4.memory _ = _; rw [m1']⟩)
  have w6 : ∀ y, y = lDt ∨ y = lDg ∨ y = lDi ∨ y = lDo1 ∨ y = lDo2 → ∃ w, u6.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨w, hw⟩ := wd1 lDt (Or.inl rfl); exact ⟨w, by lk [u6, u5]; exact hw⟩
    · obtain ⟨w, hw⟩ := wd1 lDg (Or.inr (Or.inl rfl)); exact ⟨w, by lk [u6, u5]; exact hw⟩
    · obtain ⟨w, hw⟩ := wd1 lDi (Or.inr (Or.inr rfl)); exact ⟨w, by lk [u6, u5]; exact hw⟩
    · exact ⟨_, by lk [u6, u5]; exact o1⟩
    · exact ⟨_, by lk [u6, u5]; exact o2⟩
  have D2 := eDerived_spec u6 L FL st hR6 a (lookup_setVar_same _ _ _)
    (by lk [u6, u5]; rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3]; exact ldir)
    (by lk [u6, u5]; rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3]; exact lfl)
    (w6 lDt (Or.inl rfl)) (w6 lDg (Or.inr (Or.inl rfl))) (w6 lDi (Or.inr (Or.inr (Or.inl rfl))))
    (w6 lDo1 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (w6 lDo2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  obtain ⟨n2, m2', d2, c2, g2, ta2, ck2, p1, p2, fr2, wd2⟩ := D2
  generalize hs2 : evaluateHOLFiniteState u6 (storeDerived 9 10) = q2 at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2
  obtain ⟨q2r, u7⟩ := q2
  simp only at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2; subst n2
  rw [seq_normal _ hs2]
  -- every local before the second read, from `t`
  have back : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lDfv →
      u7.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7
    rw [fr2 y a1 a2 a3 a4 a5]; lk [u6, u5]; rw [k4 y a1 a2 a3 a4 a5]; lk [t3]; rfl
  have u7df : u7.locals.lookup lDfv = some (.val (.word (st.derived f).toBitVec)) := by
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u6, u5]; rfl
  have mem7 : u7.memory = t2.memory := by rw [m2', show u6.memory = u4.memory from rfl, m1']; rfl
  have md7 : u7.memaddrs = t.memaddrs := by rw [d2, show u6.memaddrs = u4.memaddrs from rfl, d1]; rfl
  have wv : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lDfv → y ∈ scratchW →
      ∃ w, u7.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  obtain ⟨wa', hwa'⟩ := wv lDav (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u7 lDav _ _ wa' (eval_vv u7 lDo1 _ p1) hwa')]
  let u8 := setVarHOLFinite lDav (.val (.word (dWN (st.derived a)).1)) u7
  let dd := st.derOfView (.app f a)
  have hdd : (dWN dd).1 = (Der.appDataW (st.derived f) (st.derived a)).toBitVec := by
    show (st.derOfApp f a).toBitVec = _; rw [Der.derOfApp_eq ra]
  obtain ⟨wv1, hwv1⟩ := wv lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u8 lDv _ (dWN dd).1 wv1
    (by rw [hdd]; exact Der.appDataE.eval u8 _ _ (by lk [u8]; exact u7df) (lookup_setVar_same _ _ _))
    (by lk [u8]; exact hwv1))]
  let u9 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u8
  obtain ⟨wv2, hwv2⟩ := wv lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u9 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u9 0) (by lk [u9, u8]; exact hwv2))]
  let u10 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u9
  have hskv : @evalHOLExact 64 σ _ u10.toExact (fun x => Classical.propDecidable (u10.memaddrs x))
      (.cmp .notEqual (.op .or [.shift .lsr (vv lEf) (.const 31), .shift .lsr (vv lEa) (.const 31)]) (.const 0)) =
      some (.val (.word (if EStore.eViewHasScratchChild (.app f a) then 1 else 0))) := by
    have ef10 : u10.locals.lookup lEf = some (.val (.word (Enc.idxW f))) := by
      lk [u10, u9, u8]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact lef
    have ea10 : u10.locals.lookup lEa = some (.val (.word (Enc.idxW a))) := by
      lk [u10, u9, u8]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact lea
    rw [ConsLoop.eval_cmp_of u10 .notEqual _ _ _ 0 (eval_or2 u10 _ _ _ _ (eval_shr u10 _ _ _ (eval_vv u10 lEf _ ef10)
      (by decide)) (eval_shr u10 _ _ _ (eval_vv u10 lEa _ ea10) (by decide))) (eval_const u10 0)]
    have e := ConsGeo.sk_word f a
    simp only [show (31 : BitVec 64).toNat = 31 from rfl]
    cases hs : EStore.eViewHasScratchChild (.app f a)
    · have h0 : (Enc.idxW f >>> (31 : Nat) ||| Enc.idxW a >>> (31 : Nat)) = 0 := e.mpr hs
      have hb : ((Enc.idxW f >>> (31 : Nat) ||| Enc.idxW a >>> (31 : Nat)) == 0) = true := beq_iff_eq.mpr h0
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · have h0 : ¬ (Enc.idxW f >>> (31 : Nat) ||| Enc.idxW a >>> (31 : Nat)) = 0 := fun x => by rw [e.mp x] at hs; cases hs
      have hb : ((Enc.idxW f >>> (31 : Nat) ||| Enc.idxW a >>> (31 : Nat)) == 0) = false := by simpa using h0
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb, Bool.not_false, ↓reduceIte]
  have g10 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lDfv → y ≠ lDav → y ≠ lDv →
      y ≠ lDv2 → y ∈ scratchW → ∃ w, u10.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hy
    obtain ⟨w, hw⟩ := wv y a1 a2 a3 a4 a5 a6 a7 hy; exact ⟨w, by lk [u10, u9, u8]; exact hw⟩
  have w10 : ∀ y, y ∈ [lSk, lOn, lPg, lSg, lK, lL] → ∃ w, u10.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact g10 lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact g10 lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact g10 lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact g10 lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact g10 lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact g10 lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ws1, hws1⟩ := w10 lSk (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u10 lSk _ _ ws1 hskv hws1)]
  let u11 := setVarHOLFinite lSk (.val (.word (if EStore.eViewHasScratchChild (.app f a) then 1 else 0))) u10
  have fl11 : u11.locals.lookup lFl = some (.val (.word FL)) := by
    lk [u11, u10, u9, u8]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact lfl
  have hld : @evalHOLExact 64 σ _ u11.toExact (fun x => Classical.propDecidable (u11.memaddrs x)) (.load .one (vv lFl)) =
      some (.val (.word (if st.scratchOn then 1 else 0))) := by
    rw [eval_load_word u11 _ _ (eval_vv u11 lFl _ fl11) (by show u7.memaddrs _; rw [md7]; exact hR.fl.1)]
    show some (ValueHOL.val (u7.memory FL)) = _; rw [mem7, m2 _ hflO.2.2.1 hflO.2.2.2, hR.fl.2]
  obtain ⟨wo, hwo⟩ := w10 lOn (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u11 lOn _ _ wo hld (by lk [u11]; exact hwo))]
  let u12 := setVarHOLFinite lOn (.val (.word (if st.scratchOn then 1 else 0))) u11
  have dir12 : u12.locals.lookup lDir = some (.val (.word L.DIR)) := by
    lk [u12, u11, u10, u9, u8]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact ldir
  obtain ⟨wp, hwp⟩ := w10 lPg (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u12 lPg (descK 13 0) (descAddr L 13 0) wp
    (by unfold descK; exact eval_add2 u12 _ _ _ _ (eval_vv u12 lDir _ dir12) (eval_const u12 _)) (by lk [u12, u11]; exact hwp))]
  let u13 := setVarHOLFinite lPg (.val (.word (descAddr L 13 0))) u12
  obtain ⟨wg', hwg'⟩ := w10 lSg (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u13 lSg (descK 13 1) (descAddr L 13 1) wg'
    (by unfold descK; exact eval_add2 u13 _ _ _ _ (eval_vv u13 lDir _ (by lk [u13]; exact dir12)) (eval_const u13 _))
    (by lk [u13, u12, u11]; exact hwg'))]
  let u14 := setVarHOLFinite lSg (.val (.word (descAddr L 13 1))) u13
  obtain ⟨wk, hwk⟩ := w10 lK (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u14 lK _ KB wk (eval_vv u14 lKb _ (by
      lk [u14, u13, u12, u11, u10, u9, u8]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; exact lkb)) (by lk [u14, u13, u12, u11]; exact hwk))]
  let u15 := setVarHOLFinite lK (.val (.word KB)) u14
  obtain ⟨wl, hwl⟩ := w10 lL (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u15 lL (.const 2) _ wl (eval_const u15 2) (by lk [u15, u14, u13, u12, u11]; exact hwl))]
  let u16 := setVarHOLFinite lL (.val (.word 2)) u15
  have mem16 : u16.memory = t2.memory := mem7
  have md16 : u16.memaddrs = t.memaddrs := md7
  have hag16 : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → Agree L FL t u16 k tier := fun k tier h1 h2 h3 =>
    ⟨fun m hm => by rw [mem16]; exact m2 _ (hdirO k tier m h1 h2 h3 hm).2.2.1 (hdirO k tier m h1 h2 h3 hm).2.2.2,
     fun c hc => by
      rw [mem16]; exact m2 c (fun e => (hkbO k tier h1 h2 h3).1 (e ▸ hc)) (fun e => (hkbO k tier h1 h2 h3).2 (e ▸ hc))⟩
  have hR16 : ERep u16 L FL st := erep_frame hR (by rw [mem16]; exact m2 _ hflO.2.2.1 hflO.2.2.2) md16 hag16
  obtain ⟨hD0, hc0, rp, dp, sp, hup, hP⟩ := hR16.p4
  obtain ⟨hD1, hc1, rs, ds, ss, hus, hS⟩ := hR16.s4
  have hK : Words u16 KB (Enc.encApp ⟨f, a⟩) := by
    intro k hk
    have hk2 : k < 2 := by simpa [Enc.encApp] using hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine ⟨by rw [md16]; simpa using hkbd.1, ?_⟩
      rw [mem16]; show (if _ = KB + 8 then _ else if _ = KB then _ else _) = _
      simp only [show KB + BitVec.ofNat 64 (8 * 0) = KB by simp]; simp [hkb8, Enc.encApp]
    · refine ⟨by rw [md16]; simpa using hkbd.2, ?_⟩
      rw [mem16]; show (if _ = KB + 8 then _ else if _ = KB then _ else _) = _
      simp only [show KB + BitVec.ofNat 64 (8 * 1) = KB + 8 by rfl]; simp [Enc.encApp]
  have T := internTwo_spec u16 Enc.encApp dWN Enc.idxW (mkW 0) (mkW 1) (L.base 13 0) (L.base 13 1) (2 ^ 30)
    (fun i hi => by rw [hb0]; exact idxW_mkW 0 (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkW 1 (by decide) i hi) Enc.encApp_inj
    st.pers.apps st.scr.apps (L.geo 13 0) (L.geo 13 1) rp dp sp hup rs ds ss hus st.scratchOn
    (EStore.eViewHasScratchChild (.app f a)) ⟨f, a⟩ dd KB (descAddr L 13 0) (descAddr L 13 1)
    (hpow 0 (by decide)).1 (hpow 0 (by decide)).2 hc0 (Nat.le_of_lt hc0)
    (hpow 1 (by decide)).1 (hpow 1 (by decide)).2 hc1 (Nat.le_of_lt hc1) hP hS hD0 hD1 hdis hK (by simp [Enc.encApp])
    (fun i hi => by
      simp only [Enc.encApp, List.length_cons, List.length_nil] at hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · simp only [show KB + BitVec.ofNat 64 (8 * 0) = KB by simp]
        exact ⟨(hkbO 13 0 (by decide) (by decide) (by decide)).1, (hkbO 13 1 (by decide) (by decide) (by decide)).1⟩
      · exact ⟨(hkbO 13 0 (by decide) (by decide) (by decide)).2, (hkbO 13 1 (by decide) (by decide) (by decide)).2⟩)
    ⟨by lk [u16, u15, u14, u13, u12, u11, u10, u9], by lk [u16, u15, u14, u13, u12, u11, u10, u9]; rfl, by lk [u16, u15, u14, u13, u12, u11, u10, u9], by lk [u16, u15, u14, u13, u12, u11, u10, u9]⟩
    (by lk [u16, u15, u14, u13, u12, u11, u10, u9]) (by lk [u16, u15, u14, u13, u12, u11, u10, u9]) (by lk [u16, u15, u14, u13, u12, u11, u10, u9]) (by lk [u16, u15, u14, u13, u12, u11, u10, u9])
  rcases T with hs | ⟨hr, ⟨rp', dp', sp', hup', hP'⟩, ⟨rs', ds', ss', hus', hS'⟩, c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  have hint := estore_app st f a
  simp only at hint
  unfold EIRes; rw [hint]
  have hc16 : u16.code = t.code := by show u7.code = _; rw [c2]; show u4.code = _; rw [c1]; rfl
  have hg16 : u16.globals = t.globals := by show u7.globals = _; rw [g2]; show u4.globals = _; rw [g1]; rfl
  have ht16 : u16.topAddr = t.topAddr := by show u7.topAddr = _; rw [ta2]; show u4.topAddr = _; rw [ta1]; rfl
  refine Or.inr ⟨hr, ?_, c3.trans hc16, g3.trans hg16, d3.trans md16, ta3.trans ht16, fun c h1 h2 h3 => ?_⟩
  · have dsc : ∀ tier, tier < 2 → ∀ m, m < 8 →
        (evaluateHOLFiniteState u16 internTwo).2.memory (descAddr L 13 tier + BitVec.ofNat 64 (8 * m)) =
          u16.memory (descAddr L 13 tier + BitVec.ofNat 64 (8 * m)) := fun tier ht m hm =>
      fr3 _ (hdirO 13 tier m (by decide) (by decide) ht hm).1 (hdirO 13 tier m (by decide) (by decide) ht hm).2.1
    refine erep_apps hR16 _ _ ⟨fun m hm => by rw [d3, dsc 0 (by decide) m hm]; exact hD0 m hm, hc0, rp', dp', sp', hup', hP'⟩
      ⟨fun m hm => by rw [d3, dsc 1 (by decide) m hm]; exact hD1 m hm, hc1, rs', ds', ss', hus', hS'⟩
      (fr3 _ hflO.1 hflO.2.1) d3 (fun k tier h1 h2 h3 h4 => ⟨fun m hm => fr3 _ (hdirO k tier m h1 h2 h3 hm).1
        (hdirO k tier m h1 h2 h3 hm).2.1, fun c hc => fr3 c (hdisO k tier c h1 h2 h3 h4 hc).1 (hdisO k tier c h1 h2 h3 h4 hc).2⟩)
  · have n0 : ¬ inR (L.geo 13 0) c := fun hc => h1 ⟨13, 0, by decide, by decide, hc⟩
    have n1 : ¬ inR (L.geo 13 1) c := fun hc => h1 ⟨13, 1, by decide, by decide, hc⟩
    rw [fr3 c n0 n1, mem16]; exact m2 c h2 h3

end

end ConPanqueque.V
