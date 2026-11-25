import ConPanqueque.V.EBin
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning `letE ty v b`

Three children: the key `[ty, v, b]`, their derived words through the
expression store, `letDataE` (over locals `dt`, `dv`, `db`; `dt` is also the
handle decode's tier local, so the type's word waits in `dty` until the last
read), the three-child scratch bit, then the shared remainder at kind 16.
-/

namespace ConPanqueque.V

def lEty := ofString "ety"
def lEvl := ofString "evl"
def lEbd := ofString "ebd"
def lDty := ofString "dty"
def lDvv := ofString "dv"
def lDbv := ofString "db"

def eLetWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEty))
  (.seq (.store (.op .add [vv lKb, .const 8]) (vv lEvl))
  (.seq (.store (.op .add [vv lKb, .const 16]) (vv lEbd))
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv lEty))
  (.seq (storeDerivedC 9 10 badE)
  (.seq (.assign .local lDty (vv lDo1))
  (.seq (.assign .local lDh (vv lEvl))
  (.seq (storeDerivedC 9 10 badE)
  (.seq (.assign .local lDvv (vv lDo1))
  (.seq (.assign .local lDh (vv lEbd))
  (.seq (storeDerivedC 9 10 badE)
  (.seq (.assign .local lDbv (vv lDo1))
  (.seq (.assign .local lDt (vv lDty))
  (.seq (.assign .local lDv ExprData.letDataE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual (.op .or [.op .or [.shift .lsr (vv lEty) (.const 31),
      .shift .lsr (vv lEvl) (.const 31)], .shift .lsr (vv lEbd) (.const 31)]) (.const 0))) rest))))))))))))))))

def letScratch : List MlS :=
  [lDh, lDt, lDg, lDi, lDo1, lDo2, lDty, lDvv, lDbv, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

section
variable {σ : Type}

theorem erep_lets {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl LetNode EIdx UInt64)
    (hP : TabAt u L 16 0 Enc.encLet dWN P' (mkN ETag.letE 0)) (hS : TabAt u L 16 1 Enc.encLet dWN Sc' (mkN ETag.letE 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 16 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with lets := P' }, scr := { st.scr with lets := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 16 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0,
    A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    A 11 0 (by decide) (by decide) (by decide) (by decide) h.p2,
    A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4,
    A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6,
    hP,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8,
    A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0,
    A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6,
    hS,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8,
    A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

end

section
variable {σ : Type}

theorem eInternLet_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (ty v b : EIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 3 16)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8) ∧ t.memaddrs (KB + 16))
    (hkbn : KB ≠ KB + 8 ∧ KB ≠ KB + 16 ∧ KB + 8 ≠ KB + 16)
    (hb0 : L.base 16 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.letE.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 16 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.letE.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (lety : t.locals.lookup lEty = some (.val (.word (Enc.idxW ty))))
    (levl : t.locals.lookup lEvl = some (.val (.word (Enc.idxW v))))
    (lebd : t.locals.lookup lEbd = some (.val (.word (Enc.idxW b))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ letScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (ERes t L FLn FLl FLs FLe KB 3 st (st.intern (.letE ty v b)) (evaluateHOLFiniteState t (eLetWith (eRest 16 3)))) ∧
      (Stop (evaluateHOLFiniteState t (eLetWith (eRest 16 3))).1 ∨ ((st.view ty).isSome = true ∧ (st.view v).isSome = true ∧ (st.view b).isSome = true)) := by
  have KB0 : KB + BitVec.ofNat 64 (8 * 0) = KB := by simp
  have KB1 : KB + BitVec.ofNat 64 (8 * 1) = KB + 8 := rfl
  have KB2 : KB + BitVec.ofNat 64 (8 * 2) = KB + 16 := rfl
  have flne : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → F ≠ KB ∧ F ≠ KB + 8 ∧ F ≠ KB + 16 := fun F hF => by
    have h0 := (hS.fls F hF).2.2 0 (by decide); have h1 := (hS.fls F hF).2.2 1 (by decide)
    have h2 := (hS.fls F hF).2.2 2 (by decide)
    rw [KB0] at h0; rw [KB1] at h1; rw [KB2] at h2; exact ⟨h0, h1, h2⟩
  have dscne : ∀ k tier m, k < 19 → tier < 2 → m < 8 →
      descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB ∧ descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB + 8 ∧
      descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB + 16 := fun k tier m h1 h2 h3 => by
    have a0 := (hS.dsc k tier m h1 h2 h3).2.2 0 (by decide); have a1 := (hS.dsc k tier m h1 h2 h3).2.2 1 (by decide)
    have a2 := (hS.dsc k tier m h1 h2 h3).2.2 2 (by decide)
    rw [KB0] at a0; rw [KB1] at a1; rw [KB2] at a2; exact ⟨a0, a1, a2⟩
  have kbo : ∀ k tier, k < 19 → tier < 2 →
      ¬ inR (L.geo k tier) KB ∧ ¬ inR (L.geo k tier) (KB + 8) ∧ ¬ inR (L.geo k tier) (KB + 16) := fun k tier h1 h2 => by
    have a0 := hS.kbo 0 k tier (by decide) h1 h2; have a1 := hS.kbo 1 k tier (by decide) h1 h2
    have a2 := hS.kbo 2 k tier (by decide) h1 h2
    rw [KB0] at a0; rw [KB1] at a1; rw [KB2] at a2; exact ⟨a0, a1, a2⟩
  unfold eLetWith
  rw [seq_normal _ (store_word t (vv lKb) (vv lEty) KB (Enc.idxW ty) (eval_vv t lKb _ lkb) (eval_vv t lEty _ lety) hkbd.1)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW ty) else t.memory c }
  rw [seq_normal _ (store_word t1 _ (vv lEvl) (KB + 8) (Enc.idxW v)
    (eval_add2 t1 _ _ _ _ (eval_vv t1 lKb _ lkb) (eval_const t1 8)) (eval_vv t1 lEvl _ levl) hkbd.2.1)]
  let t2 : PanSemStateFiniteExact 64 σ :=
    { t1 with memory := fun c => if c = KB + 8 then .word (Enc.idxW v) else t1.memory c }
  rw [seq_normal _ (store_word t2 _ (vv lEbd) (KB + 16) (Enc.idxW b)
    (eval_add2 t2 _ _ _ _ (eval_vv t2 lKb _ lkb) (eval_const t2 16)) (eval_vv t2 lEbd _ lebd) hkbd.2.2)]
  let t3 : PanSemStateFiniteExact 64 σ :=
    { t2 with memory := fun c => if c = KB + 16 then .word (Enc.idxW b) else t2.memory c }
  have m3 : ∀ c, c ≠ KB → c ≠ KB + 8 → c ≠ KB + 16 → t3.memory c = t.memory c := by
    intro c h1 h2 h3
    show (if c = KB + 16 then _ else if c = KB + 8 then _ else if c = KB then _ else _) = _
    rw [ite_eq_right h3, ite_eq_right h2, ite_eq_right h1]
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR
    ⟨m3 _ (flne _ (Or.inl rfl)).1 (flne _ (Or.inl rfl)).2.1 (flne _ (Or.inl rfl)).2.2,
     m3 _ (flne _ (Or.inr (Or.inl rfl))).1 (flne _ (Or.inr (Or.inl rfl))).2.1 (flne _ (Or.inr (Or.inl rfl))).2.2,
     m3 _ (flne _ (Or.inr (Or.inr (Or.inl rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inl rfl)))).2.1
       (flne _ (Or.inr (Or.inr (Or.inl rfl)))).2.2,
     m3 _ (flne _ (Or.inr (Or.inr (Or.inr rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inr rfl)))).2.1
       (flne _ (Or.inr (Or.inr (Or.inr rfl)))).2.2⟩ rfl
    (fun k tier h1 h2 => ⟨fun m hm => m3 _ (dscne k tier m h1 h2 hm).1 (dscne k tier m h1 h2 hm).2.1
        (dscne k tier m h1 h2 hm).2.2,
      fun c hc => m3 c (fun e => (kbo k tier h1 h2).1 (e ▸ hc)) (fun e => (kbo k tier h1 h2).2.1 (e ▸ hc))
        (fun e => (kbo k tier h1 h2).2.2 (e ▸ hc))⟩)
  have W : ∀ y, y ∈ letScratch → ∃ w, t3.locals.lookup y = some (.val (.word w)) := hw
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t3 lFl _ FLe wf (eval_vv t3 lFle _ lfle) hwf)]
  let t4 := setVarHOLFinite lFl (.val (.word FLe)) t3
  -- a derived read of a child from a state agreeing with `t` outside the scratch locals
  have rd : ∀ (x : PanSemStateFiniteExact 64 σ) (c : EIdx), SRep x L FLn FLl FLs FLe st →
      x.locals.lookup lDh = some (.val (.word (Enc.idxW c))) → x.locals.lookup lDir = some (.val (.word L.DIR)) →
      x.locals.lookup lFl = some (.val (.word FLe)) →
      (∀ y, y = lDt ∨ y = lDg ∨ y = lDi ∨ y = lDo1 ∨ y = lDo2 → ∃ w, x.locals.lookup y = some (.val (.word w))) →
      Stop (evaluateHOLFiniteState x (storeDerivedC 9 10 badE)).1 ∨
        ((st.view c).isSome = true ∧ DRes x (dWN (st.derived c)) (evaluateHOLFiniteState x (storeDerivedC 9 10 badE))) := by
    intro x c hx h1 h2 h3 h4
    exact eDerivedC_spec x L FLe st hx.e c h1 h2 h3 (h4 lDt (Or.inl rfl)) (h4 lDg (Or.inr (Or.inl rfl)))
      (h4 lDi (Or.inr (Or.inr (Or.inl rfl)))) (h4 lDo1 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (h4 lDo2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  -- first child
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t4 lDh _ (Enc.idxW ty) wh (eval_vv t4 lEty _ (by lk [t4]; exact lety))
    (by lk [t4]; exact hwh))]
  let t5 := setVarHOLFinite lDh (.val (.word (Enc.idxW ty))) t4
  rcases rd t5 ty (srep_frame hR3 ⟨rfl, rfl, rfl, rfl⟩ rfl (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩))
    (lookup_setVar_same _ _ _) (by lk [t5, t4]; exact ldir) (by lk [t5, t4]) (fun y hy => by
      obtain ⟨w, hw⟩ := W y (by rcases hy with rfl | rfl | rfl | rfl | rfl <;> decide)
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact ⟨w, by lk [t5, t4]; exact hw⟩)
    with hSD1 | ⟨hvD1, D1⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD1), Or.inl (seq_stop _ _ _ hSD1)⟩
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D1
  generalize hs1 : evaluateHOLFiniteState t5 (storeDerivedC 9 10 badE) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u6⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  have back6 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u6.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t5, t4]; rfl
  obtain ⟨wty, hwty⟩ := hw lDty (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lDty _ _ wty (eval_vv u6 lDo1 _ o1)
    (by rw [back6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwty))]
  let u7 := setVarHOLFinite lDty (.val (.word (dWN (st.derived ty)).1)) u6
  have mem6 : u6.memory = t3.memory := m1'
  have md6 : u6.memaddrs = t.memaddrs := d1
  -- second child
  have dh7 : u7.locals.lookup lDh = some (.val (.word (Enc.idxW ty))) := by
    lk [u7]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t5]
  rw [seq_normal _ (ConsLoop.assign_local u7 lDh _ (Enc.idxW v) (Enc.idxW ty) (eval_vv u7 lEvl _ (by
    lk [u7]; rw [back6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact levl))
    dh7)]
  let u8 := setVarHOLFinite lDh (.val (.word (Enc.idxW v))) u7
  have fl8 : u8.locals.lookup lFl = some (.val (.word FLe)) := by
    lk [u8, u7]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t5, t4]
  rcases rd u8 v (srep_frame hR3 ⟨by show u6.memory _ = _; rw [mem6], by show u6.memory _ = _; rw [mem6],
      by show u6.memory _ = _; rw [mem6], by show u6.memory _ = _; rw [mem6]⟩ md6
      (fun _ _ _ _ => ⟨fun _ _ => by show u6.memory _ = _; rw [mem6], fun _ _ => by show u6.memory _ = _; rw [mem6]⟩))
    (lookup_setVar_same _ _ _)
    (by lk [u8, u7]; rw [back6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    fl8 (fun y hy => by
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨w, hw⟩ := wd1 lDt (Or.inl rfl); exact ⟨w, by lk [u8, u7]; exact hw⟩
      · obtain ⟨w, hw⟩ := wd1 lDg (Or.inr (Or.inl rfl)); exact ⟨w, by lk [u8, u7]; exact hw⟩
      · obtain ⟨w, hw⟩ := wd1 lDi (Or.inr (Or.inr rfl)); exact ⟨w, by lk [u8, u7]; exact hw⟩
      · exact ⟨_, by lk [u8, u7]; exact o1⟩
      · exact ⟨_, by lk [u8, u7]; exact o2⟩)
    with hSD2 | ⟨hvD2, D2⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD2), Or.inl (seq_stop _ _ _ hSD2)⟩
  obtain ⟨n2, m2', d2, c2, g2, ta2, ck2, p1, p2, fr2, wd2⟩ := D2
  generalize hs2 : evaluateHOLFiniteState u8 (storeDerivedC 9 10 badE) = q2 at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2
  obtain ⟨q2r, u9⟩ := q2
  simp only at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2; subst n2
  rw [seq_normal _ hs2]
  have back9 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDty →
      u9.locals.lookup y = t.locals.lookup y := fun y a1 a2 a3 a4 a5 a6 a7 a8 => by
    rw [fr2 y a1 a2 a3 a4 a5]; lk [u8, u7]; exact back6 y a1 a2 a3 a4 a5 a6 a7
  obtain ⟨wdv, hwdv⟩ := hw lDvv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u9 lDvv _ _ wdv (eval_vv u9 lDo1 _ p1)
    (by rw [back9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwdv))]
  let u10 := setVarHOLFinite lDvv (.val (.word (dWN (st.derived v)).1)) u9
  have mem9 : u9.memory = t3.memory := by rw [m2']; exact mem6
  have md9 : u9.memaddrs = t.memaddrs := by rw [d2]; exact md6
  -- third child
  have dh10 : u10.locals.lookup lDh = some (.val (.word (Enc.idxW v))) := by
    lk [u10]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u8]
  rw [seq_normal _ (ConsLoop.assign_local u10 lDh _ (Enc.idxW b) (Enc.idxW v) (eval_vv u10 lEbd _ (by
    lk [u10]; rw [back9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact lebd)) dh10)]
  let u11 := setVarHOLFinite lDh (.val (.word (Enc.idxW b))) u10
  have fl11 : u11.locals.lookup lFl = some (.val (.word FLe)) := by
    lk [u11, u10]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fl8
  rcases rd u11 b (srep_frame hR3 ⟨by show u9.memory _ = _; rw [mem9], by show u9.memory _ = _; rw [mem9],
      by show u9.memory _ = _; rw [mem9], by show u9.memory _ = _; rw [mem9]⟩ md9
      (fun _ _ _ _ => ⟨fun _ _ => by show u9.memory _ = _; rw [mem9], fun _ _ => by show u9.memory _ = _; rw [mem9]⟩))
    (lookup_setVar_same _ _ _)
    (by lk [u11, u10]; rw [back9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact ldir)
    fl11 (fun y hy => by
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨w, hw⟩ := wd2 lDt (Or.inl rfl); exact ⟨w, by lk [u11, u10]; exact hw⟩
      · obtain ⟨w, hw⟩ := wd2 lDg (Or.inr (Or.inl rfl)); exact ⟨w, by lk [u11, u10]; exact hw⟩
      · obtain ⟨w, hw⟩ := wd2 lDi (Or.inr (Or.inr rfl)); exact ⟨w, by lk [u11, u10]; exact hw⟩
      · exact ⟨_, by lk [u11, u10]; exact p1⟩
      · exact ⟨_, by lk [u11, u10]; exact p2⟩)
    with hSD3 | ⟨hvD3, D3⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD3), Or.inl (seq_stop _ _ _ hSD3)⟩
  obtain ⟨n3, m3', d3, c3, g3, ta3, ck3, r1, r2, fr3, wd3⟩ := D3
  generalize hs3 : evaluateHOLFiniteState u11 (storeDerivedC 9 10 badE) = q3 at n3 m3' d3 c3 g3 ta3 ck3 r1 r2 fr3 wd3
  obtain ⟨q3r, u12⟩ := q3
  simp only at n3 m3' d3 c3 g3 ta3 ck3 r1 r2 fr3 wd3; subst n3
  rw [seq_normal _ hs3]
  refine ⟨?_, Or.inr ⟨hvD1, hvD2, hvD3⟩⟩
  have back12 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDty → y ≠ lDvv →
      u12.locals.lookup y = t.locals.lookup y := fun y a1 a2 a3 a4 a5 a6 a7 a8 a9 => by
    rw [fr3 y a1 a2 a3 a4 a5]; lk [u11, u10]; exact back9 y a1 a2 a3 a4 a5 a6 a7 a8
  have wv12 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDty → y ≠ lDvv →
      y ∈ letScratch → ∃ w, u12.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 a8 a9 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back12 y a1 a2 a3 a4 a5 a6 a7 a8 a9]; exact hw⟩
  obtain ⟨wdb, hwdb⟩ := wv12 lDbv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u12 lDbv _ _ wdb (eval_vv u12 lDo1 _ r1) hwdb)]
  let u13 := setVarHOLFinite lDbv (.val (.word (dWN (st.derived b)).1)) u12
  obtain ⟨wdt, hwdt⟩ := wd3 lDt (Or.inl rfl)
  rw [seq_normal _ (ConsLoop.assign_local u13 lDt _ (dWN (st.derived ty)).1 wdt (eval_vv u13 lDty _ (by
    lk [u13]; rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u11, u10]
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u8, u7]))
    (by lk [u13]; exact hwdt))]
  let u14 := setVarHOLFinite lDt (.val (.word (dWN (st.derived ty)).1)) u13
  let dd := st.derOfView (.letE ty v b)
  have hdd : (dWN dd).1 = (ExprData.letDataW (st.derived ty) (st.derived v) (st.derived b)).toBitVec := by
    show (st.derOfLetAt ty v b).toBitVec = _; rw [Der.derOfLet_eq ra]
  have e14 : @evalHOLExact 64 σ _ u14.toExact (fun c => Classical.propDecidable (u14.memaddrs c)) ExprData.letDataE =
      some (.val (.word (dWN dd).1)) := by
    rw [hdd]
    exact ExprData.letDataE.eval u14 _ _ _ (by show u14.locals.lookup lDt = _; lk [u14]; rfl)
      (by show u14.locals.lookup lDvv = _; lk [u14, u13]; rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
          lk [u11, u10]; rfl)
      (by show u14.locals.lookup lDbv = _; lk [u14, u13]; rfl)
  obtain ⟨wv1, hwv1⟩ := wv12 lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u14 lDv _ (dWN dd).1 wv1 e14 (by lk [u14, u13]; exact hwv1))]
  let u15 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u14
  obtain ⟨wv2, hwv2⟩ := wv12 lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u15 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u15 0) (by lk [u15, u14, u13]; exact hwv2))]
  let u16 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u15
  have bk : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDty → y ≠ lDvv →
      y ≠ lDbv → y ≠ lDv → y ≠ lDv2 → u16.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12; lk [u16, u15, u14, u13]; exact back12 y a1 a2 a3 a4 a5 a6 a7 a8 a9
  have e16 : u16.locals.lookup lEty = some (.val (.word (Enc.idxW ty))) := by
    rw [bk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact lety
  have e16v : u16.locals.lookup lEvl = some (.val (.word (Enc.idxW v))) := by
    rw [bk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact levl
  have e16b : u16.locals.lookup lEbd = some (.val (.word (Enc.idxW b))) := by
    rw [bk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact lebd
  obtain ⟨wsk, hwsk⟩ := wv12 lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u16 lSk _ _ wsk (eval_sk3 u16 lEty lEvl lEbd ty v b e16 e16v e16b)
    (by lk [u16, u15, u14, u13]; exact hwsk))]
  let u17 := setVarHOLFinite lSk (.val (.word (if (if ty.isPersistent then (if v.isPersistent then !b.isPersistent else true)
    else true) then 1 else 0))) u16
  have mem17 : u17.memory = t3.memory := by show u12.memory = _; rw [m3']; exact mem9
  have md17 : u17.memaddrs = t.memaddrs := by show u12.memaddrs = _; rw [d3]; exact md9
  have hc17 : u17.code = t.code := by
    show u12.code = _; rw [c3]; show u9.code = _; rw [c2]; show u6.code = _; rw [c1]; rfl
  have hg17 : u17.globals = t.globals := by
    show u12.globals = _; rw [g3]; show u9.globals = _; rw [g2]; show u6.globals = _; rw [g1]; rfl
  have ht17 : u17.topAddr = t.topAddr := by
    show u12.topAddr = _; rw [ta3]; show u9.topAddr = _; rw [ta2]; show u6.topAddr = _; rw [ta1]; rfl
  have hR17 : SRep u17 L FLn FLl FLs FLe st := srep_frame hR3 ⟨by rw [mem17], by rw [mem17], by rw [mem17], by rw [mem17]⟩
    md17 (fun _ _ _ _ => ⟨fun _ _ => by rw [mem17], fun _ _ => by rw [mem17]⟩)
  have b17 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDty → y ≠ lDvv →
      y ≠ lDbv → y ≠ lDv → y ≠ lDv2 → y ≠ lSk → u17.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13; lk [u17]; exact bk y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have hint := estore_letE st ty v b
  simp only at hint
  refine eRest_spec t u17 L FLn FLl FLs FLe KB 3 16 st Enc.encLet Enc.encLet_inj (mkN ETag.letE 0) (mkN ETag.letE 1)
    (2 ^ 26) (fun i hi => by rw [hb0]; exact idxW_mkN ETag.letE 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.letE 1 (by decide) (by decide) i hi) hS.cap
    st.pers.lets st.scr.lets (EStore.eViewHasScratchChild (.letE ty v b)) ⟨ty, v, b⟩ dd _
    (fun P' S' => { st with pers := { st.pers with lets := P' }, scr := { st.scr with lets := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_lets h1 P' S' h2 h3 h4 h5 h6)
    hS (by decide) (by decide) (by simp [Enc.encLet]) (by decide) hR17 hR17.e.p7 hR17.e.s7 ?_ ?_ md17 hc17 hg17 ht17
    (by lk [u17, u16, u15]) (by lk [u17, u16]) (by lk [u17]; rfl)
    (by rw [b17 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lfle)
    (by rw [b17 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [b17 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lkb) ?_
  · intro j hj
    have hj3 : j < 3 := by simpa [Enc.encLet] using hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · refine ⟨by rw [md17, KB0]; exact hkbd.1, ?_⟩
      rw [mem17, KB0]; show (if KB = KB + 16 then _ else if KB = KB + 8 then _ else if KB = KB then _ else _) = _
      simp [hkbn.2.1, hkbn.1, Enc.encLet]
    · refine ⟨by rw [md17, KB1]; exact hkbd.2.1, ?_⟩
      rw [mem17, KB1]; show (if KB + 8 = KB + 16 then _ else if KB + 8 = KB + 8 then _ else _) = _
      simp [hkbn.2.2, Enc.encLet]
    · refine ⟨by rw [md17, KB2]; exact hkbd.2.2, ?_⟩
      rw [mem17, KB2]; show (if KB + 16 = KB + 16 then _ else _) = _; simp [Enc.encLet]
  · intro c hc
    have h0 := hc 0 (by decide); have h1 := hc 1 (by decide); have h2 := hc 2 (by decide)
    rw [KB0] at h0; rw [KB1] at h1; rw [KB2] at h2
    rw [mem17]; exact m3 c h0 h1 h2
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨FLe, by lk [u17, u16, u15, u14, u13]; rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fl11⟩
    · obtain ⟨w, hw⟩ := wv12 lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u17, u16, u15, u14, u13]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv12 lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u17, u16, u15, u14, u13]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv12 lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u17, u16, u15, u14, u13]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv12 lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u17, u16, u15, u14, u13]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv12 lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u17, u16, u15, u14, u13]; exact hw⟩

end

end ConPanqueque.V
