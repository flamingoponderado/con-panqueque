import ConPanqueque.V.EGen
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning `const n us`

The key `[n, us]`, the name's hash through the name store and the level
list's record through the level-list store, `constDataE`, the scratch bit,
then the shared remainder at kind 12.
-/

namespace ConPanqueque.V

def lEn := ofString "en"
def lEus := ofString "eus"
def lFln := ofString "fln"
def lFls := ofString "fls"
def lHs := ofString "hs"

def eConstWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEn))
  (.seq (.store (.op .add [vv lKb, .const 8]) (vv lEus))
  (.seq (.assign .local lFl (vv lFln))
  (.seq (.assign .local lDh (vv lEn))
  (.seq (storeDerivedC 0 3 badN)
  (.seq (.assign .local lHs (vv lDo1))
  (.seq (.assign .local lFl (vv lFls))
  (.seq (.assign .local lDh (vv lEus))
  (.seq (storeDerivedC 8 1 badN)
  (.seq (.assign .local lLh (vv lDo1))
  (.seq (.assign .local lLpv (vv lDo2))
  (.seq (.assign .local lDv ExprData.constDataE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual
      (.op .or [.shift .lsr (vv lEn) (.const 31), .shift .lsr (vv lEus) (.const 31)]) (.const 0))) rest)))))))))))))

def eInternConst : ProgHOL 64 := eConstWith (eRest 12 2)

section
variable {σ : Type}

theorem erep_consts {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl ConstNode EIdx UInt64)
    (hP : TabAt u L 12 0 Enc.encConst dWN P' (mkN ETag.const 0)) (hS : TabAt u L 12 1 Enc.encConst dWN Sc' (mkN ETag.const 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 12 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with consts := P' }, scr := { st.scr with consts := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 12 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0,
    A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    A 11 0 (by decide) (by decide) (by decide) (by decide) h.p2,
    hP,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4,
    A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6,
    A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8,
    A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0,
    A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    hS,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6,
    A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8,
    A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

end

section
variable {σ : Type}

def constScratch : List MlS :=
  [lDh, lDt, lDg, lDi, lDo1, lDo2, lHs, lLh, lLpv, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

theorem eInternConst_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (n : NIdx) (us : LsIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 12)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (hb0 : L.base 12 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.const.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 12 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.const.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (Enc.idxW n))))
    (leus : t.locals.lookup lEus = some (.val (.word (Enc.idxW us))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfln : t.locals.lookup lFln = some (.val (.word FLn))) (lfls : t.locals.lookup lFls = some (.val (.word FLs)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ constScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (ERes t L FLn FLl FLs FLe KB 2 st (st.intern (.const n us)) (evaluateHOLFiniteState t eInternConst)) ∧
      (Stop (evaluateHOLFiniteState t eInternConst).1 ∨ ((st.lss.ls.ns.view n).isSome = true ∧ (st.lss.view us).isSome = true)) := by
  have KB0 : KB + BitVec.ofNat 64 (8 * 0) = KB := by simp
  have KB1 : KB + BitVec.ofNat 64 (8 * 1) = KB + 8 := rfl
  have flne : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → F ≠ KB ∧ F ≠ KB + 8 := fun F hF => by
    have h0 := (hS.fls F hF).2.2 0 (by decide); have h1 := (hS.fls F hF).2.2 1 (by decide)
    rw [KB0] at h0; rw [KB1] at h1; exact ⟨h0, h1⟩
  have dscne : ∀ k tier m, k < 19 → tier < 2 → m < 8 →
      descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB ∧ descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB + 8 :=
    fun k tier m h1 h2 h3 => by
      have a0 := (hS.dsc k tier m h1 h2 h3).2.2 0 (by decide); have a1 := (hS.dsc k tier m h1 h2 h3).2.2 1 (by decide)
      rw [KB0] at a0; rw [KB1] at a1; exact ⟨a0, a1⟩
  have kbo : ∀ k tier, k < 19 → tier < 2 → ¬ inR (L.geo k tier) KB ∧ ¬ inR (L.geo k tier) (KB + 8) := fun k tier h1 h2 => by
    have a0 := hS.kbo 0 k tier (by decide) h1 h2; have a1 := hS.kbo 1 k tier (by decide) h1 h2
    rw [KB0] at a0; rw [KB1] at a1; exact ⟨a0, a1⟩
  unfold eInternConst eConstWith
  -- the key
  rw [seq_normal _ (store_word t (vv lKb) (vv lEn) KB (Enc.idxW n) (eval_vv t lKb _ lkb) (eval_vv t lEn _ len) hkbd.1)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW n) else t.memory c }
  rw [seq_normal _ (store_word t1 _ (vv lEus) (KB + 8) (Enc.idxW us)
    (eval_add2 t1 _ _ _ _ (eval_vv t1 lKb _ lkb) (eval_const t1 8)) (eval_vv t1 lEus _ leus) hkbd.2)]
  let t2 : PanSemStateFiniteExact 64 σ :=
    { t1 with memory := fun c => if c = KB + 8 then .word (Enc.idxW us) else t1.memory c }
  have m2 : ∀ c, c ≠ KB → c ≠ KB + 8 → t2.memory c = t.memory c := by
    intro c h1 h2; show (if c = KB + 8 then _ else if c = KB then _ else _) = _; rw [if_neg h2, if_neg h1]
  have hR2 : SRep t2 L FLn FLl FLs FLe st := srep_frame hR
    ⟨m2 _ (flne _ (Or.inl rfl)).1 (flne _ (Or.inl rfl)).2, m2 _ (flne _ (Or.inr (Or.inl rfl))).1 (flne _ (Or.inr (Or.inl rfl))).2,
      m2 _ (flne _ (Or.inr (Or.inr (Or.inl rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inl rfl)))).2,
      m2 _ (flne _ (Or.inr (Or.inr (Or.inr rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inr rfl)))).2⟩ rfl
    (fun k tier h1 h2 => ⟨fun m hm => m2 _ (dscne k tier m h1 h2 hm).1 (dscne k tier m h1 h2 hm).2,
      fun c hc => m2 c (fun e => (kbo k tier h1 h2).1 (e ▸ hc)) (fun e => (kbo k tier h1 h2).2 (e ▸ hc))⟩)
  have W : ∀ y, y ∈ constScratch → ∃ w, t2.locals.lookup y = some (.val (.word w)) := hw
  -- the name's hash
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lFl _ FLn wf (eval_vv t2 lFln _ lfln) hwf)]
  let t3 := setVarHOLFinite lFl (.val (.word FLn)) t2
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t3 lDh _ (Enc.idxW n) wh (eval_vv t3 lEn _ (by lk [t3]; exact len))
    (by lk [t3]; exact hwh))]
  let t4 := setVarHOLFinite lDh (.val (.word (Enc.idxW n))) t3
  have W4 : ∀ y, y ∈ constScratch → y ≠ lFl → y ≠ lDh → ∃ w, t4.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t4, t3]; exact hw⟩
  have hR4 : SRep t4 L FLn FLl FLs FLe st := srep_frame hR2 ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  rcases nDerivedC_spec t4 L FLn st.lss.ls.ns hR4.n n (lookup_setVar_same _ _ _) (by lk [t4, t3]; exact ldir)
    (by lk [t4, t3]) (W4 lDt (by decide) (by decide) (by decide)) (W4 lDg (by decide) (by decide) (by decide))
    (W4 lDi (by decide) (by decide) (by decide)) (W4 lDo1 (by decide) (by decide) (by decide))
    (W4 lDo2 (by decide) (by decide) (by decide))
    with hSD1 | ⟨hvD1, D1⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD1), Or.inl (seq_stop _ _ _ hSD1)⟩
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D1
  generalize hs1 : evaluateHOLFiniteState t4 (storeDerivedC 0 3 badN) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u5⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  have back5 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u5.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t4, t3]; rfl
  obtain ⟨whs, hwhs⟩ := hw lHs (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lHs _ _ whs (eval_vv u5 lDo1 _ o1)
    (by rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwhs))]
  let u6 := setVarHOLFinite lHs (.val (.word (dWN (st.lss.ls.ns.derived n)).1)) u5
  -- the level list's record
  have b6 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs →
      u6.locals.lookup y = t.locals.lookup y := fun y a1 a2 a3 a4 a5 a6 a7 a8 => by lk [u6]; exact back5 y a1 a2 a3 a4 a5 a6 a7
  have fl6 : u6.locals.lookup lFl = some (.val (.word FLn)) := by
    lk [u6]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t4, t3]
  rw [seq_normal _ (ConsLoop.assign_local u6 lFl _ FLs FLn (eval_vv u6 lFls _ (by
    rw [b6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lfls)) fl6)]
  let u7 := setVarHOLFinite lFl (.val (.word FLs)) u6
  have dh7 : u7.locals.lookup lDh = some (.val (.word (Enc.idxW n))) := by
    lk [u7, u6]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t4]
  rw [seq_normal _ (ConsLoop.assign_local u7 lDh _ (Enc.idxW us) (Enc.idxW n) (eval_vv u7 lEus _ (by
    lk [u7, u6]; rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact leus))
    dh7)]
  let u8 := setVarHOLFinite lDh (.val (.word (Enc.idxW us))) u7
  have mem8 : u8.memory = t2.memory := by show u5.memory = _; rw [m1']; rfl
  have md8 : u8.memaddrs = t.memaddrs := by show u5.memaddrs = _; rw [d1]; rfl
  have hR8 : SRep u8 L FLn FLl FLs FLe st := srep_frame hR2 ⟨by rw [mem8], by rw [mem8], by rw [mem8], by rw [mem8]⟩ md8
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem8], fun _ _ => by rw [mem8]⟩)
  have w8 : ∀ y, y = lDt ∨ y = lDg ∨ y = lDi ∨ y = lDo1 ∨ y = lDo2 → ∃ w, u8.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨w, hw⟩ := wd1 lDt (Or.inl rfl); exact ⟨w, by lk [u8, u7, u6]; exact hw⟩
    · obtain ⟨w, hw⟩ := wd1 lDg (Or.inr (Or.inl rfl)); exact ⟨w, by lk [u8, u7, u6]; exact hw⟩
    · obtain ⟨w, hw⟩ := wd1 lDi (Or.inr (Or.inr rfl)); exact ⟨w, by lk [u8, u7, u6]; exact hw⟩
    · exact ⟨_, by lk [u8, u7, u6]; exact o1⟩
    · exact ⟨_, by lk [u8, u7, u6]; exact o2⟩
  rcases lsDerivedC_spec u8 L FLs st.lss hR8.ls us (lookup_setVar_same _ _ _)
    (by lk [u8, u7, u6]; rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by lk [u8, u7]) (w8 lDt (Or.inl rfl)) (w8 lDg (Or.inr (Or.inl rfl))) (w8 lDi (Or.inr (Or.inr (Or.inl rfl))))
    (w8 lDo1 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (w8 lDo2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    with hSD2 | ⟨hvD2, D2⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD2), Or.inl (seq_stop _ _ _ hSD2)⟩
  obtain ⟨n2, m2', d2, c2, g2, ta2, ck2, p1, p2, fr2, wd2⟩ := D2
  generalize hs2 : evaluateHOLFiniteState u8 (storeDerivedC 8 1 badN) = q2 at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2
  obtain ⟨q2r, u9⟩ := q2
  simp only at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2; subst n2
  rw [seq_normal _ hs2]
  refine ⟨?_, Or.inr ⟨hvD1, hvD2⟩⟩
  have back9 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs →
      u9.locals.lookup y = t.locals.lookup y := fun y a1 a2 a3 a4 a5 a6 a7 a8 => by
    rw [fr2 y a1 a2 a3 a4 a5]; lk [u8, u7]; exact b6 y a1 a2 a3 a4 a5 a6 a7 a8
  have wv9 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs → y ∈ constScratch →
      ∃ w, u9.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 a8 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back9 y a1 a2 a3 a4 a5 a6 a7 a8]; exact hw⟩
  let ls := st.lss.derived us
  obtain ⟨wlh, hwlh⟩ := wv9 lLh (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u9 lLh _ _ wlh (eval_vv u9 lDo1 _ p1) hwlh)]
  let u10 := setVarHOLFinite lLh (.val (.word (dWL ls).1)) u9
  obtain ⟨wlp, hwlp⟩ := wv9 lLpv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u10 lLpv _ _ wlp (eval_vv u10 lDo2 _ (by lk [u10]; exact p2)) (by lk [u10]; exact hwlp))]
  let u11 := setVarHOLFinite lLpv (.val (.word (dWL ls).2)) u10
  let dd := st.derOfView (.const n us)
  have hdd : (dWN dd).1 = (ExprData.constDataW (st.lss.ls.ns.derived n) ls.hash (if ls.hasParam then 1 else 0)).toBitVec := by
    show (st.derOfConst n us).toBitVec = _; rw [Der.derOfConst_eq ra]; rfl
  have hs11 : u11.locals.lookup (ofString "hs") = some (.val (.word (st.lss.ls.ns.derived n).toBitVec)) := by
    show u11.locals.lookup lHs = _; lk [u11, u10]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    lk [u8, u7, u6]; rfl
  have lh11 : u11.locals.lookup (ofString "lh") = some (.val (.word ls.hash.toBitVec)) := by
    show u11.locals.lookup lLh = _; lk [u11, u10]; rfl
  have lp11 : u11.locals.lookup (ofString "lp") = some (.val (.word (if ls.hasParam then (1 : UInt64) else 0).toBitVec)) := by
    show u11.locals.lookup lLpv = _; lk [u11]; rw [bitU]; rfl
  have ev11 := ExprData.constDataE.eval u11 _ _ _ hs11 lh11 lp11
  obtain ⟨wv1, hwv1⟩ := wv9 lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u11 lDv _ (dWN dd).1 wv1 (by rw [hdd]; exact ev11) (by lk [u11, u10]; exact hwv1))]
  let u12 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u11
  obtain ⟨wv2, hwv2⟩ := wv9 lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u12 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u12 0) (by lk [u12, u11, u10]; exact hwv2))]
  let u13 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u12
  have en13 : u13.locals.lookup lEn = some (.val (.word (Enc.idxW n))) := by
    lk [u13, u12, u11, u10]; rw [back9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact len
  have eus13 : u13.locals.lookup lEus = some (.val (.word (Enc.idxW us))) := by
    lk [u13, u12, u11, u10]; rw [back9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact leus
  obtain ⟨wsk, hwsk⟩ := wv9 lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u13 lSk _ _ wsk (eval_sk2 u13 lEn lEus n us en13 eus13) (by lk [u13, u12, u11, u10]; exact hwsk))]
  let u14 := setVarHOLFinite lSk (.val (.word (if (if n.isPersistent then !us.isPersistent else true) then 1 else 0))) u13
  have mem14 : u14.memory = t2.memory := by show u9.memory = _; rw [m2']; exact mem8
  have md14 : u14.memaddrs = t.memaddrs := by show u9.memaddrs = _; rw [d2]; exact md8
  have hc14 : u14.code = t.code := by show u9.code = _; rw [c2]; show u5.code = _; rw [c1]; rfl
  have hg14 : u14.globals = t.globals := by show u9.globals = _; rw [g2]; show u5.globals = _; rw [g1]; rfl
  have ht14 : u14.topAddr = t.topAddr := by show u9.topAddr = _; rw [ta2]; show u5.topAddr = _; rw [ta1]; rfl
  have hR14 : SRep u14 L FLn FLl FLs FLe st := srep_frame hR2 ⟨by rw [mem14], by rw [mem14], by rw [mem14], by rw [mem14]⟩
    md14 (fun _ _ _ _ => ⟨fun _ _ => by rw [mem14], fun _ _ => by rw [mem14]⟩)
  have b14 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs → y ≠ lLh → y ≠ lLpv →
      y ≠ lDv → y ≠ lDv2 → y ≠ lSk → u14.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13; lk [u14, u13, u12, u11, u10]; exact back9 y a1 a2 a3 a4 a5 a6 a7 a8
  have hint := estore_const st n us
  simp only at hint
  have hsk : EStore.eViewHasScratchChild (.const n us) = (if n.isPersistent then !us.isPersistent else true) := rfl
  refine eRest_spec t u14 L FLn FLl FLs FLe KB 2 12 st Enc.encConst Enc.encConst_inj (mkN ETag.const 0) (mkN ETag.const 1)
    (2 ^ 26) (fun i hi => by rw [hb0]; exact idxW_mkN ETag.const 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.const 1 (by decide) (by decide) i hi) hS.cap
    st.pers.consts st.scr.consts (EStore.eViewHasScratchChild (.const n us)) ⟨n, us⟩ dd _
    (fun P' S' => { st with pers := { st.pers with consts := P' }, scr := { st.scr with consts := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_consts h1 P' S' h2 h3 h4 h5 h6)
    hS (by decide) (by decide) (by simp [Enc.encConst]) (by decide) hR14 hR14.e.p3 hR14.e.s3 ?_ ?_ md14 hc14 hg14 ht14
    (by lk [u14, u13, u12]) (by lk [u14, u13]) (by rw [hsk]; lk [u14])
    (by rw [b14 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lfle)
    (by rw [b14 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [b14 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lkb) ?_
  · intro k hk
    have hk2 : k < 2 := by simpa [Enc.encConst] using hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine ⟨by rw [md14, KB0]; exact hkbd.1, ?_⟩
      rw [mem14, KB0]; show (if KB = KB + 8 then _ else if KB = KB then _ else _) = _; simp [hkb8, Enc.encConst]
    · refine ⟨by rw [md14, KB1]; exact hkbd.2, ?_⟩
      rw [mem14, KB1]; show (if KB + 8 = KB + 8 then _ else _) = _; simp [Enc.encConst]
  · intro c hc
    have h0 := hc 0 (by decide); have h1 := hc 1 (by decide); rw [KB0] at h0; rw [KB1] at h1
    rw [mem14]; exact m2 c h0 h1
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨FLs, by lk [u14, u13, u12, u11, u10]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u8, u7]⟩
    · obtain ⟨w, hw⟩ := wv9 lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u14, u13, u12, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u14, u13, u12, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u14, u13, u12, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u14, u13, u12, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u14, u13, u12, u11, u10]; exact hw⟩

end

end ConPanqueque.V
