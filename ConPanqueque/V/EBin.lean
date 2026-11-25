import ConPanqueque.V.EConst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Nodes with two expression children

`lam`, `forallE` (and `app`): the key is the two handles, the derived word a
function of the two children's derived words. `eBin2With E rest` writes the
key, reads both children's derived words through the expression store,
evaluates `E` over them (locals `df`, `da`), sets the scratch bit and runs
`rest`. `eBin2_spec` gives any such intern given its word function and the
store's equations.
-/

namespace ConPanqueque.V

pan_exp lamDataE := fun (df da : UInt64) => Der.bindDataW 19 df da
pan_exp forDataE := fun (df da : UInt64) => Der.bindDataW 23 df da

def eBin2With (E : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEf))
  (.seq (.store (.op .add [vv lKb, .const 8]) (vv lEa))
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv lEf))
  (.seq (storeDerivedC 9 10 badE)
  (.seq (.assign .local lDfv (vv lDo1))
  (.seq (.assign .local lDh (vv lEa))
  (.seq (storeDerivedC 9 10 badE)
  (.seq (.assign .local lDav (vv lDo1))
  (.seq (.assign .local lDv E)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual
      (.op .or [.shift .lsr (vv lEf) (.const 31), .shift .lsr (vv lEa) (.const 31)]) (.const 0))) rest)))))))))))

def bin2Scratch : List MlS :=
  [lDh, lDt, lDg, lDi, lDo1, lDo2, lDfv, lDav, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

section
variable {σ : Type} {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

theorem eBin2_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore)
    (f a : EIdx) (k : Nat) (E : ExpHOL 64) (F : UInt64 → UInt64 → UInt64)
    (hE : ∀ (s : PanSemStateFiniteExact 64 σ) (df da : UInt64),
      s.locals.lookup (ofString "df") = some (.val (.word df.toBitVec)) →
      s.locals.lookup (ofString "da") = some (.val (.word da.toBitVec)) →
      @evalHOLExact 64 σ _ s.toExact (fun c => Classical.propDecidable (s.memaddrs c)) E =
        some (.val (.word (F df da).toBitVec)))
    (enc : α → List (BitVec 64)) (hinj : ∀ x y, enc x = enc y → x = y) (x : α)
    (hx : enc x = [Enc.idxW f, Enc.idxW a])
    (mkP mkS : Nat → EIdx) (icap : Nat)
    (hmkP : ∀ i, i < icap → Enc.idxW (mkP i) = L.base k 0 + BitVec.ofNat 64 i)
    (hmkS : ∀ i, i < icap → Enc.idxW (mkS i) = L.base k 1 + BitVec.ofNat 64 i)
    (hicap : ∀ tier, tier < 2 → (L.geo k tier).cap ≤ icap)
    (P Sc : Tbl α EIdx UInt64) (res : EStore × EIdx) (setK : Tbl α EIdx UInt64 → Tbl α EIdx UInt64 → EStore)
    (hres : res =
      (setK (twoTier P Sc st.scratchOn (if f.isPersistent then !a.isPersistent else true) x
          (F (st.derived f) (st.derived a)) mkP mkS).1
        (twoTier P Sc st.scratchOn (if f.isPersistent then !a.isPersistent else true) x
          (F (st.derived f) (st.derived a)) mkP mkS).2.1,
       (twoTier P Sc st.scratchOn (if f.isPersistent then !a.isPersistent else true) x
          (F (st.derived f) (st.derived a)) mkP mkS).2.2))
    (hlss : ∀ P' S', (setK P' S').lss = st.lss)
    (hset : ∀ (v v' : PanSemStateFiniteExact 64 σ) P' S', ERep v L FLe st → TabAt v' L k 0 enc dWN P' mkP →
      TabAt v' L k 1 enc dWN S' mkS → v'.memory FLe = v.memory FLe → v'.memaddrs = v.memaddrs →
      (∀ k' tier, 9 ≤ k' → k' < 19 → tier < 2 → k' ≠ k → Agree L FLe v v' k' tier) → ERep v' L FLe (setK P' S'))
    (htab : ∀ v : PanSemStateFiniteExact 64 σ, ERep v L FLe st → TabAt v L k 0 enc dWN P mkP ∧ TabAt v L k 1 enc dWN Sc mkS)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 k) (hk : 9 ≤ k) (hk19 : k < 19)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (lef : t.locals.lookup lEf = some (.val (.word (Enc.idxW f))))
    (lea : t.locals.lookup lEa = some (.val (.word (Enc.idxW a))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (ERes t L FLn FLl FLs FLe KB 2 st res (evaluateHOLFiniteState t (eBin2With E (eRest k 2)))) ∧
      (Stop (evaluateHOLFiniteState t (eBin2With E (eRest k 2))).1 ∨ ((st.view f).isSome = true ∧ (st.view a).isSome = true)) := by
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
  unfold eBin2With
  rw [seq_normal _ (store_word t (vv lKb) (vv lEf) KB (Enc.idxW f) (eval_vv t lKb _ lkb) (eval_vv t lEf _ lef) hkbd.1)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW f) else t.memory c }
  rw [seq_normal _ (store_word t1 _ (vv lEa) (KB + 8) (Enc.idxW a)
    (eval_add2 t1 _ _ _ _ (eval_vv t1 lKb _ lkb) (eval_const t1 8)) (eval_vv t1 lEa _ lea) hkbd.2)]
  let t2 : PanSemStateFiniteExact 64 σ :=
    { t1 with memory := fun c => if c = KB + 8 then .word (Enc.idxW a) else t1.memory c }
  have m2 : ∀ c, c ≠ KB → c ≠ KB + 8 → t2.memory c = t.memory c := by
    intro c h1 h2; show (if c = KB + 8 then _ else if c = KB then _ else _) = _; rw [ite_eq_right h2, ite_eq_right h1]
  have hR2 : SRep t2 L FLn FLl FLs FLe st := srep_frame hR
    ⟨m2 _ (flne _ (Or.inl rfl)).1 (flne _ (Or.inl rfl)).2, m2 _ (flne _ (Or.inr (Or.inl rfl))).1 (flne _ (Or.inr (Or.inl rfl))).2,
      m2 _ (flne _ (Or.inr (Or.inr (Or.inl rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inl rfl)))).2,
      m2 _ (flne _ (Or.inr (Or.inr (Or.inr rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inr rfl)))).2⟩ rfl
    (fun k tier h1 h2 => ⟨fun m hm => m2 _ (dscne k tier m h1 h2 hm).1 (dscne k tier m h1 h2 hm).2,
      fun c hc => m2 c (fun e => (kbo k tier h1 h2).1 (e ▸ hc)) (fun e => (kbo k tier h1 h2).2 (e ▸ hc))⟩)
  have W : ∀ y, y ∈ bin2Scratch → ∃ w, t2.locals.lookup y = some (.val (.word w)) := hw
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lFl _ FLe wf (eval_vv t2 lFle _ lfle) hwf)]
  let t3 := setVarHOLFinite lFl (.val (.word FLe)) t2
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t3 lDh _ (Enc.idxW f) wh (eval_vv t3 lEf _ (by lk [t3]; exact lef))
    (by lk [t3]; exact hwh))]
  let t4 := setVarHOLFinite lDh (.val (.word (Enc.idxW f))) t3
  have W4 : ∀ y, y ∈ bin2Scratch → y ≠ lFl → y ≠ lDh → ∃ w, t4.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t4, t3]; exact hw⟩
  have hR4 : SRep t4 L FLn FLl FLs FLe st := srep_frame hR2 ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  rcases eDerivedC_spec t4 L FLe st hR4.e f (lookup_setVar_same _ _ _) (by lk [t4, t3]; exact ldir)
    (by lk [t4, t3]) (W4 lDt (by decide) (by decide) (by decide)) (W4 lDg (by decide) (by decide) (by decide))
    (W4 lDi (by decide) (by decide) (by decide)) (W4 lDo1 (by decide) (by decide) (by decide))
    (W4 lDo2 (by decide) (by decide) (by decide))
    with hSD1 | ⟨hvD1, D1⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD1), Or.inl (seq_stop _ _ _ hSD1)⟩
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D1
  generalize hs1 : evaluateHOLFiniteState t4 (storeDerivedC 9 10 badE) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u5⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  have back5 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u5.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t4, t3]; rfl
  obtain ⟨wdf, hwdf⟩ := hw lDfv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDfv _ _ wdf (eval_vv u5 lDo1 _ o1)
    (by rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwdf))]
  let u6 := setVarHOLFinite lDfv (.val (.word (dWN (st.derived f)).1)) u5
  have dh6 : u6.locals.lookup lDh = some (.val (.word (Enc.idxW f))) := by
    lk [u6]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t4]
  rw [seq_normal _ (ConsLoop.assign_local u6 lDh _ (Enc.idxW a) (Enc.idxW f) (eval_vv u6 lEa _ (by
    lk [u6]; rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lea))
    dh6)]
  let u7 := setVarHOLFinite lDh (.val (.word (Enc.idxW a))) u6
  have mem7 : u7.memory = t2.memory := by show u5.memory = _; rw [m1']; rfl
  have md7 : u7.memaddrs = t.memaddrs := by show u5.memaddrs = _; rw [d1]; rfl
  have hR7 : SRep u7 L FLn FLl FLs FLe st := srep_frame hR2 ⟨by rw [mem7], by rw [mem7], by rw [mem7], by rw [mem7]⟩ md7
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem7], fun _ _ => by rw [mem7]⟩)
  have w7 : ∀ y, y = lDt ∨ y = lDg ∨ y = lDi ∨ y = lDo1 ∨ y = lDo2 → ∃ w, u7.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨w, hw⟩ := wd1 lDt (Or.inl rfl); exact ⟨w, by lk [u7, u6]; exact hw⟩
    · obtain ⟨w, hw⟩ := wd1 lDg (Or.inr (Or.inl rfl)); exact ⟨w, by lk [u7, u6]; exact hw⟩
    · obtain ⟨w, hw⟩ := wd1 lDi (Or.inr (Or.inr rfl)); exact ⟨w, by lk [u7, u6]; exact hw⟩
    · exact ⟨_, by lk [u7, u6]; exact o1⟩
    · exact ⟨_, by lk [u7, u6]; exact o2⟩
  have fl7 : u7.locals.lookup lFl = some (.val (.word FLe)) := by
    lk [u7, u6]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t4, t3]
  rcases eDerivedC_spec u7 L FLe st hR7.e a (lookup_setVar_same _ _ _)
    (by lk [u7, u6]; rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    fl7 (w7 lDt (Or.inl rfl)) (w7 lDg (Or.inr (Or.inl rfl))) (w7 lDi (Or.inr (Or.inr (Or.inl rfl))))
    (w7 lDo1 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (w7 lDo2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    with hSD2 | ⟨hvD2, D2⟩
  · exact ⟨Or.inl (seq_stop _ _ _ hSD2), Or.inl (seq_stop _ _ _ hSD2)⟩
  obtain ⟨n2, m2', d2, c2, g2, ta2, ck2, p1, p2, fr2, wd2⟩ := D2
  generalize hs2 : evaluateHOLFiniteState u7 (storeDerivedC 9 10 badE) = q2 at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2
  obtain ⟨q2r, u8⟩ := q2
  simp only at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2; subst n2
  rw [seq_normal _ hs2]
  refine ⟨?_, Or.inr ⟨hvD1, hvD2⟩⟩
  have back8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDfv →
      u8.locals.lookup y = t.locals.lookup y := fun y a1 a2 a3 a4 a5 a6 a7 a8 => by
    rw [fr2 y a1 a2 a3 a4 a5]; lk [u7, u6]; exact back5 y a1 a2 a3 a4 a5 a6 a7
  have wv8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDfv → y ∈ bin2Scratch →
      ∃ w, u8.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 a8 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back8 y a1 a2 a3 a4 a5 a6 a7 a8]; exact hw⟩
  obtain ⟨wda, hwda⟩ := wv8 lDav (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u8 lDav _ _ wda (eval_vv u8 lDo1 _ p1) hwda)]
  let u9 := setVarHOLFinite lDav (.val (.word (dWN (st.derived a)).1)) u8
  let dd := F (st.derived f) (st.derived a)
  have df9 : u9.locals.lookup (ofString "df") = some (.val (.word (st.derived f).toBitVec)) := by
    show u9.locals.lookup lDfv = _; lk [u9]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    lk [u7, u6]; rfl
  have da9 : u9.locals.lookup (ofString "da") = some (.val (.word (st.derived a).toBitVec)) := by
    show u9.locals.lookup lDav = _; lk [u9]; rfl
  obtain ⟨wv1, hwv1⟩ := wv8 lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u9 lDv _ (dWN dd).1 wv1 (hE u9 _ _ df9 da9) (by lk [u9]; exact hwv1))]
  let u10 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u9
  obtain ⟨wv2, hwv2⟩ := wv8 lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u10 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u10 0) (by lk [u10, u9]; exact hwv2))]
  let u11 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u10
  have ef11 : u11.locals.lookup lEf = some (.val (.word (Enc.idxW f))) := by
    lk [u11, u10, u9]; rw [back8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lef
  have ea11 : u11.locals.lookup lEa = some (.val (.word (Enc.idxW a))) := by
    lk [u11, u10, u9]; rw [back8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lea
  obtain ⟨wsk, hwsk⟩ := wv8 lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u11 lSk _ _ wsk (eval_sk2 u11 lEf lEa f a ef11 ea11) (by lk [u11, u10, u9]; exact hwsk))]
  let u12 := setVarHOLFinite lSk (.val (.word (if (if f.isPersistent then !a.isPersistent else true) then 1 else 0))) u11
  have mem12 : u12.memory = t2.memory := by show u8.memory = _; rw [m2']; exact mem7
  have md12 : u12.memaddrs = t.memaddrs := by show u8.memaddrs = _; rw [d2]; exact md7
  have hc12 : u12.code = t.code := by show u8.code = _; rw [c2]; show u5.code = _; rw [c1]; rfl
  have hg12 : u12.globals = t.globals := by show u8.globals = _; rw [g2]; show u5.globals = _; rw [g1]; rfl
  have ht12 : u12.topAddr = t.topAddr := by show u8.topAddr = _; rw [ta2]; show u5.topAddr = _; rw [ta1]; rfl
  have hR12 : SRep u12 L FLn FLl FLs FLe st := srep_frame hR2 ⟨by rw [mem12], by rw [mem12], by rw [mem12], by rw [mem12]⟩
    md12 (fun _ _ _ _ => ⟨fun _ _ => by rw [mem12], fun _ _ => by rw [mem12]⟩)
  have b12 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDfv → y ≠ lDav →
      y ≠ lDv → y ≠ lDv2 → y ≠ lSk → u12.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12; lk [u12, u11, u10, u9]; exact back8 y a1 a2 a3 a4 a5 a6 a7 a8
  refine eRest_spec t u12 L FLn FLl FLs FLe KB 2 k st enc hinj mkP mkS icap hmkP hmkS hicap P Sc _ x dd res setK
    hres hlss hset hS hk hk19 (by rw [hx]; rfl) (by decide) hR12 (htab u12 hR12.e).1 (htab u12 hR12.e).2 ?_ ?_ md12 hc12
    hg12 ht12 (by lk [u12, u11, u10]) (by lk [u12, u11]) (by lk [u12])
    (by rw [b12 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact lfle)
    (by rw [b12 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [b12 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact lkb) ?_
  · rw [hx]
    intro j hj
    have hj2 : j < 2 := by simpa using hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · refine ⟨by rw [md12, KB0]; exact hkbd.1, ?_⟩
      rw [mem12, KB0]; show (if KB = KB + 8 then _ else if KB = KB then _ else _) = _; simp [hkb8]
    · refine ⟨by rw [md12, KB1]; exact hkbd.2, ?_⟩
      rw [mem12, KB1]; show (if KB + 8 = KB + 8 then _ else _) = _; simp
  · intro c hc
    have h0 := hc 0 (by decide); have h1 := hc 1 (by decide); rw [KB0] at h0; rw [KB1] at h1
    rw [mem12]; exact m2 c h0 h1
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨FLe, by lk [u12, u11, u10, u9]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fl7⟩
    · obtain ⟨w, hw⟩ := wv8 lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u11, u10, u9]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv8 lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u11, u10, u9]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv8 lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u11, u10, u9]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv8 lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u11, u10, u9]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv8 lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u11, u10, u9]; exact hw⟩

end

section
variable {σ : Type}

theorem erep_lams {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl BindNode EIdx UInt64)
    (hP : TabAt u L 14 0 Enc.encBind dWN P' (mkN ETag.lam 0)) (hS : TabAt u L 14 1 Enc.encBind dWN Sc' (mkN ETag.lam 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 14 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with lams := P' }, scr := { st.scr with lams := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 14 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
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
    hP,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6,
    A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8,
    A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0,
    A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    hS,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6,
    A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8,
    A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

theorem erep_foralls {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl BindNode EIdx UInt64)
    (hP : TabAt u L 15 0 Enc.encBind dWN P' (mkN ETag.forallE 0)) (hS : TabAt u L 15 1 Enc.encBind dWN Sc' (mkN ETag.forallE 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 15 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with foralls := P' }, scr := { st.scr with foralls := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 15 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
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
    hP,
    A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8,
    A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0,
    A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    hS,
    A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8,
    A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

theorem eInternLam_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (L : Layout)
    (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (ty b : EIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 14)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (hb0 : L.base 14 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lam.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 14 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lam.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (lef : t.locals.lookup lEf = some (.val (.word (Enc.idxW ty))))
    (lea : t.locals.lookup lEa = some (.val (.word (Enc.idxW b))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (ERes t L FLn FLl FLs FLe KB 2 st (st.internLam ty b) (evaluateHOLFiniteState t (eBin2With lamDataE (eRest 14 2)))) ∧
      (Stop (evaluateHOLFiniteState t (eBin2With lamDataE (eRest 14 2))).1 ∨ ((st.view ty).isSome = true ∧ (st.view b).isSome = true)) := by
  have hint := estore_internLam st ty b
  simp only at hint
  have hd : st.derOfBindAt 19 ty b = Der.bindDataW 19 (st.derived ty) (st.derived b) := Der.derOfBind_eq ra st 19 ty b
  rw [hd] at hint
  exact eBin2_spec t L FLn FLl FLs FLe KB st ty b 14 lamDataE (Der.bindDataW 19) (fun s df da h1 h2 => lamDataE.eval s df da h1 h2)
    Enc.encBind Enc.encBind_inj ⟨ty, b⟩ rfl (mkN ETag.lam 0) (mkN ETag.lam 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN ETag.lam 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.lam 1 (by decide) (by decide) i hi) hS.cap
    st.pers.lams st.scr.lams _ (fun P' S' => { st with pers := { st.pers with lams := P' }, scr := { st.scr with lams := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_lams h1 P' S' h2 h3 h4 h5 h6)
    (fun v h => ⟨h.p5, h.s5⟩) hR hS (by decide) (by decide) hkbd hkb8 lkb lef lea ldir lfle hw

theorem eInternForallE_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (L : Layout)
    (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (ty b : EIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 15)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (hb0 : L.base 15 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.forallE.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 15 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.forallE.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (lef : t.locals.lookup lEf = some (.val (.word (Enc.idxW ty))))
    (lea : t.locals.lookup lEa = some (.val (.word (Enc.idxW b))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (ERes t L FLn FLl FLs FLe KB 2 st (st.internForallE ty b)
      (evaluateHOLFiniteState t (eBin2With forDataE (eRest 15 2)))) ∧
      (Stop (evaluateHOLFiniteState t (eBin2With forDataE (eRest 15 2))).1 ∨ ((st.view ty).isSome = true ∧ (st.view b).isSome = true)) := by
  have hint := estore_internForallE st ty b
  simp only at hint
  have hd : st.derOfBindAt 23 ty b = Der.bindDataW 23 (st.derived ty) (st.derived b) := Der.derOfBind_eq ra st 23 ty b
  rw [hd] at hint
  exact eBin2_spec t L FLn FLl FLs FLe KB st ty b 15 forDataE (Der.bindDataW 23) (fun s df da h1 h2 => forDataE.eval s df da h1 h2)
    Enc.encBind Enc.encBind_inj ⟨ty, b⟩ rfl (mkN ETag.forallE 0) (mkN ETag.forallE 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN ETag.forallE 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.forallE 1 (by decide) (by decide) i hi) hS.cap
    st.pers.foralls st.scr.foralls _
    (fun P' S' => { st with pers := { st.pers with foralls := P' }, scr := { st.scr with foralls := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_foralls h1 P' S' h2 h3 h4 h5 h6)
    (fun v h => ⟨h.p6, h.s6⟩) hR hS (by decide) (by decide) hkbd hkb8 lkb lef lea ldir lfle hw

end

end ConPanqueque.V
