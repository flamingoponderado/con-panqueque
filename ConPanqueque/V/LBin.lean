import ConPanqueque.V.LSucc
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Level nodes with two level children: `max`, `imax`

The key `[u, v]`, both children's derived records through the level store,
the hash (`maxHashE`/`imaxHashE` over locals `hu`, `hv`) and the OR of the
parameter bits, no scratch skip, then the generic remainder.
-/

namespace ConPanqueque.V

pan_exp maxHashE := fun (hu hv : UInt64) => Der.binHashW 5 hu hv
pan_exp imaxHashE := fun (hu hv : UInt64) => Der.binHashW 7 hu hv

def lEv := ofString "ev"
def lHu := ofString "hu"
def lHvv := ofString "hv"
def lPu := ofString "pu"

def lBin2With (E : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEu))
  (.seq (.store (.op .add [vv lKb, .const 8]) (vv lEv))
  (.seq (.assign .local lFl (vv lFll))
  (.seq (.assign .local lDh (vv lEu))
  (.seq (storeDerived 3 5)
  (.seq (.assign .local lHu (vv lDo1))
  (.seq (.assign .local lPu (vv lDo2))
  (.seq (.assign .local lDh (vv lEv))
  (.seq (storeDerived 3 5)
  (.seq (.assign .local lHvv (vv lDo1))
  (.seq (.assign .local lDv2 (.op .or [vv lPu, vv lDo2]))
  (.seq (.assign .local lDv E)
  (.seq (.assign .local lSk (.const 0)) rest))))))))))))

def lbin2Scratch : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lHu, lPu, lHvv, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

section
variable {σ : Type}

theorem lrep_maxs {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ls : LStore}
    (h : LRep t L FL ls) (P' Sc' : Tbl BinLNode LIdx LDer)
    (hP : TabAt u L 5 0 Enc.encBinL dWL P' (mkN LTag.max 0)) (hS : TabAt u L 5 1 Enc.encBinL dWL Sc' (mkN LTag.max 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 5 → Agree L FL t u k tier) :
    LRep u L FL { ls with pers := { ls.pers with maxs := P' }, scr := { ls.scr with maxs := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 5 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 3 0 (by decide) (by decide) (by decide) h.pz,
    A 4 0 (by decide) (by decide) (by decide) h.ps,
    hP,
    A 6 0 (by decide) (by decide) (by decide) h.pi,
    A 7 0 (by decide) (by decide) (by decide) h.pp,
    A 3 1 (by decide) (by decide) (by decide) h.sz,
    A 4 1 (by decide) (by decide) (by decide) h.ss,
    hS,
    A 6 1 (by decide) (by decide) (by decide) h.si,
    A 7 1 (by decide) (by decide) (by decide) h.sp⟩

theorem lrep_imaxs {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ls : LStore}
    (h : LRep t L FL ls) (P' Sc' : Tbl BinLNode LIdx LDer)
    (hP : TabAt u L 6 0 Enc.encBinL dWL P' (mkN LTag.imax 0)) (hS : TabAt u L 6 1 Enc.encBinL dWL Sc' (mkN LTag.imax 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 6 → Agree L FL t u k tier) :
    LRep u L FL { ls with pers := { ls.pers with imaxs := P' }, scr := { ls.scr with imaxs := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 6 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 3 0 (by decide) (by decide) (by decide) h.pz,
    A 4 0 (by decide) (by decide) (by decide) h.ps,
    A 5 0 (by decide) (by decide) (by decide) h.pm,
    hP,
    A 7 0 (by decide) (by decide) (by decide) h.pp,
    A 3 1 (by decide) (by decide) (by decide) h.sz,
    A 4 1 (by decide) (by decide) (by decide) h.ss,
    A 5 1 (by decide) (by decide) (by decide) h.sm,
    hS,
    A 7 1 (by decide) (by decide) (by decide) h.sp⟩

end

section
variable {σ : Type}

theorem lBin2_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore)
    (u v : LIdx) (k : Nat) (E : ExpHOL 64) (F : UInt64 → UInt64 → UInt64)
    (hE : ∀ (s : PanSemStateFiniteExact 64 σ) (hu hv : UInt64),
      s.locals.lookup (ofString "hu") = some (.val (.word hu.toBitVec)) →
      s.locals.lookup (ofString "hv") = some (.val (.word hv.toBitVec)) →
      @evalHOLExact 64 σ _ s.toExact (fun c => Classical.propDecidable (s.memaddrs c)) E =
        some (.val (.word (F hu hv).toBitVec)))
    (mkP mkS : Nat → LIdx) (icap : Nat)
    (hmkP : ∀ i, i < icap → Enc.idxW (mkP i) = L.base k 0 + BitVec.ofNat 64 i)
    (hmkS : ∀ i, i < icap → Enc.idxW (mkS i) = L.base k 1 + BitVec.ofNat 64 i)
    (hicap : ∀ tier, tier < 2 → (L.geo k tier).cap ≤ icap)
    (P Sc : Tbl BinLNode LIdx LDer) (res : LStore × LIdx) (setL : Tbl BinLNode LIdx LDer → Tbl BinLNode LIdx LDer → LStore)
    (hres : res =
      (setL (twoTier P Sc st.lss.ls.scratchOn false ⟨u, v⟩
          ⟨F (st.lss.ls.derived u).hash (st.lss.ls.derived v).hash,
            (st.lss.ls.derived u).hasParam || (st.lss.ls.derived v).hasParam⟩ mkP mkS).1
        (twoTier P Sc st.lss.ls.scratchOn false ⟨u, v⟩
          ⟨F (st.lss.ls.derived u).hash (st.lss.ls.derived v).hash,
            (st.lss.ls.derived u).hasParam || (st.lss.ls.derived v).hasParam⟩ mkP mkS).2.1,
       (twoTier P Sc st.lss.ls.scratchOn false ⟨u, v⟩
          ⟨F (st.lss.ls.derived u).hash (st.lss.ls.derived v).hash,
            (st.lss.ls.derived u).hasParam || (st.lss.ls.derived v).hasParam⟩ mkP mkS).2.2))
    (hns : ∀ P' S', (setL P' S').ns = st.lss.ls.ns)
    (hset : ∀ (x x' : PanSemStateFiniteExact 64 σ) P' S', LRep x L FLl st.lss.ls →
      TabAt x' L k 0 Enc.encBinL dWL P' mkP → TabAt x' L k 1 Enc.encBinL dWL S' mkS →
      x'.memory FLl = x.memory FLl → x'.memaddrs = x.memaddrs →
      (∀ k' tier, k' < 19 → tier < 2 → k' ≠ k → Agree L FLl x x' k' tier) → LRep x' L FLl (setL P' S'))
    (htab : ∀ x : PanSemStateFiniteExact 64 σ, LRep x L FLl st.lss.ls →
      TabAt x L k 0 Enc.encBinL dWL P mkP ∧ TabAt x L k 1 Enc.encBinL dWL Sc mkS)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 k) (hk : 3 ≤ k) (hk8 : k < 8)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (leu : t.locals.lookup lEu = some (.val (.word (Enc.idxW u))))
    (lev : t.locals.lookup lEv = some (.val (.word (Enc.idxW v))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfll : t.locals.lookup lFll = some (.val (.word FLl)))
    (hw : ∀ y, y ∈ lbin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    XRes t L FLn FLl FLs FLe KB 2 (withL st res.1) res.2 (evaluateHOLFiniteState t (lBin2With E (rRest k 2 lFll))) := by
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
  unfold lBin2With
  rw [seq_normal _ (store_word t (vv lKb) (vv lEu) KB (Enc.idxW u) (eval_vv t lKb _ lkb) (eval_vv t lEu _ leu) hkbd.1)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW u) else t.memory c }
  rw [seq_normal _ (store_word t1 _ (vv lEv) (KB + 8) (Enc.idxW v)
    (eval_add2 t1 _ _ _ _ (eval_vv t1 lKb _ lkb) (eval_const t1 8)) (eval_vv t1 lEv _ lev) hkbd.2)]
  let t2 : PanSemStateFiniteExact 64 σ :=
    { t1 with memory := fun c => if c = KB + 8 then .word (Enc.idxW v) else t1.memory c }
  have m2 : ∀ c, c ≠ KB → c ≠ KB + 8 → t2.memory c = t.memory c := by
    intro c h1 h2; show (if c = KB + 8 then _ else if c = KB then _ else _) = _; rw [if_neg h2, if_neg h1]
  have hR2 : SRep t2 L FLn FLl FLs FLe st := srep_frame hR
    ⟨m2 _ (flne _ (Or.inl rfl)).1 (flne _ (Or.inl rfl)).2, m2 _ (flne _ (Or.inr (Or.inl rfl))).1 (flne _ (Or.inr (Or.inl rfl))).2,
      m2 _ (flne _ (Or.inr (Or.inr (Or.inl rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inl rfl)))).2,
      m2 _ (flne _ (Or.inr (Or.inr (Or.inr rfl)))).1 (flne _ (Or.inr (Or.inr (Or.inr rfl)))).2⟩ rfl
    (fun k tier h1 h2 => ⟨fun m hm => m2 _ (dscne k tier m h1 h2 hm).1 (dscne k tier m h1 h2 hm).2,
      fun c hc => m2 c (fun e => (kbo k tier h1 h2).1 (e ▸ hc)) (fun e => (kbo k tier h1 h2).2 (e ▸ hc))⟩)
  have W : ∀ y, y ∈ lbin2Scratch → ∃ w, t2.locals.lookup y = some (.val (.word w)) := hw
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lFl _ FLl wf (eval_vv t2 lFll _ lfll) hwf)]
  let t3 := setVarHOLFinite lFl (.val (.word FLl)) t2
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t3 lDh _ (Enc.idxW u) wh (eval_vv t3 lEu _ (by lk [t3]; exact leu))
    (by lk [t3]; exact hwh))]
  let t4 := setVarHOLFinite lDh (.val (.word (Enc.idxW u))) t3
  have W4 : ∀ y, y ∈ lbin2Scratch → y ≠ lFl → y ≠ lDh → ∃ w, t4.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t4, t3]; exact hw⟩
  have hR4 : SRep t4 L FLn FLl FLs FLe st := srep_frame hR2 ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have D1 := lDerived_spec t4 L FLl st.lss.ls hR4.l u (lookup_setVar_same _ _ _) (by lk [t4, t3]; exact ldir)
    (by lk [t4, t3]) (W4 lDt (by decide) (by decide) (by decide)) (W4 lDg (by decide) (by decide) (by decide))
    (W4 lDi (by decide) (by decide) (by decide)) (W4 lDo1 (by decide) (by decide) (by decide))
    (W4 lDo2 (by decide) (by decide) (by decide))
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D1
  generalize hs1 : evaluateHOLFiniteState t4 (storeDerived 3 5) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u5⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  have back5 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u5.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t4, t3]; rfl
  obtain ⟨whu, hwhu⟩ := hw lHu (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lHu _ _ whu (eval_vv u5 lDo1 _ o1)
    (by rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwhu))]
  let u6 := setVarHOLFinite lHu (.val (.word (dWL (st.lss.ls.derived u)).1)) u5
  obtain ⟨wpu, hwpu⟩ := hw lPu (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lPu _ _ wpu (eval_vv u6 lDo2 _ (by lk [u6]; exact o2))
    (by lk [u6]; rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwpu))]
  let u7 := setVarHOLFinite lPu (.val (.word (dWL (st.lss.ls.derived u)).2)) u6
  have dh7 : u7.locals.lookup lDh = some (.val (.word (Enc.idxW u))) := by
    lk [u7, u6]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t4]
  rw [seq_normal _ (ConsLoop.assign_local u7 lDh _ (Enc.idxW v) (Enc.idxW u) (eval_vv u7 lEv _ (by
    lk [u7, u6]; rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lev))
    dh7)]
  let u8 := setVarHOLFinite lDh (.val (.word (Enc.idxW v))) u7
  have mem8 : u8.memory = t2.memory := by show u5.memory = _; rw [m1']; rfl
  have md8 : u8.memaddrs = t.memaddrs := by show u5.memaddrs = _; rw [d1]; rfl
  have hR8 : SRep u8 L FLn FLl FLs FLe st := srep_frame hR2 ⟨by rw [mem8], by rw [mem8], by rw [mem8], by rw [mem8]⟩ md8
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem8], fun _ _ => by rw [mem8]⟩)
  have fl8 : u8.locals.lookup lFl = some (.val (.word FLl)) := by
    lk [u8, u7, u6]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t4, t3]
  have D2 := lDerived_spec u8 L FLl st.lss.ls hR8.l v (lookup_setVar_same _ _ _)
    (by lk [u8, u7, u6]; rw [back5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    fl8 (by obtain ⟨w, hw⟩ := wd1 lDt (Or.inl rfl); exact ⟨w, by lk [u8, u7, u6]; exact hw⟩)
    (by obtain ⟨w, hw⟩ := wd1 lDg (Or.inr (Or.inl rfl)); exact ⟨w, by lk [u8, u7, u6]; exact hw⟩)
    (by obtain ⟨w, hw⟩ := wd1 lDi (Or.inr (Or.inr rfl)); exact ⟨w, by lk [u8, u7, u6]; exact hw⟩)
    ⟨_, by lk [u8, u7, u6]; exact o1⟩ ⟨_, by lk [u8, u7, u6]; exact o2⟩
  obtain ⟨n2, m2', d2, c2, g2, ta2, ck2, p1, p2, fr2, wd2⟩ := D2
  generalize hs2 : evaluateHOLFiniteState u8 (storeDerived 3 5) = q2 at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2
  obtain ⟨q2r, u9⟩ := q2
  simp only at n2 m2' d2 c2 g2 ta2 ck2 p1 p2 fr2 wd2; subst n2
  rw [seq_normal _ hs2]
  have back9 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHu → y ≠ lPu →
      u9.locals.lookup y = t.locals.lookup y := fun y a1 a2 a3 a4 a5 a6 a7 a8 a9 => by
    rw [fr2 y a1 a2 a3 a4 a5]; lk [u8, u7, u6]; exact back5 y a1 a2 a3 a4 a5 a6 a7
  have wv9 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHu → y ≠ lPu →
      y ∈ lbin2Scratch → ∃ w, u9.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 a8 a9 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back9 y a1 a2 a3 a4 a5 a6 a7 a8 a9]; exact hw⟩
  let lu := st.lss.ls.derived u
  let lv := st.lss.ls.derived v
  let dd : LDer := ⟨F lu.hash lv.hash, lu.hasParam || lv.hasParam⟩
  obtain ⟨whv, hwhv⟩ := wv9 lHvv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u9 lHvv _ _ whv (eval_vv u9 lDo1 _ p1) hwhv)]
  let u10 := setVarHOLFinite lHvv (.val (.word (dWL lv).1)) u9
  obtain ⟨wv2, hwv2⟩ := wv9 lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have pu10 : u10.locals.lookup lPu = some (.val (.word (dWL lu).2)) := by
    lk [u10]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u8, u7]; rfl
  rw [seq_normal _ (ConsLoop.assign_local u10 lDv2 _ (dWL dd).2 wv2
    (by rw [eval_or2 u10 _ _ _ _ (eval_vv u10 lPu _ pu10) (eval_vv u10 lDo2 _ (by lk [u10]; exact p2))]
        show some (ValueHOL.val (HolWordLab.word ((if lu.hasParam then (1 : BitVec 64) else 0) |||
          (if lv.hasParam then 1 else 0)))) = some (ValueHOL.val (HolWordLab.word (if (lu.hasParam || lv.hasParam) then 1 else 0)))
        generalize lu.hasParam = a; generalize lv.hasParam = b; cases a <;> cases b <;> rfl) (by lk [u10]; exact hwv2))]
  let u11 := setVarHOLFinite lDv2 (.val (.word (dWL dd).2)) u10
  obtain ⟨wv1, hwv1⟩ := wv9 lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hu11 : u11.locals.lookup (ofString "hu") = some (.val (.word lu.hash.toBitVec)) := by
    show u11.locals.lookup lHu = _; lk [u11, u10]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    lk [u8, u7, u6]; rfl
  have hv11 : u11.locals.lookup (ofString "hv") = some (.val (.word lv.hash.toBitVec)) := by
    show u11.locals.lookup lHvv = _; lk [u11, u10]; rfl
  rw [seq_normal _ (ConsLoop.assign_local u11 lDv _ (dWL dd).1 wv1 (hE u11 _ _ hu11 hv11) (by lk [u11, u10]; exact hwv1))]
  let u12a := setVarHOLFinite lDv (.val (.word (dWL dd).1)) u11
  obtain ⟨wsk, hwsk⟩ := wv9 lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u12a lSk (.const 0) (if false then 1 else 0) wsk (eval_const u12a 0)
    (by lk [u12a, u11, u10]; exact hwsk))]
  let u12 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) u12a
  have mem12 : u12.memory = t2.memory := by show u9.memory = _; rw [m2']; exact mem8
  have md12 : u12.memaddrs = t.memaddrs := by show u9.memaddrs = _; rw [d2]; exact md8
  have hc12 : u12.code = t.code := by show u9.code = _; rw [c2]; show u5.code = _; rw [c1]; rfl
  have hg12 : u12.globals = t.globals := by show u9.globals = _; rw [g2]; show u5.globals = _; rw [g1]; rfl
  have ht12 : u12.topAddr = t.topAddr := by show u9.topAddr = _; rw [ta2]; show u5.topAddr = _; rw [ta1]; rfl
  have hR12 : SRep u12 L FLn FLl FLs FLe st := srep_frame hR2 ⟨by rw [mem12], by rw [mem12], by rw [mem12], by rw [mem12]⟩
    md12 (fun _ _ _ _ => ⟨fun _ _ => by rw [mem12], fun _ _ => by rw [mem12]⟩)
  have b12 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHu → y ≠ lPu →
      y ≠ lHvv → y ≠ lDv2 → y ≠ lDv → y ≠ lSk → u12.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13; lk [u12, u12a, u11, u10]; exact back9 y a1 a2 a3 a4 a5 a6 a7 a8 a9
  have R := rRest_spec t u12 L FLn FLl FLs FLe KB FLl 2 k lFll (by decide) st.lss.ls.scratchOn Enc.encBinL dWL Enc.idxW
    Enc.encBinL_inj mkP mkS icap hmkP hmkS hicap P Sc false ⟨u, v⟩ dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withL st res.1))
    (fun v' hP hS' hf hd' hag => by
      rw [hres]
      exact srep_withL hR12 k _ (hns _ _) (hset u12 v' _ _ hR12.l hP hS' (hf _ (Or.inr (Or.inl rfl))) hd'
        (fun k' tier h1 h2 h3 => hag k' tier h1 h2 h3)) hf hd' hag hk hk8)
    hS (by omega) (by simp [Enc.encBinL]) (by decide) (Or.inr (Or.inl rfl)) hR12.l.fl (htab u12 hR12.l).1
    (htab u12 hR12.l).2 ?_ (by lk [u12, u12a]) (by lk [u12, u12a, u11]) (by lk [u12])
    (by rw [b12 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lfll)
    (by rw [b12 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [b12 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lkb) ?_
  · rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
    · exact Or.inl hs
    refine Or.inr ⟨by rw [hr, hres], hQ, c3.trans hc12, g3.trans hg12, d3.trans md12, ta3.trans ht12, fun c h1 h2 => ?_⟩
    have n0 : ¬ inR (L.geo k 0) c := fun hc => h1 ⟨k, 0, by omega, by decide, hc⟩
    have n1 : ¬ inR (L.geo k 1) c := fun hc => h1 ⟨k, 1, by omega, by decide, hc⟩
    have h0 := h2 0 (by decide); have h1' := h2 1 (by decide); rw [KB0] at h0; rw [KB1] at h1'
    rw [fr3 c n0 n1, mem12]; exact m2 c h0 h1'
  · intro j hj
    have hj2 : j < 2 := by simpa [Enc.encBinL] using hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · refine ⟨by rw [md12, KB0]; exact hkbd.1, ?_⟩
      rw [mem12, KB0]; show (if KB = KB + 8 then _ else if KB = KB then _ else _) = _; simp [hkb8, Enc.encBinL]
    · refine ⟨by rw [md12, KB1]; exact hkbd.2, ?_⟩
      rw [mem12, KB1]; show (if KB + 8 = KB + 8 then _ else _) = _; simp [Enc.encBinL]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨FLl, by lk [u12, u12a, u11, u10]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fl8⟩
    · obtain ⟨w, hw⟩ := wv9 lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u12a, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u12a, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u12a, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u12a, u11, u10]; exact hw⟩
    · obtain ⟨w, hw⟩ := wv9 lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u12, u12a, u11, u10]; exact hw⟩

end

section
variable {σ : Type}

theorem lInternMax_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (L : Layout)
    (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (u v : LIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 5)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (hb0 : L.base 5 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.max.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 5 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.max.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (leu : t.locals.lookup lEu = some (.val (.word (Enc.idxW u))))
    (lev : t.locals.lookup lEv = some (.val (.word (Enc.idxW v))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfll : t.locals.lookup lFll = some (.val (.word FLl)))
    (hw : ∀ y, y ∈ lbin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    XRes t L FLn FLl FLs FLe KB 2 (withL st (st.lss.ls.intern (.max u v)).1) (st.lss.ls.intern (.max u v)).2
      (evaluateHOLFiniteState t (lBin2With maxHashE (rRest 5 2 lFll))) := by
  have hint := lstore_max st.lss.ls u v
  simp only at hint
  rw [Der.lmax_eq ra] at hint
  exact lBin2_spec t L FLn FLl FLs FLe KB st u v 5 maxHashE (Der.binHashW 5) (fun s a b h1 h2 => maxHashE.eval s a b h1 h2)
    (mkN LTag.max 0) (mkN LTag.max 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN LTag.max 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN LTag.max 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.pers.maxs st.lss.ls.scr.maxs _
    (fun P' S' => { st.lss.ls with pers := { st.lss.ls.pers with maxs := P' }, scr := { st.lss.ls.scr with maxs := S' } })
    hint (fun _ _ => rfl) (fun x x' P' S' h1 h2 h3 h4 h5 h6 => lrep_maxs h1 P' S' h2 h3 h4 h5 h6)
    (fun x h => ⟨h.pm, h.sm⟩) hR hS (by decide) (by decide)
    hkbd hkb8 lkb leu lev ldir lfll hw

theorem lInternImax_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (L : Layout)
    (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (u v : LIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 6)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (hb0 : L.base 6 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.imax.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 6 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.imax.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (leu : t.locals.lookup lEu = some (.val (.word (Enc.idxW u))))
    (lev : t.locals.lookup lEv = some (.val (.word (Enc.idxW v))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfll : t.locals.lookup lFll = some (.val (.word FLl)))
    (hw : ∀ y, y ∈ lbin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    XRes t L FLn FLl FLs FLe KB 2 (withL st (st.lss.ls.intern (.imax u v)).1) (st.lss.ls.intern (.imax u v)).2
      (evaluateHOLFiniteState t (lBin2With imaxHashE (rRest 6 2 lFll))) := by
  have hint := lstore_imax st.lss.ls u v
  simp only at hint
  rw [Der.limax_eq ra] at hint
  exact lBin2_spec t L FLn FLl FLs FLe KB st u v 6 imaxHashE (Der.binHashW 7) (fun s a b h1 h2 => imaxHashE.eval s a b h1 h2)
    (mkN LTag.imax 0) (mkN LTag.imax 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN LTag.imax 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN LTag.imax 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.pers.imaxs st.lss.ls.scr.imaxs _
    (fun P' S' => { st.lss.ls with pers := { st.lss.ls.pers with imaxs := P' }, scr := { st.lss.ls.scr with imaxs := S' } })
    hint (fun _ _ => rfl) (fun x x' P' S' h1 h2 h3 h4 h5 h6 => lrep_imaxs h1 P' S' h2 h3 h4 h5 h6)
    (fun x h => ⟨h.pi, h.si⟩) hR hS (by decide) (by decide)
    hkbd hkb8 lkb leu lev ldir lfll hw

end

end ConPanqueque.V
