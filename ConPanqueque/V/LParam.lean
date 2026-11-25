import ConPanqueque.V.LBin
import ConPanqueque.V.EConst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Level `param n` and `zero`

`param n`: the key `[n]`, the name's derived word through the name store,
`paramHashE`, parameter bit 1. `zero`: the empty key and the record `(1, false)`.
Both without scratch skip, then the generic remainder.
-/

namespace ConPanqueque.V

def lParamWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEn))
  (.seq (.assign .local lFl (vv lFln))
  (.seq (.assign .local lDh (vv lEn))
  (.seq (storeDerivedC 0 3 badN)
  (.seq (.assign .local lHn (vv lDo1))
  (.seq (.assign .local lDv Der.paramHashE)
  (.seq (.assign .local lDv2 (.const 1))
  (.seq (.assign .local lSk (.const 0)) rest)))))))

def paramScratch : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lHn, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

def lZeroWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lDv (.const 1)) (.seq (.assign .local lDv2 (.const 0)) (.seq (.assign .local lSk (.const 0)) rest))

section
variable {σ : Type}

theorem lrep_params {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ls : LStore}
    (h : LRep t L FL ls) (P' Sc' : Tbl ParamNode LIdx LDer)
    (hP : TabAt u L 7 0 Enc.encParam dWL P' (mkN LTag.param 0)) (hS : TabAt u L 7 1 Enc.encParam dWL Sc' (mkN LTag.param 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 7 → Agree L FL t u k tier) :
    LRep u L FL { ls with pers := { ls.pers with params := P' }, scr := { ls.scr with params := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 7 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 3 0 (by decide) (by decide) (by decide) h.pz,
    A 4 0 (by decide) (by decide) (by decide) h.ps,
    A 5 0 (by decide) (by decide) (by decide) h.pm,
    A 6 0 (by decide) (by decide) (by decide) h.pi,
    hP,
    A 3 1 (by decide) (by decide) (by decide) h.sz,
    A 4 1 (by decide) (by decide) (by decide) h.ss,
    A 5 1 (by decide) (by decide) (by decide) h.sm,
    A 6 1 (by decide) (by decide) (by decide) h.si,
    hS⟩

theorem lrep_zeros {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ls : LStore}
    (h : LRep t L FL ls) (P' Sc' : Tbl ZeroNode LIdx LDer)
    (hP : TabAt u L 3 0 Enc.encZero dWL P' (mkN LTag.zero 0)) (hS : TabAt u L 3 1 Enc.encZero dWL Sc' (mkN LTag.zero 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 3 → Agree L FL t u k tier) :
    LRep u L FL { ls with pers := { ls.pers with zeros := P' }, scr := { ls.scr with zeros := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 3 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    hP,
    A 4 0 (by decide) (by decide) (by decide) h.ps,
    A 5 0 (by decide) (by decide) (by decide) h.pm,
    A 6 0 (by decide) (by decide) (by decide) h.pi,
    A 7 0 (by decide) (by decide) (by decide) h.pp,
    hS,
    A 4 1 (by decide) (by decide) (by decide) h.ss,
    A 5 1 (by decide) (by decide) (by decide) h.sm,
    A 6 1 (by decide) (by decide) (by decide) h.si,
    A 7 1 (by decide) (by decide) (by decide) h.sp⟩

end

section
variable {σ : Type}

theorem lInternParam_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (n : NIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 1 7)
    (hkbd : t.memaddrs KB)
    (hb0 : L.base 7 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.param.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 7 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.param.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (Enc.idxW n))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfln : t.locals.lookup lFln = some (.val (.word FLn))) (lfll : t.locals.lookup lFll = some (.val (.word FLl)))
    (hw : ∀ y, y ∈ paramScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (XRes t L FLn FLl FLs FLe KB 1 (withL st (st.lss.ls.intern (.param n)).1) (st.lss.ls.intern (.param n)).2
      (evaluateHOLFiniteState t (lParamWith (rRest 7 1 lFll)))) ∧
      (Stop (evaluateHOLFiniteState t (lParamWith (rRest 7 1 lFll))).1 ∨ ((st.lss.ls.ns.view n).isSome = true)) := by
  have KB0 : KB + BitVec.ofNat 64 (8 * 0) = KB := by simp
  have flne : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → F ≠ KB := fun F hF => by
    have := (hS.fls F hF).2.2 0 (by decide); rwa [KB0] at this
  have dscne : ∀ k tier m, k < 19 → tier < 2 → m < 8 → descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB :=
    fun k tier m h1 h2 h3 => by have := (hS.dsc k tier m h1 h2 h3).2.2 0 (by decide); rwa [KB0] at this
  have kbo : ∀ k tier, k < 19 → tier < 2 → ¬ inR (L.geo k tier) KB := fun k tier h1 h2 => by
    have := hS.kbo 0 k tier (by decide) h1 h2; rwa [KB0] at this
  unfold lParamWith
  rw [seq_normal _ (store_word t (vv lKb) (vv lEn) KB (Enc.idxW n) (eval_vv t lKb _ lkb) (eval_vv t lEn _ len) hkbd)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW n) else t.memory c }
  have m1 : ∀ c, c ≠ KB → t1.memory c = t.memory c := fun c h => by show (if c = KB then _ else _) = _; rw [ite_eq_right h]
  have hR1 : SRep t1 L FLn FLl FLs FLe st := srep_frame hR
    ⟨m1 _ (flne _ (Or.inl rfl)), m1 _ (flne _ (Or.inr (Or.inl rfl))), m1 _ (flne _ (Or.inr (Or.inr (Or.inl rfl)))),
      m1 _ (flne _ (Or.inr (Or.inr (Or.inr rfl))))⟩ rfl
    (fun k tier h1 h2 => ⟨fun m hm => m1 _ (dscne k tier m h1 h2 hm), fun c hc => m1 c (fun e => kbo k tier h1 h2 (e ▸ hc))⟩)
  have W : ∀ y, y ∈ paramScratch → ∃ w, t1.locals.lookup y = some (.val (.word w)) := hw
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lFl _ FLn wf (eval_vv t1 lFln _ lfln) hwf)]
  let t2 := setVarHOLFinite lFl (.val (.word FLn)) t1
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lDh _ (Enc.idxW n) wh (eval_vv t2 lEn _ (by lk [t2]; exact len))
    (by lk [t2]; exact hwh))]
  let t3 := setVarHOLFinite lDh (.val (.word (Enc.idxW n))) t2
  have W3 : ∀ y, y ∈ paramScratch → y ≠ lFl → y ≠ lDh → ∃ w, t3.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t3, t2]; exact hw⟩
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR1 ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  rcases nDerivedC_spec t3 L FLn st.lss.ls.ns hR3.n n (lookup_setVar_same _ _ _) (by lk [t3, t2]; exact ldir)
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
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t3, t2]; rfl
  have wv : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ∈ paramScratch →
      ∃ w, u4.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  let ld := st.lss.ls.ns.derived n
  obtain ⟨whv, hwhv⟩ := wv lHn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lHn _ _ whv (eval_vv u4 lDo1 _ o1) hwhv)]
  let u5 := setVarHOLFinite lHn (.val (.word (dWN ld).1)) u4
  let dd := st.lss.ls.derOfView (.param n)
  have hdd : dd = ⟨Der.paramHashW ld, true⟩ := Der.lparam_eq ra st.lss.ls n
  obtain ⟨wv1, hwv1⟩ := wv lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDv _ (dWL dd).1 wv1
    (by rw [hdd]; exact Der.paramHashE.eval u5 _ (by show u5.locals.lookup lHn = _; lk [u5]; rfl)) (by lk [u5]; exact hwv1))]
  let u6 := setVarHOLFinite lDv (.val (.word (dWL dd).1)) u5
  obtain ⟨wv2, hwv2⟩ := wv lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lDv2 (.const 1) (dWL dd).2 wv2 (by
      have hp : dd.hasParam = true := by rw [hdd]
      show _ = some (ValueHOL.val (HolWordLab.word (if dd.hasParam then (1 : BitVec 64) else 0)))
      rw [hp]; rfl) (by lk [u6, u5]; exact hwv2))]
  let u7 := setVarHOLFinite lDv2 (.val (.word (dWL dd).2)) u6
  obtain ⟨wsk, hwsk⟩ := wv lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u7 lSk (.const 0) (if false then 1 else 0) wsk (eval_const u7 0)
    (by lk [u7, u6, u5]; exact hwsk))]
  let u8 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) u7
  have mem8 : u8.memory = t1.memory := by show u4.memory = _; rw [m1']; rfl
  have md8 : u8.memaddrs = t.memaddrs := by show u4.memaddrs = _; rw [d1]; rfl
  have hc8 : u8.code = t.code := by show u4.code = _; rw [c1]; rfl
  have hg8 : u8.globals = t.globals := by show u4.globals = _; rw [g1]; rfl
  have ht8 : u8.topAddr = t.topAddr := by show u4.topAddr = _; rw [ta1]; rfl
  have hR8 : SRep u8 L FLn FLl FLs FLe st := srep_frame hR1 ⟨by rw [mem8], by rw [mem8], by rw [mem8], by rw [mem8]⟩ md8
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem8], fun _ _ => by rw [mem8]⟩)
  have g : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHn → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → y ∈ paramScratch → ∃ w, u8.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 hy
    obtain ⟨w, hw⟩ := wv y a1 a2 a3 a4 a5 a6 a7 hy; exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
  have b8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHn → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → u8.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; lk [u8, u7, u6, u5]; exact back y a1 a2 a3 a4 a5 a6 a7
  have hint := lstore_param st.lss.ls n
  simp only at hint
  have R := rRest_spec t u8 L FLn FLl FLs FLe KB FLl 1 7 lFll (by decide) st.lss.ls.scratchOn Enc.encParam dWL Enc.idxW
    Enc.encParam_inj (mkN LTag.param 0) (mkN LTag.param 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN LTag.param 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN LTag.param 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.pers.params st.lss.ls.scr.params false ⟨n⟩ dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withL st (st.lss.ls.intern (.param n)).1))
    (fun v' hP hS' hf hd' hag => by
      rw [hint]
      exact srep_withL hR8 7 _ rfl (lrep_params hR8.l _ _ hP hS' (hf _ (Or.inr (Or.inl rfl))) hd'
        (fun k tier h1 h2 h3 => hag k tier h1 h2 h3)) hf hd' hag (by decide) (by decide))
    hS (by decide) (by simp [Enc.encParam]) (by decide) (Or.inr (Or.inl rfl)) hR8.l.fl hR8.l.pp hR8.l.sp ?_
    (by lk [u8, u7, u6]) (by lk [u8, u7]) (by lk [u8])
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lfll)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact ldir)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lkb) ?_
  · rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
    · exact Or.inl hs
    refine Or.inr ⟨by rw [hr, hint], hQ, c3.trans hc8, g3.trans hg8, d3.trans md8, ta3.trans ht8, fun c h1 h2 => ?_⟩
    have n0 : ¬ inR (L.geo 7 0) c := fun hc => h1 ⟨7, 0, by decide, by decide, hc⟩
    have n1 : ¬ inR (L.geo 7 1) c := fun hc => h1 ⟨7, 1, by decide, by decide, hc⟩
    have h0 := h2 0 (by decide); rw [KB0] at h0
    rw [fr3 c n0 n1, mem8]; exact m1 c h0
  · intro j hj
    have hj1 : j < 1 := by simpa [Enc.encParam] using hj
    rcases (by omega : j = 0) with rfl
    refine ⟨by rw [md8, KB0]; exact hkbd, ?_⟩
    rw [mem8, KB0]; show (if KB = KB then _ else _) = _; simp [Enc.encParam]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨FLn, by lk [u8, u7, u6, u5]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3, t2]⟩
    · obtain ⟨w, hw⟩ := g lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
    · obtain ⟨w, hw⟩ := g lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
    · obtain ⟨w, hw⟩ := g lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
    · obtain ⟨w, hw⟩ := g lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
    · obtain ⟨w, hw⟩ := g lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩


end

section
variable {σ : Type}

def zeroScratch : List MlS := [lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

theorem lInternZero_spec (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 0 3)
    (hb0 : L.base 3 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.zero.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 3 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.zero.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfll : t.locals.lookup lFll = some (.val (.word FLl)))
    (hw : ∀ y, y ∈ zeroScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    XRes t L FLn FLl FLs FLe KB 0 (withL st (st.lss.ls.intern .zero).1) (st.lss.ls.intern .zero).2
      (evaluateHOLFiniteState t (lZeroWith (rRest 3 0 lFll))) := by
  have W : ∀ y, y ∈ zeroScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  let dd := st.lss.ls.derOfView .zero
  have hdd : dd = ⟨1, false⟩ := rfl
  unfold lZeroWith
  obtain ⟨w1, hw1⟩ := W lDv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lDv (.const 1) (dWL dd).1 w1 (eval_const t 1) hw1)]
  let t1 := setVarHOLFinite lDv (.val (.word (dWL dd).1)) t
  obtain ⟨w2, hw2⟩ := W lDv2 (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lDv2 (.const 0) (dWL dd).2 w2 (eval_const t1 0) (by lk [t1]; exact hw2))]
  let t2 := setVarHOLFinite lDv2 (.val (.word (dWL dd).2)) t1
  obtain ⟨w3, hw3⟩ := W lSk (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lSk (.const 0) (if false then 1 else 0) w3 (eval_const t2 0)
    (by lk [t2, t1]; exact hw3))]
  let t3 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) t2
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have hint := lstore_zero st.lss.ls
  simp only at hint
  have R := rRest_spec t t3 L FLn FLl FLs FLe KB FLl 0 3 lFll (by decide) st.lss.ls.scratchOn Enc.encZero dWL Enc.idxW
    Enc.encZero_inj (mkN LTag.zero 0) (mkN LTag.zero 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN LTag.zero 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN LTag.zero 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.pers.zeros st.lss.ls.scr.zeros false ZeroNode.mk dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withL st (st.lss.ls.intern .zero).1))
    (fun v' hP hS' hf hd' hag => by
      rw [hint]
      exact srep_withL hR3 3 _ rfl (lrep_zeros hR3.l _ _ hP hS' (hf _ (Or.inr (Or.inl rfl))) hd'
        (fun k tier h1 h2 h3 => hag k tier h1 h2 h3)) hf hd' hag (by decide) (by decide))
    hS (by decide) rfl (by decide) (Or.inr (Or.inl rfl)) hR3.l.fl hR3.l.pz hR3.l.sz (fun k hk => absurd hk (by simp [Enc.encZero]))
    (by lk [t3, t2, t1]) (by lk [t3, t2]) (by lk [t3]) (by lk [t3, t2, t1]; exact lfll) (by lk [t3, t2, t1]; exact ldir)
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
  have n0 : ¬ inR (L.geo 3 0) c := fun hc => h1 ⟨3, 0, by decide, by decide, hc⟩
  have n1 : ¬ inR (L.geo 3 1) c := fun hc => h1 ⟨3, 1, by decide, by decide, hc⟩
  exact fr3 c n0 n1

end

end ConPanqueque.V
