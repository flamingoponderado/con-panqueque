import ConPanqueque.V.RGen
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning `succ u` into the level store

The key `[u]`, the child's derived record through the level store, the new
record (`succHashE`, the child's parameter bit), no scratch skip, then the
shared remainder at kind 4. The level store sits under the expression store:
the result is the four stores with the level store updated.
-/

namespace ConPanqueque.V

def lHv := ofString "h"

def lSuccWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEu))
  (.seq (.assign .local lFl (vv lFll))
  (.seq (.assign .local lDh (vv lEu))
  (.seq (storeDerivedC 3 5 badL)
  (.seq (.assign .local lHv (vv lDo1))
  (.seq (.assign .local lDv Der.succHashE)
  (.seq (.assign .local lDv2 (vv lDo2))
  (.seq (.assign .local lSk (.const 0)) rest)))))))

def succScratch : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lHv, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

/-- The four stores with the level store replaced. -/
def withL (st : EStore) (ls : LStore) : EStore := { st with lss := { st.lss with ls := ls } }

section
variable {σ : Type}

theorem lrep_succs {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {ls : LStore}
    (h : LRep t L FL ls) (P' Sc' : Tbl SuccNode LIdx LDer)
    (hP : TabAt u L 4 0 Enc.encSucc dWL P' (mkN LTag.succ 0)) (hS : TabAt u L 4 1 Enc.encSucc dWL Sc' (mkN LTag.succ 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, k < 19 → tier < 2 → k ≠ 4 → Agree L FL t u k tier) :
    LRep u L FL { ls with pers := { ls.pers with succs := P' }, scr := { ls.scr with succs := Sc' } } := by
  have A : ∀ k tier, k < 19 → tier < 2 → k ≠ 4 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k tier h2 h3 h4).1 (hag k tier h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 3 0 (by decide) (by decide) (by decide) h.pz, hP, A 5 0 (by decide) (by decide) (by decide) h.pm,
    A 6 0 (by decide) (by decide) (by decide) h.pi, A 7 0 (by decide) (by decide) (by decide) h.pp,
    A 3 1 (by decide) (by decide) (by decide) h.sz, hS, A 5 1 (by decide) (by decide) (by decide) h.sm,
    A 6 1 (by decide) (by decide) (by decide) h.si, A 7 1 (by decide) (by decide) (by decide) h.sp⟩

theorem erep_withL {t : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore} (ls' : LStore)
    (h : ERep t L FL st) : ERep t L FL (withL st ls') := ⟨h.fl, h.p0, h.p1, h.p2, h.p3, h.p4, h.p5, h.p6, h.p7, h.p8, h.p9, h.s0, h.s1, h.s2, h.s3, h.s4, h.s5, h.s6, h.s7, h.s8, h.s9⟩

/-- The four stores after a change confined to one level kind `k` (3–7). -/
theorem srep_withL {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FLn FLl FLs FLe : BitVec 64} {st : EStore}
    (h : SRep t L FLn FLl FLs FLe st) (k : Nat) (ls' : LStore) (hns : ls'.ns = st.lss.ls.ns)
    (hl : LRep u L FLl ls')
    (hfl : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → u.memory F = t.memory F) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k' tier, k' < 19 → tier < 2 → k' ≠ k → Agree L FLe t u k' tier) (hk : 3 ≤ k) (hk8 : k < 8) :
    SRep u L FLn FLl FLs FLe (withL st ls') := by
  have A : ∀ k' tier, k' < 19 → tier < 2 → k' ≠ k → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k' tier enc dW tb mkI → TabAt u L k' tier enc dW tb mkI :=
    fun k' tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k' tier h2 h3 h4).1 (hag k' tier h2 h3 h4).2 hd
  refine ⟨erep_frame (erep_withL ls' h.e) (hfl _ (Or.inr (Or.inr (Or.inr rfl)))) hd (fun k' tier h1 h2 h3 => hag k' tier h2 h3 (by omega)),
    ⟨⟨by rw [hd]; exact h.ls.fl.1, by rw [hfl _ (Or.inr (Or.inr (Or.inl rfl)))]; exact h.ls.fl.2⟩,
      A 8 0 (by decide) (by decide) (by omega) h.ls.pl, A 8 1 (by decide) (by decide) (by omega) h.ls.sl⟩, hl, ?_⟩
  show NRep u L FLn ls'.ns
  rw [hns]
  exact ⟨⟨by rw [hd]; exact h.n.fl.1, by rw [hfl _ (Or.inl rfl)]; exact h.n.fl.2⟩,
    A 0 0 (by decide) (by decide) (by omega) h.n.pa, A 1 0 (by decide) (by decide) (by omega) h.n.ps,
    A 2 0 (by decide) (by decide) (by omega) h.n.pn, A 0 1 (by decide) (by decide) (by omega) h.n.sa,
    A 1 1 (by decide) (by decide) (by omega) h.n.ss, A 2 1 (by decide) (by decide) (by omega) h.n.sn⟩

end

section
variable {σ : Type}

/-- What an intern into any store guarantees: the handle, the four stores' new state. -/
def XRes {k : IdxKind} (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (w : Nat)
    (st' : EStore) (h : Idx k) (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨ (r.1 = some (.returned (.val (.word (Enc.idxW h)))) ∧
    SRep r.2 L FLn FLl FLs FLe st' ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
    ∀ c, ¬ inAny L c → (∀ j, j < w → c ≠ KB + BitVec.ofNat 64 (8 * j)) → r.2.memory c = t.memory c)

theorem lInternSucc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (u : LIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 1 4)
    (hkbd : t.memaddrs KB)
    (hb0 : L.base 4 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.succ.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 4 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.succ.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (leu : t.locals.lookup lEu = some (.val (.word (Enc.idxW u))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfll : t.locals.lookup lFll = some (.val (.word FLl)))
    (hw : ∀ y, y ∈ succScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    (XRes t L FLn FLl FLs FLe KB 1 (withL st (st.lss.ls.intern (.succ u)).1) (st.lss.ls.intern (.succ u)).2
      (evaluateHOLFiniteState t (lSuccWith (rRest 4 1 lFll)))) ∧
      (Stop (evaluateHOLFiniteState t (lSuccWith (rRest 4 1 lFll))).1 ∨ ((st.lss.ls.view u).isSome = true)) := by
  have KB0 : KB + BitVec.ofNat 64 (8 * 0) = KB := by simp
  have flne : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → F ≠ KB := fun F hF => by
    have := (hS.fls F hF).2.2 0 (by decide); rwa [KB0] at this
  have dscne : ∀ k tier m, k < 19 → tier < 2 → m < 8 → descAddr L k tier + BitVec.ofNat 64 (8 * m) ≠ KB :=
    fun k tier m h1 h2 h3 => by have := (hS.dsc k tier m h1 h2 h3).2.2 0 (by decide); rwa [KB0] at this
  have kbo : ∀ k tier, k < 19 → tier < 2 → ¬ inR (L.geo k tier) KB := fun k tier h1 h2 => by
    have := hS.kbo 0 k tier (by decide) h1 h2; rwa [KB0] at this
  unfold lSuccWith
  rw [seq_normal _ (store_word t (vv lKb) (vv lEu) KB (Enc.idxW u) (eval_vv t lKb _ lkb) (eval_vv t lEu _ leu) hkbd)]
  let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = KB then .word (Enc.idxW u) else t.memory c }
  have m1 : ∀ c, c ≠ KB → t1.memory c = t.memory c := fun c h => by show (if c = KB then _ else _) = _; rw [if_neg h]
  have hR1 : SRep t1 L FLn FLl FLs FLe st := srep_frame hR
    ⟨m1 _ (flne _ (Or.inl rfl)), m1 _ (flne _ (Or.inr (Or.inl rfl))), m1 _ (flne _ (Or.inr (Or.inr (Or.inl rfl)))),
      m1 _ (flne _ (Or.inr (Or.inr (Or.inr rfl))))⟩ rfl
    (fun k tier h1 h2 => ⟨fun m hm => m1 _ (dscne k tier m h1 h2 hm), fun c hc => m1 c (fun e => kbo k tier h1 h2 (e ▸ hc))⟩)
  have W : ∀ y, y ∈ succScratch → ∃ w, t1.locals.lookup y = some (.val (.word w)) := hw
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lFl _ FLl wf (eval_vv t1 lFll _ lfll) hwf)]
  let t2 := setVarHOLFinite lFl (.val (.word FLl)) t1
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lDh _ (Enc.idxW u) wh (eval_vv t2 lEu _ (by lk [t2]; exact leu))
    (by lk [t2]; exact hwh))]
  let t3 := setVarHOLFinite lDh (.val (.word (Enc.idxW u))) t2
  have W3 : ∀ y, y ∈ succScratch → y ≠ lFl → y ≠ lDh → ∃ w, t3.locals.lookup y = some (.val (.word w)) := by
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
  have wv : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ∈ succScratch →
      ∃ w, u4.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  let ld := st.lss.ls.derived u
  obtain ⟨whv, hwhv⟩ := wv lHv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lHv _ _ whv (eval_vv u4 lDo1 _ o1) hwhv)]
  let u5 := setVarHOLFinite lHv (.val (.word (dWL ld).1)) u4
  let dd := st.lss.ls.derOfView (.succ u)
  have hdd : dd = ⟨Der.succHashW ld.hash, ld.hasParam⟩ := Der.lsucc_eq ra st.lss.ls u
  obtain ⟨wv1, hwv1⟩ := wv lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDv _ (dWL dd).1 wv1
    (by rw [hdd]; exact Der.succHashE.eval u5 _ (by show u5.locals.lookup lHv = _; lk [u5]; rfl)) (by lk [u5]; exact hwv1))]
  let u6 := setVarHOLFinite lDv (.val (.word (dWL dd).1)) u5
  obtain ⟨wv2, hwv2⟩ := wv lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lDv2 _ (dWL dd).2 wv2
    (eval_vv u6 lDo2 _ (by
      have hp : dd.hasParam = ld.hasParam := by rw [hdd]
      lk [u6, u5]; rw [o2]
      show some (ValueHOL.val (HolWordLab.word (if ld.hasParam then (1 : BitVec 64) else 0))) = some (ValueHOL.val (HolWordLab.word (if dd.hasParam then 1 else 0)))
      rw [hp])) (by lk [u6, u5]; exact hwv2))]
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
  have g : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHv → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → y ∈ succScratch → ∃ w, u8.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 hy
    obtain ⟨w, hw⟩ := wv y a1 a2 a3 a4 a5 a6 a7 hy; exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
  have b8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHv → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → u8.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; lk [u8, u7, u6, u5]; exact back y a1 a2 a3 a4 a5 a6 a7
  have hint := lstore_succ st.lss.ls u
  simp only at hint
  have R := rRest_spec t u8 L FLn FLl FLs FLe KB FLl 1 4 lFll (by decide) st.lss.ls.scratchOn Enc.encSucc dWL Enc.idxW
    Enc.encSucc_inj (mkN LTag.succ 0) (mkN LTag.succ 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN LTag.succ 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN LTag.succ 1 (by decide) (by decide) i hi) hS.cap
    st.lss.ls.pers.succs st.lss.ls.scr.succs false ⟨u⟩ dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withL st (st.lss.ls.intern (.succ u)).1))
    (fun v' hP hS' hf hd' hag => by
      rw [hint]
      exact srep_withL hR8 4 _ rfl (lrep_succs hR8.l _ _ hP hS' (hf _ (Or.inr (Or.inl rfl))) hd'
        (fun k tier h1 h2 h3 => hag k tier h1 h2 h3)) hf hd' hag (by decide) (by decide))
    hS (by decide) (by simp [Enc.encSucc]) (by decide) (Or.inr (Or.inl rfl)) hR8.l.fl hR8.l.ps hR8.l.ss ?_
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
    have n0 : ¬ inR (L.geo 4 0) c := fun hc => h1 ⟨4, 0, by decide, by decide, hc⟩
    have n1 : ¬ inR (L.geo 4 1) c := fun hc => h1 ⟨4, 1, by decide, by decide, hc⟩
    have h0 := h2 0 (by decide); rw [KB0] at h0
    rw [fr3 c n0 n1, mem8]; exact m1 c h0
  · intro j hj
    have hj1 : j < 1 := by simpa [Enc.encSucc] using hj
    rcases (by omega : j = 0) with rfl
    refine ⟨by rw [md8, KB0]; exact hkbd, ?_⟩
    rw [mem8, KB0]; show (if KB = KB then _ else _) = _; simp [Enc.encSucc]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨FLl, by lk [u8, u7, u6, u5]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3, t2]⟩
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

end ConPanqueque.V
