import ConPanqueque.V.LParam
import ConPanqueque.V.ListDer
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning a level list

The key is the list's handle words, already in memory: the key pointer is
the list itself (no copy) and its length is a local. The derived record is
`lsDer`'s fold through the level store. No scratch skip; the remainder takes
the key length from the local (`rRestE`).
-/

namespace ConPanqueque.V

def lEc := ofString "ec"

def lsInternWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lLa (vv lKb))
  (.seq (.assign .local lLn (vv lEc))
  (.seq (.assign .local lFl (vv lFll))
  (.seq lsDer
  (.seq (.assign .local lDv (vv lLr))
  (.seq (.assign .local lDv2 (vv lLp))
  (.seq (.assign .local lSk (.const 0)) rest))))))

def lsScratch : List MlS := [lLa, lLn, lLr, lLp, lDh, lDt, lDg, lDi, lDo1, lDo2, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

/-- The four stores with the level-list store replaced. -/
def withLs (st : EStore) (lss : LsStore) : EStore := { st with lss := lss }

section
variable {σ : Type}

theorem srep_withLs {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FLn FLl FLs FLe : BitVec 64} {st : EStore}
    (h : SRep t L FLn FLl FLs FLe st) (lss' : LsStore) (hls : lss'.ls = st.lss.ls)
    (hpl : TabAt u L 8 0 Enc.encList dWL lss'.pers.lists (mkN LsTag.list 0))
    (hsl : TabAt u L 8 1 Enc.encList dWL lss'.scr.lists (mkN LsTag.list 1))
    (hon : lss'.scratchOn = st.lss.scratchOn)
    (hfl : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → u.memory F = t.memory F) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k' tier, k' < 19 → tier < 2 → k' ≠ 8 → Agree L FLe t u k' tier) :
    SRep u L FLn FLl FLs FLe (withLs st lss') := by
  have A : ∀ k' tier, k' < 19 → tier < 2 → k' ≠ 8 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k' tier enc dW tb mkI → TabAt u L k' tier enc dW tb mkI :=
    fun k' tier h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT => tabAt_frame hT (hag k' tier h2 h3 h4).1 (hag k' tier h2 h3 h4).2 hd
  have he : ERep t L FLe (withLs st lss') :=
    ⟨h.e.fl, h.e.p0, h.e.p1, h.e.p2, h.e.p3, h.e.p4, h.e.p5, h.e.p6, h.e.p7, h.e.p8, h.e.p9,
      h.e.s0, h.e.s1, h.e.s2, h.e.s3, h.e.s4, h.e.s5, h.e.s6, h.e.s7, h.e.s8, h.e.s9⟩
  refine ⟨erep_frame he (hfl _ (Or.inr (Or.inr (Or.inr rfl)))) hd (fun k' tier h1 h2 h3 => hag k' tier h2 h3 (by omega)),
    ⟨⟨by rw [hd]; exact h.ls.fl.1, by
      rw [hfl _ (Or.inr (Or.inr (Or.inl rfl))), show (withLs st lss').lss.scratchOn = _ from hon]; exact h.ls.fl.2⟩,
      hpl, hsl⟩, ?_, ?_⟩
  · show LRep u L FLl lss'.ls
    rw [hls]
    exact ⟨⟨by rw [hd]; exact h.l.fl.1, by rw [hfl _ (Or.inr (Or.inl rfl))]; exact h.l.fl.2⟩,
      A 3 0 (by decide) (by decide) (by decide) h.l.pz, A 4 0 (by decide) (by decide) (by decide) h.l.ps,
      A 5 0 (by decide) (by decide) (by decide) h.l.pm, A 6 0 (by decide) (by decide) (by decide) h.l.pi,
      A 7 0 (by decide) (by decide) (by decide) h.l.pp, A 3 1 (by decide) (by decide) (by decide) h.l.sz,
      A 4 1 (by decide) (by decide) (by decide) h.l.ss, A 5 1 (by decide) (by decide) (by decide) h.l.sm,
      A 6 1 (by decide) (by decide) (by decide) h.l.si, A 7 1 (by decide) (by decide) (by decide) h.l.sp⟩
  · show NRep u L FLn lss'.ls.ns
    rw [hls]
    exact ⟨⟨by rw [hd]; exact h.n.fl.1, by rw [hfl _ (Or.inl rfl)]; exact h.n.fl.2⟩,
      A 0 0 (by decide) (by decide) (by decide) h.n.pa, A 1 0 (by decide) (by decide) (by decide) h.n.ps,
      A 2 0 (by decide) (by decide) (by decide) h.n.pn, A 0 1 (by decide) (by decide) (by decide) h.n.sa,
      A 1 1 (by decide) (by decide) (by decide) h.n.ss, A 2 1 (by decide) (by decide) (by decide) h.n.sn⟩

end

section
variable {σ : Type}

theorem lsIntern_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (us : List LIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB us.length 8)
    (hW : Words t KB (us.map Enc.idxW)) (hL : us.length < 2 ^ 60)
    (hb0 : L.base 8 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LsTag.list.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 8 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LsTag.list.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (lec : t.locals.lookup lEc = some (.val (.word (BitVec.ofNat 64 us.length))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfll : t.locals.lookup lFll = some (.val (.word FLl))) (lfls : t.locals.lookup lFls = some (.val (.word FLs)))
    (hw : ∀ y, y ∈ lsScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    XRes t L FLn FLl FLs FLe KB us.length (withLs st (st.lss.intern us).1) (st.lss.intern us).2
      (evaluateHOLFiniteState t (lsInternWith (rRestE 8 (vv lEc) lFls))) := by
  have W : ∀ y, y ∈ lsScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  unfold lsInternWith
  obtain ⟨wa, hwa⟩ := W lLa (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lLa _ KB wa (eval_vv t lKb _ lkb) hwa)]
  let t1 := setVarHOLFinite lLa (.val (.word KB)) t
  obtain ⟨wn, hwn⟩ := W lLn (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lLn _ _ wn (eval_vv t1 lEc _ (by lk [t1]; exact lec)) (by lk [t1]; exact hwn))]
  let t2 := setVarHOLFinite lLn (.val (.word (BitVec.ofNat 64 us.length))) t1
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lFl _ FLl wf (eval_vv t2 lFll _ (by lk [t2, t1]; exact lfll))
    (by lk [t2, t1]; exact hwf))]
  let t3 := setVarHOLFinite lFl (.val (.word FLl)) t2
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have D := lsDer_spec t3 L FLl KB st.lss.ls us hR3.l hW hL (by lk [t3, t2, t1]) (by lk [t3, t2, t1]; exact ldir) (by lk [t3])
    (by lk [t3, t2]) (by obtain ⟨w, hw⟩ := W lLr (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩)
    (by obtain ⟨w, hw⟩ := W lLp (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩)
    (fun y hy => by
      obtain ⟨w, hw⟩ := W y (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨w, by lk [t3, t2, t1]; exact hw⟩)
  rcases D with hs | ⟨hn4, hI4, hr4, hp4⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  generalize hq : evaluateHOLFiniteState t3 lsDer = q at hn4 hI4 hr4 hp4
  obtain ⟨q1, u4⟩ := q
  simp only at hn4 hI4 hr4 hp4; subst hn4
  rw [seq_normal _ hq]
  obtain ⟨m4, d4, c4, g4, ta4, fr4, wd4, _⟩ := hI4
  let dd := st.lss.derOfView us
  have hdd := lsModel_eq ra st.lss us
  have hh : dd.hash = (lsModel st.lss.ls us).1 := by show (st.lss.derOfView us).hash = _; rw [hdd]
  have hp : dd.hasParam = (lsModel st.lss.ls us).2 := by show (st.lss.derOfView us).hasParam = _; rw [hdd]
  have back : ∀ y, y ≠ lLn → y ≠ lLr → y ≠ lLp → y ≠ lDh → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDo1 → y ≠ lDo2 →
      y ≠ lLa → y ≠ lFl → u4.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; rw [fr4 y a1 a2 a3 a4 a5 a6 a7 a8 a9]; lk [t3, t2, t1]
  have g : ∀ y, y ≠ lLn → y ≠ lLr → y ≠ lLp → y ≠ lDh → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDo1 → y ≠ lDo2 →
      y ≠ lLa → y ≠ lFl → y ≠ lDv → y ≠ lDv2 → y ≠ lSk → y ∈ lsScratch → ∃ w, u4.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 _ _ _ hy
    obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11]; exact hw⟩
  obtain ⟨wv1, hwv1⟩ := W lDv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lDv _ (dWL dd).1 wv1 (eval_vv u4 lLr _ (by rw [hr4]; show _ = some (ValueHOL.val (HolWordLab.word dd.hash.toBitVec)); rw [hh]))
    (by rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hwv1))]
  let u5 := setVarHOLFinite lDv (.val (.word (dWL dd).1)) u4
  obtain ⟨wv2, hwv2⟩ := W lDv2 (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDv2 _ (dWL dd).2 wv2 (eval_vv u5 lLp _ (by
      lk [u5]; rw [hp4]
      show _ = some (ValueHOL.val (HolWordLab.word (if dd.hasParam then (1 : BitVec 64) else 0))); rw [hp]; rfl))
    (by lk [u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hwv2))]
  let u6 := setVarHOLFinite lDv2 (.val (.word (dWL dd).2)) u5
  obtain ⟨wsk, hwsk⟩ := W lSk (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lSk (.const 0) (if false then 1 else 0) wsk (eval_const u6 0)
    (by lk [u6, u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hwsk))]
  let u7 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) u6
  have mem7 : u7.memory = t.memory := m4
  have md7 : u7.memaddrs = t.memaddrs := d4
  have hR7 : SRep u7 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [mem7], by rw [mem7], by rw [mem7], by rw [mem7]⟩ md7
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem7], fun _ _ => by rw [mem7]⟩)
  have hint := lsstore_list st.lss us
  simp only at hint
  have hWk : Words u7 KB (Enc.encList ⟨us⟩) := fun k hk => by rw [md7, mem7]; exact hW k hk
  have R := rRestE_spec t u7 L FLn FLl FLs FLe KB FLs us.length 8 lFls (vv lEc) (by decide) st.lss.scratchOn Enc.encList dWL
    Enc.idxW Enc.encList_inj (mkN LsTag.list 0) (mkN LsTag.list 1) (2 ^ 26)
    (fun i hi => by rw [hb0]; exact idxW_mkN LsTag.list 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN LsTag.list 1 (by decide) (by decide) i hi) hS.cap
    st.lss.pers.lists st.lss.scr.lists false ⟨us⟩ dd
    (fun v' => SRep v' L FLn FLl FLs FLe (withLs st (st.lss.intern us).1))
    (fun v' hP hS' hf hd' hag => by
      rw [hint]
      exact srep_withLs hR7 _ rfl hP hS' rfl hf hd' hag)
    hS (by decide) (by simp [Enc.encList]) (by omega) (Or.inr (Or.inr (Or.inl rfl))) hR7.ls.fl hR7.ls.pl hR7.ls.sl hWk
    (by lk [u7, u6, u5]) (by lk [u7, u6]) (lookup_setVar_same _ _ _)
    (by lk [u7, u6, u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lfls)
    (by lk [u7, u6, u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by lk [u7, u6, u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact lkb)
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨FLl, by lk [u7, u6, u5]; rw [fr4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]; lk [t3]⟩
      · obtain ⟨w, hw⟩ := g lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, by lk [u7, u6, u5]; exact hw⟩
      · obtain ⟨w, hw⟩ := g lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, by lk [u7, u6, u5]; exact hw⟩
      · obtain ⟨w, hw⟩ := g lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, by lk [u7, u6, u5]; exact hw⟩
      · obtain ⟨w, hw⟩ := g lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, by lk [u7, u6, u5]; exact hw⟩
      · obtain ⟨w, hw⟩ := g lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact ⟨w, by lk [u7, u6, u5]; exact hw⟩)
    (fun x hx => by
      have : x.locals.lookup lEc = some (.val (.word (BitVec.ofNat 64 us.length))) := by
        rw [hx _ (by decide)]; lk [u7, u6, u5]
        rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact lec
      exact eval_vv x lEc _ this)
  rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  refine Or.inr ⟨by rw [hr, hint], hQ, c3.trans (by show u4.code = _; rw [c4]; rfl), g3.trans (by show u4.globals = _; rw [g4]; rfl),
    d3.trans md7, ta3.trans (by show u4.topAddr = _; rw [ta4]; rfl), fun c h1 _ => ?_⟩
  have n0 : ¬ inR (L.geo 8 0) c := fun hc => h1 ⟨8, 0, by decide, by decide, hc⟩
  have n1 : ¬ inR (L.geo 8 1) c := fun hc => h1 ⟨8, 1, by decide, by decide, hc⟩
  rw [fr3 c n0 n1, mem7]

end

end ConPanqueque.V
