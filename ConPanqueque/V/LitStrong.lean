import ConPanqueque.V.EVar
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena
open ConPanqueque.Hash (leanStringHash leanNatHash natWords)

/-!
# Literal intern with the strong frame

The same programs as `eInternLitNat_spec`, with a frame that keeps every cell outside the stores — the key's
cells too. A literal interned straight from a value-heap block needs it: the key is that block.
-/

namespace ConPanqueque.V

def ERes2 {σ : Type} (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (w : Nat)
    (st : EStore) (res : EStore × EIdx) (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨ (r.1 = some (.returned (.val (.word (Enc.idxW res.2)))) ∧
    SRep r.2 L FLn FLl FLs FLe res.1 ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
    ∀ c, ¬ inAny L c → r.2.memory c = t.memory c)

section
variable {σ : Type} {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

theorem eRestE_spec2 (t u : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (w k : Nat)
    (lenE : ExpHOL 64) (st : EStore) (enc : α → List (BitVec 64)) (hinj : ∀ x y, enc x = enc y → x = y)
    (mkP mkS : Nat → EIdx) (icap : Nat)
    (hmkP : ∀ i, i < icap → Enc.idxW (mkP i) = L.base k 0 + BitVec.ofNat 64 i)
    (hmkS : ∀ i, i < icap → Enc.idxW (mkS i) = L.base k 1 + BitVec.ofNat 64 i)
    (hicap : ∀ tier, tier < 2 → (L.geo k tier).cap ≤ icap)
    (P Sc : Tbl α EIdx UInt64) (sk : Bool) (x : α) (d : UInt64) (res : EStore × EIdx)
    (setK : Tbl α EIdx UInt64 → Tbl α EIdx UInt64 → EStore)
    (hres : res = (setK (twoTier P Sc st.scratchOn sk x d mkP mkS).1 (twoTier P Sc st.scratchOn sk x d mkP mkS).2.1,
      (twoTier P Sc st.scratchOn sk x d mkP mkS).2.2))
    (hlss : ∀ P' S', (setK P' S').lss = st.lss)
    (hset : ∀ (v v' : PanSemStateFiniteExact 64 σ) P' S', ERep v L FLe st → TabAt v' L k 0 enc dWN P' mkP →
      TabAt v' L k 1 enc dWN S' mkS → v'.memory FLe = v.memory FLe → v'.memaddrs = v.memaddrs →
      (∀ k' tier, 9 ≤ k' → k' < 19 → tier < 2 → k' ≠ k → Agree L FLe v v' k' tier) → ERep v' L FLe (setK P' S'))
    (hS : SepK L FLn FLl FLs FLe KB w k) (hk : 9 ≤ k) (hk19 : k < 19) (hwl : (enc x).length = w) (hw : w < 2 ^ 61)
    (hR : SRep u L FLn FLl FLs FLe st)
    (hPa : TabAt u L k 0 enc dWN P mkP) (hSa : TabAt u L k 1 enc dWN Sc mkS)
    (hK : Words u KB (enc x))
    (hm : ∀ c, u.memory c = t.memory c)
    (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code) (hg : u.globals = t.globals) (hta : u.topAddr = t.topAddr)
    (ldv : u.locals.lookup lDv = some (.val (.word (dWN d).1)))
    (ldv2 : u.locals.lookup lDv2 = some (.val (.word (dWN d).2)))
    (lsk : u.locals.lookup lSk = some (.val (.word (if sk then 1 else 0))))
    (lfle : u.locals.lookup lFle = some (.val (.word FLe)))
    (ldir : u.locals.lookup lDir = some (.val (.word L.DIR))) (lkb : u.locals.lookup lKb = some (.val (.word KB)))
    (hw5 : ∀ y, y ∈ [lFl, lOn, lPg, lSg, lK, lL] → ∃ w, u.locals.lookup y = some (.val (.word w)))
    (hlen : ∀ x : PanSemStateFiniteExact 64 σ, (∀ y, y ∉ [lFl, lOn, lPg, lSg, lK] → x.locals.lookup y = u.locals.lookup y) →
      @evalHOLExact 64 σ _ x.toExact (fun c => Classical.propDecidable (x.memaddrs c)) lenE =
        some (.val (.word (BitVec.ofNat 64 w)))) :
    ERes2 t L FLn FLl FLs FLe KB w st res (evaluateHOLFiniteState u (rRestE k lenE lFle)) := by
  have R := rRestE_spec t u L FLn FLl FLs FLe KB FLe w k lFle lenE (by decide) st.scratchOn enc dWN Enc.idxW hinj
    mkP mkS icap hmkP hmkS hicap P Sc sk x d (fun v' => SRep v' L FLn FLl FLs FLe res.1)
    (fun v' hP hS' hf hd' hag => by
      rw [hres]
      exact low_frame hR ⟨hf _ (Or.inl rfl), hf _ (Or.inr (Or.inl rfl)), hf _ (Or.inr (Or.inr (Or.inl rfl)))⟩ hd'
        (fun k' tier h1 h2 => hag k' tier (by omega) h2 (by omega)) _ (hlss _ _)
        (hset u v' _ _ hR.e hP hS' (hf _ (Or.inr (Or.inr (Or.inr rfl)))) hd'
          (fun k' tier _ h2 h3 h4 => hag k' tier h2 h3 h4)))
    hS hk19 hwl hw (Or.inr (Or.inr (Or.inr rfl))) hR.e.fl hPa hSa hK ldv ldv2 lsk lfle ldir lkb hw5 hlen
  rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  refine Or.inr ⟨by rw [hr, hres], hQ, c3.trans hc, g3.trans hg, d3.trans hd, ta3.trans hta, fun c h1 => ?_⟩
  have n0 : ¬ inR (L.geo k 0) c := fun hc => h1 ⟨k, 0, hk19, by decide, hc⟩
  have n1 : ¬ inR (L.geo k 1) c := fun hc => h1 ⟨k, 1, hk19, by decide, hc⟩
  rw [fr3 c n0 n1]; exact hm c

end

/-- Moving an `ERes` back over a prefix that changed only locals. -/
theorem eres2_back {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FLn FLl FLs FLe KB : BitVec 64} {w : Nat}
    {st : EStore} {res : EStore × EIdx} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : ERes2 u L FLn FLl FLs FLe KB w st res r) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs)
    (hc : u.code = t.code) (hg : u.globals = t.globals) (ht : u.topAddr = t.topAddr) :
    ERes2 t L FLn FLl FLs FLe KB w st res r := by
  rcases h with hs | ⟨a, b, c, d, e, f, g⟩
  · exact Or.inl hs
  exact Or.inr ⟨a, b, c.trans hc, d.trans hg, e.trans hd, f.trans ht, fun c h1 => by rw [g c h1, hm]⟩

section
variable {σ : Type}

theorem eLitTail_spec2 (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (l : ConLeche.Literal)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encLit ⟨l⟩).length 17)
    (hK : Words t KB (Enc.encLit ⟨l⟩)) (hwl : (Enc.encLit ⟨l⟩).length < 2 ^ 61)
    (hb0 : L.base 17 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 17 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encLit ⟨l⟩).length))))
    (lhv : t.locals.lookup lHv = some (.val (.word (ConLeche.Literal.hash l).toBitVec)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ bvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes2 t L FLn FLl FLs FLe KB (Enc.encLit ⟨l⟩).length st (st.intern (.lit l))
      (evaluateHOLFiniteState t (eLitTail (rRestE 17 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ bvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  let dd := st.derOfView (.lit l)
  have hdd : dd = Der.litDataW (ConLeche.Literal.hash l) := Der.derOfLit_eq ra st l
  unfold eLitTail
  obtain ⟨w1, hw1⟩ := W lDv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lDv _ (dWN dd).1 w1
    (by rw [hdd]; exact Der.litDataE.eval t _ lhv) hw1)]
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
  have hint := estore_lit st l
  simp only at hint
  exact eRestE_spec2 t t3 L FLn FLl FLs FLe KB _ 17 (vv lEn) st Enc.encLit Enc.encLit_inj (mkN ETag.lit 0)
    (mkN ETag.lit 1) (2 ^ 26) (fun i hi => by rw [hb0]; exact idxW_mkN ETag.lit 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.lit 1 (by decide) (by decide) i hi) hS.cap
    st.pers.lits st.scr.lits false ⟨l⟩ dd _
    (fun P' S' => { st with pers := { st.pers with lits := P' }, scr := { st.scr with lits := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_lits h1 P' S' h2 h3 h4 h5 h6)
    hS (by decide) (by decide) rfl hwl hR3 hR3.e.p8 hR3.e.s8 hK (fun _ => rfl) rfl rfl rfl rfl
    (by lk [t3, t2, t1]) (by lk [t3, t2]) (by lk [t3]) (by lk [t3, t2, t1]; exact lfle) (by lk [t3, t2, t1]; exact ldir)
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
    (fun x hx => eval_vv x lEn _ (by rw [hx _ (by decide)]; lk [t3, t2, t1]; exact len))


theorem eInternLitNat_spec2 (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (n : Nat)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encLit ⟨.natVal n⟩).length 17)
    (hK : Words t KB (Enc.encLit ⟨.natVal n⟩)) (hwl : (Enc.encLit ⟨.natVal n⟩).length < 2 ^ 60)
    (hb0 : L.base 17 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 17 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encLit ⟨.natVal n⟩).length))))
    (lna : t.locals.lookup lNa = some (.val (.word (KB + 8))))
    (lnn : t.locals.lookup lNn = some (.val (.word (BitVec.ofNat 64 (Enc.limbs n).length))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ litNatScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes2 t L FLn FLl FLs FLe KB (Enc.encLit ⟨.natVal n⟩).length st (st.intern (.lit (.natVal n)))
      (evaluateHOLFiniteState t (eLitNatWith (rRestE 17 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ litNatScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  have hlw : (natWords n).map UInt64.toBitVec = Enc.limbs n := natWords_limbs n
  have hln : (natWords n).length = (Enc.limbs n).length := by rw [← hlw, List.length_map]
  have hkl : (Enc.encLit ⟨.natVal n⟩).length = (Enc.limbs n).length + 1 := by simp [Enc.encLit]
  have hK' : Words t KB (0 :: (natWords n).map UInt64.toBitVec) := by rw [hlw]; exact hK
  unfold eLitNatWith
  have H := natHashP_spec t (KB + 8) (natWords n) (by omega) (words_tail hK') lna (by rw [hln]; exact lnn)
    (W lNh (by decide)) (W lNi (by decide))
  rcases H with hs | ⟨hn, ym, yd, yc, yg, yt, yfr, yh⟩
  · have ⟨res, hres⟩ : ∃ res, (evaluateHOLFiniteState t natHashP).1 = some res := by
      rcases hs with h | ⟨ev, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    rw [seq_abort _ _ _ _ hres]; exact Or.inl hs
  generalize hy : evaluateHOLFiniteState t natHashP = q at hn ym yd yc yg yt yfr yh
  obtain ⟨qr, y⟩ := q
  simp only at hn ym yd yc yg yt yfr yh; subst hn
  rw [seq_normal _ hy]
  obtain ⟨wh, hwh⟩ := W lHv (by decide)
  have hh : (foldW (natWords n)) = ConLeche.Literal.hash (.natVal n) := by
    show _ = ConLeche.natHash n; rw [natHash_eq ra, leanNatHash_foldW]
  rw [seq_normal _ (ConsLoop.assign_local y lHv _ _ wh (eval_vv y lNh _ yh)
    (by rw [yfr _ (by decide) (by decide)]; exact hwh))]
  let y1 := setVarHOLFinite lHv (.val (.word (foldW (natWords n)).toBitVec)) y
  have yb : ∀ z, z ≠ lNh → z ≠ lNi → z ≠ lHv → y1.locals.lookup z = t.locals.lookup z := by
    intro z a b c; lk [y1]; exact yfr z a b
  have nd : ∀ z ∈ bvarScratch, z ≠ lNh ∧ z ≠ lNi ∧ z ≠ lHv := by decide
  have m1 : y1.memory = t.memory := ym
  have hR1 : SRep y1 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [m1], by rw [m1], by rw [m1], by rw [m1]⟩ yd
    (fun _ _ _ _ => ⟨fun _ _ => by rw [m1], fun _ _ => by rw [m1]⟩)
  refine eres2_back (eLitTail_spec2 ra y1 L FLn FLl FLs FLe KB st (.natVal n) hR1 hS
    (fun j hj => by rw [m1]; exact ⟨yd ▸ (hK j hj).1, (hK j hj).2⟩) (by omega) hb0 hb1
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact lkb)
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact len)
    (by rw [← hh]; exact lookup_setVar_same _ _ _)
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact lfle)
    (fun z hz => by
      obtain ⟨a, b, c⟩ := nd z hz
      obtain ⟨w, hw⟩ := W z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
      exact ⟨w, by rw [yb z a b c]; exact hw⟩)) ym yd yc yg yt


end

end ConPanqueque.V
