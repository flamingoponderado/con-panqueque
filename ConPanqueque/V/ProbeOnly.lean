import ConPanqueque.V.Intern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Probing one tier of a generic table without appending

`probeV` is `internV` with the miss branch replaced by `skip`: on a hit it
returns the twin's handle, on a miss it falls through with memory and every
local as they were (`PResV`).
-/

namespace ConPanqueque.V

def probeV : ProgHOL 64 :=
  .dec lWa .one (vv lK) (.dec lWb .one (.const 0) (.dec lWn .one (vv lL) (.dec lWeq .one (.const 0)
  (.dec lWg .one (.const 1) (.dec lWh .one (.const 0)
  (.seq hashLoop
  (.dec lJ .one (.op .and [vv lWh, vv lM]) (.dec lC .one (.op .add [vv lM, .const 1])
  (.dec lG .one (.const 1) (.dec lRes .one (.const 0) (.dec lV .one (.const 0)
  (.seq probeLoop
   (.ite (.cmp .notEqual (vv lRes) (.const 0)) (.return (hE (.op .sub [vv lRes, .const 1]))) .skip)))))))))))))

theorem skip_evalV {σ : Type} (s : PanSemStateFiniteExact 64 σ) : evaluateHOLFiniteState s .skip = (none, s) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]

/-- Locals agree outside `A`. -/
def FrV (A : List MlS) (u t : HolFiniteMapExact MlS (ValueHOL 64)) : Prop := ∀ y, y ∉ A → u.lookup y = t.lookup y

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

/-- What `probeV` guarantees: memory and the state's fixed parts unchanged; a stop, a hit returning the
twin's handle, or a miss with the locals agreeing outside `A`. -/
def PResV (A : List MlS) (t : PanSemStateFiniteExact 64 σ) (hwd : ι → BitVec 64) (tb : Tbl α ι δ) (x : α)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨ (r.2.memory = t.memory ∧ r.2.memaddrs = t.memaddrs ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    r.2.topAddr = t.topAddr ∧
    ((∃ h, tb.find? x = some h ∧ r.1 = some (.returned (.val (.word (hwd h))))) ∨
     (tb.find? x = none ∧ r.1 = none ∧ FrV A r.2.locals t.locals)))

omit [LawfulBEq α] [DecidableEq α] in
theorem presV_dec {s : PanSemStateFiniteExact 64 σ} {x : MlS} {v : BitVec 64} {A : List MlS} {hwd : ι → BitVec 64}
    {tb : Tbl α ι δ} {a : α} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : PResV (x :: A) (setVarHOLFinite x (.val (.word v)) s) hwd tb a r) :
    PResV A s hwd tb a (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (x, s.locals.lookup x) }) := by
  rcases h with h | ⟨m, d, c, g, ta, h | ⟨hf, hr, hfr⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, d, c, g, ta, Or.inl h⟩
  · refine Or.inr ⟨m, d, c, g, ta, Or.inr ⟨hf, hr, fun y hy => ?_⟩⟩
    by_cases e : y = x
    · subst e; exact lookup_resVar_same _ _ _
    · rw [lookup_resVar_other _ _ _ _ e, hfr y (by simp [e, hy])]; exact lookup_setVar_other _ _ e

omit [LawfulBEq α] [DecidableEq α] in
theorem presV_mono {A B : List MlS} {s : PanSemStateFiniteExact 64 σ} {hwd : ι → BitVec 64} {tb : Tbl α ι δ} {a : α}
    {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ} (hAB : ∀ y, y ∈ A → y ∈ B)
    (h : PResV A s hwd tb a r) : PResV B s hwd tb a r := by
  rcases h with h | ⟨m, d, c, g, ta, h | ⟨hf, hr, hfr⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, d, c, g, ta, Or.inl h⟩
  · exact Or.inr ⟨m, d, c, g, ta, Or.inr ⟨hf, hr, fun y hy => hfr y (fun hm => hy (hAB y hm))⟩⟩

end

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

omit [LawfulBEq α] [DecidableEq α] in
theorem presV_trans {A B : List MlS} {u t : PanSemStateFiniteExact 64 σ} {hwd : ι → BitVec 64} {tb : Tbl α ι δ}
    {a : α} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ} (h : PResV A u hwd tb a r)
    (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code) (hg : u.globals = t.globals)
    (ht : u.topAddr = t.topAddr) (hfr : FrV B u.locals t.locals) : PResV (A ++ B) t hwd tb a r := by
  rcases h with h | ⟨m, d, c, g, ta, h | ⟨hf, hr, hfr'⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨m.trans hm, d.trans hd, c.trans hc, g.trans hg, ta.trans ht, Or.inl h⟩
  · refine Or.inr ⟨m.trans hm, d.trans hd, c.trans hc, g.trans hg, ta.trans ht, Or.inr ⟨hf, hr, fun y hy => ?_⟩⟩
    simp only [List.mem_append, not_or] at hy
    rw [hfr' y hy.1, hfr y hy.2]

theorem probeV_spec (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64))
    (hwd : ι → BitVec 64) (mkI : Nat → ι) (base : BitVec 64) (icap : Nat)
    (hmk : ∀ i, i < icap → hwd (mkI i) = base + BitVec.ofNat 64 i) (hinj : ∀ x y, enc x = enc y → x = y)
    (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat) (g : VGeo)
    (x : α) (K : BitVec 64)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30) (hci : g.cap ≤ icap)
    (hT : VT t enc rows ders slots g hu) (hinv : Inv (α := α) (homeV enc g.b) rows slots g.n)
    (hrel : TblRel tb rows mkI) (hK : Words t K (enc x)) (hKl : (enc x).length < 2 ^ 61)
    (lK' : t.locals.lookup lK = some (.val (.word K)))
    (ll : t.locals.lookup lL = some (.val (.word (BitVec.ofNat 64 (enc x).length))))
    (lm : t.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (g.n - 1)))))
    (ls : t.locals.lookup lS = some (.val (.word g.S))) (lr : t.locals.lookup lR = some (.val (.word g.R)))
    (lhb : t.locals.lookup lHb = some (.val (.word base))) :
    PResV [] t hwd tb x (evaluateHOLFiniteState t probeV) := by
  have hpos : 0 < g.n := hinv.pos
  let hx := homeV enc g.b x
  have hxn : hx < g.n := hinv.home_lt x
  unfold probeV
  rw [dec_word_eq t lWa (vv lK) K _ (eval_vv t lK _ lK')]; apply presV_dec (v := K)
  let t1 := setVarHOLFinite lWa (.val (.word K)) t
  rw [dec_word_eq t1 lWb (.const 0) 0 _ (eval_const t1 0)]; apply presV_dec (v := 0)
  let t2 := setVarHOLFinite lWb (.val (.word 0)) t1
  rw [dec_word_eq t2 lWn (vv lL) _ _ (eval_vv t2 lL _ (by lk [t2, t1]; exact ll))]
  apply presV_dec (v := BitVec.ofNat 64 (enc x).length)
  let t3 := setVarHOLFinite lWn (.val (.word (BitVec.ofNat 64 (enc x).length))) t2
  rw [dec_word_eq t3 lWeq (.const 0) 0 _ (eval_const t3 0)]; apply presV_dec (v := 0)
  let t4 := setVarHOLFinite lWeq (.val (.word 0)) t3
  rw [dec_word_eq t4 lWg (.const 1) 1 _ (eval_const t4 1)]; apply presV_dec (v := 1)
  let t5 := setVarHOLFinite lWg (.val (.word 1)) t4
  rw [dec_word_eq t5 lWh (.const 0) 0 _ (eval_const t5 0)]; apply presV_dec (v := 0)
  let t6 := setVarHOLFinite lWh (.val (.word 0)) t5
  rcases hashLoop_spec t6 K (enc x) (by omega) hK (by lk [t6, t5, t4, t3, t2, t1])
      (by lk [t6, t5, t4, t3]) (by lk [t6]) (by lk [t6, t5]) with hs | ⟨hn1, hHI, hwh⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  generalize hh : evaluateHOLFiniteState t6 hashLoop = hst at hn1 hHI hwh
  obtain ⟨h1r, h1⟩ := hst
  simp only at hn1 hHI hwh; subst hn1
  rw [seq_normal _ hh]
  obtain ⟨hm1, hd1, hc1, hg1, ht1, hfr1, k1, _, hwa1, hwn1, hbr1⟩ := hHI
  have hwg1 : ∃ z, h1.locals.lookup lWg = some (.val (.word z)) := by
    rcases hbr1 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact ⟨_, h⟩
  have k1' : ∀ y, y ≠ lWh → y ≠ lWg → y ≠ lWn → y ≠ lWa → h1.locals.lookup y = t6.locals.lookup y :=
    fun y a1 a2 a3 a4 => hfr1 y a4 a3 a1 a2
  apply presV_mono (A := [lWa, lWb, lWn, lWeq, lWg] ++ [lWa, lWn, lWh, lWg]) (by decide)
  refine presV_trans ?_ hm1 hd1 hc1 hg1 ht1 (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact k1' y hy.2.2.1 hy.2.2.2 hy.2.1 hy.1)
  have lM1 : h1.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (g.n - 1)))) := by
    rw [k1' _ (by decide) (by decide) (by decide) (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact lm
  have hJv : @evalHOLExact 64 σ _ h1.toExact (fun a => Classical.propDecidable (h1.memaddrs a))
      (.op .and [vv lWh, vv lM]) = some (.val (.word (BitVec.ofNat 64 hx))) := by
    simp [vv, evalHOLExact, evalListHOLExact, hwh, lM1, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [show (g.n - 1) = 2 ^ g.b - 1 by rw [hn]]
    show _ &&& (_ &&& (18446744073709551615#64)) = _
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes, mask_home _ _ hb]
    rfl
  rw [dec_word_eq h1 lJ _ _ _ hJv]; apply presV_dec (v := BitVec.ofNat 64 hx)
  let u1 := setVarHOLFinite lJ (.val (.word (BitVec.ofNat 64 hx))) h1
  rw [dec_word_eq u1 lC (.op .add [vv lM, .const 1]) (BitVec.ofNat 64 g.n) _
    (by rw [eval_add2 u1 _ _ _ _ (eval_vv u1 lM _ (by lk [u1]; exact lM1)) (eval_const u1 1)]
        congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)]
  apply presV_dec (v := BitVec.ofNat 64 g.n)
  let u2 := setVarHOLFinite lC (.val (.word (BitVec.ofNat 64 g.n))) u1
  rw [dec_word_eq u2 lG (.const 1) 1 _ (eval_const u2 1)]; apply presV_dec (v := 1)
  let u3 := setVarHOLFinite lG (.val (.word 1)) u2
  rw [dec_word_eq u3 lRes (.const 0) 0 _ (eval_const u3 0)]; apply presV_dec (v := 0)
  let u4 := setVarHOLFinite lRes (.val (.word 0)) u3
  rw [dec_word_eq u4 lV (.const 0) 0 _ (eval_const u4 0)]; apply presV_dec (v := 0)
  let u5 := setVarHOLFinite lV (.val (.word 0)) u4
  have back : ∀ y, y ∉ scr → y ≠ lWh → u5.locals.lookup y = t.locals.lookup y := by
    intro y hy hh'
    simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hy
    lk [u5, u4, u3, u2, u1]
    rw [k1' y hh' n10 n8 n6]; lk [t6, t5, t4, t3, t2, t1]
  have hmem5 : u5.memory = t.memory := hm1
  have hd5 : u5.memaddrs = t.memaddrs := hd1
  have hT5 : VT u5 enc rows ders slots g hu := vt_of_eq hT hmem5 hd5
  have hK5 : Words u5 K (enc x) := fun k hk => by rw [hmem5, hd5]; exact hK k hk
  let ans := probeR rows slots g.n x g.n hx
  have hB5 : Base u5 u5 g.n g.S g.R K (enc x).length :=
    ⟨rfl, rfl, rfl, rfl, rfl, by rw [back _ (by decide) (by decide)]; exact ls,
      by rw [back _ (by decide) (by decide)]; exact lr, by rw [back _ (by decide) (by decide)]; exact lm,
      by rw [back _ (by decide) (by decide)]; exact lK', by rw [back _ (by decide) (by decide)]; exact ll,
      fun _ _ => rfl, fun y hy => by
        simp only [cscr, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, by lk [u5, u4, u3, u2, u1]; exact hwa1⟩
        · exact ⟨0, by lk [u5, u4, u3, u2, u1]; rw [k1' _ (by decide) (by decide) (by decide) (by decide)]; lk [t6, t5, t4, t3, t2]⟩
        · exact ⟨_, by lk [u5, u4, u3, u2, u1]; exact hwn1⟩
        · exact ⟨0, by lk [u5, u4, u3, u2, u1]; rw [k1' _ (by decide) (by decide) (by decide) (by decide)]; lk [t6, t5, t4]⟩
        · obtain ⟨z, hz⟩ := hwg1; exact ⟨z, by lk [u5, u4, u3, u2, u1]; exact hz⟩⟩
  have hI : LInv u5 enc rows slots g.n g.S g.R K x ans u5 :=
    ⟨hB5, g.n, hx, hxn, by lk [u5, u4, u3, u2, u1], by lk [u5, u4, u3, u2, u1], ⟨0, by lk [u5]⟩,
      Or.inl ⟨by lk [u5, u4, u3, u2, u1], by lk [u5, u4, u3, u2, u1], rfl, Nat.le_refl _⟩⟩
  rcases probeLoop_spec u5 enc rows slots g.n g.b g.S g.R K x ans hn (by omega) hT5.vmem hK5 hKl hinv.named hinj u5 hI
    with hs | ⟨hn6, hI6, hg6⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  generalize hp : evaluateHOLFiniteState u5 probeLoop = pst at hn6 hI6 hg6
  obtain ⟨p1, u⟩ := pst
  simp only at hn6 hI6 hg6; subst hn6
  rw [seq_normal _ hp]
  obtain ⟨hB6, f, j, hj, hC6, hJ6, hV6, br⟩ := hI6
  obtain ⟨_, hres6, hemp, hfull⟩ := br.resolve_left (fun ⟨hg, _⟩ => by rw [hg6] at hg; cases hg)
  have hprobe := probeR_toOpt rows slots g.n x g.n hx
  have hfind := find_probe (homeV enc g.b) tb rows slots g.n mkI hrel hinv x
  have hlhb : u.locals.lookup lHb = some (.val (.word base)) := by
    rw [hB6.fr _ (by decide), back _ (by decide) (by decide)]; exact lhb
  cases hto : ans.toOpt with
  | some i =>
    rw [hto] at hres6
    simp only [Option.map_some, Option.getD_some] at hres6
    have hi : rows[i]? = some x := (probe_correct (homeV enc g.b) rows slots g.n hinv x).1 i (by rw [← hprobe]; exact hto)
    have hil : i < rows.length := (List.getElem?_eq_some_iff.mp hi).1
    have hcapl := hT.le
    have hne : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .notEqual (vv lRes) (.const 0)) = some (.val (.word 1)) := by
      rw [ConsLoop.eval_cmp_of u .notEqual _ _ _ 0 (eval_vv u lRes _ hres6) (eval_const u 0)]
      have : ¬ BitVec.ofNat 64 (i + 1) = 0 := fun e => by have := congrArg BitVec.toNat e; simp at this; omega
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact this
    rw [ite_word u _ _ _ _ hne]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    have hw : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (hE (.op .sub [vv lRes, .const 1])) = some (.val (.word (hwd (mkI i)))) := by
      rw [hmk i (by omega)]
      unfold hE
      rw [eval_add2 u _ _ _ _ (eval_vv u lHb _ hlhb) (eval_sub2 u _ _ _ _ (eval_vv u lRes _ hres6) (eval_const u 1))]
      congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega
    have eret : evaluateHOLFiniteState u (.return (hE (.op .sub [vv lRes, .const 1]))) =
        (some (.returned (.val (.word (hwd (mkI i))))), emptyLocalsHOLFinite u) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only [hw]; simp [shapeOfHOLExact]
    rw [eret]
    have hfi : tb.find? x = some (mkI i) := by rw [hfind, ← hprobe, hto]; rfl
    exact Or.inr ⟨hB6.mem, hB6.addrs, hB6.code, hB6.globals, hB6.top, Or.inl ⟨_, hfi, rfl⟩⟩
  | none =>
    rw [hto] at hres6
    simp only [Option.map_none, Option.getD_none] at hres6
    have hne : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .notEqual (vv lRes) (.const 0)) = some (.val (.word 0)) := by
      rw [ConsLoop.eval_cmp_of u .notEqual _ _ _ 0 (eval_vv u lRes _ hres6) (eval_const u 0)]
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [ite_word u _ _ _ _ hne]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    rw [skip_evalV]
    have hfi : tb.find? x = none := by rw [hfind, ← hprobe, hto]; rfl
    refine Or.inr ⟨hB6.mem, hB6.addrs, hB6.code, hB6.globals, hB6.top, Or.inr ⟨hfi, rfl, fun y hy => ?_⟩⟩
    refine hB6.fr y (fun hm => hy ?_)
    simp only [scr, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with h | h | h | h | h | h | h | h | h | h <;> simp [h]

end

end ConPanqueque.V
