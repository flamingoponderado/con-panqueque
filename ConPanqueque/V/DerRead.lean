import ConPanqueque.V.Two
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Reading a derived value

`derRead g`: with `g` pointing at a tier's descriptor and `di` holding an
index, set `do1`, `do2` to that row's derived pair, or to zeros when the index
is out of range: con-ron's `Tbl.derAt` (`der.getD i default`), given that the
table's `dW` sends `default` to zeros.
-/

namespace ConPanqueque.V

def lDi := ofString "di"
def lDo1 := ofString "do1"
def lDo2 := ofString "do2"
def lDc := ofString "ddc"
def lDd := ofString "ddd"
def lDn := ofString "dcn"

def derRead (g : MlS) : ProgHOL 64 :=
  .dec lDc .one (ldwV g 3) (.dec lDd .one (ldwV g 5) (.dec lDn .one (.load .one (vv lDc))
   (.ite (.cmp .lower (vv lDi) (vv lDn))
     (.seq (.assign .local lDo1 (.load .one (.op .add [vv lDd, .shift .lsl (vv lDi) (.const 4)])))
       (.assign .local lDo2 (.load .one (.op .add [vv lDd, .shift .lsl (vv lDi) (.const 4), .const 8]))))
     (.seq (.assign .local lDo1 (.const 0)) (.assign .local lDo2 (.const 0))))))

/-- `derRead` with the out-of-range arm a halt: the interns' checked read (a child must decode). -/
def derReadC (g : MlS) : ProgHOL 64 :=
  .dec lDc .one (ldwV g 3) (.dec lDd .one (ldwV g 5) (.dec lDn .one (.load .one (vv lDc))
   (.ite (.cmp .lower (vv lDi) (vv lDn))
     (.seq (.assign .local lDo1 (.load .one (.op .add [vv lDd, .shift .lsl (vv lDi) (.const 4)])))
       (.assign .local lDo2 (.load .one (.op .add [vv lDd, .shift .lsl (vv lDi) (.const 4), .const 8]))))
     hang)))

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] [Inhabited δ]

theorem derRead_spec (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hdef : dW default = (0, 0)) (g : VGeo) (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (hu : Nat) (mkI : Nat → ι) (G base : BitVec 64) (gn : MlS) (i : Nat)
    (hR : TierRepV t enc dW g tb rows ders slots hu mkI) (hd : DescV t G g base) (hcap : g.cap < 2 ^ 30)
    (hg : t.locals.lookup gn = some (.val (.word G))) (hgn : gn ≠ lDc ∧ gn ≠ lDd)
    (hi : t.locals.lookup lDi = some (.val (.word (BitVec.ofNat 64 i)))) (hil : i < 2 ^ 60)
    (h1 : ∃ w, t.locals.lookup lDo1 = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lDo2 = some (.val (.word w))) :
    ∃ L, evaluateHOLFiniteState t (derRead gn) =
      (none, { t with locals := L }) ∧
      L.lookup lDo1 = some (.val (.word (dW (tb.derAt i)).1)) ∧
      L.lookup lDo2 = some (.val (.word (dW (tb.derAt i)).2)) ∧
      ∀ y, y ≠ lDo1 → y ≠ lDo2 → L.lookup y = t.locals.lookup y := by
  obtain ⟨n1, n2⟩ := hgn
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  have hT := hR.vt
  have lK := hT.layK; have lD := hT.layD; have lR := hT.layR; have lS := hT.layS; have lC := hT.layC
  have hle := hT.le
  have hsz : tb.der.size = rows.length := by
    have := congrArg List.length hR.der; simp at this; rw [this, hT.dlen]
  have evd : ∀ (s : PanSemStateFiniteExact 64 σ) (k : Nat) (hk : k < 8), s.locals.lookup gn = some (.val (.word G)) →
      s.memory = t.memory → s.memaddrs = t.memaddrs →
      @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (ldwV gn k) =
        some (.val (.word ((descV g base)[k]'(by simp [descV]; omega)))) := by
    intro s k hk e1 e2 e3
    rw [ldwV, eval_load_word s _ _ (eval_add2 s _ _ _ _ (eval_vv s gn _ e1) (eval_const s _))
      (by rw [e3]; exact (hd k hk).1), e2, (hd k hk).2]
  unfold derRead
  rw [dec_word_eq t lDc _ g.C _ (by rw [evd t 3 (by decide) hg rfl rfl]; rfl)]
  let t1 := setVarHOLFinite lDc (.val (.word g.C)) t
  rw [dec_word_eq t1 lDd _ g.D _ (by rw [evd t1 5 (by decide) (by lk [t1]; exact hg) rfl rfl]; rfl)]
  let t2 := setVarHOLFinite lDd (.val (.word g.D)) t1
  have hcn : @evalHOLExact 64 σ _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
      (.load .one (vv lDc)) = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
    rw [eval_load_word t2 _ _ (eval_vv t2 lDc _ (by lk [t2, t1])) hT.cnt.1]
    show some (ValueHOL.val (t.memory _)) = _; rw [hT.cnt.2]
  rw [dec_word_eq t2 lDn _ _ _ hcn]
  let t3 := setVarHOLFinite lDn (.val (.word (BitVec.ofNat 64 rows.length))) t2
  have hcmp : @evalHOLExact 64 σ _ t3.toExact (fun a => Classical.propDecidable (t3.memaddrs a))
      (.cmp .lower (vv lDi) (vv lDn)) = some (.val (.word (bw (i < rows.length)))) := by
    rw [ConsLoop.eval_cmp_of t3 .lower _ _ _ _ (eval_vv t3 lDi _ (by lk [t3, t2, t1]; exact hi))
      (eval_vv t3 lDn _ (lookup_setVar_same _ _ _))]
    have e : (BitVec.ofNat 64 i < BitVec.ofNat 64 rows.length) ↔ i < rows.length := by
      rw [BitVec.lt_def, toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by omega)]
    by_cases h : i < rows.length
    · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 rows.length := fun x => h (e.mp x)
      simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  rw [ite_word t3 _ _ _ _ hcmp]
  -- the restore of the three scratch locals
  have restore : ∀ (u : PanSemStateFiniteExact 64 σ) (a b : BitVec 64), u.memory = t.memory → u.memaddrs = t.memaddrs →
      u.code = t.code → u.globals = t.globals → u.topAddr = t.topAddr → u.clock = t.clock → u.be = t.be →
      u.ffi = t.ffi → u.baseAddr = t.baseAddr → u.structs = t.structs → u.eshapes = t.eshapes →
      u.shMemaddrs = t.shMemaddrs →
      u.locals.lookup lDo1 = some (.val (.word a)) → u.locals.lookup lDo2 = some (.val (.word b)) →
      (∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDc → y ≠ lDd → y ≠ lDn → u.locals.lookup y = t.locals.lookup y) →
      a = (dW (tb.derAt i)).1 → b = (dW (tb.derAt i)).2 →
      ∃ L, ((none : Option (PanSemResultExact 64)),
          { ({ ({ u with locals := HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn) } :
                PanSemStateFiniteExact 64 σ) with
            locals := HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn)) (lDd, t1.locals.lookup lDd) } :
              PanSemStateFiniteExact 64 σ) with
            locals := HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn)) (lDd, t1.locals.lookup lDd))
              (lDc, t.locals.lookup lDc) }) = (none, { t with locals := L }) ∧
        L.lookup lDo1 = some (.val (.word (dW (tb.derAt i)).1)) ∧
        L.lookup lDo2 = some (.val (.word (dW (tb.derAt i)).2)) ∧
        ∀ y, y ≠ lDo1 → y ≠ lDo2 → L.lookup y = t.locals.lookup y := by
    intro u a b m d c gl ta ck be ffi ba st es sh ha hb fr ea eb
    refine ⟨HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn)) (lDd, t1.locals.lookup lDd))
      (lDc, t.locals.lookup lDc), ?_, ?_, ?_, ?_⟩
    · obtain ⟨ul, ug, us, uc, ue, um, ud, ush, uck, ube, uffi, uba, uta⟩ := u
      simp only at m d c gl ta ck be ffi ba st es sh
      subst m d c gl ta ck be ffi ba st es sh; rfl
    · rw [lookup_resVar_other _ _ _ _ (by decide), lookup_resVar_other _ _ _ _ (by decide),
        lookup_resVar_other _ _ _ _ (by decide), ha, ea]
    · rw [lookup_resVar_other _ _ _ _ (by decide), lookup_resVar_other _ _ _ _ (by decide),
        lookup_resVar_other _ _ _ _ (by decide), hb, eb]
    · intro y y1 y2
      by_cases ec : y = lDc
      · subst ec; exact lookup_resVar_same _ _ _
      rw [lookup_resVar_other _ _ _ _ ec]
      by_cases ed : y = lDd
      · subst ed; rw [lookup_resVar_same]; lk [t1]
      rw [lookup_resVar_other _ _ _ _ ed]
      by_cases en : y = lDn
      · subst en; rw [lookup_resVar_same]; lk [t2, t1]
      rw [lookup_resVar_other _ _ _ _ en]; exact fr y y1 y2 ec ed en
  by_cases h : i < rows.length
  · simp only [bw, h, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    obtain ⟨a1, a2, a3, a4⟩ := hT.der i h
    have hix : i < tb.der.size := by rw [hsz]; exact h
    have hdi : ders[i]'(by rw [hT.dlen]; exact h) = dW (tb.derAt i) := by
      simp only [← hR.der, List.getElem_map, Array.getElem_toList, Tbl.derAt, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hix, Option.getD_some]
    have s4 : BitVec.ofNat 64 i <<< (4 : BitVec 64).toNat = BitVec.ofNat 64 (16 * i) := by
      rw [show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)]
    rw [seq_normal _ (ConsLoop.assign_local t3 lDo1 _ (dW (tb.derAt i)).1 w1
      (by rw [eval_load_word t3 _ _ (eval_add2 t3 _ _ _ _ (eval_vv t3 lDd (.val (.word g.D)) (by lk [t3, t2]))
            (eval_shl t3 _ _ _ (eval_vv t3 lDi _ (by lk [t3, t2, t1]; exact hi)) (by decide))) (by rw [s4]; exact a1)]
          rw [s4]; show some (ValueHOL.val (t.memory _)) = _; rw [a3, hdi]) (by lk [t3, t2, t1]; exact hw1))]
    let t4 := setVarHOLFinite lDo1 (.val (.word (dW (tb.derAt i)).1)) t3
    rw [ConsLoop.assign_local t4 lDo2 _ (dW (tb.derAt i)).2 w2
      (by rw [eval_load_word t4 _ _ (eval_add3 t4 _ _ _ _ _ _ (eval_vv t4 lDd (.val (.word g.D)) (by lk [t4, t3, t2]))
            (eval_shl t4 _ _ _ (eval_vv t4 lDi _ (by lk [t4, t3, t2, t1]; exact hi)) (by decide)) (eval_const t4 8))
            (by rw [s4]; exact a2)]
          rw [s4]; show some (ValueHOL.val (t.memory _)) = _; rw [a4, hdi]) (by lk [t4, t3, t2, t1]; exact hw2)]
    exact restore (setVarHOLFinite lDo2 (.val (.word (dW (tb.derAt i)).2)) t4) (dW (tb.derAt i)).1
      (dW (tb.derAt i)).2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by lk [t4]) (by lk)
      (fun y y1 y2 y3 y4 y5 => by lk [t4, t3, t2, t1]) rfl rfl
  · simp only [bw, h, ↓reduceIte, ne_eq, not_true_eq_false]
    have hdi : dW (tb.derAt i) = (0, 0) := by
      rw [← hdef]; congr 1
      simp only [Tbl.derAt, Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_none (by omega)]; rfl
    rw [seq_normal _ (ConsLoop.assign_local t3 lDo1 (.const 0) 0 w1 (eval_const t3 0) (by lk [t3, t2, t1]; exact hw1))]
    let t4 := setVarHOLFinite lDo1 (.val (.word 0)) t3
    rw [ConsLoop.assign_local t4 lDo2 (.const 0) 0 w2 (eval_const t4 0) (by lk [t4, t3, t2, t1]; exact hw2)]
    have e1 : (0 : BitVec 64) = (dW (tb.derAt i)).1 := by rw [hdi]
    have e2 : (0 : BitVec 64) = (dW (tb.derAt i)).2 := by rw [hdi]
    have l1 : (setVarHOLFinite lDo2 (.val (.word (0 : BitVec 64))) t4).locals.lookup lDo1 =
        some (.val (.word (0 : BitVec 64))) := by lk [t4]
    have l2 : (setVarHOLFinite lDo2 (.val (.word (0 : BitVec 64))) t4).locals.lookup lDo2 =
        some (.val (.word (0 : BitVec 64))) := by lk
    have R := restore (setVarHOLFinite lDo2 (.val (.word (0 : BitVec 64))) t4) 0 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl l1 l2 (fun y y1 y2 y3 y4 y5 => by lk [t4, t3, t2, t1]) e1 e2
    simp only at R ⊢
    exact R


theorem derReadC_spec (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hdef : dW default = (0, 0)) (g : VGeo) (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (hu : Nat) (mkI : Nat → ι) (G base : BitVec 64) (gn : MlS) (i : Nat)
    (hR : TierRepV t enc dW g tb rows ders slots hu mkI) (hd : DescV t G g base) (hcap : g.cap < 2 ^ 30)
    (hg : t.locals.lookup gn = some (.val (.word G))) (hgn : gn ≠ lDc ∧ gn ≠ lDd)
    (hi : t.locals.lookup lDi = some (.val (.word (BitVec.ofNat 64 i)))) (hil : i < 2 ^ 60)
    (h1 : ∃ w, t.locals.lookup lDo1 = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lDo2 = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t (derReadC gn)).1 ∨ (i < rows.length ∧ ∃ L, evaluateHOLFiniteState t (derReadC gn) =
      (none, { t with locals := L }) ∧
      L.lookup lDo1 = some (.val (.word (dW (tb.derAt i)).1)) ∧
      L.lookup lDo2 = some (.val (.word (dW (tb.derAt i)).2)) ∧
      ∀ y, y ≠ lDo1 → y ≠ lDo2 → L.lookup y = t.locals.lookup y) := by
  obtain ⟨n1, n2⟩ := hgn
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  have hT := hR.vt
  have lK := hT.layK; have lD := hT.layD; have lR := hT.layR; have lS := hT.layS; have lC := hT.layC
  have hle := hT.le
  have hsz : tb.der.size = rows.length := by
    have := congrArg List.length hR.der; simp at this; rw [this, hT.dlen]
  have evd : ∀ (s : PanSemStateFiniteExact 64 σ) (k : Nat) (hk : k < 8), s.locals.lookup gn = some (.val (.word G)) →
      s.memory = t.memory → s.memaddrs = t.memaddrs →
      @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (ldwV gn k) =
        some (.val (.word ((descV g base)[k]'(by simp [descV]; omega)))) := by
    intro s k hk e1 e2 e3
    rw [ldwV, eval_load_word s _ _ (eval_add2 s _ _ _ _ (eval_vv s gn _ e1) (eval_const s _))
      (by rw [e3]; exact (hd k hk).1), e2, (hd k hk).2]
  unfold derReadC
  rw [dec_word_eq t lDc _ g.C _ (by rw [evd t 3 (by decide) hg rfl rfl]; rfl)]
  let t1 := setVarHOLFinite lDc (.val (.word g.C)) t
  rw [dec_word_eq t1 lDd _ g.D _ (by rw [evd t1 5 (by decide) (by lk [t1]; exact hg) rfl rfl]; rfl)]
  let t2 := setVarHOLFinite lDd (.val (.word g.D)) t1
  have hcn : @evalHOLExact 64 σ _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
      (.load .one (vv lDc)) = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
    rw [eval_load_word t2 _ _ (eval_vv t2 lDc _ (by lk [t2, t1])) hT.cnt.1]
    show some (ValueHOL.val (t.memory _)) = _; rw [hT.cnt.2]
  rw [dec_word_eq t2 lDn _ _ _ hcn]
  let t3 := setVarHOLFinite lDn (.val (.word (BitVec.ofNat 64 rows.length))) t2
  have hcmp : @evalHOLExact 64 σ _ t3.toExact (fun a => Classical.propDecidable (t3.memaddrs a))
      (.cmp .lower (vv lDi) (vv lDn)) = some (.val (.word (bw (i < rows.length)))) := by
    rw [ConsLoop.eval_cmp_of t3 .lower _ _ _ _ (eval_vv t3 lDi _ (by lk [t3, t2, t1]; exact hi))
      (eval_vv t3 lDn _ (lookup_setVar_same _ _ _))]
    have e : (BitVec.ofNat 64 i < BitVec.ofNat 64 rows.length) ↔ i < rows.length := by
      rw [BitVec.lt_def, toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by omega)]
    by_cases h : i < rows.length
    · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 rows.length := fun x => h (e.mp x)
      simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  rw [ite_word t3 _ _ _ _ hcmp]
  -- the restore of the three scratch locals
  have restore : ∀ (u : PanSemStateFiniteExact 64 σ) (a b : BitVec 64), u.memory = t.memory → u.memaddrs = t.memaddrs →
      u.code = t.code → u.globals = t.globals → u.topAddr = t.topAddr → u.clock = t.clock → u.be = t.be →
      u.ffi = t.ffi → u.baseAddr = t.baseAddr → u.structs = t.structs → u.eshapes = t.eshapes →
      u.shMemaddrs = t.shMemaddrs →
      u.locals.lookup lDo1 = some (.val (.word a)) → u.locals.lookup lDo2 = some (.val (.word b)) →
      (∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDc → y ≠ lDd → y ≠ lDn → u.locals.lookup y = t.locals.lookup y) →
      a = (dW (tb.derAt i)).1 → b = (dW (tb.derAt i)).2 →
      ∃ L, ((none : Option (PanSemResultExact 64)),
          { ({ ({ u with locals := HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn) } :
                PanSemStateFiniteExact 64 σ) with
            locals := HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn)) (lDd, t1.locals.lookup lDd) } :
              PanSemStateFiniteExact 64 σ) with
            locals := HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn)) (lDd, t1.locals.lookup lDd))
              (lDc, t.locals.lookup lDc) }) = (none, { t with locals := L }) ∧
        L.lookup lDo1 = some (.val (.word (dW (tb.derAt i)).1)) ∧
        L.lookup lDo2 = some (.val (.word (dW (tb.derAt i)).2)) ∧
        ∀ y, y ≠ lDo1 → y ≠ lDo2 → L.lookup y = t.locals.lookup y := by
    intro u a b m d c gl ta ck be ffi ba st es sh ha hb fr ea eb
    refine ⟨HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq u.locals (lDn, t2.locals.lookup lDn)) (lDd, t1.locals.lookup lDd))
      (lDc, t.locals.lookup lDc), ?_, ?_, ?_, ?_⟩
    · obtain ⟨ul, ug, us, uc, ue, um, ud, ush, uck, ube, uffi, uba, uta⟩ := u
      simp only at m d c gl ta ck be ffi ba st es sh
      subst m d c gl ta ck be ffi ba st es sh; rfl
    · rw [lookup_resVar_other _ _ _ _ (by decide), lookup_resVar_other _ _ _ _ (by decide),
        lookup_resVar_other _ _ _ _ (by decide), ha, ea]
    · rw [lookup_resVar_other _ _ _ _ (by decide), lookup_resVar_other _ _ _ _ (by decide),
        lookup_resVar_other _ _ _ _ (by decide), hb, eb]
    · intro y y1 y2
      by_cases ec : y = lDc
      · subst ec; exact lookup_resVar_same _ _ _
      rw [lookup_resVar_other _ _ _ _ ec]
      by_cases ed : y = lDd
      · subst ed; rw [lookup_resVar_same]; lk [t1]
      rw [lookup_resVar_other _ _ _ _ ed]
      by_cases en : y = lDn
      · subst en; rw [lookup_resVar_same]; lk [t2, t1]
      rw [lookup_resVar_other _ _ _ _ en]; exact fr y y1 y2 ec ed en
  by_cases h : i < rows.length
  · right; refine ⟨h, ?_⟩
    simp only [bw, h, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    obtain ⟨a1, a2, a3, a4⟩ := hT.der i h
    have hix : i < tb.der.size := by rw [hsz]; exact h
    have hdi : ders[i]'(by rw [hT.dlen]; exact h) = dW (tb.derAt i) := by
      simp only [← hR.der, List.getElem_map, Array.getElem_toList, Tbl.derAt, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hix, Option.getD_some]
    have s4 : BitVec.ofNat 64 i <<< (4 : BitVec 64).toNat = BitVec.ofNat 64 (16 * i) := by
      rw [show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)]
    rw [seq_normal _ (ConsLoop.assign_local t3 lDo1 _ (dW (tb.derAt i)).1 w1
      (by rw [eval_load_word t3 _ _ (eval_add2 t3 _ _ _ _ (eval_vv t3 lDd (.val (.word g.D)) (by lk [t3, t2]))
            (eval_shl t3 _ _ _ (eval_vv t3 lDi _ (by lk [t3, t2, t1]; exact hi)) (by decide))) (by rw [s4]; exact a1)]
          rw [s4]; show some (ValueHOL.val (t.memory _)) = _; rw [a3, hdi]) (by lk [t3, t2, t1]; exact hw1))]
    let t4 := setVarHOLFinite lDo1 (.val (.word (dW (tb.derAt i)).1)) t3
    rw [ConsLoop.assign_local t4 lDo2 _ (dW (tb.derAt i)).2 w2
      (by rw [eval_load_word t4 _ _ (eval_add3 t4 _ _ _ _ _ _ (eval_vv t4 lDd (.val (.word g.D)) (by lk [t4, t3, t2]))
            (eval_shl t4 _ _ _ (eval_vv t4 lDi _ (by lk [t4, t3, t2, t1]; exact hi)) (by decide)) (eval_const t4 8))
            (by rw [s4]; exact a2)]
          rw [s4]; show some (ValueHOL.val (t.memory _)) = _; rw [a4, hdi]) (by lk [t4, t3, t2, t1]; exact hw2)]
    exact restore (setVarHOLFinite lDo2 (.val (.word (dW (tb.derAt i)).2)) t4) (dW (tb.derAt i)).1
      (dW (tb.derAt i)).2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by lk [t4]) (by lk)
      (fun y y1 y2 y3 y4 y5 => by lk [t4, t3, t2, t1]) rfl rfl
  · left
    simp only [bw, h, ↓reduceIte, ne_eq, not_true_eq_false]
    exact Or.inl (hang_spec _ _ rfl)

end

end ConPanqueque.V
