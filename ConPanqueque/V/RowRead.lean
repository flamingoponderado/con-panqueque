import ConPanqueque.V.Layout
import ConPanqueque.V.Decode
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Reading a row

`rowRead g`: with `g` pointing at a tier's descriptor and `di` holding an index, set `rp`, `rn` to
that row's key pointer and key length, or halt when the index is out of range (the twin's
`node? i = none`, a dangling handle, which it fails on).
-/

namespace ConPanqueque.V

def lRp := ofString "rp"
def lRn := ofString "rn"
def lDr := ofString "ddr"

def rowRead (g : MlS) : ProgHOL 64 :=
  .dec lDc .one (ldwV g 3) (.dec lDr .one (ldwV g 1) (.dec lDn .one (.load .one (vv lDc))
   (.ite (.cmp .lower (vv lDi) (vv lDn))
     (.seq (.assign .local lRp (.load .one (.op .add [vv lDr, .shift .lsl (vv lDi) (.const 4)])))
       (.assign .local lRn (.load .one (.op .add [vv lDr, .shift .lsl (vv lDi) (.const 4), .const 8]))))
     hang)))

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

theorem rowRead_spec (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (g : VGeo) (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (hu : Nat) (mkI : Nat → ι) (G base : BitVec 64) (gn : MlS) (i : Nat)
    (hR : TierRepV t enc dW g tb rows ders slots hu mkI) (hd : DescV t G g base) (hcap : g.cap < 2 ^ 30)
    (hg : t.locals.lookup gn = some (.val (.word G))) (hgn : gn ≠ lDc ∧ gn ≠ lDr)
    (hi : t.locals.lookup lDi = some (.val (.word (BitVec.ofNat 64 i)))) (hil : i < 2 ^ 60)
    (h1 : ∃ w, t.locals.lookup lRp = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lRn = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t (rowRead gn)).1 ∨ ∃ (hil : i < rows.length) (L : HolFiniteMapExact MlS (ValueHOL 64)) (P : BitVec 64),
      evaluateHOLFiniteState t (rowRead gn) = (none, { t with locals := L }) ∧
      L.lookup lRp = some (.val (.word P)) ∧
      L.lookup lRn = some (.val (.word (BitVec.ofNat 64 (enc rows[i]).length))) ∧
      Words t P (enc rows[i]) ∧ (enc rows[i]).length < 2 ^ 61 ∧
      ∀ y, y ≠ lRp → y ≠ lRn → L.lookup y = t.locals.lookup y := by
  obtain ⟨n1, n2⟩ := hgn
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  have hT := hR.vt
  have lK := hT.layK; have lD := hT.layD; have lR := hT.layR; have lS := hT.layS; have lC := hT.layC
  have hle := hT.le
  have evd : ∀ (s : PanSemStateFiniteExact 64 σ) (k : Nat) (hk : k < 8), s.locals.lookup gn = some (.val (.word G)) →
      s.memory = t.memory → s.memaddrs = t.memaddrs →
      @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (ldwV gn k) =
        some (.val (.word ((descV g base)[k]'(by simp [descV]; omega)))) := by
    intro s k hk e1 e2 e3
    rw [ldwV, eval_load_word s _ _ (eval_add2 s _ _ _ _ (eval_vv s gn _ e1) (eval_const s _))
      (by rw [e3]; exact (hd k hk).1), e2, (hd k hk).2]
  unfold rowRead
  have D1 : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (ldwV gn 3) =
      some (.val (.word g.C)) := by rw [evd t 3 (by decide) hg rfl rfl]; rfl
  let t1 := setVarHOLFinite lDc (.val (.word g.C)) t
  have D2 : @evalHOLExact 64 σ _ t1.toExact (fun a => Classical.propDecidable (t1.memaddrs a)) (ldwV gn 1) =
      some (.val (.word g.R)) := by rw [evd t1 1 (by decide) (by lk [t1]; exact hg) rfl rfl]; rfl
  let t2 := setVarHOLFinite lDr (.val (.word g.R)) t1
  have hcn : @evalHOLExact 64 σ _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
      (.load .one (vv lDc)) = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
    rw [eval_load_word t2 _ _ (eval_vv t2 lDc _ (by lk [t2, t1])) hT.cnt.1]
    show some (ValueHOL.val (t.memory _)) = _; rw [hT.cnt.2]
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
  by_cases h : i < rows.length
  · right
    refine ⟨h, ?_⟩
    rw [dec_word_eq t lDc _ g.C _ D1, dec_word_eq t1 lDr _ g.R _ D2, dec_word_eq t2 lDn _ _ _ hcn, ite_word t3 _ _ _ _ hcmp]
    simp only [bw, h, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    obtain ⟨P, a1, a2, a3, a4, a5, _, _⟩ := hT.row i h
    have s4 : BitVec.ofNat 64 i <<< (4 : BitVec 64).toNat = BitVec.ofNat 64 (16 * i) := by
      rw [show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)]
    rw [seq_normal _ (ConsLoop.assign_local t3 lRp _ P w1
      (by rw [eval_load_word t3 _ _ (eval_add2 t3 _ _ _ _ (eval_vv t3 lDr (.val (.word g.R)) (by lk [t3, t2]))
            (eval_shl t3 _ _ _ (eval_vv t3 lDi _ (by lk [t3, t2, t1]; exact hi)) (by decide))) (by rw [s4]; exact a1)]
          rw [s4]; show some (ValueHOL.val (t.memory _)) = _; rw [a3]) (by lk [t3, t2, t1]; exact hw1))]
    let t4 := setVarHOLFinite lRp (.val (.word P)) t3
    rw [ConsLoop.assign_local t4 lRn _ (BitVec.ofNat 64 (enc rows[i]).length) w2
      (by rw [eval_load_word t4 _ _ (eval_add3 t4 _ _ _ _ _ _ (eval_vv t4 lDr (.val (.word g.R)) (by lk [t4, t3, t2]))
            (eval_shl t4 _ _ _ (eval_vv t4 lDi _ (by lk [t4, t3, t2, t1]; exact hi)) (by decide)) (eval_const t4 8))
            (by rw [s4]; exact a2)]
          rw [s4]; show some (ValueHOL.val (t.memory _)) = _; rw [a4]) (by lk [t4, t3, t2, t1]; exact hw2)]
    refine ⟨_, P, rfl, ?_, ?_, a5, hT.short i h, ?_⟩
    · rw [lookup_resVar_other _ _ _ _ (by decide), lookup_resVar_other _ _ _ _ (by decide),
        lookup_resVar_other _ _ _ _ (by decide)]; lk [t4]
    · rw [lookup_resVar_other _ _ _ _ (by decide), lookup_resVar_other _ _ _ _ (by decide),
        lookup_resVar_other _ _ _ _ (by decide)]; lk
    · intro y y1 y2
      by_cases ec : y = lDc
      · subst ec; exact lookup_resVar_same _ _ _
      rw [lookup_resVar_other _ _ _ _ ec]
      by_cases ed : y = lDr
      · subst ed; rw [lookup_resVar_same]; lk [t1]
      rw [lookup_resVar_other _ _ _ _ ed]
      by_cases en : y = lDn
      · subst en; rw [lookup_resVar_same]; lk [t2, t1]
      rw [lookup_resVar_other _ _ _ _ en]; lk [t4, t3, t2, t1]
  · left
    have hs3 : Stop (evaluateHOLFiniteState t3 (.ite (.cmp .lower (vv lDi) (vv lDn))
        (.seq (.assign .local lRp (.load .one (.op .add [vv lDr, .shift .lsl (vv lDi) (.const 4)])))
          (.assign .local lRn (.load .one (.op .add [vv lDr, .shift .lsl (vv lDi) (.const 4), .const 8])))) hang)).1 := by
      rw [ite_word t3 _ _ _ _ hcmp]
      simp only [bw, h, ↓reduceIte, ne_eq, not_true_eq_false]
      exact hang_stop t3
    exact dec_stop t lDc _ g.C _ D1 (dec_stop t1 lDr _ g.R _ D2 (dec_stop t2 lDn _ _ _ hcn hs3))

end

/-- After a row read from `t`: memory and fixed parts as before; `rp`, `rn` hold the key's pointer and
length; `dt`, `dg`, `di` the handle's tier, tag and index; other locals as in `t`. -/
def RowRes {σ : Type} (t : PanSemStateFiniteExact 64 σ) (tier tag idx : Nat) (xs : List (BitVec 64))
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  r.1 = none ∧ r.2.memory = t.memory ∧ r.2.memaddrs = t.memaddrs ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    r.2.topAddr = t.topAddr ∧
    (∃ P, r.2.locals.lookup lRp = some (.val (.word P)) ∧ Words t P xs) ∧
    r.2.locals.lookup lRn = some (.val (.word (BitVec.ofNat 64 xs.length))) ∧ xs.length < 2 ^ 61 ∧
    r.2.locals.lookup lDt = some (.val (.word (BitVec.ofNat 64 tier))) ∧
    r.2.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 tag))) ∧
    r.2.locals.lookup lDi = some (.val (.word (BitVec.ofNat 64 idx))) ∧
    (∀ y, y ≠ lRp → y ≠ lRn → y ≠ lDt → y ≠ lDg → y ≠ lDi → r.2.locals.lookup y = t.locals.lookup y)

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

theorem rowAt_spec (t u : PanSemStateFiniteExact 64 σ) (L : Layout) (kb tag tier idx : Nat) (enc : α → List (BitVec 64))
    (dW : δ → BitVec 64 × BitVec 64) (tb : Tbl α ι δ) (mkI : Nat → ι)
    (hT : TabAt u L (kb + tag) tier enc dW tb mkI) (htier : tier < 2) (htag : kb + tag < 19) (hidx : idx < 2 ^ 30)
    (hdir : u.locals.lookup lDir = some (.val (.word L.DIR)))
    (hdt : u.locals.lookup lDt = some (.val (.word (BitVec.ofNat 64 tier))))
    (hdg : u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 tag))))
    (hdi : u.locals.lookup lDi = some (.val (.word (BitVec.ofNat 64 idx))))
    (h1 : ∃ w, u.locals.lookup lRp = some (.val (.word w))) (h2 : ∃ w, u.locals.lookup lRn = some (.val (.word w)))
    (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code) (hg : u.globals = t.globals)
    (hta : u.topAddr = t.topAddr)
    (hfr : ∀ y, y ≠ lRp → y ≠ lRn → y ≠ lDt → y ≠ lDg → y ≠ lDi → u.locals.lookup y = t.locals.lookup y) :
    Stop (evaluateHOLFiniteState u (.dec lDG .one (descE lDir kb) (rowRead lDG))).1 ∨
      ∃ (hlt : idx < tb.nodes.size),
        RowRes t tier tag idx (enc tb.nodes[idx]) (evaluateHOLFiniteState u (.dec lDG .one (descE lDir kb) (rowRead lDG))) := by
  obtain ⟨hdesc, hcap, rows, ders, slots, hu, hR⟩ := hT
  have he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) (descE lDir kb) =
      some (.val (.word (descAddr L (kb + tag) tier))) := by
    unfold descE
    rw [eval_add2 u _ _ _ _ (eval_vv u lDir _ hdir) (eval_shl u _ _ _ (eval_add3 u _ _ _ _ _ _
      (eval_mul2 u _ _ _ _ (eval_vv u lDt _ hdt) (eval_const u 19)) (eval_vv u lDg _ hdg) (eval_const u _)) (by decide))]
    congr 3; unfold descAddr; congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, Nat.shiftLeft_eq]
    omega
  let u1 := setVarHOLFinite lDG (.val (.word (descAddr L (kb + tag) tier))) u
  have RR := rowRead_spec u1 enc dW (L.geo (kb + tag) tier) tb rows ders slots hu mkI
    (descAddr L (kb + tag) tier) (L.base (kb + tag) tier) lDG idx (tierRepV_frame hR (fun _ _ => rfl) rfl)
    (fun k hk => hdesc k hk) hcap (lookup_setVar_same _ _ _) ⟨by decide, by decide⟩ (by lk [u1]; exact hdi) (by omega)
    (by obtain ⟨w, hw⟩ := h1; exact ⟨w, by lk [u1]; exact hw⟩) (by obtain ⟨w, hw⟩ := h2; exact ⟨w, by lk [u1]; exact hw⟩)
  rcases RR with hs | ⟨hil, Lc, P, e, l1, l2, hW, hsh, lfr⟩
  · exact Or.inl (dec_stop u lDG _ _ _ he hs)
  right
  have hrows : rows = tb.nodes.toList := hR.rel.nodes.symm
  have hsz : idx < tb.nodes.size := by rw [hrows] at hil; simpa using hil
  have hix : rows[idx] = tb.nodes[idx] := by subst hrows; simp
  refine ⟨hsz, ?_⟩
  rw [dec_word_eq u lDG _ _ _ he, e]
  refine ⟨rfl, hm, hd, hc, hg, hta, ⟨P, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun y y1 y2 y3 y4 y5 => ?_⟩
  · rw [lookup_resVar_other _ _ _ _ (by decide)]; exact l1
  · rw [← hix]; intro j hj; rw [← hm, ← hd]; exact hW j hj
  · rw [lookup_resVar_other _ _ _ _ (by decide), ← hix]; exact l2
  · rw [← hix]; exact hsh
  · rw [lookup_resVar_other _ _ _ _ (by decide), lfr _ (by decide) (by decide)]; lk [u1]; exact hdt
  · rw [lookup_resVar_other _ _ _ _ (by decide), lfr _ (by decide) (by decide)]; lk [u1]; exact hdg
  · rw [lookup_resVar_other _ _ _ _ (by decide), lfr _ (by decide) (by decide)]; lk [u1]; exact hdi
  · by_cases eg : y = lDG
    · subst eg; rw [lookup_resVar_same]; exact hfr _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [lookup_resVar_other _ _ _ _ eg, lfr y y1 y2]; lk [u1]; exact hfr y y1 y2 y3 y4 y5

end

/-- A store's row read: decode the handle; for a valid tag in a live tier read the row through its
descriptor, else halt (the twin's `view` is `none` there, which it fails on). -/
def storeRow (kb nt : Nat) : ProgHOL 64 :=
  .seq decodeH
   (.ite (.cmp .lower (vv lDg) (.const (BitVec.ofNat 64 nt)))
     (.ite (vv lDt)
       (.ite (.load .one (vv lFl)) (.dec lDG .one (descE lDir kb) (rowRead lDG)) hang)
       (.dec lDG .one (descE lDir kb) (rowRead lDG)))
     hang)

section
variable {σ : Type}

theorem storeRow_gen (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FL : BitVec 64) (on : Bool) (kb nt : Nat)
    (hnt : nt < 16) (i : Idx k) (Q : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ → Prop)
    (hh : t.locals.lookup lDh = some (.val (.word (Enc.idxW i))))
    (hdir : t.locals.lookup lDir = some (.val (.word L.DIR))) (hfl : t.locals.lookup lFl = some (.val (.word FL)))
    (hflm : t.memaddrs FL ∧ t.memory FL = .word (if on then 1 else 0))
    (ht : ∃ w, t.locals.lookup lDt = some (.val (.word w))) (hg : ∃ w, t.locals.lookup lDg = some (.val (.word w)))
    (hi : ∃ w, t.locals.lookup lDi = some (.val (.word w)))
    (h1 : ∃ w, t.locals.lookup lRp = some (.val (.word w))) (h2 : ∃ w, t.locals.lookup lRn = some (.val (.word w)))
    (harm : i.tag.toNat < nt → (i.tier.toNat = 0 ∨ on = true) → ∀ u : PanSemStateFiniteExact 64 σ,
      u.memory = t.memory → u.memaddrs = t.memaddrs → u.code = t.code → u.globals = t.globals →
      u.topAddr = t.topAddr →
      u.locals.lookup lDir = some (.val (.word L.DIR)) →
      u.locals.lookup lDt = some (.val (.word (BitVec.ofNat 64 i.tier.toNat))) →
      u.locals.lookup lDg = some (.val (.word (BitVec.ofNat 64 i.tag.toNat))) →
      u.locals.lookup lDi = some (.val (.word (BitVec.ofNat 64 i.idxNat))) →
      (∃ w, u.locals.lookup lRp = some (.val (.word w))) → (∃ w, u.locals.lookup lRn = some (.val (.word w))) →
      (∀ y, y ≠ lRp → y ≠ lRn → y ≠ lDt → y ≠ lDg → y ≠ lDi → u.locals.lookup y = t.locals.lookup y) →
      Stop (evaluateHOLFiniteState u (.dec lDG .one (descE lDir kb) (rowRead lDG))).1 ∨
        Q (evaluateHOLFiniteState u (.dec lDG .one (descE lDir kb) (rowRead lDG)))) :
    Stop (evaluateHOLFiniteState t (storeRow kb nt)).1 ∨ Q (evaluateHOLFiniteState t (storeRow kb nt)) := by
  obtain ⟨L1, e1, lt, lg, li, lfr⟩ := decodeH_spec t i hh ht hg hi
  unfold storeRow
  rw [seq_normal _ e1]
  let u : PanSemStateFiniteExact 64 σ := { t with locals := L1 }
  have uo1 : ∃ w, u.locals.lookup lRp = some (.val (.word w)) := by
    obtain ⟨w, hw⟩ := h1; exact ⟨w, by show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hw⟩
  have uo2 : ∃ w, u.locals.lookup lRn = some (.val (.word w)) := by
    obtain ⟨w, hw⟩ := h2; exact ⟨w, by show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hw⟩
  have ufr : ∀ y, y ≠ lRp → y ≠ lRn → y ≠ lDt → y ≠ lDg → y ≠ lDi → u.locals.lookup y = t.locals.lookup y :=
    fun y _ _ a b c => lfr y a b c
  have udir : u.locals.lookup lDir = some (.val (.word L.DIR)) := by
    show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hdir
  have tagw : i.tag.toNat < 2 ^ 32 := i.tag.toNat_lt
  have hcmp : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
      (.cmp .lower (vv lDg) (.const (BitVec.ofNat 64 nt))) = some (.val (.word (bw (i.tag.toNat < nt)))) := by
    rw [ConsLoop.eval_cmp_of u .lower _ _ _ _ (eval_vv u lDg _ lg) (eval_const u _)]
    have e : (BitVec.ofNat 64 i.tag.toNat < BitVec.ofNat 64 nt) ↔ i.tag.toNat < nt := by
      rw [BitVec.lt_def, toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by omega)]
    by_cases h : i.tag.toNat < nt
    · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]
    · have : ¬ BitVec.ofNat 64 i.tag.toNat < BitVec.ofNat 64 nt := fun x => h (e.mp x)
      simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  rw [ite_word u _ _ _ _ hcmp]
  by_cases htag : i.tag.toNat < nt
  · simp only [bw, htag, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have htl := Idx.tier_lt i
    rw [ite_word u _ _ _ _ (eval_vv u lDt _ lt)]
    rcases (by omega : i.tier.toNat = 0 ∨ i.tier.toNat = 1) with h0 | h0
    · simp only [h0, show BitVec.ofNat 64 0 = 0 from rfl, ne_eq, not_true_eq_false, ↓reduceIte]
      exact harm htag (Or.inl h0) u rfl rfl rfl rfl rfl udir (by rw [h0] at lt; rw [h0]; exact lt) lg li uo1 uo2 ufr
    · simp only [h0, show ¬ BitVec.ofNat 64 1 = 0 from by decide, ne_eq, not_false_eq_true, ↓reduceIte]
      have hld : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
          (.load .one (vv lFl)) = some (.val (.word (if on then 1 else 0))) := by
        rw [eval_load_word u _ _ (eval_vv u lFl _ (by show L1.lookup _ = _; rw [lfr _ (by decide) (by decide) (by decide)]; exact hfl))
          hflm.1]
        show some (ValueHOL.val (t.memory FL)) = _; rw [hflm.2]
      rw [ite_word u _ _ _ _ hld]
      cases hon : on
      · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
        exact Or.inl (hang_stop u)
      · simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
        exact harm htag (Or.inr hon) u rfl rfl rfl rfl rfl udir (by rw [h0] at lt; rw [h0]; exact lt) lg li uo1 uo2 ufr
  · simp only [bw, htag, ↓reduceIte, ne_eq, not_true_eq_false]
    exact Or.inl (hang_stop u)

end

end ConPanqueque.V
