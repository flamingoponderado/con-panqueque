import ConPanqueque.T.MemoModel
import ConPanqueque.T.MemoRep
import ConPanqueque.T.Intern
import ConPanqueque.V.DerWrite
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Memo tables in Pancake

A memo is a one-tier generic table (`VT`) whose descriptor's base word is `1`, so a probe hit
returns `1 + i` for row `i`; keys are two words, placed at the key buffer by the caller.
`memoProbe2(g)` returns `1 + i` on a hit and `0` on a miss.
-/

namespace ConPanqueque.T

def pG := ofString "mg"
def pLen := ofString "mlen"
def fMemoProbe := ofString "memoProbe"

/-- `memoProbe(g, len)`: probe the memo described at `g` for the `len`-word key in the key buffer. -/
def memoProbeBody : ProgHOL 64 :=
  .dec lK .one (.var .global gKb) (.dec lL .one (vv pLen) (withGeoV pG (.seq probeV (.return (.const 0)))))

variable {σ : Type}

/-- A memo probe's outcome from `t`: the row's `1 + i`, or `0` on a miss; memory and fixed parts as in `t`. -/
def MPRes {α δ : Type} [BEq α] [Hashable α] (t : PState σ) (tb : Tbl α Nat δ) (x : α)
    (r : Option (PanSemResultExact 64) × PState σ) : Prop :=
  Stop r.1 ∨ (r.2.memory = t.memory ∧ r.2.memaddrs = t.memaddrs ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    ((∃ i, tb.find? x = some i ∧ r.1 = some (.returned (.val (.word (1 + BitVec.ofNat 64 i))))) ∨
     (tb.find? x = none ∧ r.1 = some (.returned (.val (.word 0))))))

theorem mpres_restore {α δ : Type} [BEq α] [Hashable α] {s : PState σ} {tb : Tbl α Nat δ} {x : α} (y : MlS)
    (v : BitVec 64) (r : Option (PanSemResultExact 64) × PState σ)
    (h : MPRes (setVarHOLFinite y (.val (.word v)) s) tb x r) :
    MPRes s tb x (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (y, s.locals.lookup y) }) := by
  rcases h with h | ⟨m, d, c, g, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, d, c, g, h⟩

theorem memoProbe_spec {α δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]
    (t : PState σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hinj : ∀ x y, enc x = enc y → x = y) (tb : Tbl α Nat δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (hu : Nat) (g : VGeo) (G KB : BitVec 64) (x : α) (hxl : (enc x).length < 2 ^ 61)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30)
    (hT : VT t enc rows ders slots g hu) (hinv : ConsModel.Inv (α := α) (homeV enc g.b) rows slots g.n)
    (hrel : TblRel tb rows id) (hK : Words t KB (enc x)) (hdesc : DescV t G g 1)
    (hgk : t.globals.lookup gKb = some (.val (.word KB))) (hg : t.locals.lookup pG = some (.val (.word G)))
    (hl : t.locals.lookup pLen = some (.val (.word (BitVec.ofNat 64 (enc x).length)))) :
    MPRes t tb x (evaluateHOLFiniteState t memoProbeBody) := by
  unfold memoProbeBody
  rw [dec_word_eq t lK _ KB _ (eval_gv t gKb KB hgk)]
  refine mpres_restore lK KB _ ?_
  let t1 := setVarHOLFinite lK (.val (.word KB)) t
  rw [dec_word_eq t1 lL (vv pLen) (BitVec.ofNat 64 (enc x).length) _ (eval_vv t1 pLen _ (by lk [t1]; exact hl))]
  refine mpres_restore lL (BitVec.ofNat 64 (enc x).length) _ ?_
  let t2 := setVarHOLFinite lL (.val (.word (BitVec.ofNat 64 (enc x).length))) t1
  have hd2 : DescV t2 G g 1 := hdesc
  apply withGeoV_lift (fun s r => MPRes s tb x r) (fun s y v r h => mpres_restore y v r h) t2 pG G g 1 _
    (by lk [t2, t1]; exact hg) (by decide) hd2
  let u := geoStateV t2 g 1
  have hP := probeV_spec u enc (fun i => 1 + BitVec.ofNat 64 i) id 1 (2 ^ 30) (fun i _ => rfl) hinj tb rows ders slots hu
    g x KB hn hb hcap (Nat.le_of_lt hcap) (vt_frame hT (fun _ _ => rfl) rfl) hinv hrel (fun j hj => hK j hj)
    hxl (by simp only [u, geoStateV]; lk [t2, t1]) (by simp only [u, geoStateV]; lk [t2])
    (by simp only [u, geoStateV]; lk) (by simp only [u, geoStateV]; lk) (by simp only [u, geoStateV]; lk)
    (by simp only [u, geoStateV]; lk)
  rcases hP with hs | ⟨m, d, c, gl, _, ⟨i, hf, hr⟩ | ⟨hf, hr, _⟩⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  · rw [seq_abort _ _ _ _ hr]
    exact Or.inr ⟨m, d, c, gl, Or.inl ⟨i, hf, hr⟩⟩
  · have e : evaluateHOLFiniteState u probeV = (none, (evaluateHOLFiniteState u probeV).2) := by rw [← hr]
    rw [seq_normal _ e]
    have er := return_word (evaluateHOLFiniteState u probeV).2 (.const 0) 0 (eval_const _ 0)
    have es := return_state (evaluateHOLFiniteState u probeV).2 (.const 0) 0 (eval_const _ 0)
    refine Or.inr ⟨by rw [es]; exact m, by rw [es]; exact d, by rw [es]; exact c, by rw [es]; exact gl,
      Or.inr ⟨hf, er⟩⟩

section
variable {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V] {enc : K → List (BitVec 64)}
  {valW : V → BitVec 64}

/-- A hit's value word: row `i` of the key holds the memo's answer at `D + 16 i`. -/
theorem memo_value {t : PState σ} {g : VGeo} {m : Std.HashMap K V} {tb : Tbl K Nat V}
    {rows : List K} {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {hu : Nat}
    (hT : VT t enc rows ders slots g hu) (hr : TblRel tb rows id) (hder : tb.der.toList.map (dWG valW) = ders)
    (hrel : MemoRel m tb) (k : K) (i : Nat) (hf : tb.find? k = some i) :
    i < g.cap ∧ ∃ v, m[k]? = some v ∧ t.memaddrs (g.D + BitVec.ofNat 64 (16 * i)) ∧
      t.memory (g.D + BitVec.ofNat 64 (16 * i)) = .word (valW v) := by
  have hil : i < rows.length := by
    have := hr.cons k
    simp only [Tbl.find?] at hf
    rw [hf] at this
    cases e : rows.findIdx? (· = k) with
    | none => rw [e] at this; simp at this
    | some j =>
      rw [e] at this; simp at this; subst this
      exact (List.findIdx?_eq_some_iff_getElem.mp e).1
  have hle := hT.le
  obtain ⟨a1, _, a3, _⟩ := hT.der i hil
  have hsz : tb.der.size = rows.length := by
    have := congrArg List.length hder; simp at this; rw [this, hT.dlen]
  have hdi : ders[i]'(by rw [hT.dlen]; exact hil) = (dWG valW) (tb.derAt i) := by
    simp only [← hder, List.getElem_map, Array.getElem_toList, Tbl.derAt, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show i < tb.der.size by omega), Option.getD_some]
  refine ⟨by omega, tb.derAt i, by rw [hrel k, hf]; rfl, a1, by rw [a3, hdi]; rfl⟩

/-! ## `memoGet` -/

def fMemoGet := ofString "memoGet"
def lMx := ofString "mx"
def lMd := ofString "mdd"

/-- `memoGet(g, len)`: `1 +` the memo's answer for the key in the key buffer, or `0`. -/
def memoGetBody : ProgHOL 64 :=
  .dec lMx .one (.const 0) (.seq (.call (some (some (.local, lMx), none)) fMemoProbe [vv pG, vv pLen])
    (.ite (vv lMx)
      (.dec lMd .one (.load .one (.op .add [vv pG, .const 40]))
        (.return (.op .add [.load .one (.op .add [vv lMd, .shift .lsl (.op .sub [vv lMx, .const 1]) (.const 4)]),
          .const 1])))
      (.return (.const 0))))

/-- A memo answer as `memoGet` returns it. -/
def optWG {V : Type} (valW : V → BitVec 64) : Option V → BitVec 64
  | some v => valW v + 1
  | none => 0

abbrev optW : Option EIdx → BitVec 64 := optWG Enc.idxW

theorem idxW_add_one_ne (v : EIdx) : Enc.idxW v + 1 ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  have hl : (Enc.idxW v).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact v.word.toNat_lt
  simp [BitVec.toNat_add] at this; omega

theorem one_add_ne (i : Nat) (hi : i < 2 ^ 30) : (1 : BitVec 64) + BitVec.ofNat 64 i ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this; omega

theorem memoGet_spec {α : Type} (G KB : BitVec 64) (g : VGeo) (hinj : ∀ x y, enc x = enc y → x = y) (m : Std.HashMap K V) (k : K)
    (s : AState) (u : PState σ)
    (hm : MemoAtG enc valW u G g m) (hK : Words u KB (enc k)) (hkl : (enc k).length < 2 ^ 61)
    (hgk : u.globals.lookup gKb = some (.val (.word KB)))
    (hpg : u.locals.lookup pG = some (.val (.word G)))
    (hpl : u.locals.lookup pLen = some (.val (.word (BitVec.ofNat 64 (enc k).length))))
    (hcode : u.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)) :
    SpecR (fun t => t = u) memoGetBody s (pure (m[k]?) : AM (Option V))
      (fun a w s' st => s' = s ∧ w = optWG valW a ∧ st.memory = u.memory ∧ st.memaddrs = u.memaddrs ∧
        st.globals = u.globals ∧ st.code = u.code) := by
  obtain ⟨hdesc, hn, hb, hcap, tb, rows, ders, slots, hu, hT, hinv, hr, hder, hrel⟩ := hm
  intro t ht
  subst ht
  unfold memoGetBody
  rw [dec_word_eq t lMx _ 0 _ (eval_const t 0)]
  let t1 := setVarHOLFinite lMx (.val (.word 0)) t
  -- the probe
  have hc := spec_call2 (P := (· = t1)) (s := s) (m := (pure () : AM Unit))
    (Q := fun _ s' t' => s' = s ∧ t'.memory = t.memory ∧ t'.memaddrs = t.memaddrs ∧ t'.globals = t.globals ∧
      t'.code = t.code ∧ (∀ y, y ≠ lMx → t'.locals.lookup y = t1.locals.lookup y) ∧
      ((∃ i, tb.find? k = some i ∧ t'.locals.lookup lMx = some (.val (.word (1 + BitVec.ofNat 64 i)))) ∨
       (tb.find? k = none ∧ t'.locals.lookup lMx = some (.val (.word 0)))))
    lMx fMemoProbe pG pLen (by decide) (vv pG) (vv pLen) memoProbeBody (fun _ => G)
    (fun _ => BitVec.ofNat 64 (enc k).length) (fun v hv => by rw [hv]; exact hcode)
    (fun v hv => by rw [hv]; exact eval_vv _ pG _ (by lk [t1]; exact hpg))
    (fun v hv => by rw [hv]; exact eval_vv _ pLen _ (by lk [t1]; exact hpl))
    (fun v hv => ⟨0, by rw [hv]; exact lookup_setVar_same _ _ _⟩)
    (fun _ _ w s' st => s' = s ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧ st.globals = t.globals ∧
      st.code = t.code ∧
      ((∃ i, tb.find? k = some i ∧ w = 1 + BitVec.ofNat 64 i) ∨ (tb.find? k = none ∧ w = 0)))
    (fun v hv callee h1 h2 x hx => by
      subst hv hx
      have P := memoProbe_spec (callEntryStateHOLFinite t1 callee) enc (dWG valW) hinj tb rows ders slots hu g G KB
        k hkl hn hb hcap (vt_frame hT (fun _ _ => rfl) rfl) hinv hr (fun j hj => hK j hj) hdesc hgk h1 h2
      rcases P with hs | ⟨m1, d1, c1, g1, ⟨i, hf, hr'⟩ | ⟨hf, hr'⟩⟩
      · exact Or.inl hs
      · exact Or.inr ⟨_, hr', (), s, rfl, rfl, m1, d1, g1, c1, Or.inl ⟨i, hf, rfl⟩⟩
      · exact Or.inr ⟨_, hr', (), s, rfl, rfl, m1, d1, g1, c1, Or.inr ⟨hf, rfl⟩⟩)
    (fun v hv _ w s' st ⟨hs, m1, d1, g1, c1, hw⟩ => by
      subst hv
      refine ⟨hs, by simp [setKvarHOLFinite, setVarHOLFinite, m1], by simp [setKvarHOLFinite, setVarHOLFinite, d1],
        by simp [setKvarHOLFinite, setVarHOLFinite, g1], by simp [setKvarHOLFinite, setVarHOLFinite, c1],
        fun y hy => by simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ hy], ?_⟩
      rcases hw with ⟨i, hf, rfl⟩ | ⟨hf, rfl⟩
      · exact Or.inl ⟨i, hf, by simp only [setKvarHOLFinite]; exact lookup_setVar_same _ _ _⟩
      · exact Or.inr ⟨hf, by simp only [setKvarHOLFinite]; exact lookup_setVar_same _ _ _⟩)
  rcases hc t1 rfl with hs | ⟨hn1, _, s1, _, hq⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  obtain ⟨hs1, m2, d2, g2, c2, fr2, hres⟩ := hq
  subst s1
  have e := (show evaluateHOLFiniteState t1 (.call (some (some (.local, lMx), none)) fMemoProbe [vv pG, vv pLen]) =
    (none, (evaluateHOLFiniteState t1 (.call (some (some (.local, lMx), none)) fMemoProbe [vv pG, vv pLen])).2) by
      rw [← hn1])
  rw [seq_normal _ e]
  generalize (evaluateHOLFiniteState t1 (.call (some (some (.local, lMx), none)) fMemoProbe [vv pG, vv pLen])).2 = t2
    at m2 d2 g2 c2 fr2 hres
  have hpg2 : t2.locals.lookup pG = some (.val (.word G)) := by rw [fr2 _ (by decide)]; lk [t1]; exact hpg
  rcases hres with ⟨i, hf, hx⟩ | ⟨hf, hx⟩
  · obtain ⟨hic, v, hv, ha, hmv⟩ := memo_value hT hr hder hrel k i hf
    have hle := hT.le
    rw [ite_word t2 _ _ _ _ (eval_vv t2 lMx _ hx), if_pos (one_add_ne i (by omega))]
    have hD : EV t2 (.load .one (.op .add [vv pG, .const 40])) = some (.val (.word g.D)) := by
      have h5 := hdesc 5 (by decide)
      unfold EV
      rw [eval_load_word t2 _ _ (eval_add2 t2 _ _ _ _ (eval_vv t2 pG _ hpg2) (eval_const t2 _))
        (by rw [d2]; exact h5.1), m2]
      show some (ValueHOL.val (t.memory (G + BitVec.ofNat 64 (8 * 5)))) = _
      rw [h5.2]; rfl
    rw [dec_word_eq t2 lMd _ g.D _ hD]
    let t3 := setVarHOLFinite lMd (.val (.word g.D)) t2
    have hadr : (1 + BitVec.ofNat 64 i - 1) <<< (4 : BitVec 64).toNat = BitVec.ofNat 64 (16 * i) := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)]
    have hA : EV t3 (.op .add [vv lMd, .shift .lsl (.op .sub [vv lMx, .const 1]) (.const 4)]) =
        some (.val (.word (g.D + BitVec.ofNat 64 (16 * i)))) := by
      rw [← hadr]
      exact eval_add2 t3 _ _ _ _ (eval_vv t3 lMd _ (lookup_setVar_same _ _ _))
        (eval_shl t3 _ _ _ (eval_sub2 t3 _ _ _ _ (eval_vv t3 lMx _ (by lk [t3]; exact hx)) (eval_const t3 1))
          (by decide))
    have hl := eval_load_word t3 _ _ hA (by show t2.memaddrs _; rw [d2]; exact ha)
    rw [show t3.memory (g.D + BitVec.ofNat 64 (16 * i)) = .word (valW v) by
      show t2.memory _ = _; rw [m2]; exact hmv] at hl
    have hv3 : EV t3 (.op .add [.load .one (.op .add [vv lMd, .shift .lsl (.op .sub [vv lMx, .const 1]) (.const 4)]),
        .const 1]) = some (.val (.word (valW v + 1))) := eval_add2 t3 _ _ _ _ hl (eval_const t3 1)
    right
    refine ⟨valW v + 1, by rw [return_word t3 _ _ hv3], some v, s, by rw [hv]; rfl, rfl, rfl, ?_⟩
    rw [return_state t3 _ _ hv3]
    exact ⟨m2, d2, g2, c2⟩
  · have hnone : m[k]? = none := by rw [hrel k, hf]; rfl
    rw [ite_word t2 _ _ _ _ (eval_vv t2 lMx _ hx), if_neg (by simp)]
    right
    refine ⟨0, by rw [return_word t2 _ _ (eval_const t2 0)], none, s, by rw [hnone]; rfl, rfl, rfl, ?_⟩
    rw [return_state t2 _ _ (eval_const t2 0)]
    exact ⟨m2, d2, g2, c2⟩

/-! ## `memoIns`: intern the key, the value as its derived word -/

def pVal := ofString "mval"
def fMemoIns := ofString "memoIns"

/-- `memoIns(g, len, val)`: the row of the key in the key buffer (appended with `val` if new), as `1 + i`. -/
def memoInsBody : ProgHOL 64 :=
  .dec lK .one (.var .global gKb) (.dec lL .one (vv pLen) (.dec lDv .one (vv pVal) (.dec lDv2 .one (.const 0)
    (withGeoV pG internV))))

theorem vres_restore {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] {s : PState σ}
    {enc : α → List (BitVec 64)} {dW : V → BitVec 64 × BitVec 64} {hwd : Nat → BitVec 64} {mkI : Nat → Nat}
    {tb : Tbl α Nat V} {g : VGeo} {x : α} {d : V} (y : MlS) (v : BitVec 64)
    (r : Option (PanSemResultExact 64) × PState σ)
    (h : VRes (setVarHOLFinite y (.val (.word v)) s) enc dW hwd mkI tb g x d r) :
    VRes s enc dW hwd mkI tb g x d (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (y, s.locals.lookup y) }) := by
  rcases h with h | ⟨hr, rows', ders', slots', hu', hT, hi, hrel, hd, c1, c2, c3, c4, c5⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr, rows', ders', slots', hu', vt_of_eq hT rfl rfl, hi, hrel, hd, c1, c2, c3, c4, c5⟩

theorem memoIns_spec (t : PState σ) (hinj : ∀ x y, enc x = enc y → x = y) (tb : Tbl K Nat V) (rows : List K)
    (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat) (g : VGeo) (G KB : BitVec 64)
    (k : K) (v : V) (hkl : (enc k).length < 2 ^ 61)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30)
    (hT : VT t enc rows ders slots g hu) (hinv : ConsModel.Inv (homeV enc g.b) rows slots g.n)
    (hrel : TblRel tb rows id) (hder : tb.der.toList.map (dWG valW) = ders)
    (hK : Words t KB (enc k)) (hKout : ∀ i, i < (enc k).length → ¬ inR g (KB + BitVec.ofNat 64 (8 * i)))
    (hdesc : DescV t G g 1)
    (hgk : t.globals.lookup gKb = some (.val (.word KB))) (hg : t.locals.lookup pG = some (.val (.word G)))
    (hl : t.locals.lookup pLen = some (.val (.word (BitVec.ofNat 64 (enc k).length))))
    (hv : t.locals.lookup pVal = some (.val (.word (valW v)))) :
    VRes t enc (dWG valW) (fun i => 1 + BitVec.ofNat 64 i) id tb g k v (evaluateHOLFiniteState t memoInsBody) := by
  unfold memoInsBody
  rw [dec_word_eq t lK _ KB _ (eval_gv t gKb KB hgk)]
  refine vres_restore lK KB _ ?_
  let t1 := setVarHOLFinite lK (.val (.word KB)) t
  rw [dec_word_eq t1 lL (vv pLen) (BitVec.ofNat 64 (enc k).length) _ (eval_vv t1 pLen _ (by lk [t1]; exact hl))]
  refine vres_restore lL (BitVec.ofNat 64 (enc k).length) _ ?_
  let t2 := setVarHOLFinite lL (.val (.word (BitVec.ofNat 64 (enc k).length))) t1
  rw [dec_word_eq t2 lDv (vv pVal) (valW v) _ (eval_vv t2 pVal _ (by lk [t2, t1]; exact hv))]
  refine vres_restore lDv (valW v) _ ?_
  let t3 := setVarHOLFinite lDv (.val (.word (valW v))) t2
  rw [dec_word_eq t3 lDv2 (.const 0) 0 _ (eval_const t3 0)]
  refine vres_restore lDv2 0 _ ?_
  let t4 := setVarHOLFinite lDv2 (.val (.word 0)) t3
  have hd4 : DescV t4 G g 1 := hdesc
  apply withGeoV_lift (fun s r => VRes s enc (dWG valW) (fun i => 1 + BitVec.ofNat 64 i) id tb g k v r)
    (fun s y w r h => vres_restore y w r h) t4 pG G g 1 _ (by lk [t4, t3, t2, t1]; exact hg) (by decide) hd4
  let u := geoStateV t4 g 1
  exact internV_spec u enc (dWG valW) (fun i => 1 + BitVec.ofNat 64 i) id 1 (2 ^ 30) (fun i _ => rfl) hinj tb rows
    ders slots hu g k v KB hn hb hcap (Nat.le_of_lt hcap) (vt_frame hT (fun _ _ => rfl) rfl) hinv hrel hder
    (fun j hj => hK j hj) hkl hKout
    (by simp only [u, geoStateV]; lk [t4, t3, t2, t1]) (by simp only [u, geoStateV]; lk [t4, t3, t2])
    (by simp only [u, geoStateV]; lk) (by simp only [u, geoStateV]; lk) (by simp only [u, geoStateV]; lk)
    (by simp only [u, geoStateV]; lk) (by simp only [u, geoStateV]; lk) (by simp only [u, geoStateV]; lk)
    (by simp only [u, geoStateV]; lk [t4, t3]; rfl) (by simp only [u, geoStateV]; lk [t4]; rfl)
    (by simp only [u, geoStateV]; lk) (by simp only [u, geoStateV]; lk)

/-! ## `memoSet` -/

def fMemoSet := ofString "memoSet"

/-- `memoSet(g, len, val)`: record `val` for the key in the key buffer (overwriting). -/
def memoSetBody : ProgHOL 64 :=
  .dec lMx .one (.const 0) (.seq (.call (some (some (.local, lMx), none)) fMemoIns [vv pG, vv pLen, vv pVal])
    (.dec lMd .one (.load .one (.op .add [vv pG, .const 40]))
      (.seq (.store (.op .add [vv lMd, .shift .lsl (.op .sub [vv lMx, .const 1]) (.const 4)]) (vv pVal))
        (.return (.const 0)))))

theorem tierInt_find_self {α : Type} [BEq α] [LawfulBEq α] [Hashable α] (tb : Tbl α Nat V) (k : α) (v : V) :
    (tierInt tb k v id).1.find? k = some (tierInt tb k v id).2 := by
  unfold tierInt
  cases h : tb.find? k with
  | some i => simp [h]
  | none => simp [Tbl.find?, Tbl.push, Std.HashMap.getElem?_insert]

theorem idx_lt_of_find {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] {tb : Tbl α Nat V}
    {rows : List α} (hr : TblRel tb rows id) {k : α} {i : Nat} (hf : tb.find? k = some i) : i < rows.length := by
  have := hr.cons k
  simp only [Tbl.find?] at hf
  rw [hf] at this
  cases e : rows.findIdx? (· = k) with
  | none => rw [e] at this; simp at this
  | some j =>
    rw [e] at this; simp at this; subst this
    exact (List.findIdx?_eq_some_iff_getElem.mp e).1

theorem der_map_setDer {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
    {valW : V → BitVec 64} (tb : Tbl K Nat V) (ders : List (BitVec 64 × BitVec 64))
    (hd : tb.der.toList.map (dWG valW) = ders) (i : Nat) (hi : i < ders.length) (v : V) :
    (Tbl.setDer tb i v).der.toList.map (dWG valW) = ders.set i (valW v, (ders[i]'hi).2) := by
  subst hd
  simp only [Tbl.setDer, Array.set!, Array.toList_setIfInBounds, List.map_set]
  simp [dWG]

theorem memoSet_spec (G KB : BitVec 64) (g : VGeo) (hinj : ∀ x y, enc x = enc y → x = y) (m : Std.HashMap K V) (k : K) (v : V)
    (s : AState) (u : PState σ)
    (hm : MemoAtG enc valW u G g m) (hK : Words u KB (enc k)) (hkl : (enc k).length < 2 ^ 61)
    (hKout : ∀ i, i < (enc k).length → ¬ inR g (KB + BitVec.ofNat 64 (8 * i)))
    (hGout : ∀ j, j < 8 → ¬ inR g (G + BitVec.ofNat 64 (8 * j)))
    (hgk : u.globals.lookup gKb = some (.val (.word KB)))
    (hpg : u.locals.lookup pG = some (.val (.word G)))
    (hpl : u.locals.lookup pLen = some (.val (.word (BitVec.ofNat 64 (enc k).length))))
    (hpv : u.locals.lookup pVal = some (.val (.word (valW v))))
    (hcode : u.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)) :
    SpecR (fun t => t = u) memoSetBody s (pure () : AM Unit)
      (fun _ _ s' st => s' = s ∧ MemoAtG enc valW st G g (m.insert k v) ∧ (∀ c, ¬ inR g c → st.memory c = u.memory c) ∧
        st.memaddrs = u.memaddrs ∧ st.globals = u.globals ∧ st.code = u.code) := by
  obtain ⟨hdesc, hn, hb, hcap, tb, rows, ders, slots, hu, hT, hinv, hr, hder, hrel⟩ := hm
  intro t ht
  subst ht
  unfold memoSetBody
  rw [dec_word_eq t lMx _ 0 _ (eval_const t 0)]
  let t1 := setVarHOLFinite lMx (.val (.word 0)) t
  let i' := (tierInt tb k v id).2
  let tb' := (tierInt tb k v id).1
  have hc := spec_call3 (P := (· = t1)) (s := s) (m := (pure () : AM Unit))
    (Q := fun _ s' t' => s' = s ∧ t'.memaddrs = t.memaddrs ∧ t'.globals = t.globals ∧ t'.code = t.code ∧
      (∀ c, ¬ inR g c → t'.memory c = t.memory c) ∧
      (∀ y, y ≠ lMx → t'.locals.lookup y = t1.locals.lookup y) ∧
      t'.locals.lookup lMx = some (.val (.word (1 + BitVec.ofNat 64 i'))) ∧
      ∃ rows' ders' slots' hu', VT t' enc rows' ders' slots' g hu' ∧
        ConsModel.Inv (homeV enc g.b) rows' slots' g.n ∧ TblRel tb' rows' id ∧ tb'.der.toList.map (dWG valW) = ders')
    lMx fMemoIns pG pLen pVal (by decide) (by decide) (by decide) (vv pG) (vv pLen) (vv pVal) memoInsBody
    (fun _ => G) (fun _ => BitVec.ofNat 64 (enc k).length) (fun _ => valW v)
    (fun w hw => by rw [hw]; exact hcode)
    (fun w hw => by rw [hw]; exact eval_vv _ pG _ (by lk [t1]; exact hpg))
    (fun w hw => by rw [hw]; exact eval_vv _ pLen _ (by lk [t1]; exact hpl))
    (fun w hw => by rw [hw]; exact eval_vv _ pVal _ (by lk [t1]; exact hpv))
    (fun w hw => ⟨0, by rw [hw]; exact lookup_setVar_same _ _ _⟩)
    (fun _ _ w s' st => s' = s ∧ w = 1 + BitVec.ofNat 64 i' ∧ st.memaddrs = t.memaddrs ∧ st.globals = t.globals ∧
      st.code = t.code ∧ (∀ c, ¬ inR g c → st.memory c = t.memory c) ∧
      ∃ rows' ders' slots' hu', VT st enc rows' ders' slots' g hu' ∧
        ConsModel.Inv (homeV enc g.b) rows' slots' g.n ∧ TblRel tb' rows' id ∧ tb'.der.toList.map (dWG valW) = ders')
    (fun w hw callee h1 h2 h3 x hx => by
      subst hw hx
      rcases memoIns_spec (callEntryStateHOLFinite t1 callee) hinj tb rows ders slots hu g G KB k v hkl hn hb hcap
          (vt_frame hT (fun _ _ => rfl) rfl) hinv hr hder (fun j hj => hK j hj) hKout hdesc hgk h1 h2 h3 with
        hs | ⟨hr', rows', ders', slots', hu', hT', hi', hrel', hd', c1, c2, c3, _, c5⟩
      · exact Or.inl hs
      · exact Or.inr ⟨_, hr', (), s, rfl, rfl, rfl, c3, c2, c1, c5, rows', ders', slots', hu', hT', hi', hrel', hd'⟩)
    (fun w hw _ x s' st ⟨hs, hx, d1, g1, c1, m1, rows', ders', slots', hu', hT', hi', hrel', hd'⟩ => by
      subst hw hx
      refine ⟨hs, by simp [setKvarHOLFinite, setVarHOLFinite, d1], by simp [setKvarHOLFinite, setVarHOLFinite, g1],
        by simp [setKvarHOLFinite, setVarHOLFinite, c1], fun c hc => by simp [setKvarHOLFinite, setVarHOLFinite, m1 c hc],
        fun y hy => by simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ hy],
        by simp only [setKvarHOLFinite]; exact lookup_setVar_same _ _ _, rows', ders', slots', hu',
        vt_of_eq hT' rfl rfl, hi', hrel', hd'⟩)
  rcases hc t1 rfl with hs | ⟨hn1, _, s1, _, hq⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  obtain ⟨hs1, d2, g2, c2, m2, fr2, hx2, rows', ders', slots', hu', hT', hi', hrel', hd'⟩ := hq
  subst s1
  have e := (show evaluateHOLFiniteState t1 (.call (some (some (.local, lMx), none)) fMemoIns [vv pG, vv pLen, vv pVal]) =
    (none, (evaluateHOLFiniteState t1 (.call (some (some (.local, lMx), none)) fMemoIns [vv pG, vv pLen, vv pVal])).2) by
      rw [← hn1])
  rw [seq_normal _ e]
  generalize (evaluateHOLFiniteState t1 (.call (some (some (.local, lMx), none)) fMemoIns [vv pG, vv pLen, vv pVal])).2 = t2
    at d2 g2 c2 m2 fr2 hx2 hT' 
  have hpg2 : t2.locals.lookup pG = some (.val (.word G)) := by rw [fr2 _ (by decide)]; lk [t1]; exact hpg
  have hpv2 : t2.locals.lookup pVal = some (.val (.word (valW v)))  := by rw [fr2 _ (by decide)]; lk [t1]; exact hpv
  have hil : i' < rows'.length := idx_lt_of_find hrel' (tierInt_find_self tb k v)
  have hle := hT'.le
  have hD : EV t2 (.load .one (.op .add [vv pG, .const 40])) = some (.val (.word g.D)) := by
    have h5 := hdesc 5 (by decide)
    unfold EV
    rw [eval_load_word t2 _ _ (eval_add2 t2 _ _ _ _ (eval_vv t2 pG _ hpg2) (eval_const t2 _))
      (by rw [d2]; exact h5.1)]
    show some (ValueHOL.val (t2.memory (G + BitVec.ofNat 64 (8 * 5)))) = _
    rw [m2 _ (hGout 5 (by decide)), h5.2]; rfl
  rw [dec_word_eq t2 lMd _ g.D _ hD]
  let t3 := setVarHOLFinite lMd (.val (.word g.D)) t2
  have hadr : (1 + BitVec.ofNat 64 i' - 1) <<< (4 : BitVec 64).toNat = BitVec.ofNat 64 (16 * i') := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)]
  have hA : EV t3 (.op .add [vv lMd, .shift .lsl (.op .sub [vv lMx, .const 1]) (.const 4)]) =
      some (.val (.word (g.D + BitVec.ofNat 64 (16 * i')))) := by
    rw [← hadr]
    exact eval_add2 t3 _ _ _ _ (eval_vv t3 lMd _ (lookup_setVar_same _ _ _))
      (eval_shl t3 _ _ _ (eval_sub2 t3 _ _ _ _ (eval_vv t3 lMx _ (by lk [t3]; exact hx2)) (eval_const t3 1)) (by decide))
  obtain ⟨da, _, _, _⟩ := hT'.der i' hil
  rw [seq_normal _ (store_word t3 _ _ _ (valW v) hA (eval_vv t3 pVal _ (by lk [t3]; exact hpv2))
    (by show t2.memaddrs _; exact da))]
  let t4 : PState σ :=
    { t3 with memory := fun c => (if c = g.D + BitVec.ofNat 64 (16 * i') then HolWordLab.word (valW v) else t3.memory c) }
  have hr4 := return_word t4 (.const 0) 0 (eval_const t4 0)
  have hs4 := return_state t4 (.const 0) 0 (eval_const t4 0)
  right
  refine ⟨0, hr4, (), s, rfl, rfl, ?_⟩
  rw [hs4]
  have hdl : i' < ders'.length := by rw [hT'.dlen]; exact hil
  have hd2 : (ders'[i']'hdl).2 = 0 := by
    have := congrArg (fun l => (l[i']?).map Prod.snd) hd'
    simp only [List.getElem?_map, Array.getElem?_toList] at this
    rw [List.getElem?_eq_getElem hdl] at this
    cases e : tb'.der[i']? with
    | none => rw [e] at this; simp at this
    | some w => rw [e] at this; simp [dWG] at this; exact this.symm
  have hVT := vt_setDer hT' i' hil (valW v)
  rw [hd2] at hVT
  have hmi := memoRel_insert m tb rows hrel hr hinv.rows_nodup (by
    have := congrArg List.length hder; simp at this; rw [this, hT.dlen]) k v
  refine ⟨⟨fun j hj => ?_, hn, hb, hcap, Tbl.setDer tb' i' v, rows', ders'.set i' (valW v, 0), slots', hu',
    vt_of_eq hVT rfl rfl, hi', ⟨by simp [Tbl.setDer]; exact hrel'.nodes, fun a => hrel'.cons a⟩, ?_, hmi.1⟩,
    fun c hc => ?_, d2, g2, c2⟩
  · have hj' := hdesc j hj
    refine ⟨by show t2.memaddrs _; rw [d2]; exact hj'.1, ?_⟩
    show (if G + BitVec.ofNat 64 (8 * j) = g.D + BitVec.ofNat 64 (16 * i') then _ else t2.memory _) = _
    have hin : inR g (g.D + BitVec.ofNat 64 (16 * i')) := by
      have lD := hT'.layD; have lR := hT'.layR; have lC := hT'.layC; have lS := hT'.layS; have lK := hT'.layK
      refine ⟨?_, ?_⟩ <;> rw [toNat_add_of_lt _ _ (by omega)] <;> omega
    rw [if_neg (fun e => hGout j hj (by rw [e]; exact hin)), m2 _ (hGout j hj)]; exact hj'.2
  · have := der_map_setDer tb' ders' hd' i' hdl v
    rw [hd2] at this; exact this
  · show (if c = g.D + BitVec.ofNat 64 (16 * i') then _ else t2.memory c) = _
    have hin : inR g (g.D + BitVec.ofNat 64 (16 * i')) := by
      have lD := hT'.layD; have lR := hT'.layR; have lC := hT'.layC; have lS := hT'.layS; have lK := hT'.layK
      refine ⟨?_, ?_⟩ <;> rw [toNat_add_of_lt _ _ (by omega)] <;> omega
    rw [if_neg (fun e => hc (by rw [e]; exact hin)), m2 c hc]

/-! ## The twin's `inst1Get`, in a caller -/

end

/-- The key length word `1 + (d ≠ 0)`. -/
def lenE (ed : ExpHOL 64) : ExpHOL 64 := .op .add [.const 1, .cmp .notEqual ed (.const 0)]

theorem sev_lenE (Γ : Env) (ed : ExpHOL 64) (d : Nat) (hd : d < 2 ^ 63) (he : sev Γ ed = some (BitVec.ofNat 64 d))
    (h : EIdx) : sev Γ (lenE ed) = some (BitVec.ofNat 64 (encMemo (h, d)).length) := by
  simp only [lenE, sev, he]
  simp only [encMemo, List.length_cons, limbs_small d (by omega)]
  by_cases h0 : d = 0
  · subst h0; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : BitVec.ofNat 64 d ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]

theorem inst1Get_run (k : EIdx × Nat) (s : AState) : inst1Get k s = .ok ((memoSel .inst1 s.memos)[k]?, s) := rfl

/-- A twin memo read of memo `mk`, in a caller. -/
theorem specR_memoGetI {β : Type} {C : Ctx} (hok : CtxOK C) (mk : MemoK) (getOp : EIdx × Nat → AM (Option EIdx))
    (hget : ∀ key s, getOp key s = .ok ((memoSel mk s.memos)[key]?, s))
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Option EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eh ed : ExpHOL 64) (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (hx : x ∈ D)
    (heh : sev Γ eh = some (Enc.idxW h)) (hed : sev Γ ed = some (BitVec.ofNat 64 d)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ r, SpecR (Inv C s ((x, optW r) :: Γ) [] D) rest s (k r) R) :
    SpecR (Inv C s Γ M D)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eh)
        (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) ed)
          (.seq (.call (some (some (.local, x), none)) fMemoGet [.const (C.mG mk), lenE ed]) rest)))
      s (getOp (h, d) >>= k) R := by
  refine specR_storeKB2I hok eh ed (Enc.idxW h) (BitVec.ofNat 64 d) heh hed hkb ?_
  refine specR_call2IM x fMemoGet pG pLen (by decide) (.const (C.mG mk)) (lenE ed) memoGetBody (C.mG mk)
    (BitVec.ofNat 64 (encMemo (h, d)).length) hx hcodeG rfl (sev_lenE _ ed d hd hed h)
    (fun a w s' st => s' = s ∧ w = optW a ∧ SR C s st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2.2)
    (fun u hsr hM h1 h2 => ?_) (fun a w s' st hp => by obtain ⟨rfl, rfl, _⟩ := hp; exact hk a)
  have hW : Words u C.KB (encMemo (h, d)) := by
    intro j hj
    have hl : (encMemo (h, d)).length ≤ 2 := by
      simp only [encMemo, List.length_cons, limbs_small d (by omega)]; split <;> simp
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · have e0 : (encMemo (h, d))[0]'hj = Enc.idxW h := rfl
      rw [e0]; exact hM _ _ (by simp)
    · have h0 : d ≠ 0 := by
        intro e; subst e; simp [encMemo, Enc.limbs] at hj
      have e1 : (encMemo (h, d))[1]'hj = BitVec.ofNat 64 d := by
        simp only [encMemo, limbs_small d (by omega), h0, ite_false]; rfl
      rw [e1]; exact hM _ _ (by simp)
  have G := memoGet_spec (σ := σ) (α := Unit) (C.mG mk) C.KB (C.mg mk) encMemo_inj (memoSel mk s.memos) (h, d) s u (hsr.memo mk) hW
    (by simp only [encMemo, List.length_cons, limbs_small d (by omega)]; split <;> simp)
    hsr.gkb h1 h2 (by rw [hsr.code]; exact hcodeP)
  refine specR_congr (hget (h, d) s) (specR_mono G (fun v hv => hv) (fun a w s' st hp => ?_))
  obtain ⟨hs, hw, hm, hd', hg, hc⟩ := hp
  exact ⟨hs, hw, sr_of_eq hsr hm hd' hg hc⟩

/-! ## The twin's `inst1Set`, in a caller -/

theorem inst1Set_run (k : EIdx × Nat) (r : EIdx) (s : AState) :
    inst1Set k r s = .ok ((), { s with memos := memoUpd .inst1 s.memos ((memoSel .inst1 s.memos).insert k r) }) := rfl

/-- A twin memo insert into memo `mk`, in a caller. -/
theorem specR_memoSetI {β : Type} {C : Ctx} (hok : CtxOK C) (mk : MemoK) (setOp : EIdx × Nat → EIdx → AM Unit)
    (hset : ∀ key r s, setOp key r s =
      .ok ((), { s with memos := memoUpd mk s.memos ((memoSel mk s.memos).insert key r) }))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eh ed ev : ExpHOL 64) (h : EIdx) (d : Nat) (r : EIdx) (hd : d < 2 ^ 63) (hx : x ∈ D)
    (heh : sev Γ eh = some (Enc.idxW h)) (hed : sev Γ ed = some (BitVec.ofNat 64 d))
    (hev : sev Γ ev = some (Enc.idxW r)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv C { s with memos := memoUpd mk s.memos ((memoSel mk s.memos).insert (h, d) r) }
      ((x, w) :: Γ) [] D) rest { s with memos := memoUpd mk s.memos ((memoSel mk s.memos).insert (h, d) r) }
      (k ()) R) :
    SpecR (Inv C s Γ M D)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eh)
        (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) ed)
          (.seq (.call (some (some (.local, x), none)) fMemoSet [.const (C.mG mk), lenE ed, ev]) rest)))
      s (setOp (h, d) r >>= k) R := by
  let s' : AState := { s with memos := memoUpd mk s.memos ((memoSel mk s.memos).insert (h, d) r) }
  refine specR_storeKB2I hok eh ed (Enc.idxW h) (BitVec.ofNat 64 d) heh hed hkb ?_
  refine specR_call3IM x fMemoSet pG pLen pVal (by decide) (by decide) (by decide) (.const (C.mG mk)) (lenE ed) ev
    memoSetBody (C.mG mk) (BitVec.ofNat 64 (encMemo (h, d)).length) (Enc.idxW r) hx hcodeS rfl (sev_lenE _ ed d hd hed h) hev
    (fun _ _ s'' st => s'' = s' ∧ SR C s' st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2)
    (fun u hsr hM h1 h2 h3 => ?_) (fun a w s'' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk w)
  have hW : Words u C.KB (encMemo (h, d)) := by
    intro j hj
    have hl : (encMemo (h, d)).length ≤ 2 := by
      simp only [encMemo, List.length_cons, limbs_small d (by omega)]; split <;> simp
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · have e0 : (encMemo (h, d))[0]'hj = Enc.idxW h := rfl
      rw [e0]; exact hM _ _ (by simp)
    · have h0 : d ≠ 0 := by
        intro e; subst e; simp [encMemo, Enc.limbs] at hj
      have e1 : (encMemo (h, d))[1]'hj = BitVec.ofNat 64 d := by
        simp only [encMemo, limbs_small d (by omega), h0, ite_false]; rfl
      rw [e1]; exact hM _ _ (by simp)
  have hl2 : (encMemo (h, d)).length ≤ 2 := by
    simp only [encMemo, List.length_cons, limbs_small d (by omega)]; split <;> simp
  have hlen : (encMemo (h, d)).length < 2 ^ 61 := by omega
  have S := memoSet_spec (σ := σ) (C.mG mk) C.KB (C.mg mk) encMemo_inj (memoSel mk s.memos) (h, d) r s u (hsr.memo mk) hW hlen
    (fun j hj => hok.kbMemo mk j (by omega)) (fun j hj => hok.mdescMemo mk mk j hj) hsr.gkb h1 h2 h3
    (by rw [hsr.code]; exact hcodeI)
  intro t ht
  rcases S t ht with hs | ⟨w, hr, _, s'', _, hp⟩
  · exact Or.inl hs
  obtain ⟨_, hmem, hfr, hd', hg, hc⟩ := hp
  subst ht
  refine Or.inr ⟨w, hr, (), s', hset (h, d) r s, rfl, ⟨srep_frame hsr.rep ⟨hfr _ (hok.flMemo mk _ (Or.inl rfl)),
      hfr _ (hok.flMemo mk _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo mk _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo mk _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd'
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo mk kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut mk c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩),
    by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll, by rw [hg]; exact hsr.gfls,
    by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd']; exact hsr.kbuf j hj, fun mk' => ?_⟩⟩
  by_cases e : mk' = mk
  · subst e; show MemoAt _ _ _ (memoSel mk' (memoUpd mk' s.memos _)); rw [memoSel_upd_same]; exact hmem
  · show MemoAt _ _ _ (memoSel mk' (memoUpd mk s.memos _)); rw [memoSel_upd_ne mk mk' e]
    exact memoAt_frame (hsr.memo mk') (fun c hc => hfr c (hok.memoDis mk' mk c e hc))
      (fun kk hkk => hfr _ (hok.mdescMemo mk mk' kk hkk)) hd'

end ConPanqueque.T
