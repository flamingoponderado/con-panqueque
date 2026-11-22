import ConPanqueque.T.MemoModel
import ConPanqueque.T.Intern
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

/-- A memo's key: the handle, then the number's limbs (injective at every `Nat`). -/
def encMemo (k : EIdx × Nat) : List (BitVec 64) := Enc.idxW k.1 :: Enc.limbs k.2

theorem encMemo_inj : ∀ x y, encMemo x = encMemo y → x = y := by
  intro ⟨h, d⟩ ⟨h', d'⟩ e
  simp only [encMemo, List.cons.injEq] at e
  rw [Enc.idxW_inj e.1, Enc.limbs_inj e.2]

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

/-! ## The representation of a memo -/

def dWE (v : EIdx) : BitVec 64 × BitVec 64 := (Enc.idxW v, 0)

/-- The twin memo `m` is held at descriptor `G` with geometry `g`. -/
def MemoAt (t : PState σ) (G : BitVec 64) (g : VGeo) (m : Std.HashMap (EIdx × Nat) EIdx) : Prop :=
  DescV t G g 1 ∧ g.n = 2 ^ g.b ∧ g.b ≤ 56 ∧ g.cap < 2 ^ 30 ∧
  ∃ (tb : Tbl (EIdx × Nat) Nat EIdx) (rows : List (EIdx × Nat)) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (hu : Nat),
    VT t encMemo rows ders slots g hu ∧ ConsModel.Inv (homeV encMemo g.b) rows slots g.n ∧ TblRel tb rows id ∧
      tb.der.toList.map dWE = ders ∧ MemoRel m tb

theorem memoAt_frame {t u : PState σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap (EIdx × Nat) EIdx}
    (h : MemoAt t G g m) (hm : ∀ c, inR g c → u.memory c = t.memory c)
    (hdsc : ∀ k, k < 8 → u.memory (G + BitVec.ofNat 64 (8 * k)) = t.memory (G + BitVec.ofNat 64 (8 * k)))
    (hd : u.memaddrs = t.memaddrs) : MemoAt u G g m := by
  obtain ⟨hdesc, h1, h2, h3, tb, rows, ders, slots, hu, hT, hi, hr, hder, hrel⟩ := h
  exact ⟨fun k hk => by rw [hdsc k hk, hd]; exact hdesc k hk, h1, h2, h3, tb, rows, ders, slots, hu,
    vt_frame hT hm hd, hi, hr, hder, hrel⟩

theorem memoAt_of_eq {t u : PState σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap (EIdx × Nat) EIdx}
    (h : MemoAt t G g m) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) : MemoAt u G g m :=
  memoAt_frame h (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd

/-- A hit's value word: row `i` of the key holds the memo's answer at `D + 16 i`. -/
theorem memo_value {t : PState σ} {g : VGeo} {m : Std.HashMap (EIdx × Nat) EIdx} {tb : Tbl (EIdx × Nat) Nat EIdx}
    {rows : List (EIdx × Nat)} {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {hu : Nat}
    (hT : VT t encMemo rows ders slots g hu) (hr : TblRel tb rows id) (hder : tb.der.toList.map dWE = ders)
    (hrel : MemoRel m tb) (k : EIdx × Nat) (i : Nat) (hf : tb.find? k = some i) :
    i < g.cap ∧ ∃ v, m[k]? = some v ∧ t.memaddrs (g.D + BitVec.ofNat 64 (16 * i)) ∧
      t.memory (g.D + BitVec.ofNat 64 (16 * i)) = .word (Enc.idxW v) := by
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
  have hdi : ders[i]'(by rw [hT.dlen]; exact hil) = dWE (tb.derAt i) := by
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
def optW : Option EIdx → BitVec 64
  | some v => Enc.idxW v + 1
  | none => 0

theorem idxW_add_one_ne (v : EIdx) : Enc.idxW v + 1 ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  have hl : (Enc.idxW v).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact v.word.toNat_lt
  simp [BitVec.toNat_add] at this; omega

theorem one_add_ne (i : Nat) (hi : i < 2 ^ 30) : (1 : BitVec 64) + BitVec.ofNat 64 i ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this; omega

theorem memoGet_spec {α : Type} (G KB : BitVec 64) (g : VGeo) (m : Std.HashMap (EIdx × Nat) EIdx) (k : EIdx × Nat)
    (s : AState) (u : PState σ)
    (hm : MemoAt u G g m) (hK : Words u KB (encMemo k)) (hkl : (encMemo k).length < 2 ^ 61)
    (hgk : u.globals.lookup gKb = some (.val (.word KB)))
    (hpg : u.locals.lookup pG = some (.val (.word G)))
    (hpl : u.locals.lookup pLen = some (.val (.word (BitVec.ofNat 64 (encMemo k).length))))
    (hcode : u.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)) :
    SpecR (fun t => t = u) memoGetBody s (pure (m[k]?) : AM (Option EIdx))
      (fun a w s' st => s' = s ∧ w = optW a ∧ st.memory = u.memory ∧ st.memaddrs = u.memaddrs ∧
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
    (fun _ => BitVec.ofNat 64 (encMemo k).length) (fun v hv => by rw [hv]; exact hcode)
    (fun v hv => by rw [hv]; exact eval_vv _ pG _ (by lk [t1]; exact hpg))
    (fun v hv => by rw [hv]; exact eval_vv _ pLen _ (by lk [t1]; exact hpl))
    (fun v hv => ⟨0, by rw [hv]; exact lookup_setVar_same _ _ _⟩)
    (fun _ _ w s' st => s' = s ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧ st.globals = t.globals ∧
      st.code = t.code ∧
      ((∃ i, tb.find? k = some i ∧ w = 1 + BitVec.ofNat 64 i) ∨ (tb.find? k = none ∧ w = 0)))
    (fun v hv callee h1 h2 x hx => by
      subst hv hx
      have P := memoProbe_spec (callEntryStateHOLFinite t1 callee) encMemo dWE encMemo_inj tb rows ders slots hu g G KB
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
    rw [show t3.memory (g.D + BitVec.ofNat 64 (16 * i)) = .word (Enc.idxW v) by
      show t2.memory _ = _; rw [m2]; exact hmv] at hl
    have hv3 : EV t3 (.op .add [.load .one (.op .add [vv lMd, .shift .lsl (.op .sub [vv lMx, .const 1]) (.const 4)]),
        .const 1]) = some (.val (.word (Enc.idxW v + 1))) := eval_add2 t3 _ _ _ _ hl (eval_const t3 1)
    right
    refine ⟨Enc.idxW v + 1, by rw [return_word t3 _ _ hv3], some v, s, by rw [hv]; rfl, rfl, rfl, ?_⟩
    rw [return_state t3 _ _ hv3]
    exact ⟨m2, d2, g2, c2⟩
  · have hnone : m[k]? = none := by rw [hrel k, hf]; rfl
    rw [ite_word t2 _ _ _ _ (eval_vv t2 lMx _ hx), if_neg (by simp)]
    right
    refine ⟨0, by rw [return_word t2 _ _ (eval_const t2 0)], none, s, by rw [hnone]; rfl, rfl, rfl, ?_⟩
    rw [return_state t2 _ _ (eval_const t2 0)]
    exact ⟨m2, d2, g2, c2⟩

end ConPanqueque.T
