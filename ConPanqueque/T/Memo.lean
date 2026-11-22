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

end ConPanqueque.T
