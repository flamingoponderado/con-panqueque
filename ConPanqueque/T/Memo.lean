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
def fMemoProbe2 := ofString "memoProbe2"

def memoProbe2Body : ProgHOL 64 :=
  .dec lK .one (.var .global gKb) (.dec lL .one (.const 2) (withGeoV pG (.seq probeV (.return (.const 0)))))

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

theorem memoProbe2_spec {α δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]
    (t : PState σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hinj : ∀ x y, enc x = enc y → x = y) (tb : Tbl α Nat δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64))
    (slots : List Nat) (hu : Nat) (g : VGeo) (G KB : BitVec 64) (x : α) (hx2 : (enc x).length = 2)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30)
    (hT : VT t enc rows ders slots g hu) (hinv : ConsModel.Inv (α := α) (homeV enc g.b) rows slots g.n)
    (hrel : TblRel tb rows id) (hK : Words t KB (enc x)) (hdesc : DescV t G g 1)
    (hgk : t.globals.lookup gKb = some (.val (.word KB))) (hg : t.locals.lookup pG = some (.val (.word G))) :
    MPRes t tb x (evaluateHOLFiniteState t memoProbe2Body) := by
  unfold memoProbe2Body
  rw [dec_word_eq t lK _ KB _ (eval_gv t gKb KB hgk)]
  refine mpres_restore lK KB _ ?_
  let t1 := setVarHOLFinite lK (.val (.word KB)) t
  rw [dec_word_eq t1 lL (.const 2) 2 _ (eval_const t1 2)]
  refine mpres_restore lL 2 _ ?_
  let t2 := setVarHOLFinite lL (.val (.word 2)) t1
  have hd2 : DescV t2 G g 1 := hdesc
  apply withGeoV_lift (fun s r => MPRes s tb x r) (fun s y v r h => mpres_restore y v r h) t2 pG G g 1 _
    (by lk [t2, t1]; exact hg) (by decide) hd2
  let u := geoStateV t2 g 1
  have hP := probeV_spec u enc (fun i => 1 + BitVec.ofNat 64 i) id 1 (2 ^ 30) (fun i _ => rfl) hinj tb rows ders slots hu
    g x KB hn hb hcap (Nat.le_of_lt hcap) (vt_frame hT (fun _ _ => rfl) rfl) hinv hrel (fun j hj => hK j hj)
    (by omega) (by simp only [u, geoStateV]; lk [t2, t1]) (by simp only [u, geoStateV]; lk [t2]; rw [hx2]; rfl)
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

end ConPanqueque.T
