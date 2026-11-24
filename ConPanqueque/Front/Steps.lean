import ConPanqueque.Front.Name
import ConPanqueque.Scan.NatNth

/-! # Step rules for loop bodies in the `Inv` world

`specR_forI`/`specR_whileT` take loop bodies as `Step`s.  These are the `Step` forms of the
conditional, the table read and a call to a pure scanner whose answer is determined. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable)

variable {σ : Type}

theorem retSpec_of_retP {t : PanSemStateFiniteExact 64 σ} {c : ProgHOL 64} {v : BitVec 64}
    (h : RetP t c (fun w => w = v)) : RetSpec t c v := by
  rcases h with hs | ⟨w, r1, rfl, r2⟩
  · exact Or.inl hs
  · exact Or.inr ⟨r1, r2⟩

theorem step_hangI {P Q : PState σ → Prop} : Step P hang Q := fun t _ => Or.inl (stop_hang t)

theorem step_ifI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {Q : PState σ → Prop} (e : ExpHOL 64) (w : BitVec 64) (he : sev Γ e = some w)
    (h1 : w ≠ 0 → Step (Inv C s Γ M D) c1 Q) (h2 : w = 0 → Step (Inv C s Γ M D) c2 Q) :
    Step (Inv C s Γ M D) (.ite e c1 c2) Q := by
  intro t ht
  rw [ite_word t e c1 c2 w (inv_ev ht he)]
  by_cases hw : w ≠ 0
  · rw [if_pos hw]; exact h1 hw t ht
  · rw [if_neg hw]; exact h2 (by simpa using hw) t ht

/-- `x := f(a₁, …, a₄)` at a pure callee with a determined answer. -/
theorem step_call4I {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (x f x1 x2 x3 x4 : MlS) (body : ProgHOL 64) (a1 a2 a3 a4 : ExpHOL 64) (v1 v2 v3 v4 v : BitVec 64)
    (hnd : [x1, x2, x3, x4].Nodup) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one), (x4, .one)], body, .one))
    (he1 : sev Γ a1 = some v1) (he2 : sev Γ a2 = some v2) (he3 : sev Γ a3 = some v3) (he4 : sev Γ a4 = some v4)
    (hbody : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)), Inv C s Γ M D t →
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → callee.lookup x4 = some (.val (.word v4)) →
      RetSpec (callEntryStateHOLFinite t callee) body v) :
    Step (σ := σ) (Inv C s Γ M D) (callTo x f [a1, a2, a3, a4]) (Inv C s ((x, v) :: Γ) M D) := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  rcases call4_ret t x f x1 x2 x3 x4 body a1 a2 a3 a4 v1 v2 v3 v4 v w0 hnd (by rw [ht.sr.code]; exact hcode)
      (inv_ev ht he1) (inv_ev ht he2) (inv_ev ht he3) (inv_ev ht he4) hw0
      (fun callee h1 h2 h3 h4 => hbody t callee ht h1 h2 h3 h4) with
    hs | ⟨u, hu, m1, d1, g1, c1, b1, lx, lo⟩
  · exact Or.inl hs
  simp only [callTo]
  rw [hu]
  refine Or.inr ⟨rfl, sr_of_eq ht.sr m1 d1 g1 c1, fun y v' hy => ?_, fun a v' ha => by rw [m1, d1]; exact ht.mem a v' ha,
    fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact lx
    · rename_i e; rw [lo y e]; exact ht.env y v' hy
  · by_cases e : y = x
    · subst e; exact ⟨v, lx⟩
    · rw [lo y e]; exact ht.decl y hy

/-- The table read, as a step. -/
theorem step_tblGetI {k : IdxKind} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {Q : PState σ → Prop}
    (x : MlS) (hx : x ∈ D) (j cap : Nat) (tbl : IdTable (Idx k)) (hrel : TblRel C.H j cap tbl)
    (hcap : 8 * cap < 2 ^ 64) (eA ec ei : ExpHOL 64) (heA : sev Γ eA = some (cellA C j))
    (hec : sev Γ ec = some (BitVec.ofNat 64 cap)) (i : Nat) (hi : i < 2 ^ 64)
    (hei : sev Γ ei = some (BitVec.ofNat 64 i))
    (hk : ∀ h, tbl.get? i = some h →
      Step (Inv C s ((x, Enc.idxW h) :: (x, Enc.idxW h + 1) :: Γ) M D) rest Q) :
    Step (Inv C s Γ M D) (tblGetP x eA ec ei rest) Q := by
  unfold tblGetP
  refine step_ifI _ _ (sev_lower Γ ei ec i cap hei hec hi (by omega)) (fun hw => ?_) (fun _ => step_hangI)
  have hic : i < cap := by
    by_cases h : i < cap
    · exact h
    · simp [bw, h] at hw
  have hcell := hrel.1 i hic
  have hlen : j + i < C.H.length := by
    by_cases hl : j + i < C.H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hcell; cases hcell
  have hHi : C.H[j + i] = tblW (tbl.get? i) := by
    rw [List.getElem?_eq_getElem hlen] at hcell; exact Option.some.inj hcell
  refine step_seq (step_heapLoadI x _ (j + i) hlen hx (sev_tblAddr Γ C j i eA ei heA hei (by omega))) ?_
  rw [hHi]
  cases hg : tbl.get? i with
  | none =>
    refine step_ifI _ _ (sev_eq0 _ x _ (Env.get_cons_self _ _ _)) (fun _ => step_hangI) (fun hw => ?_)
    simp [bw, tblW] at hw
  | some h =>
    refine step_ifI _ _ (sev_eq0 _ x _ (Env.get_cons_self _ _ _)) (fun hw => ?_) (fun _ => ?_)
    · exact absurd (by simpa [bw] using hw) (tblW_some_ne h)
    · refine step_seq (step_assignI x _ (Enc.idxW h) hx ?_) (hk h hg)
      simp [sev, Env.get_cons_self, tblW, BitVec.add_sub_cancel]

end ConPanqueque.Front
