import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact ConPanqueque.Logic

namespace ConPanqueque.Table

/-- `u` agrees with `s` on code, globals and every local outside `xs`. -/
def Frame {σ : Type} (s u : PanSemStateFiniteExact 64 σ) (xs : List MlS) : Prop :=
  u.code = s.code ∧ u.globals = s.globals ∧ ∀ x, x ∉ xs → u.locals.lookup x = s.locals.lookup x

theorem frame_refl {σ : Type} (s : PanSemStateFiniteExact 64 σ) (xs : List MlS) : Frame s s xs :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem frame_set {σ : Type} {s u : PanSemStateFiniteExact 64 σ} {xs : List MlS} {x : MlS} (v : ValueHOL 64)
    (hf : Frame s u xs) (hx : x ∈ xs) : Frame s (setKvarHOLFinite .local x v u) xs := by
  obtain ⟨a, b, c⟩ := hf
  refine ⟨by simp [setKvarHOLFinite, setVarHOLFinite, a], by simp [setKvarHOLFinite, setVarHOLFinite, b], fun y hy => ?_⟩
  have : y ≠ x := fun e => hy (e ▸ hx)
  simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ this]; exact c y hy

theorem frame_dec {σ : Type} {s u : PanSemStateFiniteExact 64 σ} {xs : List MlS}
    (hf : Frame s u xs) : Frame s (decClockHOLFinite u) xs := by
  obtain ⟨a, b, c⟩ := hf
  exact ⟨by simp [decClockHOLFinite, a], by simp [decClockHOLFinite, b], fun y hy => by simpa [decClockHOLFinite] using c y hy⟩

theorem frame_mem {σ : Type} {s u : PanSemStateFiniteExact 64 σ} {xs : List MlS} (m : BitVec 64 → HolWordLab 64)
    (hf : Frame s u xs) : Frame s { u with memory := m } xs := by
  obtain ⟨a, b, c⟩ := hf
  exact ⟨a, b, c⟩

end ConPanqueque.Table
