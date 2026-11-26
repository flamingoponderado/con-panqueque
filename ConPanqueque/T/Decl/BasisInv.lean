import ConPanqueque.T.Decl.OffCheck
import ConPanqueque.Logic.BasisNames

/-!
# The pinned basis blocks, interned once: an invariant of the fold

`BasisInv C`: some well-formed store `st0` below the context's floor holds the pins' reserved names and a past
run of each pinned block's intern.  At any related state with the scratch tier off, `BasisKind.decls k` is then
a no-op answering a block whose names are the reserved slice.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.Logic.InternRerun ConPanqueque.Logic.BasisNames

/-- The pinned blocks interned below the floor. -/
def BasisInv (C : Ctx) : Prop :=
  ∃ st0 : EStore, StoreWF st0 ∧ Ext st0 C.St ∧ denoteNL st0 C.pins.reserved reservedBasisNameValues ∧
    ∀ k : ConLeche.BasisKind, k ≠ .quotK → ∃ (s0 s1 : AState) (r : List IConstantInfo), Off s0.store ∧
      ConRon.Arena.BasisKind.decls k s0 = .ok (r, s1) ∧ FP s1.store st0

theorem denoteNL_ext {a b : EStore} (hx : Ext a b) : ∀ (xs : List NIdx) (ns : List ConLeche.Name),
    denoteNL a xs ns → denoteNL b xs ns
  | [], [], _ => trivial
  | x :: xs, n :: ns, h => ⟨hx.lss.ls.ns x n h.1, denoteNL_ext hx xs ns h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **The pinned blocks' intern at a related state**: a no-op, its names the reserved slice. -/
theorem basis_at {σ : Type} {C : Ctx} (hb : BasisInv C) {s : AState} {t : PState σ} (hsr : SR C s t)
    (hoff : Off s.store) (k : ConLeche.BasisKind) (hk : k ≠ .quotK) :
    ∃ r : List IConstantInfo, ConRon.Arena.BasisKind.decls k s = .ok (r, s) ∧
      r.map (·.name) = resSlice k C.pins.reserved := by
  obtain ⟨st0, hwf0, hx0, hres0, hrun⟩ := hb
  obtain ⟨s0, s1, r, ho0, hr, hfp⟩ := hrun k hk
  have hx : Ext st0 s.store := hx0.trans hsr.floor
  have hnoop := basisDecls_noop k ho0 hr hfp hwf0 hsr.twf hx hoff
  refine ⟨r, hnoop, ?_⟩
  have hres : denoteNL s.store s.pins.reserved reservedBasisNameValues := by
    rw [hsr.pins]; exact denoteNL_ext hx _ _ hres0
  have := basisDecls_names' k hk ⟨hsr.twf⟩ hres hnoop
  rw [hsr.pins] at this; exact this

end ConPanqueque.T.Decl
