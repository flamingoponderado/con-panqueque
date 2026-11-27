import ConPanqueque.Front.AxiomRec
import ConPanqueque.Scan.QuotKind

/-! # A quotient record in the value heap

A `#QUOT` line: name and type through the tables, the kind string classified (`fQKind`; any other string
hangs, where the twin fails), then the five-cell record of kind `6` whose fifth cell is the kind's number
(`type` 1, `ctor` 2, `lift` 3, `ind` 4). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec DeclRec HintsRec scanNatList scanString scanHints)

set_option autoImplicit false

variable {σ : Type}

/-- The kind a number names. -/
def qkOfNat : Nat → ConLeche.QuotKind
  | 1 => .type
  | 2 => .ctor
  | 3 => .lift
  | _ => .ind

theorem processQuot_ok (st : StateD) (cv : CVRec) (kind : String) (k : Nat) (hk : quotKindOf kind = some k)
    (nmh : NIdx) (tyh : EIdx)
    (hnm : st.names.get? cv.name = some nmh) (hty : st.exprs.get? cv.type = some tyh)
    (hlps : ∀ j (hj : j < cv.levelParams.length), (st.names.get? cv.levelParams[j]).isSome) :
    processLineCoreD st (.quot cv kind) =
      pure (.inl { st with decls := st.decls.push (.quotDecl (qkOfNat k)
        ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩) }) := by
  have hm := mapM_name_ok st cv.levelParams hlps
  unfold quotKindOf at hk
  split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk <;> subst hk <;>
    simp [processLineCoreD, parseCVD, StateD.name, getDeclD, StateD.expr, hnm, hty, hm, pushDecl, qkOfNat]

/-- A quotient record: name and type, the kind classified, the record. -/
def qtVd (C : Ctx) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblGetP fz (vv fTE) (vv fCap) (vv fW3)
      (.ite (.cmp .equal (vv kSf) (.const (BitVec.ofNat 64 listSentinel))) hang
        (.seq (callTo kT fQKind [vv kBA, vv kBN, vv kSf])
          (.seq (.assign .local kVh (.op .sub [vv kT, vv kSf])) (vdTail C 6)))))

end ConPanqueque.Front
