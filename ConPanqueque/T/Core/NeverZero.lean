import ConPanqueque.T.Core.FormerSort
import ConLeche.Verify.PropWhen

/-!
# Never-zero levels, as the port computes them

`nz l`: is `l` nonzero at every valuation — the `isNever` of its zero-ness datum (`isNever_zeronessOf`).
Under a level-parameter substitution it is a walk that looks parameters up (`nzS`, `nz_subst`), which is what
`formerNeverZero` asks (`substPW_isNever`).
-/

namespace ConPanqueque.T.WC

open ConLeche ConLeche.Level

def nz : Level → Bool
  | .zero => false
  | .succ _ => true
  | .param _ => false
  | .max a b => nz a || nz b
  | .imax _ b => nz b

theorem inter_isNever (p q : PropWhen) : (p.inter q).isNever = (p.isNever || q.isNever) := by
  cases p <;> cases q <;> rfl

theorem isNever_zeronessOf : ∀ l : Level, (zeronessOf l).isNever = nz l
  | .zero => rfl
  | .succ _ => rfl
  | .param _ => rfl
  | .max a b => by
    show ((zeronessOf a).inter (zeronessOf b)).isNever = _
    rw [inter_isNever, isNever_zeronessOf a, isNever_zeronessOf b]; rfl
  | .imax _ b => by show (zeronessOf b).isNever = _; rw [isNever_zeronessOf b]; rfl

/-- `nz` after a substitution, looking parameters up. -/
def nzS (ks : List Name) (vs : List Level) : Level → Bool
  | .zero => false
  | .succ _ => true
  | .param n => nz (subst.go ks vs n)
  | .max a b => nzS ks vs a || nzS ks vs b
  | .imax _ b => nzS ks vs b

theorem nz_subst (ks : List Name) (vs : List Level) : ∀ l, nz (subst ks vs l) = nzS ks vs l
  | .zero => rfl
  | .succ _ => rfl
  | .param _ => rfl
  | .max a b => by simp only [subst, nz, nzS, nz_subst ks vs a, nz_subst ks vs b]
  | .imax a b => by simp only [subst, nz, nzS, nz_subst ks vs b]

theorem substPW_isNever (ks : List Name) (vs : List Level) (l : Level) :
    (substPW ks vs (zeronessOf l)).isNever = nzS ks vs l := by
  rw [← ConLeche.Level.zeronessOf_subst, isNever_zeronessOf, nz_subst]

end ConPanqueque.T.WC
