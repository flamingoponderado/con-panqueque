import ConLeche
import ConPanqueque.Translate.Exp

/-!
# con-leche's word functions, translated

The data-word accessors of con-leche's `Expr` (`ConLeche/Kernel/Expr.lean`),
translated from their definitions by `pan_exp` (which unfolds non-recursive
definitions) with generated proofs.
-/

open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact

namespace ConPanqueque.Translated

pan_exp hashOfData := fun (w : UInt64) => ConLeche.hashOfData w
pan_exp bvarOfData := fun (w : UInt64) => ConLeche.bvarOfData w
pan_exp fvarOfData := fun (w : UInt64) => ConLeche.fvarOfData w
pan_exp hash32 := fun (w : UInt64) => ConLeche.hash32 w

end ConPanqueque.Translated
