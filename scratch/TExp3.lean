import ConLeche
import ConPanqueque.Translate.Exp
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact
pan_exp bvT := fun (w : UInt64) => ConLeche.bvarOfData w
pan_exp fvT := fun (w : UInt64) => ConLeche.fvarOfData w
pan_exp h32T := fun (w : UInt64) => ConLeche.hash32 w
pan_exp hdT := fun (w : UInt64) => ConLeche.hashOfData w
#print axioms fvT.eval
