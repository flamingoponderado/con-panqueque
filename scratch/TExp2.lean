import ConPanqueque.Translate.Exp
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact
pan_exp hashOfDataT := fun (w : UInt64) => w / 4294967296
pan_exp hash32T := fun (w : UInt64) => w % 4294967296
pan_exp bvarT := fun (w : UInt64) => w / 65536 % 32768
pan_exp maxT := fun (x y : UInt64) => if x < y then y else x
pan_exp packT := fun (h b f : UInt64) => h * 4294967296 + b * 65536 + f * 2
#print axioms bvarT.eval
