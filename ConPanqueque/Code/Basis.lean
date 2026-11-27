import ConPanqueque.Code.Map
import ConPanqueque.T.LitIntern

namespace ConPanqueque.Code

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ecodes_ok (C : ConPanqueque.T.Ctx) (hC : C.code = codeMap (codeEntries C)) :
    ConPanqueque.T.Lit.ECodes C := by
  code_auto

end ConPanqueque.Code
