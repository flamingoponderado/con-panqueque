import ConPanqueque.Code.Map

namespace ConPanqueque.Code

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fold_ok (C : ConPanqueque.T.Ctx) (hC : C.code = codeMap (codeEntries C)) :
    ConPanqueque.T.Decl.FoldCodes .verified C := by
  code_auto

end ConPanqueque.Code
