import ConRon.Arena.Core
open ConRon.Arena

/-! `CoreFnsA.ioView` changes only the `infer` slot: its projections. -/

namespace ConPanqueque.T.WC

@[simp] theorem ioView_whnf (r : CoreFnsA) : (CoreFnsA.ioView r).whnf = r.whnf := rfl
@[simp] theorem ioView_whnfCore (r : CoreFnsA) : (CoreFnsA.ioView r).whnfCore = r.whnfCore := rfl
@[simp] theorem ioView_inferIO (r : CoreFnsA) : (CoreFnsA.ioView r).inferIO = r.inferIO := rfl
@[simp] theorem ioView_infer (r : CoreFnsA) : (CoreFnsA.ioView r).infer = r.inferIO := rfl
@[simp] theorem ioView_defeq (r : CoreFnsA) : (CoreFnsA.ioView r).defeq = r.defeq := rfl
@[simp] theorem ioView_defeqE (r : CoreFnsA) : (CoreFnsA.ioView r).defeqE = r.defeqE := rfl

end ConPanqueque.T.WC
