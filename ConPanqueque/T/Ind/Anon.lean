import ConPanqueque.T.ReIntern
import ConPanqueque.T.LInternLv

/-!
# The anonymous name

`readBlock` interns `.anonymous` as a small eliminator's elimination parameter.  The image's store holds it
(`denoteN C.St.ns anonH = some .anonymous`, an image fact), and the store only extends (`SR.floor`), so the
probe finds it: the intern is a lookup that leaves the state alone, and the port uses the handle as a constant.
-/

open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T

/-- The anonymous name's handle in the image's store. -/
def anonH : NIdx := mkN NTag.anonymous 0 0

theorem internAnon_run {σ : Type} {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t)
    (hA : denoteN C.St.ns anonH = some .anonymous) : internNNode .anonymous s = .ok (anonH, s) := by
  have hd : denoteN s.store.ns anonH = some .anonymous := h.floor.lss.ls.ns anonH _ hA
  obtain ⟨-, ⟨rkN, hN⟩⟩ := wf_parts h.twf
  have := internName_denote s rkN hN .anonymous _ anonH hd
  simpa [internName] using this

end ConPanqueque.T.Ind
