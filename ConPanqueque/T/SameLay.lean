import ConPanqueque.T.Heap

namespace ConPanqueque.T

/-- `C'` lays out as `C`: it differs only in the heap image, saved memos, store floor, environment, its heap
and its two maps (the fields a code body does not read). -/
abbrev SameLay (C C' : Ctx) : Prop :=
  C' = { C with H := C'.H, saved := C'.saved, St := C'.St, fe := C'.fe, EH := C'.EH, envM := C'.envM, tblM := C'.tblM }

end ConPanqueque.T
