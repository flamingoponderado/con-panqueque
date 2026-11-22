import ConPanqueque.V.EVar
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning `app f a`, in the shared-remainder style

`V/EIntern.lean`'s `eInternApp` came first and states its own layout hypotheses; this is the same
node through `eBin2` (the generic two-child intern) at kind 13 with wide handles, so that it has
the `SRep`/`SepK`/`ERes` interface of the other expression interns.
-/

namespace ConPanqueque.V

section
variable {σ : Type}

theorem eInternApp2_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (L : Layout)
    (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (f a : EIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB 2 13)
    (hkbd : t.memaddrs KB ∧ t.memaddrs (KB + 8)) (hkb8 : KB ≠ KB + 8)
    (hb0 : L.base 13 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824)
    (hb1 : L.base 13 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (lef : t.locals.lookup lEf = some (.val (.word (Enc.idxW f))))
    (lea : t.locals.lookup lEa = some (.val (.word (Enc.idxW a))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB 2 st (st.intern (.app f a))
      (evaluateHOLFiniteState t (eBin2With Der.appDataE (eRest 13 2))) := by
  have hint := estore_app st f a
  simp only at hint
  have hd : st.derOfView (.app f a) = Der.appDataW (st.derived f) (st.derived a) := Der.derOfApp_eq ra st f a
  rw [hd] at hint
  exact eBin2_spec t L FLn FLl FLs FLe KB st f a 13 Der.appDataE Der.appDataW
    (fun s df da h1 h2 => Der.appDataE.eval s df da h1 h2)
    Enc.encApp Enc.encApp_inj ⟨f, a⟩ rfl (mkW 0) (mkW 1) (2 ^ 30)
    (fun i hi => by rw [hb0]; exact idxW_mkW 0 (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkW 1 (by decide) i hi) (fun tier ht => Nat.le_trans (hS.cap tier ht) (by decide))
    st.pers.apps st.scr.apps _ (fun P' S' => { st with pers := { st.pers with apps := P' }, scr := { st.scr with apps := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_apps h1 P' S' h2 h3 h4 h5 h6)
    (fun v h => ⟨h.p4, h.s4⟩) hR hS (by decide) (by decide) hkbd hkb8 lkb lef lea ldir lfle hw

end

end ConPanqueque.V
