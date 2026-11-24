import ConPanqueque.Emit.Print
open ConPanqueque.Emit Flapjack

def g0 : ConPanqueque.V.VGeo := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def L0 : ConPanqueque.V.Layout := ⟨0, fun _ _ => g0, fun _ _ => 0⟩
def emptyCode : Flapjack.HolFiniteMapExact Flapjack.Pancake.PanLang.MlS
    (List (Flapjack.Pancake.PanLang.MlS × Flapjack.Pancake.PanLang.ShapeHOL) × Flapjack.Pancake.PanLang.ProgHOL 64 ×
      Flapjack.Pancake.PanLang.ShapeHOL) := ⟨fun _ => none, ⟨[], by simp⟩⟩
def C0 : ConPanqueque.T.Ctx :=
  { L := L0, FLn := 0, FLl := 0, FLs := 0, FLe := 0, KB := 0, code := emptyCode, mG := fun _ => 0,
    mg := fun _ => g0, HB := 0, HN := 0, H := [], EO := 0, saved := none, St := default, fe := default,
    EB := 0, EN := 0, EH := [], envM := {}, tblM := {}, pins := default, PO := 0 }

#eval show IO Unit from do
  let es := ConPanqueque.Code.codeEntries C0
  let globs := ["Gdir", "Gfln", "Gfll", "Gfls", "Gfle", "Gkb", "Ght", "Geo", "Glit", "Get"]
  let gdecls := String.join (globs.map (fun g => s!"var 1 v_{g} = 0;\n"))
  let mainF := "fun 1 main() {\n  return 0;\n}\n"
  let src := gdecls ++ mainF ++ String.join (es.map (fun (f, ps, b, r) => funStr f ps b r))
  IO.FS.writeFile "pancake/checker.pnk" src
  IO.println s!"{es.length} functions, {src.length} chars"
  match Flapjack.Parser.parseTopDecs (BitVec.ofInt 64) src with
  | .ok ds => IO.println s!"parsed {ds.length} declarations"
  | .error errs => IO.println s!"parse errors: {(errs.take 3).map (fun e => e.message)}"
