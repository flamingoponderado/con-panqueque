import ConPanqueque.Emit.Check
import ConPanqueque.Start.Main
open ConPanqueque.Emit Flapjack Flapjack.Pancake.PanLang ConPanqueque.Code ConPanqueque.Start

/-! Print the verified program to `pancake/checker.pnk`: the globals with the values
`InitGlobals` assumes, `main` (`mainBody`), and the code table at the concrete layout.  Each
function is parsed back with flapjack's parser and compared (after normalisation). -/

/-- A computable context with the concrete layout (the table depends only on the layout). -/
def Cemit : ConPanqueque.T.Ctx := C1 emptyCode [] [] P0

#eval show IO Unit from do
  let es := codeEntries Cemit
  let globs : List (String × Nat) :=
    [("Gdir", base), ("Gfln", base + 4096), ("Gfll", base + 4104), ("Gfls", base + 4112), ("Gfle", base + 4120),
     ("Gkb", base + 8192), ("Ght", base + H0 + 8 * NH), ("Geo", 0), ("Glit", 0), ("Get", base + E0 + 8 * 64)]
  let gdecls := String.join (globs.map (fun (g, v) => s!"var 1 v_{g} = {v};\n"))
  let mainF := s!"fun 1 main() \{\n  {progStr mainBody}\n}\n"
  let src := gdecls ++ mainF ++ String.join (es.map (fun (f, ps, b, r) => funStr f ps b r))
  IO.FS.writeFile "pancake/checker.pnk" src
  IO.println s!"{es.length} functions + main, {src.length} chars"
  match Flapjack.Parser.parseTopDecs (BitVec.ofInt 64) src with
  | .ok ds =>
    IO.println s!"parsed {ds.length} declarations"
    let funs := ds.filterMap (fun d => match Flapjack.Pancake.PanLang.declToHOL (width := 64) d with
      | .function f => some (nameStr f.name, f)
      | _ => none)
    match funs.lookup "main" with
    | none => IO.println "main missing"
    | some fd =>
      let ok := toString (repr (norm fd.body)) == toString (repr (norm (renameP mainBody)))
      IO.println s!"main round trip: {if ok then "matches" else "DIFFERS"}"
  | .error errs => IO.println s!"parse errors: {(errs.take 3).map (fun e => e.message)}"
  match roundTrip src es with
  | .ok [] => IO.println "round trip: every function matches"
  | .ok bad => IO.println s!"round trip: {bad.length} differ, e.g. {bad.take 5}"
  | .error e => IO.println e
