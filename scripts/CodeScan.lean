import ConPanqueque.Front.Top
import Lean

open Lean Meta Elab Command

/-- Walk a code-requirement structure's fields, instantiated at a free context, collecting the
`lookup` leaves (function name, body head) and the nested structures. -/
partial def collectCodes (ty : Expr) (seen : IO.Ref (Std.HashSet String)) (out : IO.Ref (Array String)) : MetaM Unit := do
  let ty ← whnfR ty
  let ty ← instantiateMVars ty
  match ty.getAppFn with
  | .const n _ =>
    if isStructure (← getEnv) n then
      let key := toString (← ppExpr ty)
      if (← seen.get).contains key then return
      seen.modify (·.insert key)
      let fields := getStructureFields (← getEnv) n
      let info ← getConstInfoInduct n
      let ctor ← getConstInfoCtor info.ctors.head!
      forallTelescopeReducing (← instantiateForall ctor.type ty.getAppArgs) fun xs _ => do
        for x in xs do
          let xt ← inferType x
          collectCodes xt seen out
    else if n == ``Eq then
      let str := toString (← ppExpr ty)
      out.modify (·.push (String.ofList (str.toList.take 160)))
    else pure ()
  | .forallE .. =>
    let str := toString (← ppExpr ty)
    out.modify (·.push ("∀ " ++ String.ofList (str.toList.take 140)))
  | _ => pure ()

elab "#codes " t:term : command => liftTermElabM do
  let e ← Term.elabTerm t none
  let seen ← IO.mkRef ({} : Std.HashSet String)
  let out ← IO.mkRef (#[] : Array String)
  forallTelescope e fun _ b => collectCodes b seen out
  let a ← out.get
  logInfo m!"{a.size} leaves, {(← seen.get).size} structures"
  IO.FS.writeFile "/tmp/claude-1004/-home-yoichi-bkp-con-pastel/4cbdfdc2-04da-472a-a83e-82678a176a82/scratchpad/codes.txt"
    (String.intercalate "\n" a.toList)

open ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Front in
#codes ∀ C : ConPanqueque.T.Ctx, FoldCodes .verified C
