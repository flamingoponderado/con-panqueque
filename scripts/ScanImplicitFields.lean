import ConPanqueque
open Lean Meta Elab Command

elab "#scan_impl2" : command => liftTermElabM do
  let env ← getEnv
  let mut hits : Array String := #[]
  for (n, _) in env.constants.toList do
    if (`ConPanqueque).isPrefixOf n then
      if let some sinfo := getStructureInfo? env n then
        let nparams := (← getConstInfoInduct n).numParams
        for f in sinfo.fieldNames do
          if let some pci := env.find? (n ++ f) then
            let r ← forallTelescopeReducing pci.type fun xs _ => do
              let mut acc : Array String := #[]
              for x in xs[(nparams+1):] do
                let ld ← x.fvarId!.getDecl
                let ty ← inferType x
                if ld.binderInfo.isImplicit && !(ty.isSort) then
                  acc := acc.push s!"{ld.userName} : {← ppExpr ty}"
              return acc
            if r.size > 0 then hits := hits.push s!"{n ++ f}: {r}"
  logInfo m!"{hits.size} hits:\n{String.intercalate "\n" hits.toList}"

#scan_impl2
