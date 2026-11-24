# Above the knot: declaration checking (design notes)

Status (dab8dcd): the kernel is closed. `knot_closed` proves that the six Pancake entry points refine con-ron's twin
knot at every fuel up to `2^62`; `inferTop` / `defeqTop` give `inferTypeCore` / `isDefEqCore` at `checkFuel`.

## What remains (twin, `deps/con-ron/proof/ConRon/Arena`)

| layer | twin files | role |
|---|---|---|
| record fold | `CheckDecl.lean` (`checkDeclsPure`, `checkDeclStep`, `checkDecl`, `checkDeclKind`) | per-record dispatch, env growth |
| front door | `CheckerBase.lean` (`checkConstantVal`, `allLevelParamsDefined`, `constsResolveFFast`, `nameNodup`) | type well-formedness |
| arms | `DeclCheck.lean` (`checkDefnVal`, `checkThmVal`, `checkOpaqueVal`, quot, pins, div/mod certs) | value checks |
| inductives | `Inductives/*` | block reading, positivity, recursor generation |
| frontend | `Frontend/*` | bytes → interned store + env |
| driver | `Checker.lean`, `Justify.lean`, `Install.lean` | stream, records |

## Layout decisions

1. **The record being checked lives in the value heap `H`**, encoded exactly like an environment entry (`CIE`
   layout), so the arms read its fields with the same loads the kernel uses on environment entries.
2. **`fe.push ci` appends the entry to the environment heap `EH`** and inserts its name into the constant table
   (`envM`); projection tables likewise into `tblM`. Between records the context changes only in `fe`, `EH`,
   `envM`, `tblM` (and `H`); the kernel's `Ctx` is rebuilt per record. The record step must re-establish
   `CtxOK` and `SR` at the grown context — in particular `EnvDen` (`ConstDen` / `TblDen` / `RecDen`) for the new
   entry, from the front door's own checks (type denotes, level parameters denote and are few, …).
3. **Error payloads are not modelled**: the verdict is accept/reject (the goal's equivalence); every failure path
   of the twin maps to the port's reject (or a halt, which is sound).
4. **Read-back walks** (`allLevelParamsDefined`, `readNames`) run on heap trees as the kernel's level code does
   (`LRep`), with the memo as a heap hash table like the kernel memos.

## Order of work

`ensureSort` → `checkConstantVal` (name/pin checks, `nameNodup`, `litShapeOk`, the walks) → defn/thm/opaque arms →
record step with env growth (`EnvDen` for the new entry) → fold → inductives → frontend → concrete code table
(`AllCodes`/`KCodes`, one program per `CheckMode`, no duplicate function names) → executables → verdict theorem.

## Status (f4ef16c)

Done: `ensureSort`, `constsResolveFFast`, `nameNodup`, `allLevelParamsDefined`, the reserved-name tests, `litShapeOk`
(all ten literal shapes), and `checkConstantVal` (`ccv_full`: no spec hypotheses, only code-table facts and the
record's preconditions). Twin failures map to `rejectP` (a stop, the soundness direction).

## The record step (next)

`checkDeclStep` = `andPinOk` · `flushCaches` · fresh memos · `checkDeclKind` · `flushCaches` · `basisNamesOk`, and
`checkDeclKind`'s arms end in `fe.push ci`. Plan:

1. **Arms first, special cases stopped.** `defn`/`thm`/`opaque`/plain `axiom` are checked in full
   (`valueGuards` = the four expression checks of `checkConstantVal` on the value; `inferTop`; `defeqTop`; the
   theorem's `lvlEq? u 0`). Branches not yet ported stop (`rejectP`), which is sound: the pinned `Nat`-operation,
   div/mod and reduce certifications, quotient records, `stdAxiomOk`/`trustCompiler`/`ofReduce` axioms, and
   inductive blocks. They are filled in afterwards, one by one.
2. **Environment growth.** Only `EnvRel`/`PinsE` (static) and `EnvAt`/`EnvDen` (in `SR`) mention `fe`, `EH`,
   `envM`. The port copies the record from the value heap into the environment heap (a deep copy: the
   level-parameter block too, relocated to an `ecell` pointer), bumps `gEt`, inserts `name ↦ ecell` into the
   constant table, and recomputes the literal flags (`gLit`) when `IFEnv.push` would. Intermediate contexts
   `{C with EH := EH ++ ws}` keep `CtxOK`/`SR` (old cells untouched). The new entry's `ConstDen` facts come from
   the front door (`checkConstantVal` checked that the type denotes, level-parameter names are distinct and few,
   …) plus `RecPre` (the record's handles denote, from the frontend).
3. **Caches and memos** are flushed by the existing clear code (`MemoClear.lean`), so `CacheAt`/`MemoAt` hold at
   the empty tables for the grown context.
4. **The fold** (`checkDeclsPureGo`) is the record step iterated; the verdict theorem relates the port's
   accept to `checkDeclsPure`'s success (con-ron's bridge takes it to con-leche).
