# Axioms, inductives and quotients: plan

Goal: the port accepts streams with `axiom`, inductive-block and quotient records, and
`main_pipeline_chunks` (or its successor) still states that an accepting run implies con-leche's
pure checker accepts. Soundness only: any sub-check the port does not cover may reject.

## What exists

- The environment encoding (`T/Store.lean`, `CIE`) already has `axiomInfo`, `indInfo`,
  `ctorInfo`, `recInfo`. The kernel core reads them: ι-reduction, K-like recursors, struct η, unit-like.
- The frontend parses every record kind (`scanLineFwd`, `Scan/LineFun.lean`), but the dispatcher
  and the declaration registry (`Front/DeclRel.lean`, `RecEnc`) handle only `def`/`thm`/`opaque`.
  `Step.lean` (`stepBody`) rejects any other kind word.
- The bridge (`Bridge/SeqFold.lean`, `seq_bridge'`) assumes every record is a value declaration
  (`IsValueDecl`).
- The pipeline (`Pipeline/Ext.lean`, `prelude_then_stream`) checks the stream from the empty
  environment plus pins, then lifts the run over con-leche's built-in prelude. It requires stream names
  outside the reserved set `FN` (`Start/Forbid.lean` rejects them).

## Dependencies

- `propext` needs a stored `Iff` family, and `Classical.choice` a stored `Nonempty` family
  (`stdAxiomOk`). Both are inductives from the stream.
- Quotient records need `Eq` stored (`quotPredsOk`). Since the port starts without prelude constants,
  that is an inductive from the stream too.
- Quotient and basis records carry reserved (pinned) names, so the forbidden-name pass and the
  `StreamOK` lift must be restated: a record may use a reserved name exactly when it is that
  reserved slot's own record (`quotPinHit`, the basis-block match).

So the order is:

1. **Registry and step dispatch for new kinds** (`RecEnc` kinds 4–6, `stepBody` arms that
   reject); no behaviour change. Frontend lines for `axiom`, `quot`, `ind` records.
2. **Inductive blocks**: twin `checkDeclKind .indDecl` = `indParamsOk`, `readBlock`
   (`Inductives/BlockShape`, `BlockTail`, `FieldTele`, `ClassRead`), `blockReadsAt` (`IotaRead`),
   `checkBlock` (`Positivity`, `GenRec`, `RecCheck`, `BlockInstall`, `StructInstall`,
   `SumInstall`, `StreamRecs`). About 5,500 lines of twin code to translate and refine.
3. **Quotients**: `checkQuotRecord` (pin match with level-parameter instantiation, `quotPredsOk`,
   `installBasisDecl`).
4. **Axioms**: `stdAxiomOk`, `trustCompilerOk`, `ofReduceAxOk`, the `sorryAx` skip.
5. **Bridge**: extend `seq_bridge'` with con-ron's arms for the three kinds
   (`ConRon.Bridge.Inductives.indSpec_of_bridge`, the quotient and axiom arms).
6. **Pipeline**: restate the forbidden-name condition and `StreamOK` for reserved-name records;
   re-prove `main_pipeline_chunks`.

Each step keeps the full build green and the main theorem's statement and axioms.

## The inductive branch, layer by layer

The reachable set from `indParamsOk`, `readBlock`, `blockReadsAt`, `checkBlock` and `basisNamesOk`
(stopping at the kernel core, `ExprOps`, `Monad`, `Env`, `Pins`) is about 310 functions and 3,240 lines of
twin code. Leaves first:

| Layer | Functions | Lines | Examples |
|---|---|---|---|
| L0 | 104 | ~860 | block-shape accessors, memoised walks (`constsResolveFGo`, `mentionsAnyGo`, `depthGo`, `targetAbsGo`), `lvlEq`, `piTele`, `nameNodup`, `indParamsOk` |
| L1 | 55 | ~516 | `blockCounts`, `blockCapsAt`, `classReadMinor`, `motiveLevel?`, `replaceFVars` block, `recFire`, `atLps` |
| L2 | 43 | ~484 | `classGenRule`, `minorTy`, `iotaPartsAt`, `blockSplit`, `checkBlockAgree`, `replaceAppsGo` |
| L3 | 25 | ~306 | `readBlock`, `classRuleCheck`, `targetRecPins`, `blockTables` |
| L4–L5 | 38 | ~506 | `checkConstantVal`, `annEq`, `nestInstType`, `targetMajorOf`, `checkSumCtor` |
| L6 | 13 | ~293 | the positivity mutual block (`nestFields` … `nestPos`), `basisNamesOk` |
| L7–L14 | 24 | ~277 | `checkBlockCtors`, `genRecCheck`, `recsRead`, `blockReadsAt`, `checkBlockTail`, `checkBlock` |

Awkward parts: about 12 fuelled walkers (fail at 0), ten per-call `HashMap` memos (the port's memo tables
fit), `flushCaches` at about ten environment transitions, `popTemp` (temporary pushes onto the environment
index), `Array` growth in the positivity state, and spec-level `Name`/`Level` values read back in
`allLevelParamsDefined`, `pinLinkOk` and `BasisKind.decls` (which re-interns a whole basis block).

## Progress

- Scanner: the line table accepts `axiom` and `quot` payloads (tags 21, 22; `Scan/ObjInst2`,
  `Scan/RecEnds2`, `Scan/Line`, `Scan/LineFun`, `Front/PlTag`). The dispatcher has no branch for them yet,
  so such lines still reject.
