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
- `readBlock` pieces, each a Pancake function with a spec against its twin fragment (`T/Ind`, all sorry-free,
  standard axioms): the split (`Split`, `SplitLemma`), `indParamsOk` (`IndParams`), `blockCounts`,
  `blockMemberCounts` (`BlockCounts`, `MemberCounts`, `FindRec`, `RecTarget`), the level-parameter checks
  (`LpsEq`, `AllLps`), `memberIdxAt?`/`ctorMember?` (`CtorMember`), `blockGroups` (`Groups`), `paramLevels`
  (`ParamLevels`), the result sort and `isProp` (`ResultSort`), the recursor shapes (`RecShapes`), `large?`
  (`Large`), the anonymous name (`Anon`, a lookup given the image fact `denoteN C.St.ns anonH = some
  .anonymous`), the members (`Members`). Heap layout of the result: `Shape` (`ShapeRep`).
- **`readBlock` done** (`ReadBlock.rb_spec`, against `unwrapE (readBlock nPd blk)`; `ReadBlockTwin.rb_twin`
  flattens the twin). Hypotheses left for the callers: `RuntimeAssumptions`, the image's anonymous name,
  `lvlEq?`'s spec (as `isPropType` takes it), and bounds on the block's lengths. Next: `blockReadsAt`
  (`IotaRead`), then `checkBlock` (`Positivity`, `GenRec`, `RecCheck`, the installs).
- **`IotaRead` below `blockReadsAt` done** (`T/Ind`, sorry-free): `piTele`, `motiveLevel?`, minors,
  `iotaRecMajor`/`iotaRecOf` (`IotaRec`, `IotaRecOf`), `liftFieldDoms`/`liftIdxArgs`/`iotaPartsOfAt`
  (`IotaParts`), `iotaBVars`/`iotaParamsAt`/`ctorLevelsAt` (`IotaCtor`), `iotaPartsAtBody` (`IotaBody`, with the
  generic block slice `sliceCopyP`), `iotaPartsAt` (`IotaPartsAt`; numeric bounds the twin never checks are runtime
  hang guards), `lvlEq` (`LvlEqE`), `listLvlEq`, `annWitness`/`annIdentBody`/`annIdentVal`/`annIdent` (`AnnEq`),
  `annEq` (`AnnEqRec`; annotation names interned as `topName` = image `anonH` + frontend `internNStr`, so callers
  need `FrontOK` and the anonymous-name image fact), `listAnnEq`, `paramsAnnEq`/`iotaPartsRel` (`IotaRel`, with
  heap block equality `blkEq`), `ruleReads` (`RuleReads`; rules live in the environment heap and are copied to the
  value heap by `ruleCopyP`), `rulesRead`/`recReads`/`recsRead` (`RecsRead`).
  The level arms of `lvlEq` run the twin's cached readbacks from the entry state and re-establish the state
  relation with `sr_congrS` (the port caches nothing there).
  Next: `blockReadsAt` = `blockConstants` (`blockIsRec`, `blockFormers`/`blockCapsAt`, `blockCtors`, `blockRecs`
  with `recFire`) written as environment records (`CIE`), the temporary push/pop of the environment index
  (`consBlockRecsTemp`, `popTemp`; reuse `T/Decl/Install`), `recsRead`; then `checkBlock`.

### `blockReadsAt`'s temporary environment (design)

The twin reads the recursors' rules against `feR` (the block's constants pushed onto the index, previous rows saved),
then pops back to `fe₀` before `checkBlock`. The port must follow the same order: `checkBlock` runs from the state
`blockReadsAt` leaves (it interns), so the two cannot be swapped without losing the store's exact mirror.

The port's environment index is a memo table (`MemoAtG`, append-only rows over an open-addressing slot array,
`ConsModel.Inv`), and `EnvRel` ties `C.fe.find?` exactly to it, so a pop has to restore the table. Options:

1. A delete in the memo model (tombstones). Changes `MemoRel` for every memo; too wide.
2. An overlay table consulted before the index during `recsRead`. Every environment lookup on that path
   (`ruleReads`' constructor, `annIdent`, `annWitness`) would take a two-level finder; three specs change and
   the block's records would live outside the environment heap.
3. **Undo log (chosen).** The pushed names are required fresh (`fe.find? n = none`; otherwise the port hangs,
   which soundness-only allows). Each temporary insert writes a fresh row past the table's row count, one empty
   slot, and the descriptor words; the pop clears those slots in reverse and restores the saved descriptor and the
   environment heap's top (`gEt`). Rows past the count are not part of the representation, so the table's memory
   is back to a state the old `MemoAtG` holds for (`memoAtG_frame`-style), and `EnvRel`/`CtxOK` hold for the old
   context. Needed: the memo insert's footprint (which words it writes) and a restore lemma.
