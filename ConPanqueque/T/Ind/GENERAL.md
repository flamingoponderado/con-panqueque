# Generalizing the inductive path: survey

Status on 2026-11-27, commit 0be975b plus the work recorded at the end. The goal is general inductive
blocks: k members, one recursor per member, then nested blocks with auxiliary recursors.

The twin (`deps/con-ron/proof/ConRon/Arena/Inductives/*`, `Arena/Install.lean`,
`Arena/Frontend/ExportC.lean`) is general. So are the bridge (`Bridge/IndTail.lean`) and the pipeline
(`Pipeline/IndExt/*`). Every restriction listed below is in the Pancake port: the procedures and
their `SpecR` refinement proofs. A port procedure may hang wherever the twin goes on. So a
restriction costs completeness, never soundness: an unsupported block makes the program hang.

## 0. Findings that come before mutual blocks

1. **Recursive constructors hung, even in one-member blocks** (closed in the second round, see §5).
   Before, the generator supported only *ordinary* fields:
   * `ClassCtor.cfo_spec`: `classFieldsOf p [] …` hangs at a field that mentions a member.
   * `ClassCtor.cms_spec`: a minor slot with inductive hypotheses hangs.
   * `GenRule.cgr_spec`: "a constructor with ordinary fields".

   So `Nat` (`succ : Nat → Nat`), `List` and every recursive type hang. `ClassRead` (the pre-pass)
   already reads inductive hypotheses. What is missing is the generator's recursive branch:
   * `classFieldsOf`'s `.recursive` arm (`piBinders`);
   * `classFieldsAgree`, `classNodesAgree` (`targetK53`) and `classLeafAt`;
   * `ClassGen.minorTy`'s `ihsGo` (`ihParts`, `closeTelescope`);
   * `classGenRule`'s `callsGo` (`classRecOf`, `closeLams`).

   Almost every mutual block is recursive, since its members mention each other. So mutual support
   is of little use without this, and this work is effectively part of milestone 2.
2. **The prelude cannot pass the fold today.** con-leche's built-in prelude has six blocks:
   `Eq`, `Nat`, `Empty`, `False`, `And` and `Bool`. All have one member and one recursor, and none
   is nested.
   * `Nat` is recursive (finding 1).
   * `ki_spec` (`IndArm2`) hangs on blocks that hit a pinned basis block (`basisNameHit`: Eq, Nat,
     Empty, False). The twin compares those blocks with the pin (`pinListOk`); `andPinOk` does the
     same for `And` (`canonEqList`).

   The prelude runs through the fold first. So until both gaps are closed, the program accepts no
   input at all. This is independent of mutual or nested support.
3. **Other restrictions on the one-member path:**
   * a member stored at a definition hangs (`CheckBlock.rmFill`; the twin reduces it);
   * at most one projection table (`cbkInst`);
   * the recursor's target must be member 0 (`rc.tgt = 0`).

## 1. The block path, procedure by procedure

Legend:
* **G**: the spec is already general over the member, constructor and recursor lists.
* **1**: specialised to one member, one class or one recursor. Other counts hang, or the spec takes
  `p.members = [ms0]`, `p.recs = [rc]`, `g.cls = [m]` or `p.k = 1`.
* **U**: unnested only.

Effort scale:
* S: under 300 lines;
* M: 300 to 1000 lines;
* L: over 1000 lines of new Pancake and proof.

| Procedure (file, spec) | Twin | State | Generalization work | Effort |
|---|---|---|---|---|
| `cbkBody` (`CheckBlockK`, `cbk_spec`) / `cbk_spec_any` (`CheckBlockAny`) | `checkBlock` | 1 | Loops over members for the name, `Bool` and freshness checks, then calls the general sub-procedures. It reads the pass's pieces for k classes, k recursors and the tables. Hangs on the K-class and nested parts. | L |
| `CBKFacts` / `CBKRun` | (port facts) | 1 | The bounds and denotations hold for all members and recursors; `indRun_of_front` already derives them for all (`HMb`, `HRb`). The `crt` field is stated at the port's own twin decomposition (`ctbPre`, `gaPre`), so it changes when those do. | S (bounds), M (crt) |
| `cnn` (`CtorNames`) | `nameNodup (allCtors.map name)` | 1 | Fill the flattened constructor names of all members, then `ndg`. Member names also need `nameNodup`, which is trivial at k = 1. | S |
| Bool-name check, `envFind` of the declared name (inline in `cbkBody`) | `memberNames.contains bt/bf`, per-member freshness | 1 | A loop over members. | S |
| `rmFill` (`CheckBlock`, `rm_spec`) | `reduceMembers` | G (no member at a definition) | none for milestone 2 | – |
| `bi_spec` (`BlockIsRec`) | `blockIsRec` | G | none | – |
| `cps` (`CheckPass`, `cps_spec`) | `checkBlockPass` | 1 | Consumes `cbi` and `sumCtors` per member; hangs unless exactly one class sits at member 0. Generalize: k classes, one per member (`classSeeds` stays empty when unnested). | M |
| `cbi` (`CheckInds`, `cbi_spec`) | `checkBlockInds` | G since §7 (was: `members.length = 1` tested) | done (§7: `ctl`, `cag`, `cbn`) | – |
| `fSumCtors` (`SumCtor`) | `checkBlockCtors` | per member | The loop exists (§7: `sca`, `SumCtorsAll`), not yet called from `cps`. | S |
| `bn` (`NestCtx`) | `blockNestCtx` | G | none | – |
| `cbc` (`ClassPass`), `crd` (`ClassRead`), `cmj`/`tmo` (`TargetMajor`) | `checkBlockClasses`, `classRead`, `classMajors` | G, U (an outside inductive halts) | none for milestone 2 | – |
| `cbp` (`CheckPos`) with `nrt`, `nul`, `num`, `nt`/`np` (`NestPos`), `RFHole`, `NestCtors` | `checkBlockPositivity` | G over members, U (empty frame stack; `nestCont` hangs) | none for milestone 2. Nested blocks need container frames (`nestCont`, `nestKeyOf`, `NestCtorNf` keys). | L (nested) |
| `sd` (`Seeds`) | `classSeeds` | U (no seeds) | Nested: seeds for outside classes plus `nestSeeds`. | M (nested) |
| `kf1`/`kf2`/`kf3` (`KindsFlat`) | `nestKindsFlat` (`blockNestedBit = false`) | G | Nested: drop the check and carry `nested`. | S |
| `cfh` (`CtorsFresh`) | constructor freshness at `env1` | 1 (only `ms0.ctors`) | Run over the flattened constructors. | S |
| `bt` (`BlockTables`, `bt_spec`) | `blockTables` | G since §9 (`bta`, at most one table in all) | done: `bta` loops over members (§9 step 5); more than one table waits for `cbkInst`'s table loop. | – |
| `ctb` (`BlockTail`, `ctb_spec`) | `checkBlockTail` | 1 | Calls `bis`, `consCtors`, `cts`, `cst`. Generalize to k classes and recursors. | M |
| `bis` (`IdxSorts`) | `checkBlockIdxSorts` | 1 | A loop over members. | S |
| `consCtors` (`ConsCtors`, `csc_spec`) | `consBlockCtors` (per group) | 1 group | A loop over groups (members). | S |
| `cts` (`BlockTail`, `cts_spec`) with `ga` (`GenRecHead`), `kexp` (`StreamK`), `srr`/`srs` (`StreamChk`) | `checkBlockRec`, `streamKCheck`, `streamRecsCheck` | 1 (`p.k = 1`, `recs = [rc]`) | `genRecCheck` over all classes and recursors; `streamKCheck`/`streamRecsCheck` per recursor (`recKExpected` is false when k > 1); `blockRecInfosTF`/`consBlockRecsTemp` over the list. | L |
| `ga` (`GenRecHead`): `trp` (`RecPins`), `lgd`/`lea` (`LargeElim`), `tmn`/`cnm` (`ClassNfs`), `tcc` (`TargetMatch`), `ccl`/`cco`/`cfo`/`cms` (`ClassCtor`), `cmc`, `elv` | `targetRecPins`, `blockLargeElimAllowed`, `targetMajorNfs`, `targetParamsDefEq`, `classesCtors`, `structElimLevel` | 1 (one member and class), ordinary fields only (finding 1) | Each over k classes. `blockLargeElimAllowed` at k > 1 is the never-zero test only. `elv` needs `structElimLevel` per class. | L |
| `gb` (`GenRecCheck`): `pb`/`psl`/`mot`/`mjr`/`grt` (`GenMotive`), `mty`/`tpw` (`GenPre`), `cro` (`ClassConst`), `cfr` (`FeR`), `cgr`/`fms`/`pvg` (`GenRule`), `crc` (`RuleCheck`) | `prefixBinders`, `classGenRecTy`, `classRecTysOk`, `classFeR`, `classRecsRulesOk` | 1 (`g.cls = [m]`, `formerTys[0]`, slot 0 a motive, one recursor at class 0), ordinary fields only | `motiveTy` and `motVar` per class (the motive index counts motives before slot `s`), `minorTy` with IHs, one generated recursor per class, the temporary push of k recursors, rules per class. | L |
| `cst`/`csb` (`BlockTables2`) | `checkBlockTables` | G over the table list (but the caller passes ≤ 1) | none | – |
| `cbkInst` (`CheckBlockInst`, `ci_spec`), `rin` (`RecInstall`), `fx` (`RecFire`), `tw` (`TblWrite`) | `blockRecs` and `pushDelta recs Q` | 1 recursor, ≤ 1 table; `fx` general (`.nested` fire at `tgt ≥ k`) | A loop over recursors (`recFire` is per recursor) and tables. | M |
| `ki` (`IndArm2`, `ki_spec`) | `checkDeclStep` at `.indDecl` | G except the basis hit (finding 2) | Calls `cbk_spec_any`, so nothing to do once that is general. Pin branch: `pinListOk` / `canonEqList`. | M (pin branch) |
| `rb` (`ReadBlock`), `br` (`BlockReadsSpec`), `ReadBlockSplit` | `readBlock`, `blockReadsAt` | G (`readBlock_splitOK` needs `members.length = 1`; general `SplitOK` follows from `readBlock` inversion) | `SplitOK` for k members (`ReadBlockSplit`: `g = [cs]` when k = 1). | S |

### Front end (`Front/IndLine*.lean`, `indLine_spec`)

The line hangs unless:
* `tys = [t]` and `rcs = [r]`;
* `t.numNested = 0`;
* the constructor records come in `t.ctors` order (`cts[j].name = t.ctors[j]`);
* `r.numMotives = 1`.

Generalizing to k types and one recursor per type (still unnested) needs:
* a type loop that writes k `indInfo` records and checks every `numParams` against `tys[0]`;
* the constructor loop per type at a running offset (the twin's `ordered` list, read positionally:
  the port hangs unless the constructor records come in block order);
* distinct names over the flattened list;
* a recursor loop: `numMotives = k`, `numMinors` = the total constructor count, and the
  `numIndices` check against the type whose name prefixes `.rec`, run over all types;
* the block layout `types ++ ctors ++ recs`.

Effort: about 1500 lines, because the loops in `IndLineE`/`F` can be reused.

`IndShape` is internal to the line. Downstream only `DeclPost … (.indDecl blk nP)` is used, with
`IndBoundsP` (already general). So the change stays inside `Front/IndLine*` and `Front/IndTwin`
(`processInd_ok` for general `tys`/`rcs`). `indRun_of_front` takes only `IndBoundsP` and is
already general in its statement.

### Prelude and pipeline

Already general:
* the prelude override pass compares whole blocks (`Prelude/BlkEq`);
* the bridge: `checkBlock_bridge` in `Bridge/IndTail`;
* the pipeline: `checkDecl_ind_ext` and `recNames` (`d.names ++ declConstants`).

## 2. Nested blocks (milestone 3)

Needs, on top of milestone 2:
* container frames in the positivity walk (`nestCont`, `NestKey` canonicalisation, `nestSeeds`);
* `classSeeds` for outside classes;
* `targetMajorOf`'s outside branch;
* the `.nested` firing mode in the install (`recFire` is already general);
* auxiliary recursors `T.rec_i` in `targetRecPins` and `streamRecsCheck`;
* in the front end, `numNested ≠ 0` and the recursor records skipped in `validateIndD`.

Effort: L across `NestPos`, `NestCtors`, `NestCtorNf`, `TargetMajor`, `Seeds`, `RecPins`,
`StreamChk`, `KindsFlat` and `IndLine`.

## 3. Suggested order

1. Recursive fields in the one-member generator (`ClassCtor`, `GenMotive.minorTy`, `GenRule`): this
   unlocks `Nat`, `List` and so on.
2. The basis-pin branch in `ki` (`pinListOk`, `andPinOk`): with step 1, the prelude passes.
3. The small k-member loops: `cnn`, `cfh`, `bis`, `consCtors`, `bt`, `cbi`, the install loop.
4. The generator over k classes (`ga`, `gb`, `FeR`, `GenRule`), then `cps`/`ctb`/`cbk` assembled
   over k members; `CBKFacts`/`CBKRun` restated generally.
5. The front end for k types (independent; can go in parallel).
6. Nested blocks.

## 4. Work done in this round

New Pancake procedures, each with its refinement proof, general over any number of members or recursors.
None is wired into `cbkBody` yet, so none is in the code table.

| File | Procedure | Refines |
|---|---|---|
| `IdxSortsAll` | `bsaBody` (`fBsa`), calls `bis` per member | `checkBlockIdxSorts mode fe p (p.members.drop i)` (`bsa_spec`) |
| `ConsCtorsAll` | `ccaBody` (`fCca`), calls `consSumCtors` per member | `pure (consBlockCtors nP ((ms.map memberGroup).drop i) fe)` (`cca_spec`; the constructor names distinct and fresh) |
| `CtorsFreshAll` | `cfaBody` (`fCfa`), calls `cfh` per member | the freshness of every member's constructors at `C.fe` (`cfa_spec`) |
| `CtorNamesAll` | `cctBody` (count), `cnaBody` (all constructor names into one block), `mnaBody` (member names), `cnkBody` (`fCnk`) | `pure (nameNodup (allCtors names) && nameNodup memberNames)` (`cnk_spec`; see `flatCtors_allCtors`, `memberNames_eq`) |
| `MembersOk` | `mokBody` (`fMok`) | no member former at the `Bool` constructors' names, every declared name fresh (`mok_spec`, `MembersOk`); `membersOk_contains` gives the twin's `memberNames.contains bt || … = false` |
| `RecInstallAll` | `riaBody` (`fRia`), calls `rin` per recursor | `pure (fe.pushAll ((recs.drop i).map plainRec))` (`ria_spec`); `blockRecs_plain`: the twin's `blockRecs` at an unnested block (`tgt < k`) |

How they slot into a general `cbkBody`:
* the name checks: `cnk` replaces `cnn`, and `mok` covers the `Bool` names and the declared names'
  freshness;
* `cfa` replaces `cfh` after the pass;
* inside `ctb`: `bsa` replaces `bis`, and `cca` replaces `consCtors`;
* the install: `ria` replaces `rin`.

Each takes the members' or recursors' pointer block of the shape (`ShapeRep`: `om`, `or`), so the caller
passes the same cells it already loads.

Statements generalized in existing files (each old statement is kept as a corollary or extended compatibly):
* `IdxSorts.bis_spec1`: one member, given only the pointer-block cell `om + 1`. Twin:
  `checkBlockIdxSorts … p [ms0]`. `bis_spec` keeps its statement.
* `CtorNames.PostCNF` has a new argument `n` and a new conjunct `n ≤ H'.length`. `cnf_spec` posts it at
  `H.length`, and `cnn_spec` is unchanged.

## 5. Second round: recursive fields in the one-member generator

Finding 1 is closed for one-member blocks: a field naming the member (its inductive hypothesis at class `0`,
with any telescope, so reflexive fields too) now runs through the generator. An inductive hypothesis at another
class hangs (none exists in a one-member block).

| File | Procedure | Refines |
|---|---|---|
| `PiCount` | `pbn` (`fPbn`) | `piBinders k h`, its binder count |
| `EraseFVars` | `rfe` (`fRfe`), `eft` (`fEft`) | `replaceFVarsGo .erase`, `eraseFVarTys` (the walk of `ReplaceFVars` with the erasing map) |
| `K53` | `elm`, `tkb` | `(xs.drop i).mapM eraseFVarTys`, `(xs.take n).drop i` |
| `K53` | `k53` (`fK53`) | `targetK53` (every `false` hangs) |
| `K53` | `cnd` (`fCnd`), `cfg` (`fCfg`) | `classNodesAgree` over a class's table entries of one constructor, `classFieldsAgree` over the kinds block |
| `ClassCtorRec` | `ihk`, `cmi`, `cfs` (`fCfs`) | the inductive hypotheses at a field, the minor slot's (`firstIhs`), `classFieldsOf p ihs` |
| `ClassCtorRec` | `cco`, `ccl` | `classCtorOf`/`classCtorsOf` at the one class, node agreement included (moved from `ClassCtor`) |
| `GenPre` | `mih` (`fMih`), `mty` | `ClassGen.minorTy.ihsGo` (`recsFrom`), `ClassGen.minorTy` with its inductive hypotheses |
| `GenRule` | `pvg` (now builds the block), `cgo` (`fCgo`), `cgr` | the prefix variables, `classGenRule.callsGo`, `classGenRule` with its recursive calls |

Representation changes:
* `CCRep`: word `o + 5` is the kinds block (`cfKindW`: `0` ordinary, `tele + 1` recursive), with `KindsOK`
  (every recursive field at class `0`, telescope below `2^32`) and `kinds.length = nF`.
* `ClassRead.PairsRep` carries the pairs' bounds (`< 2^63`, from the port's `ihOf`), so `ihk` compares words.
* `cms` no longer hangs on inductive hypotheses (`PostCMS` dropped that conjunct); `classMinorSlot_one` answers
  `firstIhs`.

New spec arguments threaded to the callers: `cgr`/`crl` take the class (`g.cls = [m]`, `m.nPc`), the
recursor's name (`classRecOf recCls cvGs 0 = some rn`) and the recursor's levels; `FeR.cfr` takes `m.nPc`
(`genRules` at `[0] [cvG]` gives `rn = cvG.name`); `ccl`/`cco` take the class-match data `k53` hands to `tcc`
(`p.members = [ms0]`, the level-parameter and opener blocks, `m.nPc < 2^62`). Lengths the port cannot read off
an `AM` result (opened telescopes, argument lists, the rule's argument list) are checked at run time against
`2^56` and hang past it.


## 5. The basis-pin branch (finding 2, the pinned basis blocks)

`ki` (`IndArm2`) no longer hangs on a block under a pinned basis block's names (`Eq`, `Nat`, `Empty`, `False`).
The record's names are matched against the reserved slices first (`bhitBody`, `BasisHit`: the kind word of the
first match, `hitW`); only a block with no match runs the freshness check (`ibkBody` wraps `ibnBody`). At a hit,
`andPinOk` passes (`andPinOk_hit`: the reserved names are none of the pinned `And` names, off `PinsOK`), and after
the block's own checks `basisNamesOk` is the twin's `pinListOk` against the pin's interning
(`basisNamesOk_hit`), which `bpnBody` (`BasisPin`, `bpn_spec`) refines:

| File | Procedure | Refines |
|---|---|---|
| `PinRec` | `genPinBlk` (inline generator) | `plainCIList cs`, every pinned constant a record (`PinRec`, `PinBlk`) |
| `PinCopy` | `pcpBody` (`fPcp`), `prlBody` (`fPrl`), `pcsBody` (`fPcs`) | `pinCopyOk`, `rulesAtLps` against the record's rules, `pinCopiesOk` |
| `PinLinks` | `fndBody`, `sgoBody`, `lgoBody`, `rllBody`, `bllBody` | `constNamed?`, `Level.subst.go` over handles (`goH`, `pinLink_val`), `rulesLinkOk`, `blockLinksOkGo` |
| `BasisPin` | `bpnBody` (`fBpn`) | `pinListOk block (BasisKind.decls k)` (scratch tier off, else hang) |
| `BasisHit` | `bhitBody` (`fBhit`), `ibkBody` (`fIbk`) | `hitW`; the freshness check at no hit |

The comparison is the twin's, renaming included (the prelude's `Eq` is `Eq.{u_1}`, the pin's `Eq.{u}`): `atLps`
runs `paramLevels` and `instLPFast` on the pin's type and rule right-hand sides; the links compare the stream
constructor's level-parameter handles with the pin constructor's renamed through the recursors' (`goH`).

`Nat` passes the pin branch but hangs earlier on its recursive constructor (finding 1).

## 6. The `And` pin (`andPinOk`'s `canonEqList` branch)

A block named exactly `[And, And.intro, And.rec]` (pins `11`, `48`, `49`) no longer hangs in `ibnBody`.
`anmBody` (`AndPin`, `fAnm`) tests the names (`AndNames`); `ibkBody` is called with `hitW + [AndNames]`, so the
freshness check is skipped at the `And` names (they are not reserved, `andNames_res` off `reserved_not_and`, which
is all `basisNamesOk` needs: `basisNamesOk_res`). `apkBody` (`fApk`) refines `andPinOk (.indDecl block nP)`: off
the `And` names it returns at once (the caller supplies the twin's `true`, `andPinOk_ind`/`andPinOk_hit`); at them
`nP = 2` (else hang), the scratch tier off (else hang), `genPinBlk` interns `andPin` (`andPinDecls_plain`), then
the three records are compared with the pin's word by word (`specR_rec0/1/2`: kind, name, level-parameter count
and handles, type, a constructor's counts and family, a recursor's counts, `K` flag, and its one rule's
constructor, field count, firing tag and right-hand side; a mismatch hangs), giving `CanonAgree`. The recursor's
`canonNames 1` is `.num .anonymous 0` interned (`numTail`, `fInternNNum`).

The twin side (`AndCanon`): `canonExprEq ps ps cs fuel e e` is `true` with the state kept when the fuel exceeds
the depth of `e`'s denotation (`canonExprEq_refl`, `edep`); the pin's records are that shallow (`andPin_shallow`,
by `decide`), so `canonEqList block pinned` is `true` at the state `canonNames 1` leaves (`canonEqList_and`).
`ki_spec` continues from `andPinOk`'s state (`andPinOk_run` carries `SeqOK`).

## 7. Mutual blocks, round 1: `checkBlockInds` at any number of members (progress log)

Goal of the round: mutual blocks (k > 1, unnested). Done so far, in order:

1. **`cbi` is general** (`CheckInds`, `cbi_spec` with its statement unchanged). The body no longer tests
   `members.length = 1`; it hangs only at k = 0 (the twin fails there) and at `nP ≥ 2^56` (a guard). It runs:
   member 0's telescope (`ct`), the other members' (`ctl`), the two agreements (`cag`), the block's `Prop`-ness,
   the new shape, every member's cvT name into an environment block (`mna` + `envBlkP`), and every member's former
   pushed (`cbn`, which also recomputes the literal flags after each push). New procedures, each refining the twin
   over `p.members.drop i`:

   | File | Procedure | Refines |
   |---|---|---|
   | `BlockTeles` | `ctlBody` (`fCtl`) | `checkBlockTeles mode fe nP (p.members.drop i)`; the sorts come back as a linked list of `[sort, next]` cells (`SLink`, at the heap base `C.HB`), each denoted (`PostCTL`); stated for any context (`∀ C`), since each step raises the store floor |
   | `BlockAgree` | `cagBody` (`fCag`) | `checkBlockAgree mode fe nP cv0 s0 rs` for the tele loop's `rs`: both telescopes opened (`of`), equal lengths, member 0's domains through `ftf` into a block, the domains defeq through `sd` (`checkStructDomsAt`; `cbd_of_csd`: its successful runs are `checkBlockDomsAt`'s, so `specR_okMonoA` switches the twin), the sort `lvlEq?`-equal to member 0's (`some true`, anything else hangs) |
   | `ConsInds` | `cbnBody` (`fCbn`) | `consBlockInds p isRec ((p.members.drop i).map (·.declared)) i fe`: per member a run-time freshness check (`envFindP`; a found name hangs, so no `Nodup` hypothesis is needed), `fMemberNZ`, `fFormerRec`, `idxIns`, `fFlags`; stated for any context (`∀ C`) since the environment grows |

   `CBICodes` gained `ac`, `ctl`, `cag`, `mna`, `cbn`; the code table was regenerated (`fCtl`, `fCag`, `fCbn`,
   `fMna` new; `check_code_names.py` reports the usual 6 BODIES warnings). The four new files are imported from
   `ConPanqueque.lean`.
   `cbi_spec` still takes `hmem` with `C.fe.find? ms.declared.name = none` per member; only `CVDen` and the
   bounds are used now (the freshness is checked at run time).

2. **`checkBlockCtors` loop** (`SumCtorsAll`, `scaBody`/`fSca`, `sca_spec`): `checkBlockCtors mode fe fe p
   (p.members.drop i)` through `scs` per member (each against its own former and the block's level parameters).
   Not wired yet (not in the code table): `cps` still calls `fSumCtors` for member 0 only.

What still hangs at k > 1, in pipeline order (the next steps):
* `cps` (`CheckPass`): replace the member-0 `fSumCtors` call by `fSca [om, 0, n, olw, nP, rs, ip, lg]`
  (`sca_spec`), and relax `ncl = 1` (`PostCPS` has `q.cls.length = 1`, read by `cbk`). `cps_spec` takes
  `p₀.members = [ms0]`, `p₀.recs = [rc]` and per-member facts for `ms0` only: restate with `∀ ms ∈ p₀.members`.
* `cbk` (`CheckBlockK`): the `nm0 = 1` and `nrl = 1` tests; swap in the round-1 loops (`cnk`, `mok`, `cfa`, `bsa`,
  `cca`, `ria`, see §4); the class reads (`nrc = 1`, `rc0 = 0`, slot 0 a motive) and `tgt = 0`.
* `ctb`/`cts`/`ga`/`gb` (the generator over k classes: `ClassCtorRec`, `K53`, `GenPre`, `GenRule`, `FeR`,
  `RecPins`, `LargeElim`, `ClassNfs`, `TargetMatch`, `StreamK`, `StreamChk`): every `g.cls = [m]`, `recs = [rc]`,
  `p.k = 1` restriction (§1 table), and inductive hypotheses at classes other than `0` (`KindsOK`).
* `bt` (`BlockTables`) over members (needs the table list built across members), `cbkInst` over tables.
* the front end (`Front/IndLine*`): `tys = [t]`, `rcs = [r]`, `numMotives = 1` (§1 "Front end").

## 8. Mutual blocks, round 2: the pass and the k-generic loops wired in (progress log)

Every step below ends with a green build; nothing here accepts a k > 1 block yet (the generator still hangs
there), but the pass and every per-member loop that `cbk` runs before and after the generator are now the general
ones, so lifting `nm0 = 1` only waits for the generator and the tables.

1. **`cps` is general** (`CheckPass`). The member-0 `fSumCtors` call is replaced by `fSca [om, 0, nm, olw, nP, rs,
   ip, lg]` (`sca_spec`, `nm` read from the members' pointer block, `olw` = member 0's level-parameter block =
   `p.lps`). The `ncl = 1` test is gone: `cse` already hangs at a class without a member; the class count is only
   guarded below `2^58` (`guardP cps_ncl 58`, needed by `cse_spec`). `cps_spec` now takes
   `p₀.members ≠ []`, `p₀.members.length < 2^55`, `p₀.recs.length < 2^59`, `∀ ms ∈ p₀.members, CPSMemberOK C p₀.nP ms`
   (the bundle of the per-member facts `cbi`/`sca`/`cbp` need: level-parameter bound and names, `nIdx`, constructor
   count, `CVDen` of the declared value, freshness, every constructor's `CVDen` and `SumCtorOK`) and
   `∀ rc ∈ p₀.recs, rc.mI < 2^56 ∧ rc.rP < 2^61`. `PostCPS` lost `q.cls.length = 1`.
   `CPSCodes` gained `sca` (the `fSca` lookup).
2. **`cbk` reads `ncl = 1` itself** (`CheckBlockK`, new local `cbk_ncl`): just before it reads class 0 it tests the
   class count (else hang). This is where the restriction now lives (with `nm0 = 1`, `nrl = 1`, `nrc = 1`, `rc0 = 0`,
   slot 0 a motive, `mb = 1`/member `0`, `tgt = 0`).
3. **`cbk`'s name checks are the k-generic loops**: `cnn` (member 0's constructors) is replaced by
   `fCnk [om, nm0]` (all constructor names and all member names distinct; the twin's condition is matched by
   `specR_congr` with `Bool.not_and`, `flatCtors` = `allCtors` by `rfl`); the inline `Bool`-name tests and the
   declared name's `envFindP` are replaced by `fMok [om, 0, nm0, bt, bf]` (`mok_spec`, `membersOk_contains` turns
   the twin's `memberNames.contains` test to `false`, freshness of member 0's declared name read off `MembersOk`).
   The loads of `cbk_oc`, `cbk_nm`, `cbk_od`, `cbk_dnm` were dropped (the locals stay declared, unused).
   `cfh` (member 0's constructors fresh at the formers' environment) is replaced by `fCfa [om, 0, nm0]`.
   `CBKCodes` gained `cnk`, `mok`, `cfa`, `ria`.
4. **`ctb` runs `bsa` and `cca`** (`BlockTail`): `ctb_k := load ctb_om` (the member count), then
   `fBsa [om, 0, k, nP, rs]` (`checkBlockIdxSorts … p.members`) and `fCca [om, 0, k, nP]`
   (`consBlockCtors nP (p.members.map memberGroup)`; the twin's `ctorGroups` is that list by `rfl`). `ctb_spec`'s
   statement is unchanged (still `p.members = [ms0]` elsewhere); `CTBCodes` gained `bsa`, `cca`.
5. **The install runs `ria`** (`CheckBlockInst`): `cbkInst` calls `fRia [cbk_or1, 0, cbk_nrl]` (the pass's recursor
   pointer block, the recursor count) instead of `fRin [cbk_orr1]`. `ci_spec` takes the recursor list
   (`PtrsRep … rcs`, `rcs.length < 2^58`, per-recursor level-parameter bound and `CVDen`) and refines
   `pure (pushTables Q (pushAll (rcs.map plainRec) K.fe))`, the twin's `pushDelta` at `blockRecs = rcs.map plainRec`
   (`blockRecs_plain`, every unnested recursor has `tgt < k`). `cbk` passes `[rc]` (defeq to the old `push`).

Code table regenerated (`fSca`, `fCnk` and its helpers, `fMok`, `fCfa`, `fBsa`, `fCca`, `fRia` now reachable).
`CheckBlockAny` (the hang paths of `cbkBody` at `nm0 ≠ 1`/`nrl ≠ 1`) follows the body: the four dropped loads were
removed there too. Full `lake build` green (no `sorry`), `main_pipeline_prelude` unchanged.

Suggested next step: the generator over k classes (§1 rows `ga`, `gb`, `cts`), starting with `ctb_spec`'s
member-0 premises (`hms`, `hmc`, `hcvd` at `consSumCtors`) restated at `consBlockCtors p.nP p.ctorGroups`; then
`cbk_spec` over `∀ ms ∈ p₀.members` and the `nm0`/`nrl`/`ncl`/`nrc` tests replaced by loops over classes.

What still hangs at k > 1, in pipeline order (unchanged from §7 except the done items):
* `cbk`: the tests `nm0 = 1`, `nrl = 1`, `ncl = 1`, `nrc = 1`, `rc0 = 0`, slot 0 a motive, the class at member `0`,
  `tgt = 0`, `≤ 1` table (`guardP cbk_nqq 1`). (`fRmFill` and `fBlockIsRec` now get the member count `cbk_nm0`
  instead of the constant `1`.) Lifting `nm0 = 1` also means restating `cbk_spec` over `∀ ms ∈ p₀.members` (its
  hypotheses `hms`, `hcl`, `hni`, `hcs`, … are member-0 shaped; `cps_spec`'s `CPSMemberOK` is the bundle to pass).
* `ctb_spec`/`cts`/`ga`/`gb` (the generator over k classes, the §1 table), `CBKRun.crt` (stated at `m ∈ q.cls`,
  `rc ∈ q.p.recs`, so already list-shaped, but `ctb_spec`'s `hcvd` premise is member-0 shaped:
  `consSumCtors p.nP ms0.cvT.name ms0.ctors` should become `consBlockCtors p.nP p.ctorGroups`).
* `bt` over members and `cbkInst`'s table branch over a list of tables.
* the front end (`Front/IndLine*`).

## 9. Mutual blocks, round 3: the generator's k-generic pieces (progress log)

Every step ends with a green build. Nothing accepts a k > 1 block end to end yet: the generator's class-shaped
core (`tmn`, `ccl`/`cco`, `gb`) still takes one class at member `0`. What changed is that every piece of the
generator's head and tail that does not depend on the class walk is now k-generic, `ctb_spec` speaks of the
twin's `consBlockCtors`, and the tables are built over all members.

1. **`ctb_spec` at `consBlockCtors`** (`BlockTail`): the premise `hcvd` and the postcondition (`PostCB`) are stated at
   `consBlockCtors p.nP p.ctorGroups C.fe` (the twin's `fe₂`) instead of member 0's `consSumCtors`. `cca` already
   answers that environment, so the proof lost its `hms` rewrite there; `cbk_spec`'s discharge of `hcvd` lost the
   `consSumCtors = consBlockCtors` bridge (`hcc`), it passes `hrun.crt` directly.
2. **The large-elimination guard at any member count** (`LargeElim`, `GenRecHead`): `lea`/`lgd` take the member
   count `k` (`leaK`, `lgdK`). Never-zero sort: pass; otherwise `k = 1` and at most one constructor pass, anything
   else hangs (the twin's `blockLargeElimAllowed p false` is `false` there, so it fails). `lea_spec`/`lgd_spec` take
   `p.k < 2^63` instead of `p.k = 1`. `ga` reads `k` from the members' pointer block (`gaK := load ga_om`) and
   `gaNk := nP + k` (was `nP + 1`).
3. **`recKExpected` at any member count** (`StreamK`): `kx` reads `k` from the shape (`load (load sh)`) and returns
   `false` unless `k = 1`. `kx_spec` takes the shape's member cells (`hom`, `hkm`, `p.k < 2^63`) and any member
   index `t` (`m.member = some t`) instead of `p.k = 1`, `m.member = some 0`. `cts` passes them from `ShapeRep`.
4. **`classStreamRecs` over all recursors** (new `StreamRecsAll`, `csrBody`/`fCsr`, `csr_spec`): each recursor's
   constant checked (`ccv` with `false false false`) from the recursors' pointer block, answering
   `(rcs.drop i).map (·.cvR)` (`PostCSR`). Wired: `ga` loads the shape's recursor block (`ga_orl`, `ga_nrl`) and
   calls `fCsr` instead of `ccv` on the one record; `GACodes` gained `csr`. `ga_spec` still has `recs = [rc]` for
   the rest of its body. `csr_spec` takes, per recursor, the level-parameter bound and denotations (`hks`).
5. **`blockTables` over all members** (new `BlockTablesAll`, `btaBody`/`fBta`, `bta_spec`): member `i`'s tables
   (`bt`), then the rest's; the two blocks are joined when one is empty, two non-empty ones hang (the install still
   takes at most one table, `guardP cbk_nqq 1`). `blockTables_cons` splits the twin's walk at the head member and
   `blockTables_len` bounds its answer (at most one table per member). `bt_spec` is now per member: it takes
   `p.lps = ms0.cvT.levelParams` instead of `p.members = [ms0]` and refines `blockTables p [ms0]`
   (`readBlock` checks that every member has the block's level parameters, so the premise holds for every member).
   Wired: `cbk` calls `fBta [om, 0, nm0, nP]` instead of `fBt [omr, nP]`; `CBKCodes` gained `bta`.
   `bta_spec` takes `∀ ms ∈ p.members, p.lps = ms.cvT.levelParams` and the per-member bounds.

What still hangs at k > 1, in pipeline order (the next steps, with what each needs):
* `cbk`: `nm0 = 1`, `nrl = 1`, `ncl = 1`, `nrc = 1`, `rc0 = 0`, slot 0 a motive, the class at member `0` (`mb = 1`),
  `tgt = 0`. Lifting them means restating `cbk_spec` over `∀ ms ∈ p₀.members` (`CPSMemberOK` is the bundle) and
  `CBKRun`/`CBKFacts` over the lists, then passing the class pointer block (`TMBlk`, `cbk_oms`) to the generator
  instead of class 0's unpacked fields.
* The generator's class walk (§1 rows `ga`, `gb`), which is the real remaining work:
  - `tmn` (`ClassNfs`): its spec answers `tbl.drop i` (every entry kept; an entry of another class hangs at `cnm`).
    At k classes `targetMajorNfs` filters: the port must build the kept entries' block per class
    (`classesNfs` = a loop over the `TMBlk`, each class's own constructors `m.ctors`, its levels and parameters),
    and `tcc` (`TargetMatch`) must compare against the class's former (`formerTys[t]`, `t = m.member`) instead of
    member 0's `ty0`/`olp`.
  - `ccl`/`cco`/`cfs` (`ClassCtorRec`): `classesCtors` over classes; `KindsOK` restricts every recursive field to
    class `0` — the kinds word must carry the class (`cfKindW`), and `ihk` must look up the IH's class
    (`firstIhs` over `rd`'s minor slots of the class), then `cfg`/`cnd` (`K53`), `mih`/`mty` (`GenPre`) and `cgo`
    (`GenRule`) must read that class instead of `0`.
  - `gb` (`GenRecCheck`): one `classRecTyOk` per recursor (`classRecTysOk` with `rd.recCls`), the motive per class
    (`motiveTy`, `motVar` counting the motives before the slot), `classFeR` pushing k recursors (`FeR`: a loop of
    the one-recursor push, then a loop of pops), `classRecsRulesOk` per recursor.
  - `cts` (`BlockTail`): `streamKCheck`/`streamRecsCheck`/`blockRecInfosTF` over the list (the one-record pieces
    `kx`, `srr`, `srs` loop naturally once the generator returns k records).
* `cbkInst`'s table branch over a list (the caller passes at most one table; `bta` hangs on two).
* The front end (`Front/IndLine*`: `tys = [t]`, `rcs = [r]`, `numMotives = 1`), §1 "Front end".

Code table regenerated (`fCsr`, `fBta` new; `check_code_names.py`: the usual 6 BODIES warnings). The two new files
are imported from `ConPanqueque.lean`. Full `lake build` green (0 errors, no `sorry`), `main_pipeline_prelude`
unchanged.

Suggested next step: `tmn`/`classesNfs` over the class block (the first class-shaped piece `ga` runs), with its
spec answering the filtered entries per class; then `ccl` over classes with the class carried in the kinds word.

## 10. Mutual blocks, round 4: the generator core over classes (progress log)

Every step ends with a green build. Still nothing accepts a k > 1 block end to end (the `ga`/`gb` class walk and
`cbk`'s tests remain), but the class-matching half of the generator (§9 plan item 1) is now k-generic.

1. **`targetAbs` over all members** (`TargetAbs`): `tab`/`ta` take the members' pointer block (`tabMs`/`taMs`) and
   a block of holes (`tabHb`/`taHb`) instead of one name and one hole. The const arm looks the constant's name up
   with `fMemFindIdx` (`mfi`, the members' `cvT` names) and, on a hit `t`, returns hole `t` from the block.
   `tab_spec`/`ta_spec` refine `targetAbsGo (ms.map (·.cvT.name)) us holes` for any member list, given
   `PtrsRep … om ms`, `BlkAt … ohb (holes.map Enc.idxW)` and `holes.length = ms.length`. `TABCodes` gained `mfi`.
2. **`targetHoles` into a block** (new `thf`/`fThf` "targetHolesFill" in `TargetMatch`, `thf_spec`): member `i`'s
   hole `.fvar (b + i)` at its former's type (`cvT.type`, read off the member record), interned in member order and
   stored at cell `i` of a fresh block (`PostTHF`: the holes, their count, the cells).
3. **`targetParamsDefEq`, `targetClassMatch` at any member count** (`TargetMatch`): `tpd` passes the members' block
   and the holes block to `ta` (`tpd_spec` over `ms`, `holes`). `tcc` no longer takes `ty0`/`nm`: it takes the
   members' block `om`, reads `k`, allocates a `k + 1` block, fills it with `thf` (the twin's `targetHoles formerTys
   pfvs.length`, run inside every match exactly as the twin does) and calls `tpd` at depth `pn + k`. `tcc_spec`
   refines `targetClassMatch mode fe p fts …` at `fts = p.formers.map (·.type)` with `EBlk … p.lps` (no
   `p.members = [ms0]`). `TCCCodes`: `fv` replaced by `thf`. `K53` (`classNodesAgree`'s match) passes `k53Ms`
   (the `[ms0.cvT.type]` / `ms0.cvT.levelParams` premises turned into `p.formers`/`p.lps` with `hms`).
4. **`targetMajorNfs` filters** (`ClassNfs`): an entry whose constructor is not one of the class's is skipped
   (was: hang), a kept entry still has to match (`tcc`; a mismatch hangs). `tmn` takes the members' block instead
   of `ty0`/`nm`; `tmn_spec` (any `p`, formers `fts = p.formers.map (·.type)`) answers
   `(tbl.drop i).filter (fun e => ctors.any (·.1.name == e.ctor))`. The kept entries are **not copied**: the only
   reader of a class's `nfs` is `classCtorOf`'s `m.nfs.filter (·.ctor == c)`, and `nfs_filter_ctor` shows that the
   class's filtered table, filtered again to one of its constructors, is the table filtered to it. So `cco`/`ccl`
   keep reading the whole table `ot` (`cco_spec`/`ccl_spec` take `tbl` and the premise
   `m.nfs.filter (·.ctor == c) = tbl.filter (·.ctor == c)` per constructor).
   `ga_spec`'s class is now `{ m with nfs := tbl.filter (fun e => m.ctors.any (·.1.name == e.ctor)) }` (also in
   `PostGR`, the `gb` call, `hgaPre`); `ctb` follows (`BlockTail`, `q.tbl`). The statements of `ctb_spec`,
   `cbk_spec` and `main_pipeline_prelude` are unchanged.
5. **`classesNfs` over the class block** (new `cns`/`fCns` "classesNfs" in `ClassNfs`, `cns_spec`): class `i` of a
   `TMBlk` (its constructors, levels, parameters read off the `TMRep`) through `tmn`, then the rest; refines
   `classesNfs mode fe p fts tbl (ms.drop i)` with answer `(ms.drop i).map (fun m => { m with nfs := tbl.filter … })`.
   Not wired yet: `ga` still unpacks class 0 (it gets class 0's fields from `cbk` through `ctb`); wiring needs the
   class pointer block (`cbk_oms`) threaded through `ctb` into `ga`, which is part of item 2 below. Not in the code
   table until wired (`check_code_names.py` does not see it).

Code table regenerated (`fThf` new; `fTab`, `fTa`, `fTpd`, `fTcc`, `fTmn` changed). Full `lake build` green
(no `sorry`), `main_pipeline_prelude` unchanged.

What still hangs at k > 1 (ordered plan, continuing §9's):
1. **Thread the class block into the generator**: `cbk` passes `cbk_oms` (the `TMBlk`, `PostCPS`) and the class
   count through `ctb` into `ga` (new `ctb`/`ga` parameters; `ctb_spec`/`ga_spec` take `TMBlk C C.H oms q.params
   q.cls` instead of class 0's unpacked fields and `hcls : q.cls = [m]`); `ga` calls `fCns [oms, 0, ncl, ot, nt,
   olp, om, pp, npp]` instead of `fTmn` (`cns_spec` is ready; `ga_spec`'s `genRecCheck_eq` lemma must then be
   restated without `hk : p.k = 1`, keeping `classesNfs` as a call).
2. **`ccl`/`cco`/`cfs` over classes** (`ClassCtorRec`): a loop `classesCtors` over the class block (per class its
   constructors, `c` its index); `cfKindW` must carry the class (e.g. `(tele + 1) + 2^32 * cls`, the telescope is
   already bounded by `2^32` in `KindsOK`); `ihk` returns the hit's class (`firstIhs` on `rd`'s minor slot of the
   class); `KindsOK` relaxed to `.recursive c tele` with `c < #classes`; `cfg`/`cnd` (`K53`) read class `c`'s
   `TMRep` (`targetMajorAt ms c`) instead of class 0's unpacked fields; `cco_spec`'s `classCtorOf … [m] 0` becomes
   `… ms c`. The `nfs` premise of `cco_spec` is already in the shape every class needs (`nfs_filter_ctor`).
3. **`mih`/`mty` (`GenPre`) and `cgo` (`GenRule`)**: read the IH's class from the kinds word (motive index of
   class `c` = `motVar` counting the motives before the slot) instead of `0`.
4. **`gb` per recursor** (`GenRecCheck`, `FeR`): `classRecTysOk` loop (`classRecTyOk` with `rd.recCls[r]`), a
   motive per class (`motiveTy`), `classFeR` as a loop of the one-recursor push and a loop of pops,
   `classRecsRulesOk` per recursor; `PostGR` over the output list.
5. **`cts`** (`BlockTail`): `streamKCheck`/`streamRecsCheck`/`blockRecInfosTF` over the output list (the
   one-record `kx`, `srr`, `srs` looped).
6. **`cbk`**: drop `nm0 = 1`, `nrl = 1`, `ncl = 1`, `nrc = 1`, `rc0 = 0`, slot-0 motive, member-0 class, `tgt = 0`;
   restate `cbk_spec`/`CBKRun`/`CBKFacts` over all members (`CPSMemberOK`); `cbkInst`'s table branch over a list.
7. **Front end** (`Front/IndLine*`, `IndBoundsP`/`indRun_of_front`), §1 "Front end".

## 11. Mutual blocks, round 5: the class block in the generator, kinds carry the class (progress log)

Every step ends with a green build. Still nothing accepts a k > 1 block end to end; `cbk` still tests `ncl = 1`
and the generator's per-class core (`ccl`/`cco`, `gb`) still works on class 0.

1. **The class block reaches `ga`** (§10 plan item 1). `cbk` passes its `cbk_oms` (the pass's `TMBlk`) and the
   class count `cbk_ncl` to `ctb` (new trailing parameters `ctb_oms`, `ctb_ncl`), which passes them on to `ga`
   (`ga_oms`, `ga_ncl`). `ga` calls `fCns [oms, 0, ncl, ot, nt, olp, om, pp, npp]` (`cns_spec`, `classesNfs` over
   the class block) instead of `fTmn` on class 0's unpacked fields; `GACodes.tmn` became `GACodes.cns`.
   `ctb_spec` takes `oms` and `hT : TMBlk C C.H oms q.params q.cls` (the `q.cls = [m]` premise stays: `ccl` and `gb`
   still read class 0); `ga_spec` takes `hT : TMBlk C C.H oms m.pfvs [m]` (derived in `ctb_spec` from `hcls` and the
   block's `pfvs` field). `genRecA` is stated for any class list `cls`, and `genRecCheck_eq` holds for every
   unnested block with `p.k ≠ 0` and every class at a member (`∀ m ∈ cls, m.member.isSome`); `p.k = 1` is gone.
   The statements of `cbk_spec` and `main_pipeline_prelude` are unchanged.
2. **The kinds word carries the class** (first half of §10 plan item 2). `cfKindW (.recursive c tele)` is now
   `(tele + 1) + 2 ^ 32 * c` (was `tele + 1`), and `KindsOK` allows any class: every kind is `.ordinary` or
   `.recursive c tele` with `tele + 1 < 2 ^ 32` and `c < 2 ^ 24` (was: class `0` only).
   * `ihk` (`ClassCtorRec`, "ihsAtField") returns `0` (no inductive hypothesis at the field), `c + 2` (exactly
     one, at class `c < 2 ^ 24`) or `1` (anything else); `ihkVal` and its lemmas (`ihkVal_cons`, `ihkVal_le`,
     `ihkVal_zero`, `ihkVal_hit`, which replaced `ihkVal_one`) follow. `PostIK` bounds the answer by `2 ^ 24 + 2`.
   * `cfs` ("classFieldsOf") hangs at an answer below `2` on an occurring field and otherwise writes
     `(|bs| + 1) + (K - 2) * 2 ^ 32` (`kindW_word`), so `cfs_spec` answers the twin's `.recursive c |bs|` for the
     hit's class `c` (was: a hit at a class other than `0` hung here).
   * The three readers of the kinds word, `cfg` (`K53`, `classFieldsAgree`), `mih` (`GenPre`, `minorTy.ihsGo`) and
     `cgo` (`GenRule`, `classGenRule.callsGo`), test the word with `guardP _ 32` right after its `≠ 0` test: a word
     at class `c ≠ 0` hangs there (they still read class 0's record), class `0` decodes as before. So the hang
     moved from the producer to the consumers, which is where plan item 3 below replaces it by the class's record.
   No statement above `ccl` changed (`CCRep` keeps `KindsOK`).
3. **The minor-slot lookups take the class** (prerequisite of `cco` at class `c`). `isHitC c cn` (was: class `0`
   built in), `cmsHit l c cn`, `firstIhs c cn`, `cmsHits_cons`/`cmsHits_props`/`classMinorSlot_one rd c cn` (the twin's
   `classMinorSlot rd c cn` at any class). The three slot walks gained a trailing class parameter and compare the slot's
   class with it instead of `0`: `cms` (`ClassCtor`, "minorSlotCount", `cms_spec … cn cc hcc`), `cmi` (`ClassCtorRec`,
   "minorSlotIhs", `cmi_spec`, `PostCMI … cn cc`) and `fms` (`GenRule`, "findMinorSlot", `fms_spec`, `PostFMS … cn cc`;
   `find_zip_hit` takes the class). The callers still pass class `0`: `cco` (`fCms`/`fCmi` with `.const 0`) and `cgr`
   (`fFms` with `.const 0`), so no statement above them changed.

Code table regenerated after the steps above (`fCns` new; the other changes keep every procedure name, so the table
is otherwise unchanged; `check_code_names.py`: the usual 6 BODIES warnings). Full `lake build` green (0 errors, no
`sorry`), `main_pipeline_prelude` unchanged.

What still hangs at k > 1 (ordered plan, continuing §10's; items 1 and the kinds/slot halves of 2 are done):
1. **`cfg` over the class list** (`K53`): `cfg_spec` still takes `p.members = [ms0]` and answers
   `classFieldsAgree … [ms0.cvT.type] [m] …`. Restate it over `fts = p.formers.map (·.type)` (as `tcc` already is,
   §10 step 3), `p.lps`, and a class list `ms` with `ms[0]? = some m` (the guard admits only class-0 hypotheses, so
   `targetMajorAt ms 0 = m` is the only class it reads); its `ms0.cvT.type`/`ms0.cvT.name` parameters (`cfgTy0`,
   `cfgNm`, passed on to `cnd`/`k53`) then become `p.formers`/`p.lps`-based, as `k53Ms` already is.
2. **`cco`/`ccl` at class `c`, then `ccs` (`classesCtors`) over the class block** (`ClassCtorRec`): `cco` takes the
   class index (passed on to `fCms`/`fCmi`, which are ready) and class `c`'s `ds` (for `instPis`) and `member` (for
   `targetCtorAt`) besides class 0's fields (for `cfg`); `cco_spec` answers `classCtorOf … ms c ctor` with
   `ms[c]? = some mc`, `ms[0]? = some m0`. `ccl` loops `cco` over class `c`'s constructors; a new `ccs` loops `ccl`
   over the `TMBlk` (per class its `CtorsRep`, `ds`, `member`), answering `classesCtors … ms 0 ms` as a block of
   `PRep … CCRep` blocks; `ga` calls `ccs` instead of `ccl` and `cmc` compares against the summed lengths.
3. **Readers of the IH's class** (`mih`/`mty` in `GenPre`, `cgo` in `GenRule`, `cfg` in `K53`): replace the
   `guardP _ 32` hang by decoding `c = w >>> 32`, `tele = (w &&& (2^32-1)) - 1` and reading class `c`'s record
   (motive index of class `c` = `motVar`, counting the motives before the slot; `ihParts g c`).
4. **`gb` per recursor** (`GenRecCheck`, `FeR`, `RuleCheck`, `GenMotive`): `ClassGen` with `cls`/`ctors` lists
   (`gb_spec` takes `g.cls = [m]`, `ctors = [xs]`, `recs = [rc]`, `recCls = [0]`, slot 0 a motive):
   `classRecTysOk` loop (`classRecTyOk` with `rd.recCls[r]`), a motive per class, `classFeR` as a loop of the
   one-recursor push and a loop of pops, `classRecsRulesOk` per recursor; `PostGR` over the output list. Then
   `ga_spec`/`ctb_spec` drop `q.cls = [m]`/`p.recs = [rc]` (the class block is already threaded, step 1).
5. **`cts`** (`BlockTail`): `streamKCheck`/`streamRecsCheck`/`blockRecInfosTF` over the output list.
6. **`cbk`**: drop `nm0 = 1`, `nrl = 1`, `ncl = 1`, `nrc = 1`, `rc0 = 0`, slot-0 motive, member-0 class, `tgt = 0`;
   `cbk_spec`/`CBKRun`/`CBKFacts` over all members (`CPSMemberOK`); `cbkInst`'s table branch over a list.
7. **Front end** (`Front/IndLine*`, `IndBoundsP`/`indRun_of_front`), §1 "Front end".

## 12. Mutual blocks, round 6: node agreement and the constructors over the class block (progress log)

Every step ends with a green build. Still nothing accepts a k > 1 block end to end (`cbk` still tests `ncl = 1`
and the rest of §11's restrictions; `gb` and the IH readers in `GenPre`/`GenRule` still read class 0), but the whole
`classesCtors` stage of the generator (node agreement included) is now k-generic and wired.

1. **`k53`/`cnd`/`cfg` off member 0** (`K53`, §11 plan item 1). `k53_spec`, `cnd_spec`, `cfg_spec` (and `cco_spec`,
   `ccl_spec`) no longer take `p.members = [ms0]`: they take `fts` with `fts = p.formers.map (·.type)`,
   `p.members.length < 2 ^ 58`, `p.lps` for the level parameters, and two arbitrary words `wty wnm` for the dead
   `k53_ty0`/`k53_nm` parameters (no procedure reads them since §10 step 3; they are only passed through).
2. **`cfg` decodes the field's class** (§11 plan items 1 and 3 for `cfg`). New `KindDecode` (lemmas `kindW_cls`,
   `kindW_tele`; `TMBlkR`, a block of `TMRep` records with no condition on `nfs`/`pfvs`, with `tmBlkR_mono`,
   `tmBlkR_of_tmBlk`, `tmBlkR_nfs`). `cfg` ("classFieldsAgree") takes the class block `oms` and the class count
   instead of class 0's unpacked fields (`cfgParams` lost `cfgK`, `k53Npc`, `k53Us`, `k53Pa`, `k53Nd`, gained
   `cfgOms`, `cfgNcl`; the five became locals). At a recursive field it computes `c = w >>> 32` (hang unless
   `c < ncl`; the twin's `targetMajorDefault` is never reached), `tele = (w &&& (2^32-1)) - 1`, reads class `c`'s
   `ind`, `lvls`, `ds`, `nPc` off the block (`guardP` 58 on `nPc` and `|ds|`) and runs `classLeafAt`/`cnd` against
   class `c`. `cfg_spec` answers `classFieldsAgree … fts ms …` for any class list `ms` with
   `TMBlkR C H0 oms ms`, `∀ m ∈ ms, m.pfvs = pfvs`. The `guardP cfgX 32` hang is gone.
3. **`cco`/`ccl` at class `cl`** (§11 plan item 2, first half). `cco` ("classCtorOf") gained trailing parameters
   `ccoC` (the class index, passed to `fCms`/`fCmi` instead of `.const 0`), `ccoOms`, `ccoNcl` (passed to `cfg`);
   `ccl` passes `cclC`, `cclOms`, `cclNcl` through. `cco_spec`/`ccl_spec` answer `classCtorOf … ms cl` /
   `classCtorsOf … ms cl` for `ms[cl]? = some m`, `m.member = some t0` (any member), `TMBlkR C C.H oms ms`;
   `hnpc0` relaxed to `2 ^ 63`.
4. **`classesCtors` over the class block** (new `ccs`/`fCcs` "classesCtors" and `sll`/`fSll` "sumLengths" in
   `ClassCtorRec`). `ccs` reads class `i`'s constructors, `ds`, `ind`, `lvls`, `nPc` off the `TMBlkR` and runs `ccl`
   at class `i`, then the rest, answering `classesCtors … ms i (ms.drop i)` as a block of blocks (`PostCCss`);
   `ccs_spec` needs every class at a member, per-class bounds, and the `nfs` premise per class. `sll` sums the
   inner lengths (a sum reaching `2 ^ 62` hangs), answering `acc + ((xss.drop i).map List.length).sum`.
   **Wired**: `ga` calls `fCcs [oms, 0, ncl, …]` then `fSll` and compares the minor count with the sum (the twin's
   `(ctors.map List.length).sum`), then loads class 0's block for `gb` (still single-class). `GACodes.ccl` became
   `GACodes.ccs` + `GACodes.sll`; `classesCtors_one` recovers class 0's run for the rest of `ga_spec`.
5. **`motiveSlotOf`** (new `MotiveSlot`, `msl`/`fMsl`, `msl_spec`): the slot of the `c`-th motive from slot `i`
   on, `0` if none; `motiveSlot_eq` turns the twin's `ClassRead.motiveSlot` into the walked form. Not wired yet
   (not in the code table): it is the piece `mih`/`cgo`/`gb` need for `ClassGen.motVar c`.

Code table regenerated (`fCcs`, `fSll` new; `fCfg`, `fCco`, `fCcl`, `fGa` changed; `check_code_names.py`: the usual
6 BODIES warnings). `KindDecode` and `MotiveSlot` are imported from `ConPanqueque.lean`. The statements of
`ga_spec`, `ctb_spec`, `cbk_spec` and `main_pipeline_prelude` are unchanged.

What still hangs at k > 1 (ordered plan, continuing §11's; items 1, 2 and the `cfg` part of 3 are done):
1. **Readers of the IH's class in `GenPre`/`GenRule`** (`mih`, `cgo`, and `mty`'s conclusion motive): replace the
   `guardP _ 32` hang by the `cfg` decoding (`kindW_cls`/`kindW_tele`), read class `t`'s `nPc` off a `TMBlkR`
   (hang past the block; the twin's `nPc := 0` default is never needed) and the motive variable
   `fvar (nP + msl slots t)` (`msl_spec` + `motiveSlot_eq` give `ClassGen.motVar t`). This needs the class block and
   the slot block threaded from `ga` through `gb` into `mty`/`mih`/`cgr`/`cgo` (their specs take
   `g.cls = [m]`, `hsl0` today; replace by `TMBlkR C H oms g.cls` + `SlotBlk … g.slots`).
2. **`gb` per recursor** (`GenRecCheck`, `FeR`, `RuleCheck`, `GenMotive`), unchanged from §11 item 4; `ga` already
   holds every class's constructors (`ga_css`, a block of blocks), so `gb` should take that block instead of class
   0's (`ga` now loads `ga_css[0]` only to feed today's `gb`).
3. **`ga_spec`/`ctb_spec` over class lists**: drop `q.cls = [m]`, `p.recs = [rc]`, `p.members = [ms0]`; `ccs_spec`
   already states everything per class (`classesCtors_one` is then no longer needed).
4. **`cts`** (`BlockTail`): `streamKCheck`/`streamRecsCheck`/`blockRecInfosTF` over the output list.
5. **`cbk`**: drop `nm0 = 1`, `nrl = 1`, `ncl = 1`, `nrc = 1`, `rc0 = 0`, slot-0 motive, member-0 class, `tgt = 0`;
   `cbk_spec`/`CBKRun`/`CBKFacts` over all members (`CPSMemberOK`); `cbkInst`'s table branch over a list.
6. **Front end** (`Front/IndLine*`, `IndBoundsP`/`indRun_of_front`), §1 "Front end".

## 13. Mutual blocks, round 7: the IH readers, the prefix and the rules over the class block (progress log)

Every step ends with a green build. Still nothing accepts a k > 1 block end to end (`cbk` still tests `ncl = 1` and
the rest of §11's restrictions; `ga`/`gb` still check one recursor at class `0`), but every *per-class reader* in the
generator now reads its class off the class block, and the prefix (`prefixBinders`) is generated for any number of
classes and motives.

1. **IH readers decode the class** (§12 plan item 1). `mih` (`GenPre`, "minorIhs") and `cgo` (`GenRule`,
   "ruleCalls") replace the `guardP _ 32` hang by the `cfg` decoding (`kindW_cls`/`kindW_tele`): class
   `c = w >>> 32` (hang unless `c <` the class block's length word), telescope `(w &&& (2^32-1)) - 1`, class `c`'s
   `nPc` read off the class block (`guardP` 58). `mih` takes the class block and the slot block (`mih_oms`,
   `mih_osl`, replacing `mih_npc`) and builds the motive variable `fvar (nP + motiveSlotOf slots c)` (`fMsl`, first
   use of `msl`; `motiveSlot_eq` turns the twin's `ClassGen.motVar`); `cgo` takes the class block and a block of
   recursor names indexed by class (`cgo_oms`, `cgo_rnb`, replacing `cgo_npc`/`cgo_rn`), its spec asking
   `classRecOf recCls cvGs t = some rns[t]` for every `t < |rns|` (a class past the block hangs).
   `mih_spec`/`cgo_spec` take `TMBlkR … g.cls` (+ `SlotBlk … g.slots` / the names block) instead of `g.cls = [m]`.
   `blk_len_lt` moved from `K53` to `GenPre`.
2. **`minorTy` at class `c`** (`mty`, `GenPre`): params `[cc, d, oms, osl, nP, cl]` (was class 0's `ds`, `lvls`,
   `nPc` unpacked); reads class `cl`'s `lvls`, `ds`, `nPc` off the block (`guardP` 58/56), the conclusion's motive
   through `msl`. `mty_spec` answers `g.minorTy cl x d` for any `cl < 2^63` (past the block hangs).
3. **`classGenRule` and `classRulesOk` at class `cl`** (`cgr`, `GenRule`; `crl`, `RuleCheck`): the minor-slot search
   (`fms`) at `cl` (was `.const 0`), the class block and the names block passed to `cgo`. `crl_spec` answers
   `classRulesOk … cl xs`; the names block is a premise under the `∀ H` (it is allocated after the context, like the
   pushed block). `cfr` (`FeR`) passes its pushed-names block `[cvG.name]` as the names block (one recursor at class
   0: `classRecOf [0] [cvG] 0 = cvG.name`), and the class block; `cfr_spec` lost `hnpc`, gained `oms`/`TMBlkR`.
4. **`ClassGen.major`, `motiveTy`, `classGenRecTy` at class `c`** (`mjr`, `mot`, `grt`, `GenMotive`): `mjr` takes
   `[oms, fts, cl, d]` — class `cl`'s record off the class block and its former type off a former-type block
   (`BlkAt … g.formerTys`), both hanging past the block (`guardP` 56 on `nIdx`, `|ds|`); `mot` `[oms, fts, cl, d,
   elim]`; `grt` `[pre, |pre|, nP, oms, fts, osl, cl]` (its motive through `msl`). Specs answer `g.major cl d`,
   `g.motiveTy cl d`, `classGenRecTy g cl`.
5. **`prefixBinders` over any number of classes** (`psl`, `pb`, `GenMotive`): `psl` walks the slot stream with a
   running motive count (`psl_mc`, `motCnt slots i`, `motCnt_succ`): a motive slot is `mot` at class
   `motCnt slots i` (the twin's count of motives before it; the twin's anonymous filter predicate is matched with
   `List.filter_congr`), a minor slot `.minor c C _` looks `C` up in class `c`'s block of the constructor
   block-of-blocks (`ga_css`, `PostCCss`'s `PRep … PRep … CCRep`; a class past it hangs) and runs `mty` at `c`. No
   more slot-0-is-the-motive or class-0-only restriction in the prefix. `pb` passes `[ps, sl, n, nP, css, fts, el,
   oms]`.
6. **Threading**: `cro` (`ClassConst`) passes `oms`/`fts`/`osl` to `grt` (still at class 0, its own member/index
   checks still class 0's); `gb` takes `[opp, osl, nsl, nP, oc, nc, nIdx, elim, orr, oms, css, fts]` (lost class 0's
   `ds`, `|ds|`, former type, `ind`, `lvls`, `nPc`); `ga` passes its `ga_css` and allocates the former-type block
   `[ms0.cvT.type]` (`ga_fts`) right before `gb`. `gb_spec` lost `hft`, `hsl0`, `hds`, `hdl`, `hnpc`, gained the
   constructor block-of-blocks and the former-type block. The statements of `ga_spec`, `ctb_spec`, `cbk_spec` and
   `main_pipeline_prelude` are unchanged.

Code table regenerated (no new procedure names; `fMsl` "motiveSlotOf" now reachable and in the table; `gaBody` now
takes the context, `gaBody C`, since it allocates; `check_code_names.py`: the usual 6 BODIES warnings). Full
`lake build` green (0 errors, no `sorry`), `main_pipeline_prelude` unchanged.

What still hangs at k > 1 (ordered plan, continuing §12's; item 1 is done, and the prefix half of item 2):
1. **`cro` at class `c`** (`ClassConst`, `classRecTyOk … c`): read class `c`'s record (`nIdx`, and the member word
   `optNatW member` at record offset 2) instead of taking class 0's `nIdx`/`m.member = some 0`; the member test is
   `rc.tgt == member.getD k` (decode: `0 ↦ k`, `t + 1 ↦ t`; compute it without an `ite` inside a `seq`, e.g.
   `(Mb - 1) + (Mb == 0) * (k + 1)`, or split before the record reads); pass `c` to `grt` (ready, `grt_spec … cl`).
2. **`classRecTysOk` loop** (new procedure over the stream's recursor records `ga_orl`/`ga_nrl` and the `recCls`
   block, `BlkAt … (rd.recCls.map ofNat)` from `ClassRead`): per recursor `r` run `cro` at class `recCls[r]`, collect
   the `cvG` records into a block; `gb_spec` over `p.recs`, `cvRis = p.recs.map (·.cvR)`, `rd.recCls` (drop
   `hrecs : p.recs = [rc]`, `hrc0`).
3. **`genRules` over the recursors** (`FeR`, `cfr`): the push of every rule-less recursor (`classFeR.go` as a loop of
   today's one push), the flush, `crl` per recursor at class `recCls[r]` over `css[recCls[r]]` (`crl_spec` is
   already per class, `cl`), the names block built from `classRecOf recCls cvGs t` for every class (a loop: first `r`
   with `recCls[r] = t`; `cgo` hangs on a class past the block, so a block of the classes that have a recursor is
   enough), the pops in reverse, the flush; `PostGR` over the output list `[(cvG, m, rhss)]`.
4. **`ga_spec`/`ctb_spec` over class lists**: drop `q.cls = [m]`, `p.recs = [rc]`, `p.members = [ms0]`,
   `rd.recCls = [0]`; `ccs_spec` already states everything per class (`classesCtors_one` no longer needed); the
   former-type block must become `formerTysC = ms2.mapM (classFormerTy …)` (today `ga` allocates `[ms0.cvT.type]`;
   for an unnested block it is the class's member's `cvT.type`, a loop over the class block reading each class's
   member and the members' block).
5. **`cts`** (`BlockTail`): `streamKCheck`/`streamRecsCheck`/`blockRecInfosTF` over the output list.
6. **`cbk`**: drop `nm0 = 1`, `nrl = 1`, `ncl = 1`, `nrc = 1`, `rc0 = 0`, slot-0 motive, member-0 class, `tgt = 0`;
   `cbk_spec`/`CBKRun`/`CBKFacts` over all members (`CPSMemberOK`); `cbkInst`'s table branch over a list.
7. **Front end** (`Front/IndLine*`, `IndBoundsP`/`indRun_of_front`), §1 "Front end".

## 14. Mutual blocks, round 8: the recursor types and the rules over every recursor (progress log)

Items 1–3 of §13's plan are done as procedures and specs general in the recursor list; `gb` calls them (still at
`p.recs = [rc]`, `g.cls = [m]`, `recCls = [0]`, because `ga`/`ctb`/`cbk`/`cts` are still one-member).  Every step
ends with a green build; no `sorry`.

1. **`cro` at class `c`** (`ClassConst`, `classRecTyOk … c`): params `[rr, ns, pre, prl, nP, oms, fts, osl, cl]`
   (lost `ni`).  Reads the class block's length (a class past it hangs), class `c`'s record pointer, its `nIdx`
   (`guardP` 56) and its member word (`optNatW`, record offset 2).  An outside class (`member = none`, word `0`)
   hangs (nested blocks only); otherwise the recursor's `tgt` is compared with `word - 1`.  `croTail` (the
   `rP`/`mI` checks, `grt` now at `cl`, the constant check, the defeq) is unchanged otherwise.  `cro_spec` lost
   `hcls`/`hmm`/`hni`, gained `cl < 2^63`.
2. **`classRecTysOk` loop** (`RecTys`, new procedure `crs` "classRecTysOk"): over the stream's recursor records (a
   `PtrsRep … RecRep` block) and the recursors' classes (the `ClassRead` word block `recCls`), `cro` on recursor `i`
   at class `recCls[i]`, the generated constants collected (`PRep … CVRep`, `PostCVGs`); a class list shorter than
   the recursor list hangs.  `crs_spec` answers `classRecTysOk mode fe g k (rcs.drop i) ((rcs.map (·.cvR)).drop i)
   (recCls.drop i)`.  `ptrsRep_len_lt` (a pointer block is shorter than `2^61`).
   *Wiring*: `gb` takes the recursor block and the class block (`gbOrl`, `gbOrc`, new params) and calls `crs`
   (`classRecTysOk_one` inverts the run at one recursor); `ga` passes its `gaOrl` and a new param `gaOrc`; `ctb`
   passes a new param `ctbOrc`; `cbk` passes the `ClassRead` record's class block `cbkOrc`.  `ga_spec`/`ctb_spec`
   gained `orc`/`hRC : BlkAt … (rd.recCls.map ofNat)`.
3. **`genRules` over every recursor** (`RecRules`, `RecPush`, `RecNames`, `RecGen`):
   * `crr` "classRecsRulesOk" (`RecRules`): recursor `i` at class `c = recCls[i]` runs `crl` over class `c`'s
     constructor block (the block-of-blocks `css`), and contributes the triple record `[rules block, constant,
     class c's record]` (`RRRep`, `PostOut`); stops when either list runs out (the twin's zip); a class past `css`
     or the class block hangs.  `crr_spec` answers `classRecsRulesOk mode C.fe pushed g recCls cvGs (cvGs.drop i)
     (recCls.drop i)`.
   * `gpr` "genRulesPush" (`RecPush`): recursor `i`'s rule-less record written (`constRec`, rules block empty), its
     name inserted (present: hang), the flags read, recursors `i+1…` recursively, then the name undone and the
     flags read again; past the last recursor the flush and `crr`.  `gpr_spec` is by fuel induction over contexts
     whose environment is the one with recursors `0…i-1` pushed (`classFeR.go`), answering `gprM … i C.fe`
     (`gprM_succ`/`gprM_end`, `classFeR_go_fst`), and comes back at exactly the entry environment (`PostGP`: the
     constant map answering alike, `sr_fe`/`specR_feI` to switch the environment).
   * `cvn` "constNames" (the pushed names), `frc` "firstRecAt" and `rnb` "classRecNames" (`RecNames`): every
     class's first recursor name, `classRecOf_of_first` (`firstRecFrom`); a class with no recursor hangs.
   * `cfk` "genRulesAll" (`RecGen`): names, recursor names, `gpr`, the flush; the environment handed back is the
     twin's `feBack` (`classFeR`'s pops, flags set back), which answers as the entry one (`classFeR_pop`,
     `classFeR_pop_flags`; `feBack_find`/`_findTable`/`_tblGate`/`_flagsOK`/`_litsPinned`).  `cfk_spec` answers
     `genRules mode C.fe p g recCls cvGs` with `PostGRK` (the output list as triple records).
   *Wiring*: `gb` calls `cfk` instead of `cfr` and returns the first triple (`genRules_out_one` inverts the run at
   one recursor, so `gb_spec`'s `PostGR` is unchanged).  `cfr` (`FeR`) is no longer called.

The statements of `ga_spec` (+ `orc`), `ctb_spec` (+ `orc`), `cbk_spec` and `main_pipeline_prelude` are otherwise
unchanged.  New procedures in the code table: `classRecTysOk`, `classRecsRulesOk`, `genRulesPush`, `constNames`,
`firstRecAt`, `classRecNames`, `genRulesAll`.

Binary (re-emitted, compiled from a snapshot of `checker.pnk` in the scratchpad, literal work included): 113/612
e2e fixtures accepted (95 before; the gain is the literal lines). No change from accept to reject. No fixture
accepted that `e2e-expected.txt` lists as reject/decline/error; the seven accepted `cmp_*_s` files appear only as
the solution half of `--compare` pairs (whole solution exports, checked in full). The mutual fixtures still die
in the front end (`f_line23`), which sits upstream of every piece changed here.

What remains for k > 1 (ordered):
1. **`gb_spec` over the lists**: drop `hrecs`, `hcls`, `hctors`, `[0]`; `recCls = rd.recCls`, `cvRis = p.recs.map
   (·.cvR)`; return the whole output list (`PostGRK`'s `PRep … RRRep`) instead of its first triple, and restate
   `PostGR` over the list (its consumers: `ga`, `ctb`, `cts`).  `hcvd` becomes a statement about
   `classRecTysOk`'s output (every generated type denotes).
2. **`ga_spec`/`ctb_spec` over class lists** (§13 item 4): `ga` still checks one member's pins, one class's table
   entries (`tmn`) and allocates the former-type block `[ms0.cvT.type]`; generalize to `formerTysC`.
3. **`cts`** over the output list (`streamKCheck`/`streamRecsCheck`/`blockRecInfosTF`), §13 item 5.
4. **`cbk`** (§13 item 6) and the **front end** (§13 item 7; the 29 mutual fixtures die there, `f_line23` 7673).
