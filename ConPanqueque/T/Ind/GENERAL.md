# Generalizing the inductive path: survey

Status on 2026-11-27, commit 0be975b plus the work recorded at the end. The goal is general inductive
blocks: k members, one recursor per member, then nested blocks with auxiliary recursors.

The twin (`deps/con-ron/proof/ConRon/Arena/Inductives/*`, `Arena/Install.lean`,
`Arena/Frontend/ExportC.lean`) is general. So are the bridge (`Bridge/IndTail.lean`) and the pipeline
(`Pipeline/IndExt/*`). Every restriction listed below is in the Pancake port: the procedures and
their `SpecR` refinement proofs. A port procedure may hang wherever the twin goes on. So a
restriction costs completeness, never soundness: an unsupported block makes the program hang.

## 0. Findings that come before mutual blocks

1. **Recursive constructors hang, even in one-member blocks.** The generator supports only
   *ordinary* fields:
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
| `cbi` (`CheckInds`, `cbi_spec`) | `checkBlockInds` | 1 (`members.length = 1` tested) | Needs `checkBlockTeles` and `checkBlockAgree` (the sorts and parameter telescopes of members 1..k-1 against member 0's), and `consBlockInds` over all members (`fFormerRec` per member, with the `isRec` and caps records). | M |
| `fSumCtors` (`SumCtor`) | `checkBlockCtors` | per member | One call per member, in a loop. | S |
| `bn` (`NestCtx`) | `blockNestCtx` | G | none | – |
| `cbc` (`ClassPass`), `crd` (`ClassRead`), `cmj`/`tmo` (`TargetMajor`) | `checkBlockClasses`, `classRead`, `classMajors` | G, U (an outside inductive halts) | none for milestone 2 | – |
| `cbp` (`CheckPos`) with `nrt`, `nul`, `num`, `nt`/`np` (`NestPos`), `RFHole`, `NestCtors` | `checkBlockPositivity` | G over members, U (empty frame stack; `nestCont` hangs) | none for milestone 2. Nested blocks need container frames (`nestCont`, `nestKeyOf`, `NestCtorNf` keys). | L (nested) |
| `sd` (`Seeds`) | `classSeeds` | U (no seeds) | Nested: seeds for outside classes plus `nestSeeds`. | M (nested) |
| `kf1`/`kf2`/`kf3` (`KindsFlat`) | `nestKindsFlat` (`blockNestedBit = false`) | G | Nested: drop the check and carry `nested`. | S |
| `cfh` (`CtorsFresh`) | constructor freshness at `env1` | 1 (only `ms0.ctors`) | Run over the flattened constructors. | S |
| `bt` (`BlockTables`, `bt_spec`) | `blockTables` | 1 | A loop over members: a structure-like member (one constructor, no indices) gives a table, otherwise none. Each table goes through `cst` and the install loop. | S |
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
