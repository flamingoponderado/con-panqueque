# The frontend and the verdict (design notes)

Status (98fcd25): the declaration layer ends in a con-leche verdict.

- `T/Decl/Start.lean`: `checkDeclsPure_spec`. The Pancake fold refines the twin's
  `checkDeclsPure` from the driver's index (`feStart`).
- `Bridge/SeqFold.lean`: `seq_bridge'`. An accepting twin `checkDeclsPure .verified` run on value
  records is an accepting con-leche `checkDeclsPure` run on the denoted stream. con-ron bridges
  only its pooled check phase; this is the sequential one.
- `T/Decl/FoldVerdict.lean`: `fold_verdict`. The Pancake fold stops (`Stop`) or returns. When it
  returns, con-leche accepts.

`fold_verdict`'s hypotheses are what the frontend must establish:

| hypothesis | meaning | established by |
|---|---|---|
| `CtxOK C`, `SR C s t` (in `Pre`) | Pancake memory represents twin state `s` | frontend specs |
| `C.fe = feStart C.pins`, `s.pins = C.pins` | the driver's start index | pin interning |
| `BlkAt C.H ob …`, `RecOK C rᵢ dᵢ` | the record block in the heap | frontend record install |
| `FoldCodes .verified C` | the code table | concrete program |
| `StateOK s`, `PinsOK s`, `PersPins s`, `PinsDenote …` | twin store facts | con-ron `stages_frame` |
| `denoteDecls s.store ds = some dsP` | records denote con-leche's | con-ron `stages_frame` |
| `IsValueDecl` for every record | port scope | frontend rejects other kinds (until ported) |

## The twin pipeline (con-ron `Bridge/Stages.lean`)

    internReservedPins → builtinPreludeE → parseChunks → preparePrelude → internAllPins → check

`stages_frame` turns runs of the first five stages into everything in the right-hand column
above. The Pancake frontend must refine those five twin stages, run in sequence on one state.

**Caveat (scope):** `preparePrelude` puts the built-in prelude in front of the stream, and the
prelude has inductive blocks (`Nat`, `Eq`, …) and axioms. Until those kinds are ported, the
Pancake checker stops on every real input. The soundness theorem holds, but only vacuously.
Porting inductives is therefore on the critical path to a useful checker, alongside the frontend.

## The scanner

The twin's `feedChunk`/`applyFinalLine` call con-leche's `scanLineFwd`
(`deps/con-leche/ConLeche/Frontend/Scan/Fast.lean`, 2612 lines). The Pancake scanner is a
function-by-function port of `scanLineFwd` and is proved to refine it. That refinement *is* the
required numeral-scanning equivalence: `readNat`/`readNat64`/`readNatAt` are ported with their
machine-word and long-run split, and big `natVal` literals go through the arena's limb
representation.

- Input buffer: bytes in Pancake memory read with `loadByte`. Needs a byte-region predicate
  `BytesAt m a bs` and a `loadByte` rule in `Logic/` (not yet present).
- Chunks: one FFI `read` per chunk into the buffer, as in `parseChunksGo`. The end-to-end theorem
  is relative to the FFI oracle's byte stream, as con-pastel's is.
- Records: `LineRec` is consumed at once by `applyLine` (interning). The Pancake scanner writes
  the scanned fields into a scratch block, and the interning half reads them. There is no
  separate record datatype in memory.

## The interning half

`applyLine`, `parseNameEntryD`, `parseLevelEntryD`, `parseExprEntryD`, `parseCVD`, `pushDecl`:
table lookups plus the store's intern operations, which are already ported (`T/Intern*`).
Declarations go into the record block in the `RecOK` layout (kind word, CVE, value, hint).

## Order of work

1. `loadByte` rule and the byte-region predicate.
2. Scanner primitives (`skipWs`, `skipDigits`, `readNat*`, `keyEnd`, `matchLit`, …) with
   refinement specs.
3. The record scanners, then `scanLineFwd`.
4. Interning (`applyLine`), `parseChunks`, then the prelude (static data, parsed by the same code).
5. `preparePrelude`, `internAllPins`, `internReservedPins`.
6. The code table, the executable (C harness: FFI read, exit code), and the top-level theorem.
7. Remaining kinds: axioms, quot, inductives, pinned `Nat`/reduce certification.

## Scanner status and the record-scanner plan (556b9a8)

Proved against con-leche (each `*_refines`: the Pancake function stops or returns con-leche's
value, frame unchanged):
- `skipWs`, `skipDigits` (generic skip loop `Skip.lean`);
- `readNatAt`, capped at `2^62` (`ReadNat.lean`);
- `numEnd` (`NumEnd.lean`);
- `keyAt` (`Keys.lean`/`KeyFun.lean`: the decision tree as data, generated from the source,
  plus a generic table compiler);
- `keyEnd` (`KeyEnd.lean`).

Infrastructure: `RetSpec` (pure callee), `call3_ret`, `retSpec_seq/ite/dec`.

**Record scanners.** Every `scan*Loop` is one object loop:

    ws → '}' (seen-mask complete?) | ',' | '"' key → keyEnd, valueAt, keyAt → per-key action

Each action scans one value (nat, string, nat list, bool, nested object), checks a duplicate bit
and sets a slot. Error payloads are not modelled: an `.err` is a rejection. Plan:
1. A generic interpreter `objLoop spec` over a slot table (key → bit, value kind, slot).
2. Prove each con-leche loop equals `objLoop` at its table, by induction on the measure with a
   shared tactic.
3. Compile the table to Pancake once and prove it once, as for `keyAt`.

Capped numbers (`natCap`) are sound because any index at or above `2^62` misses every table, so
both sides reject.

## Status at be8464b: the line scanner is done; interning is next

Proved (no `sorry`): each Pancake scanner refines or is sound for con-leche's, up to
`scanLineFwd` (`lineStmt_spec`). `lineFun x` returns one output of a line: the next position, the
payload tag, the index kind, the index, or the payload's value or position. The code assumptions
reduce to concrete table entries (`ScanCodes`, `RecTable`, `lineCodes_of`).

**Interning (`applyLine`).** The twin threads a pure `StateD` holding three stream-indexed handle
tables (`IdTable`). Plan:
- The tables are fixed-capacity word arrays in the value heap `H` (`ctxH`, `sr_heapStore`),
  sized from the input length. An index past the capacity is rejected, which is sound.
- `TblRel C st` relates the arrays to `StateD`.
- Each record kind is a SpecR procedure:
  - names: `internNNode` (the string component is read again from the buffer by its position);
  - levels: `internLNode`;
  - expressions: `internE`, and `internLsNode` for `const`;
  - declarations: `parseCVD`, appending to the record block in the `RecOK` layout.

**Frontend gaps that still reject every real file:**
- escaped and non-ASCII strings;
- axioms, quot and inductives (scanner and kernel).

**Header (9957d6d and after):** `kMeta` is the line table's `.objP 17 0 fRecMeta metaHdr` entry.
`metaHdr` is con-leche's `kMeta` branch as a record scanner. `brFun_sound` (`Scan/Braced.lean`)
skips the braced value, and `hdrEnd_sound` is the record function's soundness. A string inside
the header must be plain, as elsewhere.

**Hints:** `Scan/Hints.lean` has `hiFun_sound`. The value is `"abbrev"` or `"opaque"` (a literal
choice) or `{"regular":n}`. The object loop's `.hints` action calls `fHints` and keeps the value's
position in the slot: `SlotOK (.h x)` holds when `scanHints b p = ok x _`, or when x is the default
`regular 0` and the slot holds the sentinel. Interning reads the hint again from that position.
`ScanCodes` gains the `fHints` entry. The preamble shared with `ObjFun` is now `Scan/ObjBase.lean`.

**max/imax:** `levMax`/`levImax` (Line.lean) are con-leche's branch as record scanners. The
Pancake record function `lpFun` (`Scan/LevPair.lean`) reads exactly `[a, d]`. `lpFun_sound` walks
con-leche's `scanNatListLoop` step by step (`nlLoop_ws/digit/comma/close`).

**natVal:** `natValPl` = `srMap (.expr ∘ .natVal) (scanQuotedNat b v)`. The Pancake `qnFun`
(`Scan/QNat.lean`) returns the end, and the payload slot keeps the position, so interning reads
the digits again (big values go to the arena limbs).

## The interning half: plan (2026-11-24)

The line scanner (`lineFun`, RetP world) is done for the value-declaration fragment. What remains
of the frontend runs in the SpecR/Inv world of the declaration layer:

1. **The input buffer lives in the value heap `H`.** The ported intern specs (`PostE`, …) give SR
   afterwards but no frame for memory outside the arena, so a buffer kept elsewhere would lose
   `BytesAt` after the first intern. SR tracks `H` exactly (`heap_cell`), so `BytesAt` at
   `cellA C j0` follows from the packed words `C.H[j0 + i/8]` (`bytesAt_of_heap`).
2. **Chunks come from one FFI `read` each.** Pancake's `extCall` writes the oracle's bytes over the
   array argument (`extCallStepHOLExact`). A read into the buffer cells re-establishes
   `SR (ctxH C H')` with the packed words replaced. The end-to-end theorem is relative to the
   oracle's byte stream.
3. **Tables are fixed-capacity arrays in `H`**, one per kind (names, levels, exprs).
   `TblRel C j cap tbl`: cell `j + i` holds `0` for an unbound index and `idxW h + 1` for a bound
   one, for every `i < cap`; no index `≥ cap` is bound. A record at an index `≥ cap` is rejected,
   which is sound. `IdTable.get?_insert` is the only table fact needed.
4. **Record fields** are read again by `recFun spec inits (vv (slotName k))` (the slot variant of
   `recBody_spec`), one call per field. Strings and `natVal`s are re-read from their position.
5. **`applyLine`** is a SpecR procedure per payload tag. It reads the fields, looks up the
   handles, calls the ported intern procedure and inserts the handle. Declarations append to the
   record block in the `RecOK` layout.
6. Then `feedChunk`/`parseChunks`, `StateD.init`, the prelude (static text, parsed by the same
   code), pins, the code table and the C harness, and finally the top theorem: from the oracle's
   chunks and an accepting exit, con-ron's stage runs, then `stages_frame`/`fold_verdict`.

### Interning status (2026-11-24, 8b1a17c)

Done, each a SpecR rule against the twin's entry function at the table relation (`Front/`):
- `Buf`: `bytesAt_of_heap`. `Tbl`: `TblRel` and get/fresh/set. `RetCall`: `specR_retP3`.
- `Level`: succ, param, max, imax (`parseLevelEntryD`).
- `Expr`: bvar, sort, app, lam, forallE, letE, proj (`parseExprEntryD`).
- `lineFunPk` returns the tag and payload position from one scan. The index, kind and nat value
  come from the record, so separate calls agree on them.

Next:
- **Names.** The key (`Enc.encStr` = prefix handle, then one word per byte) is copied from the
  buffer into heap scratch above the frontend's data, as `internLs` does for level lists. Body specs
  `nameStr_body_spec`/`nameNum_body_spec` wrap `nInternStr_spec`/`nInternNum_spec` with that
  heap key. Their separation facts go in a frontend `FrontOK C`, not `CtxOK`, to avoid rebuilding
  the kernel. The twin's order is the prefix lookup first, then the freshness test.
  A name number is rejected at `natCap`, since the capped value would be wrong.
- `const` (the level list key, `internLs`), `natVal` (limbs from the digits), `strVal`.
- Declarations (`parseCVD`, `pushDecl` into the `RecOK` block), `applyLine` with placement,
  `feedChunk`, the chunk reads, the prelude, pins, the code table, the harness, the top theorem.

### Interning status (1b825bd)

All `Front/` rules are SpecR rules against the twin's entry functions:
- names `str`/`num` (`parseNameEntryD`);
- levels: all kinds;
- expressions: all but `natVal`/`strVal` (`const` via `nnFun`, a count loop and the key fill loop);
- `def` declarations (`processLineCoreD`), into a registry of records in the `RecOK` layout
  (`RecEnc`, `DeclsRel`).

Byte reads are byte-order independent (`byteE`), so scanners can be called from the `Inv` world.

Still to come: `thm`/`opaque` (`dfP` minus safety and hint), `natVal`/`strVal`, the
`applyLine` dispatcher with placement, `feedChunk` and the chunk reads, init, prelude, pins, the
code table, the harness and the top theorem.

### Line procedures (ce439ef and after)

Every record kind now has a line procedure that reads its fields again and runs the interning
procedure. Each has a SpecR rule against the twin's entry function:
- `Scan/SlotKinds`: `objLoop` keeps each slot's kind. `scanNatList_len` bounds list lengths by
  the buffer size.
- `Scan/DeclFields`, generated by `scripts/gen_declfields.py`: `recFun spec inits (vv (slotName k))`
  at the record's position returns slot `k` of the slot list that builds con-leche's record.
  This covers def, thm, opaque, str, num, app, lam, forallE, letE, const and proj.
- `Front/DeclLine`: `thLine`, `opLine` (unsafe hangs), `dfLine`.
- `Front/ExprLine`: `binLine` (app, lam, forallE), `letLine`, `projLine`, `constLine`. `capG x`
  hangs unless the capped word is below `natCap`, so the interning procedures run at exact indices.
- `Front/NameLine`: `numLine`. `strLine` re-runs the plain string scanner (`ssFun_sound2`) for the
  body's span, so only plain strings get through.
- `Front/LevelLine`: `natLine` (bvar, sort, succ, param: the payload slot is the number) and
  `lvPairLine` (max, imax: `nnFun` elements 0 and 1).
- `Front/FrontSt`: the state between lines (`Lay`, three `TblRel`s, `DeclsRel`, `BufOK`). It is
  preserved by one table-cell change (`frontSt_setE/L/N`, given `i < cap`) and by a declaration
  (`frontSt_decl`).

Next, the dispatcher (`applyLine`):
1. Each line procedure becomes a code entry with the uniform parameters
   `[fTN, fTL, fTE, fCap, fI, fU, kPos, kBA, kBN, kRB, kCapD]`. The body is `prologue L core`
   (`specR_prologue` gives the `Inv` world from `Pre`). The caller uses `specR_callNIH` and gets
   `FrontSt` at the image the post names.
2. `applyLineP`: `lineFun` calls at the line start for the tag (`sPl`), the payload slot
   (`slotName 0`), `sIdx`, `sIK` and the next position (`sI`). The calls agree because
   `scanLineFwd` is deterministic. Then:
   - guard `fI < fCap`, so `ExPost`/`LvPost`/`NmPost` change a cell inside their table;
   - branch on the tag: header/blank hang unless placed (`lineNo == 0`), and the kinds the twin
     rejects (strVal, natVal for now) hang;
   - call the kind's line function with `fU := kPos := slot0`.
   Spec: `SpecR … (applyLine st r lineNo)` with post `∃ H', SR (ctxH C H') ∧ FrontSt … H' st'`.
3. Then `feedChunk` (`specR_whileT` over lines), the FFI chunk read, init, prelude, pins, the
   code table, the harness and the top theorem.

### Line functions (aec89bf)

`Front/LineCall`: `linePs` are the uniform parameters. `specR_protoCall` combines prologue and
`specR_callNIA`. `specR_{ex,lv,nm,dc}LineCall` carry the callee's post to
`FrontSt C … H' st'` at the image the post names. `Front/LineFns`: `lineVs`/`lineEnv` are the
entry environment, and there are 17 `*Core` lemmas: each line procedure at
`Inv C s (lineEnv …) [] (ctxLocals ++ L)` with its locals list `L`; `L_none` discharges the
call rule's `hL`. `Front/Tags`: `tag_t` maps a tag to its `lineTblP` entry, and `objPl` maps an
object entry to con-leche's payload.

Dispatcher plan (`Front/Dispatch`, next):
- Code entries: `lineFun x` for `x ∈ {sPl, slotName 0, sIdx, sI}`, and one line function per tag
  (`prologue L core`).
- `applyLineP`: four `lineFun` calls into `kTg`, `kS0`, `kIx` and `kNx`. Then, if `kTg = 17`
  (header), continue only when `kLn = 0`. Otherwise require `kLn ≠ 0`, guard `kIx < fCap` for
  non-declaration tags, and call the tag's function with `fI := kIx` and `fU := kPos := kS0`.
  Tags 0, 13 and 20 (blank, strVal, natVal) hang.
- One lemma per branch: PlOK with that tag → `tag_t` → payload → `lineEnd` gives the record →
  `applyLine st rec lineNo` (placed, since `lineNo ≠ 0`) becomes `parseXEntryD … >>= pure ∘ .inl`
  → `specR_xLineCall` with the core. The scanner's start `v < b.size` comes from its `{` check.

### The dispatcher is done (ff41ea2). The line loop comes next.

`Front/PlTag`: `plOK_tag_eq` shows the tag word is a function of the payload, and `lineEnd_pl`
shows the payload is a function of the record. `Front/ScanPhase`: `specR_scanPhase` makes four
`lineFun` calls; because `scanLineFwd` is a function, their words fit together (`ScanOut`).
`Front/Apply`: `FrontCodes σ C` bundles the whole code table. `dispatch_spec` and `applyLine_spec`
show that one line refines con-ron's `applyLine`. The continuation runs at `FrontSt` of the new
image, with `kNx` holding the next position.

Line loop plan:
- **The whole input is one buffer.** con-leche's `parseChunks_eq_parseBytes` gives
  `parseChunks cs = parseBytes (concat cs)`, and con-ron's `parseBytes_run` relates its
  `parseBytes` to con-leche's. The stage theorem (`Bridge/Stages.lean`) gets a `parseBytes`
  variant.
- **The loop is a self-recursive function `feed`.** Its parameters are the line-function ones
  plus `kLI` (the line's start) and `kLn` (the line count). Its core:
  `if kLI < kBN then applyLineP (if kNx = 0 then return 0 else if kLI < kNx then
  (kR1 := feed(…, kNx, kLn+1); return kR1) else hang) else return 0`.
  `specR_whileT` needs `Step` bodies, while the line spec is continuation-style, so recursion
  through `specR_protoCall` fits better. The spec is proved by induction on `b.size - i`, and the
  call depth is bounded by a resource-limit halt.
- **A twin `feedAll st b i n`** applies every line, the last one without a newline included
  (`j = 0` stops after applying). A pure lemma: `feedAll st b 0 0 = ok st'` implies con-ron's
  `parseBytes b` ends with `st'.decls` (`feedChunk` then `applyFinalLine` apply the same records
  in the same order).

### The line loop is done (a9451e4)

`Front/Feed`: `feedAll`, the twin, and `feedAll_tail` (it agrees with con-ron's
`feedChunk` + `applyFinalLine`). `Front/FeedFn`: the recursive `feed` function. `feedCore_spec`,
by induction on `b.size - i`, shows it refines `feedAll` and ends at `FrontSt` of some image
(`FeedPost`). The frontend now refines `parseBytes`'s line processing for the value-declaration
fragment, given `FrontSt` at the start.

Remaining for the frontend:
1. **Init.** Zero the three tables (a store loop), set the registry count to 0, and intern
   `Name.anonymous` and `Level.zero` at index 0, as `StateD.init` does. The result is `FrontSt`
   for `StateD.init`'s state.
2. **Input.** One FFI read of the whole input into the buffer cells (`Packed`, `BufOK`), with the
   size guard.
3. **Prelude and pins**: con-ron's `builtinPreludeE` is `parseBytes` of a static text, so the
   same code runs on a buffer the harness fills with that text. Then `preparePrelude` and
   `internAllPins`.
4. **Code table**: concrete `FrontCodes` entries (each `fLine t` body, the field readers, the
   scanners).
5. **Top theorem**: from an accepting exit, con-ron's stages run on the input. This needs a
   `parseBytes` variant of `Bridge/Stages.lean`, then `fold_verdict`.

Init detail: con-ron's `PinsOK` (after `internReservedPins`) says the zero name handle decodes
to `.anonymous`, and `pins.zeroLevel` decodes to `.zero`. So `StateD.init` only probes
(`find?` hits) and leaves the `AState` unchanged. Its tables are `singleton anonH` and
`singleton zeroL`, both handle words the program knows (the zero name handle, and the
`Ctx.pins` zero level). The program's init is therefore stores only: zero the tables, write
`anonH+1` at `jN`, `zeroL+1` at `jL` and count 0 at `rb`. No interning call is needed.

Init: the open obstacle (b8e5626). `zeroFill_spec` (Front/Init) zeroes the tables. Writing the
two index-0 handles needs one of:
- (a) **Store lemmas**: `denoteN ns default = some .anonymous` (`PinsOK.anon`) plus WF implies
  `ns.find? .anonymous = some default`, and likewise `ls.find? .zero = some pins.zeroLevel`. Then
  `StateD.init` is probe-only and the program stores the constant word 0 (+1) and the pin
  block's zero-level word (`SR.pins`, block at `PO`). This needs a find-of-view lemma for the
  hash tables; none exists in con-ron (`NStore.find?_cases` goes the other way).
- (b) **Ported calls**: the level is easy, since `fInternLZero`/`internLZero_body_spec` exist.
  The name needs a new anonymous-name intern procedure (`nStrWith`'s pattern, kind 0, a
  `FrontOK` separation clause for the anons table).
(b) keeps the frontend independent of pin facts. (a) is less code if the lemma is short.
Update: (a) is viable. con-ron's `NWFAt.consP` (Arena/WF.lean:131, and its level/expression
analogues) states `pers.find? v = some i ↔ view i = some v ∧ i.isPersistent`. With
`PinsOK.anon` (decode → view), word 0 being persistent, and `NStore.find?` probing `pers`
first, we get `internNNode .anonymous s = pure default s`. The zero level is similar, through
`pins.zeroLevel` (its persistence presumably comes from a StateOK pins clause).

### The whole-program verdict (417aa9f)

- `Front/InitTwin`: `stateD_init_probe`. After the pins, `StateD.init` only probes
  (through `NWFAt.consP`).
- `Front/InitProg`: `initP_spec` (zero-fill plus three stores) establishes `FrontSt` for that state.
- `Front/ParseTwin`: `parseBytes_of_feedAll` and `parse_twin`, through con-ron's
  `parseBytes_run`, give con-leche's `parseBytes` result and the denotations.
- `Front/ParseTop`: `parseP_spec` (init, then `feed(…,0,0)`).
- `Front/ToFold`: `registry_block` turns the registry into the fold's `BlkAt`/`RecOK` input.
- `Front/FoldCall`: `foldCall_spec`, the fold at the context raised to the current store.
- `Front/Main`: `front_verdict`. From a pinned `StateOK` state with the input in the buffer
  cells and the code table present, if `mainP` returns, then
  `ConLeche.Frontend.parseBytes b = .ok rc` and con-leche's `checkDeclsPure` accepts
  `rc.decls`. (con-leche's `parseChunks_eq_parseBytes` extends this to the chunked parse.)

Not yet done:
- Loading the input (FFI read into the buffer cells).
- The stage composition up to con-leche's top-level verdict: prelude and `preparePrelude`, which
  need inductives and axioms in the fold.
- A concrete code table (`FrontCodes`/`FoldCodes` instances).
- The C harness and executable.

### Input read and the top theorem (b9a6f96)

- `Front/ByteSet`: `byteW_setByte` (a byte store sets one byte of its word).
- `Front/ReadMem`: the `writeH` image, `sr_write` (`write_bytearray` into heap cells keeps `SR`)
  and `writeH_byte` (reading back).
- `Front/Read`: `read_step`. The `extCall` either ends in an FFI event or returns `8·Lw` bytes
  `nb` from the oracle, writes them into the buffer cells, and appends the event
  `⟨read, [], bs.zip nb⟩` to the trace.
- `Front/ReadBuf`: `inputOf nb n` and `bufOK_of_read`.
- `Front/Top`: `topP` (read, then the length from the header cell, guarded, then `mainP`) and
  `top_verdict`. From a pinned start, if `topP` returns, then the trace records the read of `nb`,
  `ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc`, and
  `ConLeche.checkDeclsPure` accepts `rc.decls`.
  The harness convention is: header cell = input length (little-endian), bytes from the next cell.

Still assumed (not yet established by code):
1. **The start state.** `Inv`/`SR` for the arena, `StateOK`/`PinsOK`/`PersPins` (the pin phase),
   the table/registry/buffer layout, and `be = false`.
2. **The code table**: `FrontCodes σ C`, `FoldCodes .verified C` and `fFeed`, for one concrete
   function list.
3. **The prelude and con-leche's top-level verdict**: the prelude stage needs inductives,
   axioms and quot in the fold.
4. **The harness and executable**.
