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
