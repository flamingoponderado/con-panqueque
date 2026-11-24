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
