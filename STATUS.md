# Status: what is proved, and what is not

The goal is narrowed to **soundness relative to con-leche's pure checker**.
Commit 967b787 delivers that result, under the hypotheses listed below.
The port does **not** prove that it gives the same verdict as con-leche on every
input. The gaps below are documented future work.

## The theorem

[`ConPanqueque.Start.main_pipeline_prelude`](ConPanqueque/Start/Main4.lean) says:
take the Pancake program `mainBody3`, the program that `scripts/Emit.lean` emits
and `cake --pancake` compiles. Start it from the initial state (`InitMem`,
`InitGlobals`, little-endian). If it returns, then:

- it recorded a `read` FFI event with input bytes `b`;
- con-leche's frontend parses that input: `parseChunks [b] = .ok r`;
- con-leche's built-in prelude parses: `builtinPreludeE = .ok pre`;
- con-leche's pure checker accepts the input prepared with it:
  `∃ E, PureRun [] (preparePrelude pre r.decls).toList Env.empty E`
  (`[]`: the `Nat`-operation pin list the program's fold uses).

How the program gets there (`ConPanqueque/Prelude/`): after the stream's parse it stores the
prelude's bytes (`builtinPreludeText`'s UTF-8, `Prelude/Text.lean` + `Prelude/Bytes.lean`)
over the input buffer and parses them into the same registry from fresh tables
(`parseP2`; `feedAll_withPre`: the twin's parse ignores the records in front). The override
pass (`overP`) keeps the prelude in front and drops every stream record whose name is a
prelude record's key — it must be that record word for word (`recEqP`) and the only stream
record of that name, else hang; stream blocks hang for now. The hoist check (`hoistP`)
hangs unless each pinned `Nat` operation's ground is declared before it, which makes
`hoistTargets` empty (`Prelude/Hoist.lean`). The fold runs over the result, which is
`(preparePrelude pre r.decls).toList` (`Prelude/Prep.lean`, `Prelude/Final.lean`).

Axioms: `propext`, `Classical.choice`, `Quot.sound`. The proof uses no
`native_decide`, no `bv_decide` and no `sorry`.

## Hypotheses of the theorem

1. `RuntimeAssumptions` (`Hash.lean`): Lean's runtime `mixHash`, `String.hash` and
   big-`Nat` hash agree with their written-out definitions.
2. `System.Platform.numBits = 64`.

(The former hypothesis `PreludeOK` is gone: the program checks the prelude's records itself.)

## Gaps (not proved; future work)

- **con-leche's real verdict.** con-leche's executable exits 0 from its cached
  checker (`Cached.checkDecls`) at `natOpPinSets`. The theorem reaches the pure checker at
  the pin list `[]` only.
- **Completeness.** The direction "con-leche accepts ⇒ port accepts" is not proved.
- **Coverage.** The fold's dispatcher still rejects inductive lines, and the prelude is
  mostly inductive blocks, so the program accepts nothing yet. The override pass compares
  value records only; comparing a stream block with a prelude block (and detecting a
  stream block that declares a prelude key) is future work — it hangs on stream blocks.

## Executable evidence (not proofs)

- 394 translated functions round-trip.
- End-to-end run over the 612 fixtures: 2 accepted (both expected), 610 rejected,
  0 accepted unexpectedly.
