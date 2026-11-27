# Soundness: the statement and everything it assumes

## The statement

[`ConPanqueque.Start.main_pipeline_prelude`](../ConPanqueque/Start/Main4.lean):
take the Pancake program `mainBody3` and start it from the initial state
(`InitMem`, `InitGlobals`, little-endian). If it returns, then it read input `b`,
`ConLeche.Frontend.parseChunks [b] = .ok r`, `ConLeche.Frontend.builtinPreludeE = .ok pre`, and

```
∃ E, ConLeche.PureRun [] (preparePrelude pre r.decls).toList Env.empty E
```

The C harness exits 0 (`accept`) only when the program returns. Every reject path
prints `reject` and exits 1. So an `accept` from the port means con-leche's **pure**
checker accepts the input prepared with con-leche's own built-in prelude.

## Assumptions

Anyone relying on the theorem must trust each of these.

### A1. (removed) The prelude

The program parses con-leche's built-in prelude itself: its bytes are con-leche's
`builtinPreludeText` (proved: `Prelude/Text.lean`'s `preludeText_eq`, a kernel-only
definitional check of the `include_str` literal against generated character chunks), and
the fold checks the prelude's records like the input's. No hypothesis about the prelude
remains.

### A2. Runtime hashes match their definitions (`RuntimeAssumptions`)

`ConPanqueque/Hash.lean`: Lean's runtime `mixHash`, `String.hash` and big-`Nat`
hash equal the written-out functions the Pancake code implements.

### A3. 64-bit platform

`System.Platform.numBits = 64`.

### A4. The tool chain

- Lean's kernel, with the axioms `propext`, `Classical.choice` and `Quot.sound`.
  No `sorry`, `native_decide` or `bv_decide`.
- Flapjack's Lean model of Pancake semantics is faithful to the `cake --pancake`
  compiler that builds the binary. CakeML's own correctness theorem covers the
  compiler, not the Flapjack port of its semantics.
- The C harness `pancake/ffi_checker.c`, read by hand: it exits 0 only on
  `cml_exit(0)`.

## What the theorem does not say

- It is not about con-leche's executable. That binary's exit 0 comes from
  `Cached.checkDecls`. con-leche proves cached ⇒ pure; pure ⇒ cached is unproved
  and may be false.
- It is not completeness: con-leche accepting an input does not imply the port
  accepts it.
- The fold still rejects inductive records, and the prelude is mostly inductive blocks,
  so the port accepts nothing yet.

See [../STATUS.md](../STATUS.md) for the overall status.
