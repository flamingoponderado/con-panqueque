# Soundness: the statement and everything it assumes

## The statement

`ConPanqueque.Start.main_pipeline_chunks` (`ConPanqueque/Start/Main3.lean`):
take the Pancake program `mainBody2` and start it from the initial state
(`InitMem`, `InitGlobals`, little-endian). If it returns, then it read input `b`,
`ConLeche.Frontend.parseChunks [b] = .ok r`, and

```
∃ E, ConLeche.PureRun pins (preparePrelude pre r.decls).toList Env.empty E
```

The C harness exits 0 (`accept`) only when the program returns. Every reject path
prints `reject` and exits 1. So an `accept` from the port means con-leche's **pure**
checker accepts the input with its built-in prelude in front.

## Assumptions

Anyone relying on the theorem must trust each of these.

### A1. con-leche accepts its own prelude (`PreludeOK`): unproved

`PreludeOK pins pre envP` (`ConPanqueque/Start/Main3.lean`) is a **hypothesis** of
the theorem. No Lean proof discharges it. It says:

- `run`: con-leche's pure checker accepts the built-in prelude's declarations from
  the empty environment, `PureRun pins pre.decls.toList Env.empty envP`;
- `names`: every constant in the resulting environment `envP` has a name in the
  forbidden-name list `FN`, the list the port refuses to let an input redeclare;
- `keys`: every prelude record's key is in `FN`;
- `noOp`: no prelude record is a Nat-operation record.

The program does not recheck the prelude. It starts from an environment where the
prelude is assumed accepted, and checks the input stream against it. If con-leche
rejected its own prelude, the conclusion `PureRun …` could fail, and the theorem
would say nothing.

**Evidence, not proof.** `#eval` shows the prelude is accepted, with 23 constants.

**Why it is not proved:**
- The kernel cannot reduce `builtinPreludeE`, because it depends on `USize` and
  `System.Platform.numBits`.
- `decide +kernel` on the parsed prelude ran out of resources and was killed
  (exit 143).
- `native_decide` would close it, but it trusts the Lean compiler, the same trust
  the project rules out for `bv_decide`.

**How to remove it:** prove `PreludeOK` in the kernel one declaration at a time,
using con-leche's `PureRun` step lemmas.

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
- It covers only streams of definitions, theorems and opaques. Inductives, axioms
  and quotients are rejected.

See [../STATUS.md](../STATUS.md) for the overall status.
