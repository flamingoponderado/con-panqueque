# Status: what is proved, and what is not

The goal is narrowed to **soundness relative to con-leche's pure checker**.
Commit 967b787 delivers that result, under the hypotheses listed below.
The port does **not** prove that it gives the same verdict as con-leche on every
input. The gaps below are documented future work.

## The theorem

`ConPanqueque.Start.main_pipeline_chunks` (`ConPanqueque/Start/Main3.lean`) says:
take the Pancake program `mainBody2`, the program that `scripts/Emit.lean` emits
and `cake --pancake` compiles. Start it from the initial state (`InitMem`,
`InitGlobals`, little-endian). If it returns, then:

- it recorded a `read` FFI event with input bytes `b`;
- con-leche's frontend parses that input: `parseChunks [b] = .ok r`;
- con-leche's pure checker accepts the input with its built-in prelude in front:
  `∃ E, PureRun pins (preparePrelude pre r.decls).toList Env.empty E`.

The C harness (`pancake/ffi_checker.c`) prints `accept` and exits 0 only when the
program returns. Every reject path goes through `hang`, which prints `reject` and
exits 1 (`Logic/Stop.lean`, `hang_stop`). So **"the port accepts" implies "con-leche's
pure checker accepts"**.

Axioms: `propext`, `Classical.choice`, `Quot.sound`. The proof uses no
`native_decide`, no `bv_decide` and no `sorry`.

## Hypotheses of the theorem

1. `RuntimeAssumptions` (`Hash.lean`): Lean's runtime `mixHash`, `String.hash` and
   big-`Nat` hash agree with their written-out definitions.
2. `System.Platform.numBits = 64`.
3. `PreludeOK pins pre envP`: con-leche's pure checker accepts its own built-in
   prelude from the empty environment. The resulting environment and the prelude's
   keys use only names in the forbidden-name list `FN`, and the prelude has no
   Nat-operation records. This holds when run (`#eval`: the prelude is accepted,
   23 constants), but it is not proved in Lean:
   - the kernel cannot evaluate `builtinPreludeE`, because it depends on `USize` /
     `numBits`;
   - a `decide +kernel` attempt on the parsed prelude ran out of resources and was
     killed (exit 143);
   - `native_decide` would close it, but that trusts the compiler, like the banned
     `bv_decide`, so it is not used.

## Gaps (not proved; future work)

- **Prelude.** Discharge `PreludeOK` by a kernel-checked proof, for example by
  splitting it into per-declaration lemmas.
- **con-leche's real verdict.** con-leche's executable exits 0 from its cached
  checker (`Cached.checkDecls`). con-leche proves cached ⇒ pure. The theorem above
  reaches the pure checker only. It does not prove pure ⇒ cached, which may be false
  in general (for example, the cached checker gives up on some inputs above its
  size limits). So "port accepts ⇒ con-leche's binary exits 0" is not proved.
- **Completeness.** The direction "con-leche accepts ⇒ port accepts" is not proved.
  The chosen direction was soundness only.
- **Coverage.** The port rejects every stream with inductive types, axioms or
  quotients. It accepts only definitions, theorems and opaques over the built-in
  prelude, so real Lean exports are rejected.

## Executable evidence (not proofs)

- 394 translated functions round-trip.
- End-to-end run over the 612 fixtures: 2 accepted (both expected), 610 rejected,
  0 accepted unexpectedly.
