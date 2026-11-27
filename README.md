# con-panqueque

A port of [con-leche](https://github.com/leanprover/con-leche), a verified
Lean 4 kernel checker, to [Pancake](https://cakeml.org/pancake), using
[Flapjack](https://github.com/flamingoponderado/flapjack)'s Lean port of the
Pancake language and compiler. A sibling of
[con-pastel](https://github.com/flamingoponderado/con-pastel), which
translates con-leche to CakeML.

**Status: soundness relative to con-leche's pure checker, under stated hypotheses.**
The theorem [`main_pipeline_prelude`](ConPanqueque/Start/Main4.lean) proves that if the
compiled checker accepts an input, con-leche's frontend parses it, con-leche's own
built-in prelude parses (`builtinPreludeE = .ok pre`), and con-leche's pure checker accepts
the input prepared with that prelude (`preparePrelude pre r.decls`). The program parses the
prelude's bytes itself (`ConPanqueque/Prelude/`), drops the input's identical copies of
prelude records (and hangs on any other overlap), and checks that the `Nat`-operation
hoist is the identity. The proof assumes that Lean's runtime hashes match their
definitions. The port does not prove that it gives the same verdict as con-leche: it does
not reach con-leche's cached checker, it does not prove completeness, and it still rejects
inductive records (so it accepts nothing until the inductive arm is wired). See
[docs/SOUNDNESS.md](docs/SOUNDNESS.md) for every assumption, [STATUS.md](STATUS.md)
for the exact statement and gaps, and [PLAN.md](PLAN.md) for the design.

## Layout

- `deps/con-leche`, `deps/flapjack`: submodules (Lean v4.36.0).
- `ConPanqueque/`: the Lean side (specifications, translator, proofs).
- `pancake/`: Pancake programs and the C FFI harness; `make -C pancake test`
  downloads the CakeML compiler release (checked against its SHA-256),
  compiles `count.pnk` with `cake --pancake` and runs it.

## Building

```sh
git submodule update --init
lake build            # the Lean side
make -C pancake test  # the Pancake toolchain check
```

## Running the checker

The checker is the Pancake program `mainBody2` (`ConPanqueque/Start/Main3.lean`), the program the theorem
is about. `scripts/Emit.lean` prints it as Pancake source and checks that the printed text parses back to
the same program; `cake --pancake` compiles it; `pancake/ffi_checker.c` is the C harness (input on stdin,
memory mapped at a fixed address).

```sh
lake build                          # the proofs must build first
lake env lean scripts/Emit.lean     # writes pancake/checker.pnk
make -C pancake checker             # cake --pancake + cc -> pancake/build/checker (~2 min)
pancake/build/checker < deps/con-leche/tests/e2e/wide_ok.ndjson
```

It reads a lean4export NDJSON file on stdin and prints `accept` (exit 0) or `reject` (exit 1). Only `accept`
carries the theorem's guarantee. A rejection may also mean an unsupported feature (inductives, axioms,
quotients) or an exhausted resource. Set `PNK_MEM_SIZE` / `PNK_STACK_SIZE` (MiB) to change the memory the
harness maps.

**Platform.** The Makefile fetches the x86-64 CakeML compiler (`cake-x64-64`) and builds an x86-64 binary,
so the checker currently runs on x86-64 Linux only. CakeML's Pancake compiler also targets RISC-V and ARM
(among others); a build for those targets would need the matching `cake` release, a harness compiled for that
target, and a check that the fixed memory address in `ffi_checker.c` is available there. None of this is set
up yet.

## Licence

con-panqueque is derived from con-leche and from
[con-ron](https://github.com/leanprover/con-ron) (whose Lean "twin" of the
checker and its refinement proof the Pancake port follows), and is distributed
under the same licence as both, the Apache License 2.0:

- [LICENSE](LICENSE): con-leche's licence, copied from con-leche;
- [LICENSE-con-ron](LICENSE-con-ron): con-ron's licence, copied from con-ron.

Changes from con-leche and con-ron: the checker is being rewritten in Pancake;
see the commit history.
