# con-panqueque

A port of [con-leche](https://github.com/leanprover/con-leche), a verified
Lean 4 kernel checker, to [Pancake](https://cakeml.org/pancake), using
[Flapjack](https://github.com/flamingoponderado/flapjack)'s Lean port of the
Pancake language and compiler. A sibling of
[con-pastel](https://github.com/flamingoponderado/con-pastel), which
translates con-leche to CakeML.

**Status: soundness relative to con-leche's pure checker, under stated hypotheses.**
The theorem [`main_pipeline_chunks`](ConPanqueque/Start/Main3.lean#L280) proves that if the
compiled checker accepts an input, con-leche's frontend parses it and con-leche's
pure checker accepts it with the built-in prelude in front. The proof assumes con-leche
accepts its own prelude (`PreludeOK`, checked by `#eval` but not proved) and that Lean's
runtime hashes match their definitions. The port does not prove that it gives the same
verdict as con-leche: it does not reach con-leche's cached checker, it does not prove
completeness, and it rejects inductives, axioms and quotients. See [docs/SOUNDNESS.md](docs/SOUNDNESS.md) for every assumption, [STATUS.md](STATUS.md)
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

## Licence

con-panqueque is derived from con-leche and from
[con-ron](https://github.com/leanprover/con-ron) (whose Lean "twin" of the
checker and its refinement proof the Pancake port follows), and is distributed
under the same licence as both, the Apache License 2.0:

- [LICENSE](LICENSE): con-leche's licence, copied from con-leche;
- [LICENSE-con-ron](LICENSE-con-ron): con-ron's licence, copied from con-ron.

Changes from con-leche and con-ron: the checker is being rewritten in Pancake;
see the commit history.
