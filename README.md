# con-panqueque

A port of [con-leche](https://github.com/leanprover/con-leche), a verified
Lean 4 kernel checker, to [Pancake](https://cakeml.org/pancake), using
[Flapjack](https://github.com/flamingoponderado/flapjack)'s Lean port of the
Pancake language and compiler. A sibling of
[con-pastel](https://github.com/flamingoponderado/con-pastel), which
translates con-leche to CakeML.

**Status: milestone 0 (toolchain).** Nothing of con-leche is ported yet.
See [PLAN.md](PLAN.md) for the design and milestones.

## Layout

- `deps/con-leche`, `deps/flapjack`: submodules (Lean v4.35.0).
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

con-panqueque is derived from con-leche and is distributed under the same
licence, the Apache License 2.0 ([LICENSE](LICENSE), copied from
con-leche). Changes from con-leche: the checker is being rewritten in
Pancake; see the commit history.
