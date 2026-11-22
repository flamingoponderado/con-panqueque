# con-panqueque

A port of [con-leche](https://github.com/leanprover/con-leche), a verified
Lean 4 kernel checker, to [Pancake](https://cakeml.org/pancake), using
[Flapjack](https://github.com/flamingoponderado/flapjack)'s Lean port of the
Pancake language and compiler. A sibling of
[con-pastel](https://github.com/flamingoponderado/con-pastel), which
translates con-leche to CakeML.

**Status: milestones 1, 3, 4 in progress.** Verified so far (Lean proofs over
Flapjack's Pancake semantics, axioms `propext`/`Classical.choice`/`Quot.sound`):
a program logic and separation logic over Pancake memory; the arena allocator
and node constructors for con-leche's `Expr` (hash-consed data words included);
a translator for con-leche's word-level code; memo tables; a memoized expression
fold; and the first kernel operation, `Expr.instantiate1` (`ConPanqueque/Inst1.lean`).
No checker runs end to end yet. See [PLAN.md](PLAN.md) for the design and milestones.

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

con-panqueque is derived from con-leche and from
[con-ron](https://github.com/leanprover/con-ron) (whose Lean "twin" of the
checker and its refinement proof the Pancake port follows), and is distributed
under the same licence as both, the Apache License 2.0:

- [LICENSE](LICENSE): con-leche's licence, copied from con-leche;
- [LICENSE-con-ron](LICENSE-con-ron): con-ron's licence, copied from con-ron.

Changes from con-leche and con-ron: the checker is being rewritten in Pancake;
see the commit history.
