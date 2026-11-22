# con-panqueque: plan

A port of [con-leche](https://github.com/leanprover/con-leche) (a Lean 4
kernel checker written and verified in Lean) to
[Pancake](https://cakeml.org/pancake), CakeML's low-level language, using
[Flapjack](https://github.com/flamingoponderado/flapjack)'s Lean port of
Pancake's syntax, semantics and compiler.

## Why Pancake

[con-pastel](https://github.com/flamingoponderado/con-pastel) translates
con-leche to CakeML with a correctness proof. After the optimisations of
its PRs #41–#62 it is still 3–12× slower than con-leche on con-leche's
heavy fixtures, and what remains is mostly CakeML's runtime model
(con-pastel's `docs/CAKEML-WISHLIST.md`):

| con-pastel cost | in Pancake |
|---|---|
| copying GC re-copies a 1.6 GB live set (`natmul_deep_major`: 63 s of 74 s) | no collector: memory is managed by the program |
| every 64-bit word boxed (a heap object per intermediate) | words are the only values; no boxing |
| no word multiply (22-bit limb emulation in hashing) | native `*` |
| identity token (a ref) per expression node for pointer equality | addresses are words: `==` |
| persistent arrays (Braun trees) where con-leche updates in place | memory loads and stores |
| 0-ary constants rebuilt at every use | static data, built once |

The price: Pancake has no datatypes, no closures, no allocation and no
bignums. All of them become explicit, and so does their proof.

## Shape of the port

1. **Data representation.** Inductive values (`Expr`, `Level`, `Name`,
   declarations) become blocks in Pancake memory: a header word (constructor
   tag, cached data word) followed by fields, which are words or addresses.
   Expression nodes are hash-consed where con-leche shares them, so pointer
   equality is word equality.
2. **Memory.** A bump allocator over `@base`. con-leche checks one
   declaration at a time: a per-declaration scratch region is reset after
   each declaration, and the results that outlive it (the declaration, its
   cache entries) are copied to a permanent region. No collector.
3. **Natural numbers.** Small values unboxed (a tag bit); large ones as limb
   arrays with a Pancake bignum library (add, sub, mul, div/mod, shifts,
   comparisons, gcd/log2 as the kernel's `Nat` acceleration needs).
4. **Control.** con-leche's kernel is first-order recursion over expressions
   plus caches (hash maps). Recursion maps to Pancake functions; caches to
   open-addressing hash tables in memory; higher-order uses (`List.map f`,
   folds) are specialised per call site.
5. **Frontend.** The ndjson reader (con-leche's `Frontend`) as a byte-level
   scanner over an input buffer filled by one `read` FFI call per chunk.

## Correctness

The target theorem has the shape of con-pastel's `conPastel_correct`: the
compiled program's observable behaviour (its output on the input stream) is
con-leche's verdict, under explicit assumptions about the FFI and the
runtime. The pieces:

- **Pancake semantics:** Flapjack's `Flapjack.Pancake.Semantics` (a Lean
  port of CakeML's `panSem`), and its proved compiler theorem down to the
  target (RISC-V proved; x86-64 and ARMv8 as Flapjack documents).
- **Refinement:** each Pancake function refines a con-leche function under a
  representation relation between Lean values and memory (separation-logic
  style: the blocks reachable from a word represent a value).
- **Generation:** as in con-pastel, the Pancake code and its refinement
  proofs are produced by a translator from the Lean definitions, so that
  con-leche's own correctness proofs carry over. Hand-written Pancake (the
  allocator, bignums, hash tables) gets hand-written proofs once.

## Milestones

0. **Toolchain** (done): repository, licence, a Pancake program compiled
   with `cake --pancake` and linked with a C FFI harness (`pancake/`).
1. **Memory model:** block layout, the bump allocator and the
   representation relation in Lean; a Pancake allocator with its proof
   against Flapjack's semantics.
2. **Words and naturals:** the bignum library, specified by Lean's `Nat`.
3. **First translated functions:** a translator for a first-order fragment
   (words, naturals, structures, lists) emitting Pancake and refinement
   proofs; con-leche's hashing (`mixHash`, data words) as the first target.
4. **Expressions:** `Level`, `Name`, `Expr` as hash-consed blocks; con-leche's
   expression utilities (instantiate, abstract, lift/lower) translated.
5. **Kernel:** whnf, infer, defeq with their caches.
6. **Frontend and main:** the ndjson reader, the declaration loop, the
   verdict; end-to-end theorem; comparison on con-leche's fixtures.

Until milestone 6 works, development is on `main` directly.

## Lean version

con-leche and Flapjack's `lean-v4.35.0` branch both use Lean v4.35.0
(`lean-toolchain`); they are submodules under `deps/`.
