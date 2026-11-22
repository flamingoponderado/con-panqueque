# con-panqueque: plan

**Goal:** port con-leche to Pancake and prove that the port gives the same
verdict as con-leche.

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
   declarations) become blocks in Pancake memory: a tag word, the cached
   hash/data word, then fields (words or addresses). These values are DAGs
   (shared prefixes and subterms), so their nodes live in an immutable,
   append-only arena: the arena is one owned region in separation logic, and
   a value's shape is a non-separating predicate over the arena's words
   (`NameAt h p n`), monotone under heap extension. Mutable structures
   (caches, tables, the free region) are separating assertions. Expression
   nodes are hash-consed where con-leche shares them, so pointer equality is
   word equality.
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
1. **Memory model** (in progress): a program logic over Flapjack's
   semantics (`ConPanqueque/Logic/Basic.lean`: sequencing, assignment,
   `while` with a clock-bounded measure, one-word loads/stores, calls), a
   separation logic over Pancake memory (`Logic/Sep.lean`: `↦`, `∗`, frame
   rule, word blocks, `ListRep`), the bump allocator with its bounds check
   and freshness (`Alloc.lean`), and a first data-structure refinement: a
   Pancake loop computing `List.length` over `ListRep`
   (`Examples/ListLength.lean`).
2. **Words and naturals:** the bignum library, specified by Lean's `Nat`.
3. **Translator** (in progress): `pan_exp` (`Translate/Exp.lean`) compiles
   con-leche's word-level definitions (arithmetic, shifts, `/` `%` by powers
   of two, `if` on comparisons, unfolding of non-recursive definitions) to
   Pancake expressions with generated proofs. Next: straight-line functions
   (proofs by evaluation), calls (`call_pure`, `call1`), and structural
   recursion over arena data (the pattern of `LevelFns.lhp_spec`), so that
   the kernel's functions translate rather than being written by hand.
4. **Expressions:** `Level`, `Name`, `Expr` as hash-consed blocks; con-leche's
   expression utilities (instantiate, abstract, lift/lower) translated.
5. **Kernel:** whnf, infer, defeq with their caches.
6. **Frontend and main:** the ndjson reader, the declaration loop, the
   verdict; end-to-end theorem; comparison on con-leche's fixtures.

Until milestone 6 works, development is on `main` directly.

## Status (2026-11-22)

Verified (Lean proofs over Flapjack's Pancake semantics; axioms `propext`,
`Classical.choice`, `Quot.sound` only):

- program logic, separation logic, arena allocation (`AInv`, `hOf`, `Grows`),
  guarded node/cell constructors (out of space ⇒ the program stops: `Stop`);
- node constructors with con-leche's hash-consed data words for every `Expr`
  and `Level` constructor; translator `pan_exp` with compositional proofs;
- memo tables and a memoized expression fold;
- the substitution template (`Subst.lean`) and its six instances, i.e. every
  substitution the cached checker calls: `instantiate1`, `liftLooseBVars`,
  `abstract1`, `abstractRange`, `instantiateLevelParams`, `instantiateList`
  (closed values); `Level.subst` with substitution lists and the level-list
  functions (`levelsHash`, `levelsHaveParam`, mapping).

Not yet ported: everything else of the cached checker
(`deps/con-leche/ConLeche/Cached`), about 5,000 lines of monadic Lean:
`CoreC.lean` (whnf/infer/defeq, iota/projection/eta, Nat-literal reduction,
≈2,000 lines), the inductive-declaration checks (`IndBlock`, `IndRec`,
`IndPositivity`, `IndTail`, ≈1,600 lines), the checker state and caches
(`StateC`), declaration checking (`CheckerC`, `Decls`), and the ndjson reader
(`ParsedC`, `StreamIndex`); plus a bignum library and memoization of the
rebuilding functions (DAG sharing).

### Assessment

Porting the remainder by hand at the rate above (roughly one verified
function per several hundred lines of proof) is a many-month effort. The
realistic route is the one con-pastel took for CakeML: a translator from
con-leche's (monadic, first-order) Lean definitions to Pancake that emits each
function's refinement proof, built on the pieces above (data representation,
allocation with `Stop`, `step_call`/`pure_step` composition, the template
proofs). Its prerequisites: a memory representation and refinement predicate
for every datatype the checker uses (`ConstantInfo`, `Option`/`Except`,
`List`/`Array`, the cache maps as `Table`s), a translation of the `CheckCM`
state monad (state in globals/tables, errors as a result word), and the
generic recursion rules already proved here.


## Lean version

con-leche and Flapjack's `lean-v4.35.0` branch both use Lean v4.35.0
(`lean-toolchain`); they are submodules under `deps/`.

## Translator design (started)

- **Values.** `ArenaRep α` (`ConPanqueque/ArenaRep.lean`) gives each datatype
  a representation predicate over the arena, monotone under growth; results of
  translated functions are stated as `RResA` (stop, or a representing word).
- **The monad.** con-leche's `CheckCM = StateT CState (Except CheckError)`.
  - *Errors*: a translated function returns a tagged word (or uses a reserved
    result global); the checker's verdict only depends on whether an error
    occurred and which, so the error payload is a small enumeration.
  - *State*: `CState` is a record of memo maps (`whnfC`, `inferC`, `defeqC`,
    …) plus `maxNatSize`. Every map is a pure memo of a function con-leche
    proves correct (`CSOK`), so a lookup miss never changes a result. In
    Pancake each becomes a pointer-keyed `Table` (`Table.lean`, as in
    `MemoFold.lean`) with an entry-correctness invariant
    (`key ↦ val ⇒ ExprAt key e ∧ ExprAt val (f e)`); structurally equal
    expressions at different addresses just miss. The refinement relation
    for `CheckCM` is then: on success, the result represents con-leche's
    result and the tables satisfy their invariants; misses cost only time.
  - *Fuel* (`peelFuel` and friends) is transparent and maps to clock.
- **Control.** First-order recursion through `step_call` / `pure_step`
  (`Rebuild.lean`), node and cell allocation through `mkNode` / `mkCell`
  with `Stop` on exhaustion, case analysis on tags through `iteChain`.

## con-ron as a route (2026-11-22)

[con-ron](https://github.com/leanprover/con-ron) ports con-leche to Rust with a
proof in two layers:

- a **twin** (`proof/ConRon/Arena`, ≈39k lines of Lean): an executable checker
  with the Rust's data structures (hash-consed DAG in per-constructor arrays,
  `u32` handles, two tiers, cache tables), monad
  `ReaderT PersTier (StateT AState (Except CheckError))`, explicit fuel;
- **Theorem 1** (`proof/ConRon/Bridge`, ≈118k lines): the twin refines
  con-leche's pure checker, for the whole checker (kernel, inductives, stream);
- **Theorem 2** (`proof/ConRon/Refine2`, ≈138k lines): the Rust (via Aeneas)
  refines the twin, largely mechanical (`lockstep` tactic).

Both headline theorems (`model_exists`, `no_False_declaration`) are **partial
correctness, one direction**: if con-ron accepts, con-leche's soundness
conclusion holds; con-ron may decline (resource limits: `Native`) where
con-leche accepts, and Theorem 1 does not relate rejections.

For con-panqueque this suggests: write the Pancake program to mirror the
twin (its arrays and tables as memory regions, handles as words), and prove
**Pancake refines the twin** in lockstep — the analogue of Theorem 2 — then
compose with con-ron's Theorem 1 to get con-ron's soundness statement for the
Pancake binary. That reuses the ≈118k-line kernel proof instead of redoing
it. Costs: the twin's store layout differs from the arena here (`hOf`,
pointer nodes with data words), so the data representation layer would be
redone against the twin's `AState`; and the result is one-directional (an
accepted file is consistent), not "same verdict" in both directions. A
converse (con-leche rejects ⇒ Pancake rejects) would need a new, two-sided
refinement proof that neither con-ron nor this repository has.
