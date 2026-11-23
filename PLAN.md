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

## Decision (2026-11-22): follow con-ron's twin, soundness first

The user chose con-ron's route. Target theorem, shaped like con-ron's
`no_False_declaration`: if the compiled Pancake checker, run on an input,
reports acceptance, then con-leche's soundness conclusion holds for that input
(no declaration proves `False`; the environment has a model). Resource limits
(arena or table full, clock) are a decline, about which nothing is claimed;
a rejection for a different reason than con-leche's is acceptable. Numeral
scanning differences against con-leche must be proved equivalent.

Composition: Pancake ⇒ (lockstep refinement, to prove here) the twin's
`PooledAccepts` with one worker ⇒ (con-ron's Theorem 1,
`Arena.pooledAccepts_bridge`, reused) con-leche's `checkDeclsPure` accepts ⇒
(con-leche's soundness) the model / no `False`.

Setup: Lean v4.36.0 (flapjack branch `lean-v4.36.0`), con-leche at con-ron's
pin `bc66761`, con-ron as the submodule `deps/con-ron`, whose `ConRon.Arena`
(twin) and `ConRon.Bridge` (Theorem 1) are built as libraries of this package.

Refinement shape, per twin function `f : … → AM β`: a Pancake function `f'`
and a lemma "state relation holds ∧ arguments related ∧ `f'` returns normally
with result `r'` ⇒ `f … s = .ok (r, s₁)` with `r`, `s₁` related to `r'` and the
final Pancake state". Only the success direction is needed for soundness, so
Pancake failures (including `Stop`) need no counterpart.

Steps:
1. memory representation of the twin's `AState`: the per-constructor node
   arrays and derived columns (`Tbl.nodes`, `Tbl.der`), the cons tables
   (`Std.HashMap`, refined by an open-addressed table), the memo and cache
   maps, the pins; handles as words;
2. the store primitives (`view`, `derivedE`, `intern*`) and their lockstep
   lemmas;
3. a translator from the twin's monadic Lean to Pancake with generated
   lockstep proofs, reusing the composition lemmas here (`step_call`,
   `pure_step`, `iteChain`, `Stop`);
4. the twin's frontend, checker and driver loop, translated; the top-level
   theorem.

### Parallelism (user's idea, 2026-11-22)

Workers can be `fork()`ed processes: con-ron's frozen persistent tier (the
parsed file, pins, stream index) is only read after the fork, and Pancake has
no collector that would touch it, so its pages are never written and
copy-on-write never copies them; each child appends only to its own scratch
region and cache tables. Each child's run is one worker's job list in con-ron's
`ParallelAll` premise; like con-ron's thread pool, the fork/wait driver is
outside the verified core and enters the final theorem as that premise.

Two executables (user, 2026-11-22): a **single-threaded** checker, whose
theorem has only the core assumptions (FFI read/write, runtime hashing), and a
**multi-process** one, whose theorem additionally assumes the `fork`/`wait`
syscall shims behave as specified. Both share the verified per-worker job
runner.

## Translator status (2026-11-23)

The refinement judgement and its combinators are in `ConPanqueque/T/`:

- `Spec P c s m Q` / `SpecR P c s m R` (`T/Spec.lean`): from every Pancake state
  satisfying `P`, program `c` either stops (`Stop`: resource limit or a twin
  failure, compiled to a halt) or finishes (resp. returns a word) and the twin
  computation `m` from state `s` succeeds with the result and states related.
  Only the success direction, which is what soundness needs.
- `SR C s t` (`T/Store.lean`): the twin state is represented — the stores
  (`SRep`), the context words in globals, the code map, the key buffer, the
  `instantiate1` memo (`MemoAt`). `CtxOK C` collects the static layout facts.
- `Inv C s Γ M D t` (`T/Inv.lean`): `SR` plus a symbolic environment (locals
  with known words), known memory words and declared locals; expressions are
  evaluated symbolically (`sev`, proved sound), so a step's side conditions
  are mostly `rfl`/`decide`. Continuation-style combinators: assignments,
  loads, `if` on Pancake or twin conditions, returns, calls (1–3 parameters,
  callee specs from entry states), the uniform function prologue.
- Store primitives at the twin's level: `view` (all ten expression
  constructors, fields as known memory), `viewApp`, `derivedE`, `internAppE`
  (with the twin's probe/capacity wrapper), memo `inst1Get`/`inst1Set`
  (Pancake functions `memoProbe`/`memoGet`/`memoIns`/`memoSet` over a generic
  table, refining `Std.HashMap` lookups and inserts).
- Translated so far, with refinement proofs: `getAppFn` (`T/Ex/GetAppFn2.lean`),
  `sizeB` (`T/Ex/SizeB.lean`) and `instantiate1Go` (`T/Ex/Inst1.lean`: the
  derived-word cutoff, the tag dispatch, five memoized arms rebuilding through
  the interns).
- Intern functions for every expression constructor the rebuilding walks use
  (`app`, `lam`, `forallE`, `letE`, `bvar`, `proj`), each refining the twin's
  monadic wrapper (probe, capacity test, `EStore.intern`).

Next: memo clearing (the top-level `instantiate1Fast`), the other memos,
caches and pins in `SR`, the level/name stores' views; then a tactic that
applies the combinators by goal shape, and the bulk translation.

### Progress (2026-11-23, later)

Translated with refinement proofs since (all over the standard axioms only):

- **Memos.** The six `(EIdx × Nat) → EIdx` memos and the two `EIdx → Nat`
  memos (`bvarBC`, `fvarBC`) in `SR`, by region; generic get/set/clear
  combinators (`T/Memo.lean`, `T/MemoN.lean`, `T/MemoClear.lean`).
- **Walks over expressions.** `instantiate1` (`T/Ex/Inst1*.lean`),
  `liftLooseBVars` (`T/Ex/Lift.lean`), `fvarRangeGo`/`fvarB`
  (`T/Ex/FvarRange.lean`), `bvarBoundGo`/`bvarB` (`T/Ex/BvarBound.lean`),
  `abstract1` (`T/Ex/Abstract1.lean`), `abstractRange`
  (`T/Ex/AbstractRange.lean`), `hasFvarFast`, `looseBVarsBoundedFast`,
  `piResult`, `lamBody`, `fvarTypeD` (`T/Ex/Small.lean`).
- **Heap values (roadmap item 1).** An append-only value heap: `Ctx.H` is an
  image the heap extends (`SR.heap`), so callees' allocations stay invisible;
  a caller that needs a returned value continues at a bigger image
  (`T/Heap.lean`: allocation, loads, owned-cell stores). Lists and arrays of
  handles are blocks `[n, x₀, …]` (`T/Blk.lean`), with a verified copy loop
  (`T/Copy.lean`) and a counted-loop rule (`T/Loop.lean`).
- **Functions over lists and arrays.** `getAppArgs` (returns a block),
  `mkAppN`/`mkAppNFrom` (`T/Ex/AppArgs.lean`, `T/Ex/MkApp.lean`), and the
  bulk instantiation family `instantiateList`, `instantiateListGo`,
  `instantiateRevRange`, `instantiateListFast` (`T/Ex/InstList*.lean`).
- Calls of any arity (`T/CallN.lean`).

### Roadmap from here (2026-11-23)

The hand proofs (`getAppFn`, `sizeB`, `instantiate1Go`) fixed the shape of the
primitives and combinators. The twin code still to translate on the path to
the top-level theorem is about 18k lines (`Core` 4.6k, `ExprOps` 2.3k,
`DeclCheck`, `Inductives/*`, the frontend, pins, the stream index). With the
primitives in place a function costs tens to a few hundred lines of proof, so
the plan is to continue function by function, adding primitives as needed;
automation (item 2) is a speed-up, not a prerequisite. Pieces needed along
the way:

1. **Heap values.** Lists, options, products and records (the twin's
   `List EIdx`, `IConstantInfo`, …) as immutable cells in an append-only heap
   region with a bump pointer in a global; a representation predicate per type
   that is monotone under allocation; `SR` gains the heap invariant.
2. **The translator proper.** A command that, for a twin definition, builds
   the Pancake body and its `SpecR` proof together: a tactic that walks the
   twin term (`bind`, `match`, `if`, `pure`, `let`, calls) and applies the
   combinators with the code as a metavariable, discharging side conditions by
   `sev`/`decide`; calls to other translated functions and to primitives go
   through a table of call specs.

The memo, cache and pin tables of `AState` join `SR` as the functions that use
them are translated (the `instantiate1` memo is the template).

### Progress (2026-11-23, levels)

Levels are represented by `LRep` (an arena handle, or a heap block `[tag, kids]`
built by the port), compared deeply. Verified, each a Pancake function with
its `SpecR`:

- `levelEq` (`T/LvlEq.lean`), `combining`/`simplify` (`T/LvlComb.lean`,
  `T/LvlSimp.lean`), `subst` (`T/LvlSubst.lean`).
- The `leqCore` mutual block: `byCases` (`T/LvlLeq.lean`), `innerTag` plus
  `imaxRules` (`T/LvlImax.lean`), `rest` (`T/LvlRest.lean`), `leqCore`
  and the fuel induction `leq_all` (`T/LvlLeqCore.lean`). Each case follows
  con-leche's match order, pinned by twin case lemmas (`ir_c1..7`,
  `rest_pp..rest_else`).
- `isEquiv` (`T/LvlEquiv.lean`); its `l == r` disjunct is verdict-neutral
  (`isEquiv_noPtr`), so the port starts at the simplified comparison.
- `lvlEq?` at two handles (`T/LvlEqQ.lean`). The port does not cache.
  Under con-ron's cache invariants (`ReadLCacheOK`, `LvlEqCacheOK`, part
  of its `CheckOK`), a cache hit gives the same answer as recomputing, so
  `eqvBody` refines `lvlEq?`. The post keeps the store and memos; `SR`
  ignores caches.

Cache policy from here: caches whose values are readbacks or verdicts are
not mirrored. Their con-ron invariants are taken as hypotheses at the entry
state. The top-level composition gets them from con-ron's `CheckOK`
preservation.

### Progress (2026-11-24, instantiateLevelParams pieces)

Verified (each a Pancake function with its `SpecR`):

- Level lists: `lvlsEq?` (`T/LvlEqList.lean`, view `V/LsView.lean`).
- Interning:
  - Level nodes (`T/LIntern.lean`) and level trees from heap or arena representations (`internLv`, `T/LInternLv.lean`).
  - Level lists with the key block in the heap (`T/LsInternT.lean`).
  - `sort`/`const`/`fvar` expression nodes (`T/EIntern2.lean`).
- Re-intern identity (`T/ReIntern.lean`, `T/SubstLsH.lean`): on a well-formed store (con-ron's `StoreWF`), interning the readback of a handle returns that handle and leaves the state unchanged. This is why the port keeps arena handles where the twin rebuilds trees.
- Substitution at a parameter list:
  - `goM` and `substM` (`T/LvlSubstM.lean`).
  - Handle level: `substLMemoAt` (`T/SubstLH.lean`).
  - List level: `substLsMemoAt` (`T/SubstLsLoop.lean`, `T/SubstLsTop.lean`).
  - The twin's per-call memos `instLPLC`/`instLPLsC` are not mirrored. Instead, invariants (`MemoLOK`/`MemoLsOK`: a row is the re-intern of its substituted readback) plus re-intern identity make recomputation agree with a memo hit (`specR_transfer`).

Next: the `instLPGo` walk (ten arms; the `instLPC` memo is mirrored through
`specR_memoGetI`/`SetI`), then `instLPFast` (name/level readbacks, memo
clears).

### Progress (2026-11-24, `instantiateLevelParams` complete)

`instLPFast` is refined (`T/InstLPFast.lean`, `ilpf_spec`), with the walk `instLPGo` (`T/InstLP.lean`, `ilp_spec`).

- Dispatch: the `hasLP` cutoff (bit 0 of the derived word), then tag tests on the handle word.
- Arms: `app`, `lam`, `forallE`, `letE`, `proj` and `fvar` go through the mirrored `instLPC` memo; `sort` and `const` go through the level and level-list substitutions; `bvar` and `lit` return the handle unchanged.
- Fuel: induction on fuel; at fuel 0 the port hangs where the twin fails.
- Precondition: con-ron's own instLP invariants (`StateOK`, `InstLPMemoF`, `InstLPLMemoA`, `InstLPLsMemoA`, the readback-cache invariants). After each recursive call they are re-established from con-ron's `instLPGo_spec`, applied to the twin's run.
- Memo clears: the twin's clear also empties two memos the port does not mirror. A general clear lemma (`specR_memoClearIG`) only asks the twin's post-state to agree on the mirrored memos.

### Core: cache policy (2026-11-24)

Core's caches split into two kinds.

- **Not mirrored.** Readback and verdict caches (`readLC`, `readLsC`, `readNC`, `lvlEqC`, `lvlsEqC`). Recomputing these interns nothing new, and con-ron's cache invariants make a hit equal the recomputation.
- **Mirrored.** The entry caches (`whnfCoreC`, `whnfCoreCheapC`, `whnfC`, `inferC`, `inferIOC`, `defeqC`, `constTyC`, `constValC`, `ruleBodyC`). Recomputing these would intern intermediate nodes the twin's store lacks, so `SR` (which pins the store exactly) would fail. They become Pancake tables like the memos: `MemoAtG` with key encoders `[h]`, `[a, b]`, `[n, us]`, …, and new `Region` kinds plus their `CtxOK` separation facts.

ExprOps still to port: `wscopedBFast`, `fvarLeaves`/`leafGuard` (walks with a `seen` set), `instantiateLiftFast` (`inst1L` memo, mirrored). `takeEidx`/`eidxCopyUpto` are inlined as block copies where Core uses them.

### Progress (2026-11-24, Core infrastructure)

- **Mirrored caches in `SR`.** The three fixed caches (`constTyC`, `constValC`, `ruleBodyC`) are `SR.cache` (`CacheAt`, regions `.c k`).
- **Eager tower.** The six mode memos live on two sides (regions `.m false k`, `.m true k`, descriptors `EO` apart). The global `gEo` holds the active side's offset; the port's eager flag is `gEo ≠ 0`. `Ctx.saved` records the plain memos held by the enclosing `enterEager`, which fixes the active side for every spec. `SR.mode` is `ModeAt` (`T/Store.lean`).
  - `enterEager`/`leaveEager` flip `gEo` and switch the context (`T/Eager.lean`).
  - Mode-memo reads and writes address `mG (.m false k) + gEo` (`T/Mode.lean`). The defeq memo has a pair key and a `Bool` value (`T/DefeqMemo.lean`).
  - Generic memo read/write lemmas, given a key already in the key buffer, plus `SR` rebuilds after mode or fixed-cache writes (`T/MemoG.lean`).
- **Environment.** `Ctx.fe` is the twin's `IFEnv` (fixed while a declaration is checked). Its constants and projection tables are blocks in a separate append-only environment heap (`EHeapAt`; layouts `CIE`, `TblE`, `RuleE`).
  - Two hash tables keyed by `NIdx` point into that heap. Their contents are ghost maps `C.envM`/`C.tblM`, which represent `fe.find?`/`fe.findTable?` (`EnvRel`, a `CtxOK` fact).
  - The literal flags are in the global `gLit`.
  - `SR.env` is `EnvAt`. `find?` is `specR_envFindI`; field loads are `specR_envLoadI` (`T/Env.lean`).

Next: Core bodies bottom-up (constant instantiation `constTyAt`/`constValAt` with the fixed caches, `whnfCore` pieces, `inferBody`, `defeqBody`), then the knot as Pancake functions with a fuel induction.

### Progress (2026-11-24, the knot)

`T/Knot.lean` proves the knot shape with the bodies left abstract.

- **Entry points.** Six Pancake entry points (`whnfCore`, `whnf`, `infer`, `defeq`, `defeqE`, `inferIO`), each taking the fuel first. Each checks the fuel (zero hangs where the twin fails) and runs `whnf`'s stuck-tag shortcut. It then probes its mode memo. On a miss it calls its body at fuel − 1 and stores the answer. `defeqE` enters and leaves the eager tower around this.
- **Twin equations.** The twin's `coreKnot` at fuel `n+1` unfolds by `rfl` to the shapes these entry points implement.
- **`knot_all`.** The entry points refine `coreKnot mode C.side C.fe id n` at every fuel `n ≤ 2^62` and every context. The hypotheses are:
  - each body refines its twin (`whnfCoreBody`, `whnfBody`, `inferBody`, `defeqBody`, `inferBodyIO`) when the entry points refine the knot one level down;
  - an abstract twin invariant `TI` survives entering the eager tower.
- **Remaining.** The five bodies and everything they call. The check mode (`verified`/`trusted`) still needs a runtime representation.

### Progress (2026-11-24, first Core helpers)

- **`constValAt`** (`T/Core/ConstVal.lean`).
  - The `constValC` probe; on a miss, the level-parameter names are copied from the environment heap into the value heap (`T/EnvCopy.lean`), `instLPFast` is called, and the result is stored.
  - Fixed-cache reads and writes are `T/FixMemo.lean`.
- **`unfoldDefinition`** (`T/Core/Unfold.lean`).
  - Steps: `getAppFn`, the `const` test and view, `find?`, the `defnInfo` tag, the level-count check, `constValAt`, `getAppArgs`, `mkAppN`.
  - Its twin-side preconditions (denotations of the stored names and value, the cache invariants) are hypotheses. Every one of them follows from con-ron's `CheckOK` (see `Bridge/Core/Walks/Cached.lean`, `constValAt_spec`), which becomes the knot's `TI`.

### Next: literal arithmetic (blocks `whnfBody` via `reduceNat`)

`reduceNat` computes on `Nat` literals of any size. A literal's store row is `[0, limbs n…]`: canonical little-endian 64-bit limbs, with no zero top limb. Pieces:

1. **Limb blocks.** A number is represented as a value-heap block `BlkAt H o (limbs n)`. A copy loop moves a literal row (store memory, via the view's `wordsAt` facts) into a heap block.
2. **Bignum functions.**
   - Each function is a Pancake function over limb blocks, refined against `Nat`:
     - comparisons (`beq`, `ble`, `<`);
     - `add`, truncated `sub`, `succ`/`pred`;
     - `mul` (schoolbook, with 64×64→128 products from 32-bit halves, since Pancake has no high multiply);
     - `div`/`mod` (shift-subtract long division first);
     - `gcd` (Euclid);
     - `pow` (square-and-multiply, after `powGuard`);
     - `land`/`lor`/`xor`, `shiftLeft`/`shiftRight`;
     - `log2`, for `natSizeBytes`.
   - Each result is trimmed to canonical form.
3. **Literal interning.** Keys longer than the 3-word key buffer are needed. Either:
   - point the intern code's key local at a second, large key region (if the V-level cons-table specs are parametric in the key address), or
   - generalize the key-buffer size `KN` in `SR`/`CtxOK`.
4. **Then** `natBinOpResult`, `reduceNat`, `whnfStep`/`whnfLoop`/`whnfBody`.

### Progress (2026-11-24, bignums started)

- **Comparison.** `bigCmp` on two literal handles (`T/Big/Cmp.lean`): limb count, then a counted top-down verdict loop.
- **Literal copy.** `litToHeap` copies a literal's limbs into a fresh value-heap block (`T/Big/LitCopy.lean`). It re-views the handle for every limb, because a heap store forgets store-row facts.
- **Addition.** Heap-block addition (`T/Big/Add.lean`, `add_spec`): two carry loops, the final carry, and a canonical length. The proof goes through `T/Big/AddMath.lean` (carry-chain arithmetic, the 64-bit add-with-carry) and `limbs_eq_digits` (written digits are the canonical limbs).
- **Subtraction.** Truncated subtraction for `y ≤ x` (`T/Big/Sub.lean`, `sub_spec`): two borrow loops, then a counted scan for the canonical length.
- **Multiplication.** Schoolbook (`T/Big/Mul.lean`, `mul_spec`). The 64×64→128 multiply-accumulate is built from 32-bit halves (`T/Big/MulMath.lean`). The rows are proved through a closed form of the partially written cells (`T/Big/MulRow.lean`), with a Step-level loop rule for the nested loop (`step_forI`).
- **Bitwise operations and shifts.**
  - `land`/`lor`/`xor` (`T/Big/Bit.lean`) are generated from the subtraction proofs, with the borrow held at 0.
  - `shiftRight` (`T/Big/Shr.lean`) works limb by limb with two-step word shifts.
  - `shiftLeft` (`T/Big/Shl.lean`) is the verified product with the one-limb block `[2^r]`, then `q` zero limbs and a copy.
  - `sev` now evaluates variable shift amounts.
- **Remaining for `reduceNat`.**
  - Arithmetic: `div`/`mod`, `gcd`, `pow`, `log2`.
  - Literal interning from a heap block, with the large key region.
  - Then `natBinOpResult` and `reduceNat`.

### Decision (2026-11-24): `div`/`mod`/`gcd` on large literals decline

Pancake has no division instruction, and resource-limit declines are allowed (soundness only needs "the port accepts ⇒ the twin accepts").

- `div`, `mod` and `gcd` are computed exactly when both operands fit in one limb, by a verified 64-step word division loop.
- With a larger operand the port declines: it halts without an answer, which is `Stop` in the specs. An explicit decline message through the FFI can replace the halt later.
- `pow` is square-and-multiply on the verified `mul`, after the twin's `powGuard`.
- `natSizeBytes n` is `8 · max(|limbs n|, 1)`, so no bit logarithm is needed.
