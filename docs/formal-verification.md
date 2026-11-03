# Formal verification

All formal verification uses **Lean 4**, pinned in
`formal/lean/lean-toolchain`. There are no external Lean dependencies. The
models cover pure algorithms and an abstract apply/uninstall lifecycle; they
are hand-written specifications, not mechanically verified Zig code.

Lifecycle safety is proved by induction for arbitrary resource sets and finite histories, replacing
bounded enumeration. Known failure traces are positive theorems demonstrating
violations, so the suite passes only when those witnesses remain valid.
**The current Zig receipt protocol still has D2/A1.** Proving the proposed
checkpoint policy does not implement it.

## Run and maintain

```sh
formal/run.sh          # build every imported module and audit its axioms
```

Install Lean through `elan`; the runner uses `lake` on PATH or sources
`$HOME/.elan/env`. The workspace selects Lean 4.32.2. CI runs the same command.

For interactive proof development:

```sh
cd formal/lean
lake build
lake env lean Check.lean
```

`lake build` alone does **not** perform the axiom audit. `Check.lean` examines
all declarations originating in imported `DevEnv` modules, including private
helpers, definitions and unused axioms. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed transitively. `sorry`, `native_decide`, and custom
axioms fail the runner. There is no theorem list or shared temporary log.

When adding a module, import it from `DevEnv.lean`. Keep its source mapping and
assumptions current here. Changes to mapped Zig functions require review of
the model and corresponding tests; a green Lean build cannot detect source
changes on its own.

## Analysis and implementation plan

The migration reviewed `apply`, `planner`, `receipt`, `clean`, `uninstall`,
installer resolution and path handling, alongside `docs/review.md`, the state
model, embedded Zig tests and fake-installer regressions. The resulting work:

1. Preserve the lifecycle actions, four save policies and concrete failure
   traces; prove checkpoint safety without finite tool/release/plan bounds.
2. Prove successful completion and progress under explicit fair scheduling.
3. Close the resolver termination gap, include Stow removals in the diff, and
   formalize the previously fixed skip-link behavior.
4. Audit all formal declarations and generated artifacts.
5. Review the models against source again, run validation, and document the
   implementation obligations and remaining verification priorities.

## Coverage and source correspondence

| Lean module | Source or design | Checked result |
| --- | --- | --- |
| `Managed` | `dev_env/configs.zig:isManagedTarget`, `installer/apply.zig:isManagedExecutable` | Exact lexical path boundary over `UInt8` bytes; self/child acceptance, sibling/shorter rejection; raw-prefix and traversal limitations |
| `Ids` | `shared/ids.zig` | Set difference membership, emptiness, compaction membership and uniqueness under explicit sort contracts |
| `Diff` | `dev_env/planner.zig:computeDiff`, tool merge in `applyOutcome` | Install/remove disjointness across releases, merged receipt tools equal desired tools, idempotence, complete diff emptiness characterization including Stow removals |
| `Resolve`, `Termination` | Tool-method closure loop in `installer/resolver.zig:resolve` | Fixed point iff closed; seed preservation; least closure; termination within the finite universe bound |
| `Configs` | `dev_env/apply.zig:applyConfigs`, after conflict scanning and refresh | Existing skipped packages stay in `keep_linked`; absent skipped packages are not invented |
| `Lifecycle` | Abstract `applyOutcome` / uninstall, current and proposed receipt policies | Reachability and inductive safety of the two-phase checkpoint design |
| `Progress`, `Temporal` | Successful abstract apply execution and crash-free histories | All policies converge from accurate receipts; after planning stops, fair scheduling reaches convergence or uninstall clears the lock, including from an in-flight apply |
| `Regressions` | D2/A1 interruption scenarios | Reachable leaks, phantom installs, false no-op, and incomplete uninstall under weaker policies |

### Pure algorithm assumptions

`Diff.Lock.packages` represents `ResolveResponse.stow_packages`; it is not a
field of the on-disk lock. Empty diff means equal release/tool/config sets and
**no extra recorded packages**. It does not mean package equality:
`missing_package_can_be_hidden` proves that an inconsistent receipt can claim
a config while omitting its Stow package and still produce an empty diff.
`stale_package_blocks_noop` covers the opposite case.

Tool-merge convergence assumes the installer returns exactly the requested
installed tools. Config idempotence assumes all desired configs/packages were
successfully applied. Neither theorem establishes disk truth, validates an
installer response, or covers skipped configs by that assumption.

The resolver uses synchronous list rounds as a membership abstraction of Zig's
in-place `EnumSet` scans. Shared dependencies can occur twice in a list round,
so list length is **not** bounded by the enum size. `bounded_closure` counts
unseen universe entries instead; `bounded_by_universe` proves a fixed point in
at most `U.length` growing rounds, followed by a possible final no-change scan.
Every dependency must belong to `U`. This is a tool-closure result, not a proof
of the separate config queue, method selection, topological sort or Zig graph
library. `rounds_least` rules out unnecessary additions to the closure.

Path theorems establish lexical containment. They assume callers normalize
paths and do not prove symlink race safety or filesystem ownership. The
original `List Char` model has been corrected to `List UInt8`; ASCII literals
in regression examples are converted byte by byte. Not every destructive
operation uses the boundary predicate: uninstall still has raw-prefix checks.

### Lifecycle policies

Ownership claims and installed claims need opposite checkpoint ordering:
reserve deletion rights before creation, and drop installed claims before
destruction. Publish installation success only after the side effect succeeds.

| Policy | Meaning | Lean evidence |
| --- | --- | --- |
| `final` | Current coarse apply order; receipt saved last | Reachable ownership loss, phantom claim, false no-op and uninstall leftovers |
| `afterInstall` | Additional receipt write after tools | Still leaks before that write and still permits phantom claims after removal |
| `writeAhead` | Also reserve ownership before creating | Removal still permits phantom claims |
| `twoPhase` | Also retract installed claims before removal | Inductive safety for every reachable state in this abstraction |

`Lifecycle.next_inv` preserves a strengthened invariant for every transition.
`reachable_safety` then proves ownership completeness, absence of phantom tool
and config claims, and empty disk/Stow sets when the receipt is absent. It
holds inside apply phases as well as after crashes. `uninstall_leaves_nothing`
proves complete abstract removal given ownership completeness.
`diffEmpty_desired_present` derives actual desired presence from a truthful
receipt and an empty diff.

### Migration map and progress

| Former check | Lean replacement |
| --- | --- |
| `TypeOK` | State field types: booleans, natural release IDs, named phases and characteristic sets |
| `OwnershipComplete` | `reachable_safety` / `OwnershipComplete` |
| `NoPhantomInstall` | `reachable_safety` / `NoPhantomInstall` |
| `UninstallLeavesNothing` | `NoReceiptEmpty`, `uninstall_leaves_nothing`; reachable failure witness for current policy |
| `DiffEmptyMeansDesiredPresent` | `diffEmpty_desired_present`, `final_false_noop` |
| `EventuallyConverges` | `apply_converges`, `stable_plan_eventually_converges`, `Temporal.eventually_converges_or_uninstalled` |
| Expected failure of `MC_current` | Reachable, named theorems in `Regressions`; no parsing an expected tool error |

Safety permits arbitrarily many plans, crashes, retries and uninstalls. Release
IDs and resource names are unbounded; the old `MaxPlans` bound is unnecessary.
One resource name still abstracts one tool and one config package, as in the
old lifecycle model. The pure diff model treats their name sets independently.

Progress is conditional on a stable plan, successful operations, an accurate
starting disk/receipt correspondence, and a fair scheduler. `Follows` allows
only the next action or stuttering; `Fair` requires actual advances eventually.
Lean proves that arbitrary finite action sequences eventually occur, then
applies that result to apply. The two-phase stable driver converges in at most
seven **actions**, with no bound on intervening stuttering. Launched apply
completion is proved for all four policies.

`Temporal.crash_free_healthy` derives the required correspondence from the
initial state and every crash-free transition; callers need not assume it for
a reachable history. `eventually_converges_or_uninstalled` proves the old
convergence-or-cleared-lock goal from **any** such state, including an in-flight
apply. Arbitrarily many plans may precede that state. The subsequent stream
must satisfy `StableStep` (advance, stutter or enabled uninstall) and action
fairness. This replaces the old `plans = MaxPlans` trigger with an explicit
stable-tail assumption rather than retaining an artificial plan counter.
The crash-free relation is also proved to be a restriction of `Lifecycle.Next`.

No liveness is claimed under endless crashes, permanent failures, repeated plan
changes in the tail, or arbitrary crash leftovers.

## Remaining obligations and priorities

| Priority / finding | What is missing | Next proof and executable test |
| --- | --- | --- |
| 1 — D2/A1, C7 | Zig saves the receipt after side effects | Implement ownership/installed checkpoints and inject failures before/after each write, deletion, install and Stow step; compare emitted receipts with model states |
| 1 — persistence | Rename provides atomic replacement, but no file/directory sync is performed | Define process-crash versus power-loss guarantees, then prove durable checkpoint ordering against those guarantees |
| 1 — partial operations | Lifecycle install/config/uninstall actions are atomic; real operations are not | Split per-tool/version/link actions, include failed replacement, partial Stow, deletion failure and interrupted uninstall; prove ownership and truthful claims after each |
| 1 — deletion boundaries | Raw-prefix uninstall checks; receipt prefixes are trusted; deletion errors may be ignored | Unify normalized containment checks; test sibling paths, traversal, foreign links and failed deletion before extending removal proofs |
| 2 — A2 | Config/package correspondence and receipt consistency are unvalidated assumptions | Encode typed pairs or validate lengths, uniqueness and correspondence; prove projection consistency; test malformed installer/receipt data |
| 2 — D1 and C4 | Skip membership is proved, but not link targets/content or blocking ancestors | Prove retained links still reach retained trees across releases and clean; test file ancestors, dangling links and upgrade/skip/clean together |
| 2 — resolver | Config queue, method selection and dependency-first ordering are outside the model | Prove config closure and tool prerequisites, successful order and rejection of cycles/unknown dependencies; connect to existing resolver tests |
| 2 — recovery and concurrency | External deletion, stale/corrupt receipts, concurrent apply/clean/uninstall and fixed `.tmp` filenames | Define reconciliation/locking protocol; add corruption and concurrent-writer tests before proving recovery |
| 3 — A5, A6/A7, C2/C5/C6 | Archive consumption, shell selection, discovery, command construction, online re-planning | Resolve product/protocol behavior first; use focused integration tests, then model stable rules where worthwhile |

The existing fake suite covers successful apply/idempotence, upgrades,
removals, config conflicts, the D1 modified-config skip case, and clean/uninstall.
It does not systematically inject failures between side effects and receipt
writes. Its fail-policy test currently expects no receipt after a first config
conflict; checkpoint implementation must update that expectation to an honest
partial receipt with retained ownership.

No claim here covers archive extraction, upstream downloads/builds, system
package rollback, GNU Stow internals, OS durability, memory safety, or automatic
refinement from Zig to Lean. System packages intentionally retained by
uninstall are outside the managed disk set. The dev-env repository contains
the implementation review and integration test coverage.
