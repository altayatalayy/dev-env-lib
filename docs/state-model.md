# State model and lifecycle

Two JSON files under `$XDG_DATA_HOME/dev-env/` hold all persistent state. Both
use temp-file replacement followed by rename and both carry a `schema` field
that must equal the compiled-in `schema_version` or loading is a hard error.
This avoids exposing partial JSON to readers under a single writer. There is
no file/directory sync or writer locking, so power-loss durability and concurrent
writes are not established.

## `lock.json` — desired state

```zig
Lock = {
    schema, installer_release, installer_path, platform,
    selected_tools,     // what the user asked for
    resolved_tools,     // closure: selected + every dependency
    resolved_configs,   // config closure for the selected tools
    include_configs,
    install_layout,     // { bin, opt, cache_dir }
}
```

Written by `plan`, `apply`, and `upgrade` — all three go through
`planner.buildPlan`, so **`apply` always re-plans**; there is no way to apply a
stale lock. `plan` is exactly `apply` minus the execution.

`selected_tools` and `resolved_tools` are both stored because they answer
different questions. `selected_tools` is the user's intent and survives an
upgrade; `resolved_tools` is what the *current* installer derived from it and is
recomputed every run.

## `installed.json` — actual state

```zig
Receipt = {
    schema, installer_release, installer_path, platform, install_layout,
    tools,            // []InstalledTool: name, kind, version, opt_dir, exports, bin_links
    configs,          // config names currently applied
    stow_packages,    // stow package names currently stowed
    skipped_configs,  // configs deliberately not applied (policy = skip)
    owned_symlinks,   // every symlink dev-env or the installer created
    owned_prefixes,   // every <opt>/<tool> tree ever created
}
```

`installer_path` is recorded, not just `installer_release`. Removal must run
against **the exact binary that performed the install**, because only that
release knows the file layout it produced. `uninstall` and the removal half of
`apply` both refuse to proceed if that binary is gone.

`owned_prefixes` is a *superset* of the active prefixes on purpose: after an
upgrade, `<opt>/neovim` still holds the old version directory alongside the new
one. Keeping the prefix recorded is what lets `clean` find and reclaim inactive
versions later. Prefixes are dropped only when their tool is uninstalled.

## Selection

`planner.selectTools` picks the base selection, then adjusts it:

| Input | Base |
| --- | --- |
| `--tools a,b` | exactly `a,b` (each must exist, else `UnknownTool`) |
| no flag, lock exists | the locked `selected_tools` |
| no flag, no lock | every tool the installer advertises |

then `--add` (must exist) and `--remove` (must be selected, else
`ToolNotSelected`), then sort + dedupe.

The asymmetry is deliberate: an explicitly named tool that does not exist is an
*error*, but a tool carried over from an old lock that the newly selected
installer no longer ships is *dropped with a warning*. Upgrades preserve intent
where possible instead of failing.

## The diff

`planner.computeDiff(lock, plan, receipt)` reduces the two states to the work
`apply` must do:

| Field | Definition |
| --- | --- |
| `install_tools` | `lock.resolved_tools \ receipt.tools` — **or all of `resolved_tools` if the release changed** |
| `remove_tools` | `receipt.tools \ lock.resolved_tools` |
| `add_configs` | `lock.resolved_configs \ receipt.configs` |
| `remove_configs` | `receipt.configs \ lock.resolved_configs` |
| `remove_stow_packages` | `receipt.stow_packages \ plan.stow_packages` |
| `release_change` | `receipt.installer_release ≠ lock.installer_release` |

No receipt at all means "install everything". A release change forces every
resolved tool to be re-applied, because the new release may pin different
versions for tools whose *names* did not change.

`Diff.isEmpty()` is the idempotence gate: a second `apply` with nothing to do
short-circuits, refreshing only the env-export snapshot in the receipt if the
plan's exports drifted.

## Apply order

`apply.applyOutcome` executes in a fixed order, and the order matters:

1. **Compute the diff.** Empty → refresh exports if needed, return.
2. **System packages** via `apt`. The manager first probes which
   packages are already present, so a no-op run does not invoke the package
   manager at all.
3. **Merge surviving receipt tools** — tools that are neither installed nor
   removed carry over unchanged.
4. **Uninstall removed tools** through the *old* installer binary.
5. **Install new tools** through the *new* installer, dependency-ordered.
6. **Configs**, if enabled and there is anything to stow or unstow:
   1. extract the new release's dotfiles to `releases/<release>/dotfiles.new`
   2. scan every leaf target in `$HOME` for conflicts → apply the policy
   3. unstow packages that are no longer wanted
   4. reconcile the release dotfiles tree against the fresh extract
   5. point `stow-source/<pkg>` at the release tree
   6. `stow --restow`
   7. `apply-configs` for git checkouts and post-stow steps
7. **Write `installed.json`.**

Config conflict scanning precedes the config mutation steps under the default
`fail` policy. Tool and system-package changes have already happened by this
point; a config conflict can therefore leave a partial apply without a new
receipt (D2/A1).

## Conflict classification

`configs.classifyTarget` maps a would-be config target to one of:

| State | Meaning | Treated as conflict |
| --- | --- | --- |
| `missing` | nothing there | no |
| `managed` | symlink (or symlinked ancestor) resolving into a dev-env root | no |
| `foreign_file` | a real file | yes |
| `foreign_dir` | a real directory | yes |
| `foreign_symlink` | a symlink pointing outside dev-env roots | yes |

Ancestors are checked first: if `$HOME/.config` is itself a dev-env symlink,
everything under it is `managed` without stat'ing each leaf. Real directories
along the path are fine — GNU Stow merges trees, so only leaf entries can
collide. `--no-folding` is passed to stow so it never replaces a real directory
with a symlink to one.

Policies: `fail` (default — log conflicts and stop before config mutation),
`backup` (move the target under `backups/<timestamp>/home/…`, then stow),
`skip` (leave the
package unstowed when it was absent, preserve its link when already stowed,
and record it in `skipped_configs`).

The same three policies apply a second time, inside `refreshDotfiles`, when the
*managed* copy of a config has been edited locally — detected by comparing the
release tree against a fresh extract byte for byte.

## Lifecycle invariants and verification status

[Lean verification](formal-verification.md) checks these rules at different
levels; a proof of an abstract design is not a proof of every Zig I/O path.

1. **Receipt convergence:** the pure successful tool merge yields the desired
   tool set, assuming the installer reports exactly the requested tools.
2. **Idempotence:** an unchanged, fully applied plan has an empty diff; skipped
   configs and environment export refreshes have separate behavior.
3. **Disjointness:** install and remove sets are disjoint even across releases.
4. **Path boundaries:** the managed-link predicate proves lexical component
   containment. Some uninstall checks still use raw prefixes, so this does not
   establish isolation for every deletion.
5. **Removability and truthful claims:** the proposed two-phase receipt policy
   preserves abstract ownership and installation claims across crashes. The
   current final-write implementation violates both in reachable failure traces.
6. **Progress:** successful abstract apply converges under a stable plan and
   fair scheduling, with accurate starting disk/receipt state. Arbitrary repeated
   failures and external filesystem mutations are outside this result.

The highest priority is implementing receipt checkpoints with failure injection
at each side-effect boundary. Interrupted uninstall, partial installer/Stow
operations, durable writes and concurrent commands need further modeling and
implementation work. See [review.md](review.md).
