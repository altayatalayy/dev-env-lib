import DevEnv.Ids

/-!
# The desired/actual diff

Models `planner.computeDiff` and the tool-merge step of `apply.applyOutcome`.
This is the core of dev-env: everything else is I/O around this calculation.

The properties proved here are the ones the whole design rests on:

* **disjointness** — a tool is never both installed and removed in one run;
* **convergence** — after a successful apply, the machine's tool set is exactly
  the lock's resolved set;
* **idempotence** — the diff computed immediately after an apply is empty, so a
  second apply does nothing;
* **an empty diff means tool/config sets agree and no stale Stow packages remain**.
  Disk truth and config/package pairing are separate obligations.

Only names matter here, so tools and configs are modelled as `String`.
-/

namespace DevEnv.Diff

open DevEnv.Ids

/-- Desired tool/config fields from the lock, plus packages from ResolveResponse. -/
structure Lock where
  release : String
  tools : List String
  configs : List String
  packages : List String := []

/-- `installed.json`, reduced to what the diff reads. -/
structure Receipt where
  release : String
  tools : List String
  configs : List String
  packages : List String := []

structure Diff where
  install : List String
  remove : List String
  addConfigs : List String
  removeConfigs : List String
  removePackages : List String
  releaseChanged : Bool

/--
`planner.computeDiff`. A missing receipt means "install everything"; a changed
installer release forces every resolved tool to be re-applied, because the new
release may pin different versions under the same names.
-/
def computeDiff (lock : Lock) : Option Receipt → Diff
  | none =>
    { install := lock.tools, remove := [],
      addConfigs := lock.configs, removeConfigs := [], removePackages := [],
      releaseChanged := false }
  | some a =>
    if a.release = lock.release then
      { install := missingFrom lock.tools a.tools,
        remove := missingFrom a.tools lock.tools,
        addConfigs := missingFrom lock.configs a.configs,
        removeConfigs := missingFrom a.configs lock.configs,
        removePackages := missingFrom a.packages lock.packages,
        releaseChanged := false }
    else
      { install := lock.tools,
        remove := missingFrom a.tools lock.tools,
        addConfigs := missingFrom lock.configs a.configs,
        removeConfigs := missingFrom a.configs lock.configs,
        removePackages := missingFrom a.packages lock.packages,
        releaseChanged := true }

/-- `Diff.isEmpty`, including the Stow-package removal field. -/
def isEmpty (d : Diff) : Prop :=
  d.install = [] ∧ d.remove = [] ∧ d.addConfigs = [] ∧ d.removeConfigs = [] ∧
    d.removePackages = [] ∧ d.releaseChanged = false

/--
The tool set `apply` writes back to `installed.json`:

```zig
for (old.tools) |tool| {
    if (contains(diff.install_tools, tool.tool)) continue;
    if (contains(diff.remove_tools, tool.tool)) continue;
    try merged_tools.append(tool);
}
// ... then append everything the installer reported installing
```
-/
def appliedTools (d : Diff) (old : List String) : List String :=
  old.filter (fun t => !d.install.contains t && !d.remove.contains t) ++ d.install

theorem mem_appliedTools {d : Diff} {old : List String} {x : String} :
    x ∈ appliedTools d old ↔ (x ∈ old ∧ x ∉ d.install ∧ x ∉ d.remove) ∨ x ∈ d.install := by
  simp [appliedTools, List.mem_filter]

/-! ## Field shapes -/

theorem diff_same {lock : Lock} {a : Receipt} (h : a.release = lock.release) :
    computeDiff lock (some a) =
      { install := missingFrom lock.tools a.tools,
        remove := missingFrom a.tools lock.tools,
        addConfigs := missingFrom lock.configs a.configs,
        removeConfigs := missingFrom a.configs lock.configs,
        removePackages := missingFrom a.packages lock.packages,
        releaseChanged := false } := by
  simp [computeDiff, h]

theorem diff_changed {lock : Lock} {a : Receipt} (h : a.release ≠ lock.release) :
    computeDiff lock (some a) =
      { install := lock.tools,
        remove := missingFrom a.tools lock.tools,
        addConfigs := missingFrom lock.configs a.configs,
        removeConfigs := missingFrom a.configs lock.configs,
        removePackages := missingFrom a.packages lock.packages,
        releaseChanged := true } := by
  simp [computeDiff, h]

/-! ## Disjointness -/

/--
A tool is never scheduled for installation and removal in the same run — under
a release change just as much as without one. Without this, `apply` could
install a tool and then have the old installer delete it.
-/
theorem install_remove_disjoint (lock : Lock) (a : Receipt) (x : String) :
    ¬(x ∈ (computeDiff lock (some a)).install ∧ x ∈ (computeDiff lock (some a)).remove) := by
  rintro ⟨hi, hr⟩
  by_cases hrel : a.release = lock.release
  · rw [diff_same hrel] at hi hr
    simp only [mem_missingFrom] at hi hr
    exact hi.2 hr.1
  · rw [diff_changed hrel] at hi hr
    simp only [mem_missingFrom] at hr
    exact hr.2 hi

/-! ## Convergence -/

/--
**Apply converges.** Starting from any receipt, applying the computed diff
produces exactly the lock's resolved tool set — no leftovers, nothing missing.
-/
theorem appliedTools_eq_desired (lock : Lock) (a : Receipt) (x : String) :
    x ∈ appliedTools (computeDiff lock (some a)) a.tools ↔ x ∈ lock.tools := by
  rw [mem_appliedTools]
  by_cases hrel : a.release = lock.release
  · rw [diff_same hrel]
    simp only [mem_missingFrom]
    constructor
    · rintro (⟨hold, -, hnr⟩ | hi)
      · by_cases hlock : x ∈ lock.tools
        · exact hlock
        · exact absurd ⟨hold, hlock⟩ hnr
      · exact hi.1
    · intro hlock
      by_cases hold : x ∈ a.tools
      · exact Or.inl ⟨hold, fun h => h.2 hold, fun h => h.2 hlock⟩
      · exact Or.inr ⟨hlock, hold⟩
  · rw [diff_changed hrel]
    simp only [mem_missingFrom]
    constructor
    · rintro (⟨hold, -, hnr⟩ | hi)
      · by_cases hlock : x ∈ lock.tools
        · exact hlock
        · exact absurd ⟨hold, hlock⟩ hnr
      · exact hi
    · exact fun hlock => Or.inr hlock

/-- The no-receipt case converges too: everything resolved gets installed. -/
theorem appliedTools_eq_desired_fresh (lock : Lock) (x : String) :
    x ∈ (computeDiff lock none).install ↔ x ∈ lock.tools := by
  simp [computeDiff]

/-! ## Idempotence -/

/-- The receipt `apply` writes after converging. -/
def receiptAfterApply (lock : Lock) (a : Receipt) : Receipt :=
  { release := lock.release,
    tools := appliedTools (computeDiff lock (some a)) a.tools,
    configs := lock.configs, packages := lock.packages }

/--
**Apply is idempotent.** Re-running `apply` against an unchanged lock computes
an empty diff, so the second run short-circuits before touching the package
manager, the installer, or `$HOME`.
-/
theorem diff_after_apply_isEmpty (lock : Lock) (a : Receipt) :
    isEmpty (computeDiff lock (some (receiptAfterApply lock a))) := by
  have hconv := appliedTools_eq_desired lock a
  have hrel : (receiptAfterApply lock a).release = lock.release := rfl
  rw [isEmpty, diff_same hrel]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [missingFrom_eq_nil_iff]; exact fun x hx => (hconv x).2 hx
  · rw [missingFrom_eq_nil_iff]; exact fun x hx => (hconv x).1 hx
  · rw [missingFrom_eq_nil_iff]; exact fun x hx => hx
  · rw [missingFrom_eq_nil_iff]; exact fun x hx => hx
  · rw [missingFrom_eq_nil_iff]; exact fun x hx => hx

/-! ## The empty diff means the states agree -/

/--
`Diff.isEmpty` means equal releases and tool/config sets, with no extra receipt
packages. It does not independently check for missing Stow packages.
-/
theorem isEmpty_iff_agree (lock : Lock) (a : Receipt) :
    isEmpty (computeDiff lock (some a)) ↔
      a.release = lock.release ∧
      (∀ x, x ∈ lock.tools ↔ x ∈ a.tools) ∧
      (∀ x, x ∈ lock.configs ↔ x ∈ a.configs) ∧
      (∀ x ∈ a.packages, x ∈ lock.packages) := by
  by_cases hrel : a.release = lock.release
  · rw [isEmpty, diff_same hrel]
    simp only [missingFrom_eq_nil_iff, and_true]
    constructor
    · rintro ⟨hi, hr, hac, hrc, hp⟩
      exact ⟨hrel, fun x => ⟨hi x, hr x⟩, fun x => ⟨hac x, hrc x⟩, hp⟩
    · rintro ⟨-, htools, hconfigs, hp⟩
      exact ⟨fun x hx => (htools x).1 hx, fun x hx => (htools x).2 hx,
             fun x hx => (hconfigs x).1 hx, fun x hx => (hconfigs x).2 hx, hp⟩
  · rw [isEmpty, diff_changed hrel]
    simp only [Bool.true_eq_false, and_false, false_iff, not_and]
    intro h; exact absurd h hrel

/-- Stale package removals must prevent the no-op path even when names agree. -/
theorem stale_package_blocks_noop :
    ¬isEmpty (computeDiff ⟨"r", [], [], []⟩ (some ⟨"r", [], [], ["old"]⟩)) := by
  simp [isEmpty, computeDiff, missingFrom]

/-- A2 coverage gap: without a validated config/package correspondence, equal
config names can mask a missing package. The model exposes the real diff rule. -/
theorem missing_package_can_be_hidden :
    isEmpty (computeDiff ⟨"r", ["tool"], ["config"], ["package"]⟩
      (some ⟨"r", ["tool"], ["config"], []⟩)) := by
  simp [isEmpty, computeDiff, missingFrom]

end DevEnv.Diff
