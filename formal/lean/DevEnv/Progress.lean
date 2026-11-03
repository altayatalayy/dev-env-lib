import DevEnv.Lifecycle

/-! Crash-free completion and temporal progress. Fairness means the scheduler
actually executes the next action eventually; infinite stuttering is excluded.
No re-plan, uninstall, external mutation, or failure occurs during this run. -/
namespace DevEnv.Progress
open Lifecycle

variable {α : Type}

def run (p : Policy) : Nat → State α → State α
  | 0, s => s
  | n + 1, s => run p n (advance p s)

def Converged (s : State α) : Prop :=
  s.phase = .idle ∧ s.recRelease = s.lockRelease ∧
  ∀ x, s.disk x = s.desired x ∧ s.stowed x = s.desired x ∧
    s.tools x = s.desired x ∧ s.configs x = s.desired x

/-- Exact convergence requires an accurate starting receipt, as on a crash-free
history. Safety alone permits unclaimed leftovers after an earlier crash. -/
theorem apply_converges (p : Policy) (s : State α)
    (hd : ∀ x, s.disk x = s.tools x)
    (hr : s.hasReceipt = false → ∀ x, s.tools x = false) :
    Converged (run p 6 (start p s)) := by
  cases p <;> simp only [Converged, run, start, advance, reserves] <;>
    constructor <;> try rfl
  all_goals
    constructor
    · rfl
    · intro x; have hx := hd x; have hh := fun h => hr h x; grind

/-- A terminating fresh apply gives a truthful receipt and an empty next diff. -/
theorem completion_diff_empty {s : State α} (h : Converged s) (hr : s.hasReceipt = true) :
    diffEmpty s := by
  exact ⟨hr, h.2.1, fun x => (h.2.2 x).2.2.1, fun x => (h.2.2 x).2.2.2⟩

/-- A stream executes only the next action or a stutter. -/
def Follows (f : α → α) (trace : Nat → α) : Prop :=
  ∀ n, trace (n + 1) = trace n ∨ trace (n + 1) = f (trace n)

def Fair (f : α → α) (trace : Nat → α) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ trace (m + 1) = f (trace m)

/-- Stuttering cannot hide the next transition on a fair stream. -/
theorem eventually_next {f : α → α} {trace : Nat → α}
    (hs : Follows f trace) (hf : Fair f trace) (n : Nat) :
    ∃ k, n ≤ k ∧ trace k = f (trace n) := by
  obtain ⟨m, hnm, hm⟩ := hf n
  have walk : ∀ d, trace (n + d) = trace n ∨
      ∃ k, n ≤ k ∧ trace k = f (trace n) := by
    intro d
    induction d with
    | zero => exact Or.inl rfl
    | succ d ih =>
      rcases ih with he | he
      · rcases hs (n + d) with hh | hh
        · left; calc
            trace (n + (d + 1)) = trace (n + d + 1) := by congr 1
            _ = trace (n + d) := hh
            _ = trace n := he
        · right; exact ⟨n + d + 1, by omega, by simpa [he] using hh⟩
      · exact Or.inr he
  rcases walk (m - n) with he | he
  · have hmn : n + (m - n) = m := by omega
    rw [hmn] at he
    exact ⟨m + 1, by omega, by rw [hm, he]⟩
  · exact he

def iterate (f : α → α) : Nat → α → α
  | 0, s => s
  | n + 1, s => iterate f n (f s)

/-- Fair scheduling eventually executes any finite sequence, with no bound on
how much stuttering the scheduler inserts between actions. -/
theorem eventually_iterate {f : α → α} {trace : Nat → α}
    (hs : Follows f trace) (hf : Fair f trace) (steps n : Nat) :
    ∃ k, n ≤ k ∧ trace k = iterate f steps (trace n) := by
  induction steps generalizing n with
  | zero => exact ⟨n, Nat.le_refl _, rfl⟩
  | succ steps ih =>
    obtain ⟨m, hnm, hm⟩ := eventually_next hs hf n
    obtain ⟨k, hmk, hk⟩ := ih m
    exact ⟨k, Nat.le_trans hnm hmk, by rw [hk, hm]; rfl⟩

theorem run_eq_iterate (p : Policy) (n : Nat) (s : State α) :
    run p n s = iterate (advance p) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _

/-- Temporal replacement for the launched, stable-plan part of the old
EventuallyConverges property, for every save policy and arbitrary state size. -/
theorem eventually_converges (p : Policy) (s : State α) (trace : Nat → State α)
    (hstart : trace 0 = start p s)
    (hd : ∀ x, s.disk x = s.tools x)
    (hr : s.hasReceipt = false → ∀ x, s.tools x = false)
    (hs : Follows (advance p) trace) (hf : Fair (advance p) trace) :
    ∃ n, Converged (trace n) := by
  obtain ⟨n, _, hn⟩ := eventually_iterate hs hf 6 0
  refine ⟨n, ?_⟩
  rw [hn, hstart, ← run_eq_iterate]
  exact apply_converges p s hd hr

/-- Stable-plan driver including ApplyStart and its empty-diff short circuit. -/
noncomputable def drive (s : State α) : State α := by
  classical
  exact if s.phase = .idle then
    if s.hasLock = true ∧ ¬diffEmpty s then start .twoPhase s else s
  else advance .twoPhase s

/-- A converged receipt is an absorbing state for the stable-plan driver. -/
theorem drive_converged {s : State α} (hc : Converged s) (hr : s.hasReceipt = true) :
    drive s = s := by
  have he := completion_diff_empty hc hr
  simp [drive, hc.1, he]

set_option maxRecDepth 2048 in
theorem drive_start_completes (s : State α) :
    iterate drive 6 (start .twoPhase s) = run .twoPhase 6 (start .twoPhase s) := by
  simp only [iterate, drive, start, reserves, advance, run]
  rfl

/-- With a stable lock, the driver either already agrees or reaches agreement
in seven actions (start plus six phases). Skipped configs and failures are
outside this successful-run abstraction. -/
theorem drive_converges (s : State α) (hi : s.phase = .idle)
    (hl : s.hasLock = true)
    (hd : ∀ x, s.disk x = s.tools x) (hc : ∀ x, s.stowed x = s.configs x)
    (hr : s.hasReceipt = false → ∀ x, s.tools x = false) :
    ∃ n, n ≤ 7 ∧ Converged (iterate drive n s) := by
  classical
  by_cases he : diffEmpty s
  · refine ⟨0, by omega, hi, he.2.1, ?_⟩
    intro x
    exact ⟨(hd x).trans (he.2.2.1 x), (hc x).trans (he.2.2.2 x),
      he.2.2.1 x, he.2.2.2 x⟩
  · refine ⟨7, Nat.le_refl _, ?_⟩
    have hstart : drive s = start .twoPhase s := by simp [drive, hi, hl, he]
    rw [iterate, hstart, drive_start_completes]
    exact apply_converges .twoPhase s hd hr

/-- Stable planning plus fair scheduling gives eventual convergence, including
waiting for ApplyStart. There is no finite bound on scheduler stuttering. -/
theorem stable_plan_eventually_converges (s : State α) (trace : Nat → State α)
    (hzero : trace 0 = s) (hi : s.phase = .idle) (hl : s.hasLock = true)
    (hd : ∀ x, s.disk x = s.tools x) (hc : ∀ x, s.stowed x = s.configs x)
    (hr : s.hasReceipt = false → ∀ x, s.tools x = false)
    (hs : Follows drive trace) (hf : Fair drive trace) :
    ∃ n, Converged (trace n) := by
  obtain ⟨steps, _, hconv⟩ := drive_converges s hi hl hd hc hr
  obtain ⟨n, _, hn⟩ := eventually_iterate hs hf steps 0
  exact ⟨n, by rw [hn, hzero]; exact hconv⟩

end DevEnv.Progress
