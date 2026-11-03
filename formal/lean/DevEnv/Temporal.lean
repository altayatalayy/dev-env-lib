import DevEnv.Progress

/-! Global crash-free history and the stable-tail leads-to property. Planning
can occur arbitrarily often before the tail begins; uninstall remains allowed
in the tail and discharges the goal by clearing the lock. -/
namespace DevEnv.Temporal
open Lifecycle Progress
variable {α : Type}

def Accurate (s : State α) : Prop :=
  (∀ x, s.disk x = s.tools x ∧ s.stowed x = s.configs x) ∧
  (s.hasReceipt = false → ∀ x, s.tools x = false)

def Healthy (s : State α) : Prop :=
  Accurate (run .twoPhase 6 s) ∧
  (s.phase ≠ .idle → Converged (run .twoPhase 6 s))

theorem run_idle {s : State α} (h : s.phase = .idle) : run .twoPhase 6 s = s := by
  simp [run, advance, h]

theorem run_advance (s : State α) :
    run .twoPhase 6 (advance .twoPhase s) = run .twoPhase 6 s := by
  cases hp : s.phase <;> simp [run, advance, hp]

theorem accurate_of_converged {s : State α} (h : Converged s) (hr : s.hasReceipt = true) :
    Accurate s := by
  refine ⟨fun x => ⟨?_, ?_⟩, by simp [hr]⟩
  · exact (h.2.2 x).1.trans (h.2.2 x).2.2.1.symm
  · exact (h.2.2 x).2.1.trans (h.2.2 x).2.2.2.symm

inductive NoCrashNext : State α → State α → Prop where
  | plan (s r names) : s.phase = .idle → NoCrashNext s (plan s r names)
  | start (s) : s.phase = .idle → s.hasLock = true → ¬diffEmpty s → NoCrashNext s (start .twoPhase s)
  | advance (s) : NoCrashNext s (advance .twoPhase s)
  | uninstall (s) : s.phase = .idle → s.hasReceipt = true → NoCrashNext s (uninstall s)
  | stutter (s) : NoCrashNext s s

inductive NoCrashReachable : State α → Prop where
  | init : NoCrashReachable {}
  | step : NoCrashReachable s → NoCrashNext s t → NoCrashReachable t

/-- The crash-free relation is a restriction of the migrated lifecycle. -/
theorem noCrashNext_is_next {s t : State α} (h : NoCrashNext s t) : Next .twoPhase s t := by
  cases h with
  | plan r names hi => exact .plan _ r names hi
  | start hi hl hd => exact .start _ hi hl hd
  | advance => exact .advance _
  | uninstall hi hr => exact .uninstall _ hi hr
  | stutter => exact .stutter _

theorem noCrashReachable_is_reachable {s : State α} (h : NoCrashReachable s) :
    Reachable .twoPhase s := by
  induction h with
  | init => exact .init
  | step _ hn ih => exact .step ih (noCrashNext_is_next hn)

theorem healthy_step {s t : State α} (h : Healthy s) (hn : NoCrashNext s t) : Healthy t := by
  cases hn with
  | plan r names hi =>
    have ha : Accurate s := by simpa [run_idle hi] using h.1
    have hp : (plan s r names).phase = .idle := hi
    unfold Healthy
    rw [run_idle hp]
    exact ⟨ha, fun hn => False.elim (hn hp)⟩
  | start hi _ _ =>
    have ha : Accurate s := by simpa [run_idle hi] using h.1
    have hc := apply_converges .twoPhase s (fun x => (ha.1 x).1) ha.2
    exact ⟨accurate_of_converged hc rfl, fun _ => hc⟩
  | advance =>
    refine ⟨?_, ?_⟩
    · simpa [run_advance] using h.1
    · intro ht
      have hi : s.phase ≠ .idle := by
        intro hi; apply ht; simp [advance, hi]
      simpa [run_advance] using h.2 hi
  | uninstall hi _ =>
    have ha : Accurate s := by simpa [run_idle hi] using h.1
    have hp : (uninstall s).phase = .idle := hi
    simp only [Healthy, run_idle hp, hp, ne_eq, not_true_eq_false, false_implies, and_true]
    refine ⟨?_, ?_⟩
    · intro x
      have hx := ha.1 x
      simp only [uninstall]
      grind
    · simp [uninstall]
  | stutter => exact h

theorem crash_free_healthy {s : State α} (h : NoCrashReachable s) : Healthy s := by
  induction h with
  | init => simp [Healthy, Accurate, run, advance]
  | step _ hn ih => exact healthy_step ih hn

def phaseSteps : Phase → Nat
  | .idle => 0
  | .reserving => 6
  | .removing => 5
  | .installing => 4
  | .persisting => 3
  | .configuring => 2
  | .saving => 1

set_option maxRecDepth 2048 in
theorem drive_inflight {s : State α} (h : s.phase ≠ .idle) :
    iterate drive (phaseSteps s.phase) s = run .twoPhase 6 s := by
  cases hp : s.phase
  · exact False.elim (h hp)
  all_goals simp [phaseSteps, hp, iterate, drive, run, advance]

def Done (s : State α) : Prop := Converged s ∨ s.hasLock = false

theorem healthy_completes {s : State α} (h : Healthy s) :
    ∃ n, Done (iterate drive n s) := by
  by_cases hl : s.hasLock = true
  · by_cases hi : s.phase = .idle
    · have ha : Accurate s := by simpa [run_idle hi] using h.1
      obtain ⟨n, _, hc⟩ := drive_converges s hi hl (fun x => (ha.1 x).1)
        (fun x => (ha.1 x).2) ha.2
      exact ⟨n, Or.inl hc⟩
    · exact ⟨phaseSteps s.phase, Or.inl (by rw [drive_inflight hi]; exact h.2 hi)⟩
  · exact ⟨0, Or.inr (by change s.hasLock = false; cases he : s.hasLock <;> simp_all)⟩

/-- Once planning stops, only progress, stuttering, or enabled uninstall remain. -/
def StableStep (s t : State α) : Prop :=
  t = s ∨ t = drive s ∨ (s.phase = .idle ∧ s.hasReceipt = true ∧ t = uninstall s)

/-- The old convergence-or-cleared-lock temporal goal, from ANY crash-free
reachable state, including an in-flight apply. There is no resource/plan bound.
`Fair` is action fairness on the deterministic stable driver. -/
theorem eventually_converges_or_uninstalled (trace : Nat → State α)
    (hr : NoCrashReachable (trace 0))
    (hs : ∀ n, StableStep (trace n) (trace (n + 1)))
    (hf : Fair drive trace) : ∃ n, Done (trace n) := by
  classical
  apply Classical.byContradiction
  intro hn
  have hnot : ∀ n, ¬Done (trace n) := fun n hd => hn ⟨n, hd⟩
  have hfollow : Follows drive trace := by
    intro n
    rcases hs n with he | he | ⟨_, _, he⟩
    · exact Or.inl he
    · exact Or.inr he
    · exact False.elim (hnot (n + 1) (Or.inr (by rw [he]; rfl)))
  obtain ⟨steps, hd⟩ := healthy_completes (crash_free_healthy hr)
  obtain ⟨n, _, he⟩ := eventually_iterate hfollow hf steps 0
  exact hnot n (by rw [he]; exact hd)

end DevEnv.Temporal
