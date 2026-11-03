import DevEnv.Progress

/-! Kernel-checked, reachable failure witnesses. These are expected violations,
not proofs that the current Zig implementation is crash safe. -/
namespace DevEnv.Regressions
open Lifecycle Progress

-- Bool gives two distinct resource names.
def selected : Names Bool := fun x => x

def firstPlan : State Bool := plan {} 1 selected

def leaked (p : Policy) : State Bool := crash (run p 2 (start p firstPlan))

theorem firstPlan_reachable (p : Policy) : Reachable p firstPlan :=
  .step .init (.plan {} 1 selected rfl)

theorem run_reachable (p : Policy) (n : Nat) {s : State α} (h : Reachable p s) :
    Reachable p (run p n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih (.step h (.advance s))

theorem firstStart_reachable (p : Policy) : Reachable p (start p firstPlan) := by
  apply Reachable.step (firstPlan_reachable p)
  exact .start firstPlan rfl rfl (by simp [diffEmpty, firstPlan, plan])

theorem final_leak_reachable : Reachable .final (leaked .final) :=
  .step (run_reachable .final 2 (firstStart_reachable .final))
    (.crash _ (by decide))

theorem final_loses_ownership : ¬OwnershipComplete (leaked .final) := by
  intro h
  have := (h true).1
  simp [leaked, run, start, firstPlan, plan, advance, reserves, crash, selected] at this

theorem afterInstall_still_leaks : ¬OwnershipComplete (leaked .afterInstall) := by
  intro h
  have := (h true).1
  simp [leaked, run, start, firstPlan, plan, advance, reserves, crash, selected] at this

theorem afterInstall_leak_reachable : Reachable .afterInstall (leaked .afterInstall) :=
  .step (run_reachable .afterInstall 2 (firstStart_reachable .afterInstall))
    (.crash _ (by decide))

/-- A completed, truthful install, followed by a plan to remove it. -/
def installed (p : Policy) : State Bool := run p 6 (start p firstPlan)
def removalPlan (p : Policy) : State Bool := plan (installed p) 1 (fun _ => false)
def phantom (p : Policy) : State Bool :=
  crash (run p (if reserves p then 2 else 1) (start p (removalPlan p)))

theorem phantom_reachable (p : Policy) : Reachable p (phantom p) := by
  have hi := run_reachable p 6 (firstStart_reachable p)
  have hp : Reachable p (removalPlan p) := .step hi
    (.plan _ 1 (fun _ => false) (by cases p <;> rfl))
  have hs : Reachable p (start p (removalPlan p)) := .step hp
    (.start _ (by cases p <;> rfl) rfl (by
      intro h
      have ht := h.2.2.1 true
      cases p <;> contradiction))
  exact .step (run_reachable p _ hs) (.crash _ (by cases p <;> decide))

theorem weaker_policies_claim_missing (p : Policy) (h : p ≠ .twoPhase) :
    ¬NoPhantomInstall (phantom p) := by
  intro hn
  have ht := (hn true).1
  cases p with
  | twoPhase => exact h rfl
  | final | afterInstall | writeAhead => exact Bool.noConfusion (ht rfl)

/-- Re-selecting the removed tool makes the stale receipt suppress repair. -/
theorem final_false_noop :
    diffEmpty (plan (phantom .final) 1 selected) ∧
    (plan (phantom .final) 1 selected).disk true = false := by
  constructor
  · refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro x <;> cases x <;> rfl
  · rfl

theorem fresh_failure_has_no_receipt :
    (leaked .final).hasReceipt = false ∧ (leaked .final).disk true = true := ⟨rfl, rfl⟩

theorem false_noop_reachable : Reachable .final (plan (phantom .final) 1 selected) :=
  .step (phantom_reachable .final) (.plan _ 1 selected rfl)

/-- Add a second tool, crash before saving, then perform an enabled uninstall.
The first tool is recorded and removed; the unrecorded second tool survives. -/
def addPlan : State Bool := plan (installed .final) 1 (fun _ => true)
def partialAdd : State Bool := crash (run .final 2 (start .final addPlan))

theorem partialAdd_reachable : Reachable .final partialAdd := by
  have hp : Reachable .final addPlan :=
    .step (run_reachable .final 6 (firstStart_reachable .final))
      (.plan _ 1 (fun _ => true) rfl)
  have hs : Reachable .final (start .final addPlan) := .step hp
    (.start _ rfl rfl (by intro h; have ht := h.2.2.1 false; contradiction))
  exact .step (run_reachable .final 2 hs) (.crash _ (by decide))

theorem incomplete_uninstall_reachable : Reachable .final (uninstall partialAdd) :=
  .step partialAdd_reachable (.uninstall _ rfl rfl)

theorem completed_uninstall_leaves_orphan :
    (uninstall partialAdd).hasReceipt = false ∧ (uninstall partialAdd).disk false = true :=
  ⟨rfl, rfl⟩

/-- The checkpoint policy prevents this same removal/crash failure. -/
theorem twoPhase_phantom_safe : NoPhantomInstall (phantom .twoPhase) :=
  (reachable_safety (phantom_reachable .twoPhase)).2.1

end DevEnv.Regressions
