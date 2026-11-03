import DevEnv.Resolve

/-! Finite-universe termination for the tool closure abstraction. Count unseen
universe entries, not the work list length: `Resolve.step` can add a shared
dependency twice in one round. No no-duplicates assumption is needed. -/
namespace DevEnv.Resolve

variable {α : Type} [BEq α] [LawfulBEq α]

def remaining (U s : List α) : List α := U.filter (fun x => !s.contains x)

theorem remaining_step (deps : α → List α) (U s : List α) :
    remaining U (step deps s) = (remaining U s).filter (fun x => !(step deps s).contains x) := by
  simp only [remaining, List.filter_filter]
  apply List.filter_congr
  intro x hx
  have hm := @subset_step α _ _ deps s x
  simp only [List.contains_eq_mem]
  grind

theorem remaining_decreases (deps : α → List α) (U s : List α)
    (hd : ∀ t, ∀ d ∈ deps t, d ∈ U) (hn : ¬Closed deps s) :
    (remaining U (step deps s)).length < (remaining U s).length := by
  rw [remaining_step, List.length_filter_lt_length_iff_exists]
  simp only [Closed] at hn
  simp only [Classical.not_forall] at hn
  obtain ⟨t, ht, d, hd', hnot⟩ := hn
  refine ⟨d, ?_, ?_⟩
  · simp [remaining, hd t d hd', hnot]
  · simp [mem_step.2 (Or.inr ⟨t, ht, hd'⟩)]

def rounds (deps : α → List α) : Nat → List α → List α
  | 0, s => s
  | n + 1, s => rounds deps n (step deps s)

/-- The closure loop reaches a fixed point in at most |U \ s| growing rounds.
The implementation may make one additional pass to observe `changed = false`.
This proof allows cycles and duplicated dependency declarations. -/
theorem bounded_closure (deps : α → List α) (U s : List α)
    (hd : ∀ t, ∀ d ∈ deps t, d ∈ U) :
    ∃ n, n ≤ (remaining U s).length ∧ Closed deps (rounds deps n s) := by
  classical
  generalize he : (remaining U s).length = measure
  induction measure using Nat.strongRecOn generalizing s with
  | ind measure ih =>
    by_cases hc : Closed deps s
    · exact ⟨0, Nat.zero_le _, hc⟩
    · have hlt := remaining_decreases deps U s hd hc
      obtain ⟨n, hn, hc'⟩ := ih _ (by omega) (step deps s) rfl
      exact ⟨n + 1, by omega, hc'⟩

/-- The bound is independent of the requested set's length or duplicates. -/
theorem bounded_by_universe (deps : α → List α) (U s : List α)
    (hd : ∀ t, ∀ d ∈ deps t, d ∈ U) :
    ∃ n, n ≤ U.length ∧ Closed deps (rounds deps n s) := by
  obtain ⟨n, hn, hc⟩ := bounded_closure deps U s hd
  exact ⟨n, Nat.le_trans hn (List.length_filter_le _ _), hc⟩

/-- Every round stays inside any dependency-closed superset of the seeds.
Together with closure and seed preservation this establishes least closure. -/
theorem rounds_least (deps : α → List α) (s target : List α)
    (hs : ∀ x ∈ s, x ∈ target) (hc : Closed deps target) (n : Nat) :
    ∀ x ∈ rounds deps n s, x ∈ target := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    apply ih
    intro x hx
    rcases mem_step.1 hx with hx | ⟨t, ht, hd⟩
    · exact hs x hx
    · exact hc t (hs t ht) x hd

theorem rounds_preserve_seeds (deps : α → List α) (s : List α) (n : Nat) :
    ∀ x ∈ s, x ∈ rounds deps n s := by
  induction n generalizing s with
  | zero => exact fun _ h => h
  | succ n ih => exact fun x hx => ih _ x (subset_step hx)

end DevEnv.Resolve
