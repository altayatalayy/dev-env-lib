/-! `dev_env/apply.zig:applyConfigs`: keep_linked is the union of restowed
packages and skipped packages with an existing stow-source entry. Models the
D1 regression after conflict classification/refresh, not filesystem resolution. -/
namespace DevEnv.Configs

variable {α : Type} [BEq α] [LawfulBEq α]

def keepLinked (toStow skipped existing : List α) : List α :=
  toStow ++ skipped.filter existing.contains

theorem mem_keepLinked (toStow skipped existing : List α) (x : α) :
    x ∈ keepLinked toStow skipped existing ↔
      x ∈ toStow ∨ (x ∈ skipped ∧ x ∈ existing) := by
  simp [keepLinked]

theorem skipped_existing_preserved (toStow skipped existing : List α) (x : α)
    (hs : x ∈ skipped) (he : x ∈ existing) : x ∈ keepLinked toStow skipped existing :=
  (mem_keepLinked ..).2 (Or.inr ⟨hs, he⟩)

theorem skipped_absent_not_claimed (toStow skipped existing : List α) (x : α)
    (ht : x ∉ toStow) (he : x ∉ existing) : x ∉ keepLinked toStow skipped existing := by
  simp [mem_keepLinked, ht, he]

/-- The old receipt construction lost skipped-but-existing packages. -/
theorem old_skip_loses_link :
    "tmux" ∉ ([] : List String) ∧
    "tmux" ∈ keepLinked [] ["tmux"] ["tmux"] := by decide

end DevEnv.Configs
