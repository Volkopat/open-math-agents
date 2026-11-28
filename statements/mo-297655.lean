import Mathlib

/-!
# A stronger version of the Erdős–Turán conjecture on arithmetic progressions

Source: https://mathoverflow.net/questions/297655/is-a-stronger-version-of-the-erdos-turan-conjecture-on-arithmetic-progessions-re
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The size of `S ⊆ ℕ` is `|S| = ∑_{n ∈ S} 1/n`. The page's first question (Q1) asks whether, for
each `k > 0`, there is a finite constant `c_k` such that every `S` free of `k`-term arithmetic
progressions has `|S| ≤ c_k`. `main` states the positive answer; a proof of its negation answers
no. (The further questions on explicit `c_k` and greedy sets are not stated.)

Conventions: sets of positive integers; a `k`-term arithmetic progression is `a, a + d, …,
a + (k-1)d` with `d ≥ 1`; `|S| ≤ c` means every finite subset has reciprocal sum `≤ c` (so `|S|`
is finite).
-/

namespace OMA.S_mo_297655

/-- `S` contains no `k`-term arithmetic progression. -/
def APFree (k : ℕ) (S : Set ℕ) : Prop :=
  ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

theorem main :
    ∀ k : ℕ, 0 < k → ∃ c : ℝ, ∀ S : Set ℕ, (∀ n ∈ S, 0 < n) → APFree k S →
      ∀ F : Finset ℕ, (F : Set ℕ) ⊆ S → ∑ n ∈ F, (1 : ℝ) / n ≤ c := by
  sorry

end OMA.S_mo_297655
