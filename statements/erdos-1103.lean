import Mathlib

/-!
# Erdős Problem 1103

Source: https://www.erdosproblems.com/1103
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `A` be an infinite sequence of integers such that every `n ∈ A + A` is squarefree.
How fast must `A` grow?

The source records that Erdős noted such a sequence exists which grows exponentially, but did not
expect one of polynomial growth. Following the rule to state the expected answer when the source
gives one, the statement below says: no such sequence has polynomial growth.

Conventions:
* `A` is a set of positive integers listed increasingly as `a_0 < a_1 < …`, i.e.
  `a_j = Nat.nth (· ∈ A) j`; growth is only meaningful for positive terms, and `0 ∉ A` is
  automatic since `0 + 0 = 0` is not squarefree;
* `A + A` is the full sumset, so `a + a = 2a` must be squarefree as well;
* polynomial growth means `a_j ≤ j ^ C` for some `C` and all large `j` (a constant factor
  `K j ^ C` can be absorbed by enlarging `C`); the statement is its negation for every such `A`.
-/

namespace OMA.S_erdos_1103

open Filter

/-- Erdős Problem 1103 (Erdős's expectation): an infinite set `A ⊆ ℕ` all of whose pairwise sums
`a + b` (`a, b ∈ A`, possibly equal) are squarefree cannot have polynomial growth. -/
theorem main : ∀ A : Set ℕ, A.Infinite → (∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)) →
    ¬ ∃ C : ℕ, ∀ᶠ j : ℕ in atTop, Nat.nth (· ∈ A) j ≤ j ^ C := by
  sorry

end OMA.S_erdos_1103
