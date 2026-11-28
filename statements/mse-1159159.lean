import Mathlib

/-!
# Weakening Goldbach by allowing finitely many composites and 1

Source: https://math.stackexchange.com/questions/1159159
Credit: @jagraj28

The question asks whether it is open that there is a finite set `N` of positive integers such
that every positive even integer `n` is `n = n₁ + n₂` with `n₁, n₂ ∈ ℙ ∪ N`, where `ℙ` is the set
of primes. The question has no answer.

`main` states the existence of such a set. The Goldbach conjecture implies `main` with
`N = {1}` (`2 = 1 + 1`, and every even `n ≥ 4` is a sum of two primes); no weaker known result
seems to give it. A proof of `¬ main` would show that no finite set suffices.

Conventions.
* `N` is a `Finset ℕ` whose elements are all positive, as in the question.
* "Positive even integer" is `0 < n ∧ Even n`.
* `n₁` and `n₂` need not be distinct and are unordered (the statement is symmetric).
-/

namespace OMA.S_mse_1159159

/-- There is a finite set `N` of positive integers such that every positive even integer is a
sum of two elements of `ℙ ∪ N`. -/
theorem main : ∃ N : Finset ℕ, (∀ m ∈ N, 0 < m) ∧
    ∀ n : ℕ, 0 < n → Even n →
      ∃ n₁ n₂ : ℕ, (n₁.Prime ∨ n₁ ∈ N) ∧ (n₂.Prime ∨ n₂ ∈ N) ∧ n = n₁ + n₂ := by
  sorry

end OMA.S_mse_1159159
