import Mathlib

/-!
# OEIS A014688: primes of the form `prime(n) + n`

Source: https://oeis.org/A014688
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = prime(n) + n`. Conjecture (OEIS entry): this sequence contains infinitely many primes,
yet contains arbitrarily long runs of consecutive composite terms.

Conventions:
* `prime(n)` is the `n`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`, `n ≥ 1`.
-/

namespace OMA.S_oeis_a014688

/-- Infinitely many `n ≥ 1` have `prime(n) + n` prime, and there are arbitrarily long runs of
consecutive `n` with `prime(n) + n` composite. -/
theorem main : {n : ℕ | 1 ≤ n ∧ (Nat.nth Nat.Prime (n - 1) + n).Prime}.Infinite ∧
    ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ ∀ j < L, ¬ (Nat.nth Nat.Prime (n + j - 1) + (n + j)).Prime := by
  sorry

end OMA.S_oeis_a014688
