import Mathlib

/-!
# Infinitely many primes in OEIS A260647

Source: https://oeis.org/A260647 (Arkadiusz Wesolowski)
Credit: @prophetlabs

A260647 consists of sums of two distinct positive triangular numbers.
The conjecture concerns infinitely many different prime values of these sums.
-/

namespace OMA.S_oeis_a260647

/-- The triangular number with index `k`, including the value zero at index zero. -/
def triangular (k : ℕ) : ℕ := k * (k + 1) / 2

theorem main :
    {p : ℕ | p.Prime ∧ ∃ i j : ℕ, 0 < i ∧ i < j ∧ p = triangular i + triangular j}.Infinite := by
  sorry

end OMA.S_oeis_a260647
