import Mathlib

/-!
# OEIS A111213: Difference between the closest squares surrounding prime p is prime.

Source: https://oeis.org/A111213
Credit: @unserus

OEIS: "Conjecture: The number of terms in this sequence is infinite."
A prime `p` is never a square, so the closest squares around it are `k^2 < p < (k+1)^2` with
`k = ⌊√p⌋ = Nat.sqrt p`, and their difference is `2k + 1`. The sequence lists `2k + 1`, in order
of `p`, for each prime `p` for which `2k + 1` is prime (with repetitions: `p = 29` gives `11`).
So the sequence has infinitely many terms exactly when infinitely many primes `p` qualify.
-/

namespace OMA.S_oeis_a111213

/-- The primes `p` contributing a term: the difference `2 ⌊√p⌋ + 1` of the surrounding squares
is prime. -/
def contributing : Set ℕ := {p : ℕ | p.Prime ∧ (2 * Nat.sqrt p + 1).Prime}

/-- A111213 has infinitely many terms. -/
theorem main : contributing.Infinite := by
  sorry

end OMA.S_oeis_a111213
