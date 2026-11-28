import Mathlib

/-!
# OEIS A274987: Primes p such that A274601(p) is a prime

Source: https://oeis.org/A274987
Credit: @unserus

OEIS: "It is conjectured that the sequence is infinite."

A274601(n) = 2*3^(s-1) - n, where s is the number of trits of n in balanced
ternary; equivalently (OEIS formula) A274601(n) = 2*3^floor(log_3(2n-1)) - n,
written here with `Nat.log 3 (2 * n - 1)` (the floor of the base-3 logarithm).
The subtraction does not truncate for `n ≥ 1`, because `2n - 1 < 3^(k+1)` with
`k = floor(log_3(2n-1))` gives `n ≤ 2 * 3^k`. The conjecture is that infinitely
many primes `p` have `A274601(p)` prime.
-/

namespace OMA.S_oeis_a274987

/-- A274601(n) = 2 * 3^floor(log_3(2n-1)) - n. -/
def a274601 (n : ℕ) : ℕ := 2 * 3 ^ Nat.log 3 (2 * n - 1) - n

/-- The terms of A274987. -/
def a274987Set : Set ℕ := {p | p.Prime ∧ (a274601 p).Prime}

/-- A274987 is infinite. -/
theorem main : a274987Set.Infinite := by
  sorry

end OMA.S_oeis_a274987
