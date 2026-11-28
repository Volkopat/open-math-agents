import Mathlib

/-!
# OEIS A054800: First term of balanced prime quartets

Source: https://oeis.org/A054800
Credit: @unserus

OEIS: "First term of balanced prime quartets: p(m+1)-p(m) = p(m+2)-p(m+1) =
p(m+3)-p(m+2)." and (Charles R Greathouse IV, Apr 23 2011): "This sequence is
infinite if Dickson's conjecture holds."

The terms are the primes `p(m)` that start four consecutive primes in arithmetic
progression. With the 0-indexed `Nat.nth Nat.Prime i`, the condition on `i` is
`p(i+1) - p(i) = p(i+2) - p(i+1) = p(i+3) - p(i+2)` (the primes are strictly
increasing, so the subtractions do not truncate). The open statement is that
the sequence is infinite, i.e. infinitely many such `i` exist.
-/

namespace OMA.S_oeis_a054800

/-- The `i`-th prime, 0-indexed. -/
noncomputable abbrev p (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- The indices `i` such that `p i, p (i+1), p (i+2), p (i+3)` are in arithmetic
progression. -/
def quartetStarts : Set ℕ :=
  {i | p (i + 1) - p i = p (i + 2) - p (i + 1) ∧ p (i + 2) - p (i + 1) = p (i + 3) - p (i + 2)}

/-- There are infinitely many balanced prime quartets. -/
theorem main : quartetStarts.Infinite := by
  sorry

end OMA.S_oeis_a054800
