import Mathlib

/-!
# A401848: orbits of x -> x^(omega(x)-1) + 1

Source: https://oeis.org/A401848

A401848 (Nguyen Trong Nhan) is the trajectory of 30 under the map
x -> x^(omega(x)-1) + 1, where omega(x) is the number of distinct prime divisors of x.
Its comments state the conjecture: for every integer k >= 2, the orbit starting at k
eventually reaches 2.

Conventions:
* omega(x) is `x.primeFactors.card`; for x >= 2 it is at least 1, so the exponent
  `omega(x) - 1` is never truncated along an orbit starting at k >= 2.
* The orbit of k is `fun m => f^[m] k`; reaching 2 means `f^[m] k = 2` for some m >= 0.
-/

namespace OMA.S_oeis_a401848

/-- The map `x ↦ x ^ (ω(x) - 1) + 1`. -/
def f (x : ℕ) : ℕ := x ^ (x.primeFactors.card - 1) + 1

/-- Every orbit starting at `k ≥ 2` eventually reaches `2`. -/
theorem main : ∀ k : ℕ, 2 ≤ k → ∃ m : ℕ, f^[m] k = 2 := by
  sorry

end OMA.S_oeis_a401848
