import Mathlib

/-!
# A014085: Number of primes between n^2 and (n+1)^2.

Source: https://oeis.org/A014085
Credit: @divmxnd0x

Conjecture (Legendre's conjecture, stated in A014085 as "still open"): for `n > 0` there is
always a prime between `n^2` and `(n+1)^2`, i.e. `a(n) > 0` for all positive `n`.

Formalization notes:
* `a n` counts the primes `p` with `n^2 < p < (n+1)^2` (offset 0, data `0, 2, 2, 2, 3, 2, 4, ...`);
  for `n ≥ 1` the endpoints are squares, hence not prime, so strict and non-strict inequalities
  give the same count.
-/

namespace OMA.S_oeis_a014085

/-- A014085(n): the number of primes strictly between `n^2` and `(n+1)^2`. -/
def a (n : ℕ) : ℕ := ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime).card

/-- Legendre's conjecture: `a(n) > 0` for every `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a014085
