import Mathlib

/-!
# A391055: iterating x -> gpf(3x+1) always reaches 2

Source: https://oeis.org/A391055

A391055 (Alain Rocchelli), offset 1: a(n) is the number of iterations of x -> gpf(3*x+1)
starting at n until the value 2 is reached; a(n) = -1 if 2 is not reached.
Conjecture (in the entry): a(n) is never equal to -1.

Conventions:
* gpf(m) is the greatest prime factor of m, written `m.primeFactors.sup id`; along the
  iteration the argument `3 * x + 1` is at least 4, so this is a genuine prime.
* a(n) ≠ -1 means that some iterate `f^[k] n` (k >= 0) equals 2; n ranges over n >= 1.
-/

namespace OMA.S_oeis_a391055

/-- The greatest prime factor of `m` (for `m ≥ 2`). -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

/-- The map `x ↦ gpf(3x + 1)`. -/
def f (x : ℕ) : ℕ := gpf (3 * x + 1)

/-- For every `n ≥ 1`, iterating `f` from `n` reaches `2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, f^[k] n = 2 := by
  sorry

end OMA.S_oeis_a391055
