import Mathlib

/-!
# A230362: Least prime p with 2*p^2 - 1 and 2*(n-p)^2 -1 both prime, or 0 if such a prime p does not exist.

Source: https://oeis.org/A230362
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A230362 (Zhi-Wei Sun, Oct 16 2013): 0 < a(n) <
sqrt(2n)*(log n) except for n = 1, 2, 3, 232, 1478, 6457.

Conventions:
* The sequence has offset 1 (data 3, 13, 7, 2, 2, 2, 3, 2, 2, 2, 3, 2, ...).
* a(n) is the least prime p with 2*p^2 - 1 and 2*(n-p)^2 - 1 both prime (or 0 if there is none).
  Here n - p may be negative (e.g. a(1) = 3 with 2*(1-3)^2 - 1 = 7), so (n-p)^2 is written as the
  square of `Int.natAbs` of the integer difference; the truncated natural subtraction 2*0^2 - 1 =
  0 (when p = n) is not prime, in agreement with -1 not being prime.
* `0 < a(n) < sqrt(2n)*log(n)` holds exactly when some prime p with both primality conditions
  satisfies p < sqrt(2n)*log(n); the statement asserts this for every n > 0 outside the six listed
  exceptions (it does not assert that the bound fails at the exceptions).
* Real quantities (sqrt, log, exp) are computed in `ℝ` with the natural numbers cast; log is the
  natural logarithm `Real.log`.
-/

namespace OMA.S_oeis_a230362

/-- The conjecture recorded in A230362. -/
theorem main : ∀ n : ℕ, 0 < n → n ∉ ({1, 2, 3, 232, 1478, 6457} : Finset ℕ) →
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) < Real.sqrt (2 * n) * Real.log n ∧ (2 * p ^ 2 - 1).Prime ∧
      (2 * Int.natAbs ((n : ℤ) - p) ^ 2 - 1).Prime := by
  sorry

end OMA.S_oeis_a230362
