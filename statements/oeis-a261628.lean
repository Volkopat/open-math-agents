import Mathlib

/-!
# A261628: Least prime p such that n-(p*n'-1) and n+(p*n'-1) are both prime where n' = (3+(-1)^n)/2, or 0 if no such prime p exists.

Source: https://oeis.org/A261628
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A261628 (Zhi-Wei Sun, Aug 27 2015): 0 < a(n) <
sqrt(2*n)*log(5*n) for all n > 6.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 3, 0, 5, 2, 3, 2, 7, 3, ...).
* a(n) is the least prime p such that n - (p*n' - 1) and n + (p*n' - 1) are both prime, where n' =
  (3 + (-1)^n)/2 is 1 for odd n and 2 for even n (helper `np`, written as 2 - n % 2). If p*n' - 1
  > n the truncated natural subtraction gives 0, which is not prime, in agreement with a negative
  number not being prime.
* `0 < a(n) < sqrt(2n)*log(5n)` holds exactly when some prime p with both primality conditions
  satisfies p < sqrt(2n)*log(5n), and it is stated in this form.
* Real quantities (sqrt, log, exp) are computed in `ℝ` with the natural numbers cast; log is the
  natural logarithm `Real.log`.
-/

namespace OMA.S_oeis_a261628

/-- n' = (3 + (-1)^n)/2: 1 for odd n and 2 for even n. -/
def np (n : ℕ) : ℕ := 2 - n % 2

/-- The conjecture recorded in A261628. -/
theorem main : ∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧
    (p : ℝ) < Real.sqrt (2 * n) * Real.log (5 * n) ∧
    (n - (p * np n - 1)).Prime ∧ (n + (p * np n - 1)).Prime := by
  sorry

end OMA.S_oeis_a261628
