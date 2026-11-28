import Mathlib

/-!
# A231631: Least positive integer k < n with k!*(n-k) + 1 prime, or 0 if such an integer k does not exist.

Source: https://oeis.org/A231631
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A231631 (Zhi-Wei Sun, Nov 11 2013): 0 < a(n) <
sqrt(n)*(log n) for all n > 2.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, ...).
* a(n) is the least positive integer k < n with k!*(n-k) + 1 prime (or 0 if there is none). `0 <
  a(n) < sqrt(n)*log(n)` holds exactly when some positive integer k < n with k!*(n-k) + 1 prime
  satisfies k < sqrt(n)*log(n), and it is stated in this form.
* Real quantities (sqrt, log, exp) are computed in `ℝ` with the natural numbers cast; log is the
  natural logarithm `Real.log`.
-/

namespace OMA.S_oeis_a231631

/-- The conjecture recorded in A231631. -/
theorem main : ∀ n : ℕ, 2 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧
    (k : ℝ) < Real.sqrt n * Real.log n ∧ (Nat.factorial k * (n - k) + 1).Prime := by
  sorry

end OMA.S_oeis_a231631
