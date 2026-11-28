import Mathlib

/-!
# A390117: Least integer m > 1 such that m*n + 1 is a prime.

Source: https://oeis.org/A390117
Credit: @azmiozgen

Conjecture (from the entry):
(i) a(n) <= 2*sqrt(n+6) for all n > 0.
(ii) For any n > 0, there is a positive integer m <= 2*sqrt(n+3) such that m*n - 1 is prime.

Formalization notes:
* a(n) = the least m > 1 with m*n + 1 prime (such m exists for n ≥ 1 by Dirichlet's theorem).
* Both parts are stated, with the square roots in ℝ.
* Controls (computed): a(1..33) = 2, 2, 2, 3, 2, 2, 4, 2, 2, 3, 2, 3, 4, 2, 2, 6, 6, 2, 10, 2, 2,
  3, 2, 3, 4, 2, 4, 4, 2, 2, 10, 3, 2, as in the entry; (i) holds for n < 20000.
-/

namespace OMA.S_oeis_a390117

/-- A390117(n): the least `m > 1` with `m * n + 1` prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 < m ∧ (m * n + 1).Prime}

/-- Both parts of the conjecture. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℝ) ≤ 2 * Real.sqrt (n + 6)) ∧
      ∀ n : ℕ, 0 < n →
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ 2 * Real.sqrt (n + 3) ∧ (m * n - 1).Prime := by
  sorry

end OMA.S_oeis_a390117
