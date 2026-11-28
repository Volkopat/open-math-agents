import Mathlib

/-!
# A049982: Number of strictly increasing arithmetic progressions of >= 2 positive integers with sum n

Source: https://oeis.org/A049982
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
For every positive integer n,
  a(n) = Sum_{m | n, m odd > 1} floor(2 * (n - m) / (m * (m - 1)))
       + Sum_{m | n} floor((n - m * (5 - (-1)^(n/m)) / 2 + m^2 * (1 - (-1)^(n/m))) / (2 * m * (2 * m - 1))).

Conventions:
A strictly increasing arithmetic progression of k >= 2 positive integers with sum n is
determined by (a, d, k) with a >= 1, d >= 1, k >= 2, and 2 * k * a + d * k * (k - 1) = 2 * n.
-/

namespace OMA.S_oeis_a049982

/-- Number of strictly increasing arithmetic progressions of >= 2 positive integers with sum n. -/
noncomputable def a (n : ℕ) : ℕ :=
  {t : ℕ × ℕ × ℕ | 1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧
    2 * t.2.2 * t.1 + t.2.1 * t.2.2 * (t.2.2 - 1) = 2 * n}.ncard

/-- Conjectured divisor-sum formula for A049982. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) =
        (∑ m ∈ n.divisors.filter (fun m => Odd m ∧ 1 < m),
          Int.floor ((2 * ((n : ℚ) - (m : ℚ))) / ((m : ℚ) * ((m : ℚ) - 1)))) +
        (∑ m ∈ n.divisors,
          Int.floor
            (((n : ℚ) - (m : ℚ) * (5 - (-1 : ℚ) ^ (n / m)) / 2 +
              (m : ℚ) ^ 2 * (1 - (-1 : ℚ) ^ (n / m))) /
              (2 * (m : ℚ) * (2 * (m : ℚ) - 1)))) := by
  sorry

end OMA.S_oeis_a049982
