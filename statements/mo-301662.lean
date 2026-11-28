import Mathlib

/-!
# Are all the numbers `π(n²)/n²` (`n = 1, 2, 3, …`) pairwise distinct?

Source: https://mathoverflow.net/questions/301662 (Zhi-Wei Sun, CC BY-SA 4.0).

For `x > 0` let `π(x)` be the number of primes not exceeding `x`. Question: are all the numbers
`π(n²)/n²` (`n = 1, 2, 3, …`) pairwise distinct? The asker conjectured (2015) that the answer is
yes; computations further suggest that `π(n²)/n²` is strictly decreasing from `n = 15647` on
(that stronger claim, and the analogues for `π(n^k)/n^k`, are not stated here). The one answer
on the page is explicitly partial.

We state the affirmative answer.

Formalization notes:
* `π(x)` is Mathlib's `Nat.primeCounting x`, the number of primes `≤ x`.
* The ratios are compared in `ℚ`; pairwise distinctness over `n ≥ 1` is stated as injectivity.
* Checked numerically: the ratios are pairwise distinct for `1 ≤ n < 540`.
-/

namespace OMA.S_mo_301662

/-- The numbers `π(n²)/n²`, `n ≥ 1`, are pairwise distinct. -/
theorem main : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    (Nat.primeCounting (m ^ 2) : ℚ) / (m ^ 2 : ℚ) = (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ) →
      m = n := by
  sorry

end OMA.S_mo_301662
