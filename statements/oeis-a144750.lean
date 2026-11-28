import Mathlib

/-!
# OEIS A144750, pseudo-factorials modulo 9

Sources: https://oeis.org/A144750 and https://oeis.org/A098777
Credit: @caprest

Chai Wah Wu conjectured the recurrence and ordinary generating function in 2018.
The denominator has constant coefficient −1, so multiplying by it gives an
equivalent identity in integer formal power series.
-/

namespace OMA.S_oeis_a144750

/-- Roland Bacher's pseudo-factorials, OEIS A098777. -/
def pseudoFactorial : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1 : ℤ) ^ (n + 1) *
      ∑ k : Fin (n + 1), (n.choose k.val : ℤ) * pseudoFactorial k.val *
        pseudoFactorial (n - k.val)
termination_by n => n
decreasing_by all_goals omega

/-- The representative between 0 and 8, including for negative pseudo-factorials. -/
def a (n : ℕ) : ℤ := pseudoFactorial n % 9

theorem main :
    (∀ n : ℕ, 7 < n →
      a n = a (n - 2) + a (n - 3) - a (n - 5) - a (n - 6) + a (n - 8)) ∧
    (let X : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk a * ((X - 1) * (X + 1) * (X ^ 6 - X ^ 3 + 1)) =
       -8 * X ^ 7 - 4 * X ^ 6 + 3 * X ^ 5 + 8 * X ^ 4 + 7 * X ^ 3 -
         6 * X ^ 2 - 8 * X - 1) := by
  sorry

end OMA.S_oeis_a144750
