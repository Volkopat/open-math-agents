import Mathlib

/-!
# Mathar's recurrence for OEIS A345651

A345651 is the fourth column of A008296, the triangle of Lehmer-Comtet numbers of the first kind,
whose column k has exponential generating function ((1 + x) log(1 + x))^k / k!.
So a(n) = n! [x^n] ((1 + x) log(1 + x))^4 / 4!, with offset 4 (a(4) = 1).
R. J. Mathar conjectured on September 15, 2021 that the sequence is D-finite with recurrence
a(n) + 2(2n-13) a(n-1) + (6n^2-84n+295) a(n-2) + (2n-15)(2n^2-30n+113) a(n-3) + (n-8)^4 a(n-4) = 0.
The entry does not give a range. It is stated here for n ≥ 9: at n = 8 the left side is 24 even
from the listed terms a(4), ..., a(8) alone, and n = 9 is the first n ≥ 4 at which it holds.

Source: https://oeis.org/A345651
Credit: @jes5199
-/

namespace OMA.S_oeis_a345651

open PowerSeries

/-- The exponential generating function of column 4 of A008296, times 4!. -/
noncomputable def egf : PowerSeries ℚ := ((1 + X) * log ℚ) ^ 4

noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) / (Nat.factorial 4 : ℚ) * coeff n egf

theorem main : ∀ n : ℕ, 9 ≤ n →
    a n + 2 * (2 * n - 13 : ℚ) * a (n - 1) + (6 * n ^ 2 - 84 * n + 295 : ℚ) * a (n - 2) +
      (2 * n - 15 : ℚ) * (2 * n ^ 2 - 30 * n + 113 : ℚ) * a (n - 3) +
      ((n : ℚ) - 8) ^ 4 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a345651
