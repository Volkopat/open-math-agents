import Mathlib

/-!
# Mathar's recurrence conjecture for OEIS A082143

Source: https://oeis.org/A082143
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A082/A082143.seq
Credit: @sntntHb

OEIS A082143 (offset 0) is the first subdiagonal of the number array A082137, the square
array defined by T(n, k) = (2^(n-1) + 0^n/2)*C(n + k, n). The entry gives
a(n) = (2^(n-1) + 0^n/2)*C(2n+1, n), that is a(n) = T(n, n + 1), with first terms
1, 3, 20, 140, 1008, 7392.

Conjecture (R. J. Mathar, Oct 19 2014, quoted from the entry):
(n+1)*a(n) +4*(-2*n-1)*a(n-1) = 0.
The entry gives no range. At n = 1 the left side is 2*3 - 12*1 = -6, so the recurrence is
stated here for every n >= 2.
-/

namespace OMA.S_oeis_a082143

/-- The square array A082137: T(n, k) = (2^(n-1) + 0^n/2)*C(n + k, n). -/
def T (n k : ℕ) : ℚ :=
  ((2 : ℚ) ^ ((n : ℤ) - 1) + (0 : ℚ) ^ n / 2) * (Nat.choose (n + k) n : ℚ)

/-- OEIS A082143: the first subdiagonal of A082137, a(n) = T(n, n + 1). -/
def a (n : ℕ) : ℚ := T n (n + 1)

/-- Mathar's conjectured recurrence, for every n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℚ) + 1) * a n + 4 * (-2 * (n : ℚ) - 1) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a082143
