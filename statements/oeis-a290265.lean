import Mathlib

/-!
# A290265: Mathar's recurrence

Source: https://oeis.org/A290265
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A290265 (offset 0): the number of non-palindromic Motzkin paths of length n;
data 0, 0, 0, 2, 4, 16, 38, 114, 288, 800, 2092, 5702, ...

Conjecture (in the formula section of the entry, unsigned; the author of the entry is R. J. Mathar,
Jul 25 2017):
-(16*n-47)*(n+2)*(n+1)*a(n) -(n+1)*(9*n^2-167*n+188)*a(n-1) +n*(139*n^2-450*n+59)*a(n-2)
+(n-1)*(187*n^2-1619*n+2250)*a(n-3) -(n-2)*(97*n^2+346*n-2255)*a(n-4)
+(-311*n^3+2398*n^2-5779*n+4112)*a(n-5) +3*(-153*n^3+1458*n^2-4361*n+4348)*a(n-6)
-3*(n-6)*(169*n^2-1152*n+1799)*a(n-7) -9*(n-6)*(n-7)*(23*n-82)*a(n-8) = 0.

Formalization: the entry gives the formula a(n) = A001006(n) - A005773(1+floor(n/2)), and this formula
is used as the definition here. T is the formal power series over ℚ with T^2 = 1-2*x-3*x^2 and
constant term 1, that is T = sqrt(1-2x-3x^2) (the constant term selects the branch of the square
root); m is the g.f. of the Motzkin numbers A001006, determined by 2*x^2*m = 1 - x - T; and B is the
g.f. of A005773 (offset 0: 1, 1, 2, 5, 13, 35, ...), which is 1/2+(1/2)*((1+x)/(1-3*x))^(1/2) in that
entry, that is 1/2 + T/(2*(1-3*x)); it is determined by 2*(1-3*x)*B = 1 - 3*x + T. `main` is stated
for every a : ℕ → ℚ with a(n) = [x^n] m - [x^(1+floor(n/2))] B for all n (`n / 2` is the floor
division of natural numbers). The recurrence involves a(n-8), so it is stated for n ≥ 8, with the
coefficients expanded; it is checked by the data, for example at n = 8:
(-7290)*(288) + (5148)*(114) + (42840)*(38) + (8862)*(16) + (-40326)*(4) + (-47880)*(2)
+ (-46692)*(0) + (-20394)*(0) + (-1836)*(0) = 0.
-/

namespace OMA.S_oeis_a290265

open PowerSeries

/-- Mathar's conjectured recurrence for A290265, a(n) = A001006(n) - A005773(1+floor(n/2)),
for n ≥ 8. -/
theorem main : ∀ T m B : ℚ⟦X⟧, T ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 T = 1 →
    2 * X ^ 2 * m = 1 - X - T →
    2 * (1 - 3 * X) * B = 1 - 3 * X + T →
    ∀ a : ℕ → ℚ, (∀ n : ℕ, a n = coeff n m - coeff (1 + n / 2) B) →
    ∀ n : ℕ, 8 ≤ n →
      (94 + 109 * (n : ℚ) - (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3) * a n + (-188 - 21 * (n : ℚ) + 158 * (n : ℚ) ^ 2 - 9 * (n : ℚ) ^ 3) * a (n - 1) +
        (59 * (n : ℚ) - 450 * (n : ℚ) ^ 2 + 139 * (n : ℚ) ^ 3) * a (n - 2) + (-2250 + 3869 * (n : ℚ) - 1806 * (n : ℚ) ^ 2 + 187 * (n : ℚ) ^ 3) * a (n - 3) +
        (-4510 + 2947 * (n : ℚ) - 152 * (n : ℚ) ^ 2 - 97 * (n : ℚ) ^ 3) * a (n - 4) + (4112 - 5779 * (n : ℚ) + 2398 * (n : ℚ) ^ 2 - 311 * (n : ℚ) ^ 3) * a (n - 5) +
        (13044 - 13083 * (n : ℚ) + 4374 * (n : ℚ) ^ 2 - 459 * (n : ℚ) ^ 3) * a (n - 6) + (32382 - 26133 * (n : ℚ) + 6498 * (n : ℚ) ^ 2 - 507 * (n : ℚ) ^ 3) * a (n - 7) +
        (30996 - 18288 * (n : ℚ) + 3429 * (n : ℚ) ^ 2 - 207 * (n : ℚ) ^ 3) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a290265
