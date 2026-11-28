import Mathlib

/-!
# A026026: Mathar's recurrence

Source: https://oeis.org/A026026
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A026026 (offset 2): a(n) = number of (s(0), s(1), ..., s(2*n-1)) such that s(i) is a nonnegative
integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n, s(0) = 3, s(2*n-1) = 4. Also a(n) = T(2*n-1,n-1),
where T is defined in A026022;
data 1, 3, 10, 35, 125, 451, 1638, 5980, 21930, 80750, 298452, 1106921, ...

Conjecture (R. J. Mathar, Jun 22 2013):
-(n+3)*(11*n-38)*a(n) +2*(35*n^2-86*n-102)*a(n-1) -4*(13*n-30)*(2*n-5)*a(n-2) = 0.

Formalization: the entry records the g.f. as the expansion of x^2*(1+x^2*C^4)*C^3, where
C = (1-(1-4*x)^(1/2))/(2*x) is the g.f. for the Catalan numbers, and this is used as the definition
here. S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G = x^2*(1 + x^2*c^4)*c^3;
a(n) = [x^n] G. The sequence has offset 2, and [x^k] G = 0 for k < 2. The recurrence involves a(n-2); with
a(k) read as [x^k] G (so a(k) = 0 below the offset) it holds for n ≥ 3, and `main` is stated
for this range, which contains every n ≥ 4 (where all indices are at least the offset).
It is checked by the data, for example at n = 3:
(30)*(3) + (-90)*(1) + (-36)*(0) = 0.
-/

namespace OMA.S_oeis_a026026

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A026026, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G = X ^ 2 * (1 + X ^ 2 * c ^ 4) * c ^ 3 →
    ∀ n : ℕ, 3 ≤ n →
      (114 + 5 * (n : ℚ) - 11 * (n : ℚ) ^ 2) * coeff n G + (-204 - 172 * (n : ℚ) + 70 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-600 + 500 * (n : ℚ) - 104 * (n : ℚ) ^ 2) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a026026
