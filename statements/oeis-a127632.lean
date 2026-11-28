import Mathlib

/-!
# A127632: Mathar's recurrence

Source: https://oeis.org/A127632
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A127632 (offset 0): expansion of c(x*c(x)), where c(x) is the g.f. for A000108;
data 1, 1, 3, 11, 44, 185, 804, 3579, 16229, 74690, 347984, 1638169, ...

Conjecture (R. J. Mathar, May 04 2018):
3*n*(n-1)*(4*n-9)*(n+1)*a(n) - 8*n*(n-1)*(20*n^2-67*n+48)*a(n-1) +
8*(4*n-5)*(n-1)*(22*n^2-94*n+99)*a(n-2) - 8*(4*n-11)*(4*n-5)*(4*n-9)*(2*n-5)*a(n-3) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; U is the Catalan g.f.
c(x), determined by 2*x*U = 1 - T; V is the formal power series with V^2 = 1 - 4*x*U and constant term
1, that is V = sqrt(1 - 4*x*c(x)) (the constant terms select the branches of the square roots); and
G = c(x*c(x)) is determined by G*(2*x*U) = 1 - V (its constant term is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (216)*(11) + (-1296)*(3) + (1680)*(1) + (-168)*(1) = 0.
-/

namespace OMA.S_oeis_a127632

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A127632, for n ≥ 3. -/
theorem main : ∀ T U V G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    2 * X * U = 1 - T →
    V ^ 2 = 1 - 4 * X * U →
    coeff 0 V = 1 →
    G * (2 * X * U) = 1 - V →
    coeff 0 G = 1 →
    ∀ n : ℕ, 3 ≤ n →
      (27 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 27 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 4) * coeff n G + (384 * (n : ℚ) - 920 * (n : ℚ) ^ 2 + 696 * (n : ℚ) ^ 3 - 160 * (n : ℚ) ^ 4) * coeff (n - 1) G +
        (3960 - 10888 * (n : ℚ) + 10816 * (n : ℚ) ^ 2 - 4592 * (n : ℚ) ^ 3 + 704 * (n : ℚ) ^ 4) * coeff (n - 2) G + (-19800 + 39760 * (n : ℚ) - 28736 * (n : ℚ) ^ 2 + 8960 * (n : ℚ) ^ 3 - 1024 * (n : ℚ) ^ 4) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a127632
