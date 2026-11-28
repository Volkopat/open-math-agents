import Mathlib

/-!
# A243255: Mathar's recurrence

Source: https://oeis.org/A243255
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A243255 (offset 0): expansion of 1/2 - (1/2)*(sqrt((2*sqrt(-3*x^2 - 2*x + 1) + 3*x - 2)/x));
data 0, 1, 2, 6, 20, 73, 283, 1149, 4833, 20901, 92406, 415878, ...

Conjecture (R. J. Mathar, Jul 15 2017): D-finite with recurrence
2*n*(2*n+1)*a(n) + (-65*n^2+119*n-42)*a(n-1) + 3*(97*n^2-373*n+342)*a(n-2) -
9*(23*n-68)*(n-3)*a(n-3) - 567*(n-3)*(n-4)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-2*x-3*x^2 and constant term 1; U is the formal
power series with x*U^2 = 2*T + 3*x - 2 and constant term 1, that is U = sqrt((2*sqrt(-3x^2-2x+1) + 3x - 2)/x)
(the constant terms select the branches of the square roots); and G is given by 2*G = 1 - U (its
constant term 0 follows from that of U and is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (72)*(20) + (-606)*(6) + (1206)*(2) + (-216)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a243255

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A243255, for n ≥ 4. -/
theorem main : ∀ T U G : ℚ⟦X⟧, T ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 T = 1 →
    X * U ^ 2 = 2 * T + 3 * X - 2 →
    coeff 0 U = 1 →
    2 * G = 1 - U →
    coeff 0 G = 0 →
    ∀ n : ℕ, 4 ≤ n →
      (2 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (-42 + 119 * (n : ℚ) - 65 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (1026 - 1119 * (n : ℚ) + 291 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-1836 + 1233 * (n : ℚ) - 207 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-6804 + 3969 * (n : ℚ) - 567 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a243255
