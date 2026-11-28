import Mathlib

/-!
# A240722: Mathar's recurrence

Source: https://oeis.org/A240722
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A240722 (offset 0): expansion of log'((-1-sqrt(1-8*x)+sqrt(2+2*sqrt(1-8*x)+8*x))/(4*x));
data 1, 7, 46, 323, 2326, 17062, 126764, 950819, 7184422, 54604082, 416990564, 3197008718, ...

Conjecture (R. J. Mathar, Jun 14 2016):
-(3*n-1)*(2*n+1)*(n+1)*a(n) +2*(21*n^3+14*n^2-2*n-1)*a(n-1) +8*n*(3*n+2)*(2*n-1)*a(n-2) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-8*x and constant term 1; W is the formal power
series with W^2 = 2 + 2*T + 8*x and constant term 2, that is W = sqrt(2 + 2*sqrt(1-8x) + 8x) (the
constant terms select the branches of the square roots); F is determined by 4*x*F = -1 - T + W; and
G = F'/F, the logarithmic derivative of F, is determined by G*F = F' (F = 1 + x + ... has constant term 1, so
this relation forces G(0) = F'(0)/F(0) = 1; that value is recorded as an explicit, redundant hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (-75)*(46) + (438)*(7) + (384)*(1) = 0.
-/

namespace OMA.S_oeis_a240722

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A240722, for n ≥ 2. -/
theorem main : ∀ T W F G : ℚ⟦X⟧, T ^ 2 = 1 - 8 * X →
    coeff 0 T = 1 →
    W ^ 2 = 2 + 2 * T + 8 * X →
    coeff 0 W = 2 →
    4 * X * F = -1 - T + W →
    G * F = derivative ℚ F →
    coeff 0 G = 1 →
    ∀ n : ℕ, 2 ≤ n →
      (1 - 7 * (n : ℚ) ^ 2 - 6 * (n : ℚ) ^ 3) * coeff n G + (-2 - 4 * (n : ℚ) + 28 * (n : ℚ) ^ 2 + 42 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-16 * (n : ℚ) + 8 * (n : ℚ) ^ 2 + 48 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a240722
