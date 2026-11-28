import Mathlib

/-!
# A089073: Mathar's recurrence

Source: https://oeis.org/A089073
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A089073 (offset 1): number of symmetric non-crossing connected graphs on n equidistant nodes on a circle;
data 1, 1, 2, 5, 10, 32, 64, 231, 462, 1792, 3584, 14586, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
n*(n+2)*(23*n^2-162*n+199) *a(n) +12*(27*n^2-47*n-10) *a(n-1) +24*(-27*n^2+47*n+10) *a(n-2)
+48 *(27*n^2-47*n-10) *a(n-3) -12*(3*n-13)*(3*n-5)*(23*n^2-116*n+60) *a(n-4) = 0.

Formalization: the entry gives a(2k) = (1/2)*A078531(k), a(2k+1) = A078531(k), where A078531 is, by its title, the sequence of
coefficients of the power series B with B(x)^2 - 4*x*B(x)^3 = 1, B(0) = 1; these formulas are used as the
definition here. Hence Sum_{n>=1} a(n)*x^n = (1/2 + x)*B(x^2) - 1/2. T is the formal power series over ℚ
with T^2 - 4*x^2*T^3 = 1 and constant term 1; this equation has exactly one power series solution with
constant term 1, and B(x^2) satisfies it, so T = B(x^2). The g.f. G of the sequence is determined by
2*G = (1 + 2*x)*T - 1 (its constant term is 0, the coefficient 1/2 of x^0 in (1/2 + x)*B(x^2) not being a
term of the sequence);
a(n) = [x^n] G. The sequence has offset 1 and the recurrence involves a(n-4), so it is stated for n ≥ 5,
where every index is at least the offset; it is checked by the data, for example at n = 5:
(-1260)*(10) + (5160)*(5) + (-10320)*(2) + (20640)*(1) + (-13200)*(1) = 0.
-/

namespace OMA.S_oeis_a089073

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A089073, for n ≥ 5. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 - 4 * X ^ 2 * T ^ 3 = 1 →
    coeff 0 T = 1 →
    2 * G = (1 + 2 * X) * T - 1 →
    ∀ n : ℕ, 5 ≤ n →
      (398 * (n : ℚ) - 125 * (n : ℚ) ^ 2 - 116 * (n : ℚ) ^ 3 + 23 * (n : ℚ) ^ 4) * coeff n G + (-120 - 564 * (n : ℚ) + 324 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (240 + 1128 * (n : ℚ) - 648 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-480 - 2256 * (n : ℚ) + 1296 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-46800 + 129360 * (n : ℚ) - 99588 * (n : ℚ) ^ 2 + 27432 * (n : ℚ) ^ 3 - 2484 * (n : ℚ) ^ 4) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a089073
