import Mathlib

/-!
# A217539: Mathar's recurrence

Source: https://oeis.org/A217539
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A217539 (offset 0): number of Dyck paths of semilength n which satisfy the condition: number of
returns + number of hills < number of peaks;
data 0, 0, 0, 1, 4, 17, 66, 252, 946, 3523, 13054, 48248, ...

Conjecture (R. J. Mathar, Nov 11 2012):
2*(n+1)*(n-3)*a(n) +(-15*n^2+53*n-12)*a(n-1) +(28*n^2-157*n+165)*a(n-2) + 3*(3*n^2+2*n-26)*a(n-3)
-18*(2*n-7)*(n-4)*a(n-4) = 0.

Formalization: the entry gives the formula a(n) = C(n) - (n-1)*M(n-2) - M(n-1) for n > 0, with C(n) the
Catalan numbers and M(n) the Motzkin numbers, and this formula is used as the definition here, together
with the listed term a(0) = 0. S and T are the formal power series over ℚ with S^2 = 1-4*x,
T^2 = 1-2*x-3*x^2 and constant terms 1, that is S = sqrt(1-4x) and T = sqrt(1-2x-3x^2) (the constant
terms select the branches of the square roots); c is the Catalan g.f., determined by 2*x*c = 1 - S, so
C(n) = [x^n] c; and m is the Motzkin g.f., determined by 2*x^2*m = 1 - x - T, so M(n) = [x^n] m.
`main` is stated for every a : ℕ → ℚ with a(0) = 0 and a(n) = C(n) - (n-1)*M(n-2) - M(n-1) for n ≥ 1
(at n = 1 the term (n-1)*M(n-2) has the factor 0; in Lean the index n - 2 is then 0). The recurrence
involves a(n-4), so it is stated for n ≥ 4, with the coefficients expanded; it is checked by the data,
for example at n = 4: (10)*(4) + (-40)*(1) + (-15)*(0) + (90)*(0) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a217539

open PowerSeries

/-- Mathar's conjectured recurrence for A217539, a(n) = C(n) - (n-1)*M(n-2) - M(n-1), for n ≥ 4. -/
theorem main : ∀ S T c m : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    T ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 T = 1 →
    2 * X * c = 1 - S →
    2 * X ^ 2 * m = 1 - X - T →
    ∀ a : ℕ → ℚ, a 0 = 0 →
    (∀ n : ℕ, 1 ≤ n → a n = coeff n c - ((n : ℚ) - 1) * coeff (n - 2) m - coeff (n - 1) m) →
    ∀ n : ℕ, 4 ≤ n →
      (-6 - 4 * (n : ℚ) + 2 * (n : ℚ) ^ 2) * a n + (-12 + 53 * (n : ℚ) - 15 * (n : ℚ) ^ 2) * a (n - 1) +
        (165 - 157 * (n : ℚ) + 28 * (n : ℚ) ^ 2) * a (n - 2) + (-78 + 6 * (n : ℚ) + 9 * (n : ℚ) ^ 2) * a (n - 3) +
        (-504 + 270 * (n : ℚ) - 36 * (n : ℚ) ^ 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a217539
