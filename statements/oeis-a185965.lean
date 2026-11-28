import Mathlib

/-!
# A185965: central coefficients of the number triangle A185962

Source: https://oeis.org/A185965 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

A185962 is the Riordan array `((1-x)^2/(1-x+x^2), x(1-x)^2/(1-x+x^2))`: with
`g(x) = (1-x)^2/(1-x+x^2)`, column `k` has generating function `g(x) * (x g(x))^k`, so
`T(n,k) = [x^n] g(x) (x g(x))^k`. The sequence is `a(n) = T(2n, n)`.
Offset `0`, data `1, -2, 0, 8, -10, -30, 98, 40, -648, 680, ...`.

Conjectures (R. J. Mathar, Dec 03 2014):
1. `15*n*(n-1)*a(n) +10*(2*n-1)*(n-1)*a(n-1) +(109*n^2-263*n+180)*a(n-2)
    +4*(-2*n^2-10*n+57)*a(n-3) +60*(n-4)^2*a(n-4) -6*(2*n-7)*(n-5)*a(n-5) = 0`, for `n ≥ 5`;
2. `3*n*(n-1)*(57*n-136)*a(n) +(n-1)*(171*n^2-415*n+14)*a(n-1)
    +2*(532*n^3-2281*n^2+2755*n-840)*a(n-2) -2*(n-3)*(304*n^2-835*n+216)*a(n-3)
    +2*(19*n-5)*(n-4)*(2*n-5)*a(n-4) = 0`, for `n ≥ 4`
(the indices where all terms are defined). Computed in `ℚ`.
-/

namespace OMA.S_oeis_a185965

open PowerSeries

/-- `g(x) = (1-x)^2/(1-x+x^2)`. -/
noncomputable def g : PowerSeries ℚ := (1 - X) ^ 2 * (1 - X + X ^ 2)⁻¹

/-- The Riordan array A185962: `T(n,k) = [x^n] g(x) (x g(x))^k`. -/
noncomputable def T (n k : ℕ) : ℚ := coeff n (g * (X * g) ^ k)

/-- A185965: `a(n) = T(2n, n)`. -/
noncomputable def a (n : ℕ) : ℚ := T (2 * n) n

/-- Both conjectured P-recurrences of A185965 (R. J. Mathar). -/
theorem main :
    (∀ n : ℕ, 5 ≤ n →
      15 * (n : ℚ) * (n - 1) * a n + 10 * (2 * (n : ℚ) - 1) * (n - 1) * a (n - 1)
        + (109 * (n : ℚ) ^ 2 - 263 * n + 180) * a (n - 2)
        + 4 * (-2 * (n : ℚ) ^ 2 - 10 * n + 57) * a (n - 3)
        + 60 * ((n : ℚ) - 4) ^ 2 * a (n - 4) - 6 * (2 * (n : ℚ) - 7) * (n - 5) * a (n - 5) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      3 * (n : ℚ) * (n - 1) * (57 * n - 136) * a n
        + ((n : ℚ) - 1) * (171 * n ^ 2 - 415 * n + 14) * a (n - 1)
        + 2 * (532 * (n : ℚ) ^ 3 - 2281 * n ^ 2 + 2755 * n - 840) * a (n - 2)
        - 2 * ((n : ℚ) - 3) * (304 * n ^ 2 - 835 * n + 216) * a (n - 3)
        + 2 * (19 * (n : ℚ) - 5) * (n - 4) * (2 * n - 5) * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a185965
