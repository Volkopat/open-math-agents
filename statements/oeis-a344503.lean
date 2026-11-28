import Mathlib

/-!
# A344503: Mathar's recurrence

Source: https://oeis.org/A344503
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A344503 (offset 0): a(n) = Sum_{k=0..n} (-1)^(n-k)*binomial(n, k)^2*hypergeom([(k-n)/2, (k-n+1)/2],
[k+2], 4) (the inverse binomial convolution of the Motzkin numbers);
data 1, 0, -1, 3, 0, -5, 15, 0, -28, 84, 0, -165, 495, 0, -1001, 3003, ...

Conjecture (R. J. Mathar, Nov 02 2021): D-finite with recurrence
-18*(2*n+1)*(2*n-1)*(n+1)*a(n) +2*(-36*n^3+554*n^2-1128*n+27)*a(n-1)
+6*(-12*n^3-188*n^2+1235*n-1618)*a(n-2) +9*(54*n^3-27*n^2-183*n+320)*a(n-3)
+54*(n-3)*(9*n^2-125*n+75)*a(n-4) +81*(n-3)*(n-4)*(6*n+127)*a(n-5) = 0.

Formalization: the entry gives the closed forms a(3*n) = binomial(3*n, n),
a(3*n - 1) = -binomial(3*n - 1, n - 1) and a(3*n - 2) = 0, which together give every term of the
sequence; these closed forms are used as the definition here (they reproduce all the listed data).
`main` is stated for every a : ℕ → ℚ with a(3j) = binomial(3j, j), a(3j+1) = 0 and
a(3j+2) = -binomial(3j+2, j) for all j ≥ 0 (the second and third are the entry's formulas with n = j+1).
The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for example at
n = 5: (-10692)*(-5) + (7474)*(0) + (-9858)*(3) + (49320)*(-1) + (-35100)*(0) + (25434)*(1) = 0.
-/

namespace OMA.S_oeis_a344503

/-- Mathar's conjectured recurrence for A344503 (given by its closed forms), for n ≥ 5. -/
theorem main : ∀ a : ℕ → ℚ, (∀ j : ℕ, a (3 * j) = ((3 * j).choose j : ℚ)) →
    (∀ j : ℕ, a (3 * j + 1) = 0) →
    (∀ j : ℕ, a (3 * j + 2) = -((3 * j + 2).choose j : ℚ)) →
    ∀ n : ℕ, 5 ≤ n →
      -18 * (2 * (n : ℚ) + 1) * (2 * (n : ℚ) - 1) * ((n : ℚ) + 1) * a n +
        2 * (-36 * (n : ℚ) ^ 3 + 554 * (n : ℚ) ^ 2 - 1128 * (n : ℚ) + 27) * a (n - 1) +
        6 * (-12 * (n : ℚ) ^ 3 - 188 * (n : ℚ) ^ 2 + 1235 * (n : ℚ) - 1618) * a (n - 2) +
        9 * (54 * (n : ℚ) ^ 3 - 27 * (n : ℚ) ^ 2 - 183 * (n : ℚ) + 320) * a (n - 3) +
        54 * ((n : ℚ) - 3) * (9 * (n : ℚ) ^ 2 - 125 * (n : ℚ) + 75) * a (n - 4) +
        81 * ((n : ℚ) - 3) * ((n : ℚ) - 4) * (6 * (n : ℚ) + 127) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a344503
