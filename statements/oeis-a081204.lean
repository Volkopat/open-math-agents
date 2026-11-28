import Mathlib

/-!
# A081204: staircase on Pascal's triangle

Source: https://oeis.org/A081204 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Arrange Pascal's triangle as a square array; this sequence is a diagonal staircase on it.
We use the formula listed in the entry, `a(n) = binomial(ceiling(n/2) + n, n)`.
Offset `0`, data `1, 2, 3, 10, 15, 56, 84, 330, 495, 2002, ...`.

Conjectures (R. J. Mathar, Nov 07 2014):
1. `4*n*(n+1)*(6*n^2 - 15*n + 8)*a(n) + 6*n*(9*n-7)*a(n-1)
    - 3*(3*n-4)*(3*n-2)*(6*n^2-3*n-1)*a(n-2) = 0`, for `n ≥ 2`;
2. `8*n^2*(n+1)*a(n) - 12*n*(83*n^2 - 313*n + 232)*a(n-1) + 6*(-9*n^3 - 377*n + 384)*a(n-2)
    + 9*(3*n-5)*(83*n-64)*(3*n-7)*a(n-3) = 0`, for `n ≥ 3`
(the indices where all terms are defined). These are known results: `a(n)` is hypergeometric in
`n` along each parity class (`a(2m) = binomial(3m, m)`, `a(2m+1) = binomial(3m+2, m+1)`).
-/

namespace OMA.S_oeis_a081204

/-- A081204: `a(n) = binomial(ceiling(n/2) + n, n)`. -/
def a (n : ℕ) : ℕ := ((n + 1) / 2 + n).choose n

/-- Both conjectured P-recurrences of A081204 (R. J. Mathar). -/
theorem main :
    (∀ n : ℕ, 2 ≤ n →
      4 * (n : ℤ) * (n + 1) * (6 * n ^ 2 - 15 * n + 8) * a n + 6 * (n : ℤ) * (9 * n - 7) * a (n - 1)
        - 3 * (3 * (n : ℤ) - 4) * (3 * n - 2) * (6 * n ^ 2 - 3 * n - 1) * a (n - 2) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      8 * (n : ℤ) ^ 2 * (n + 1) * a n - 12 * (n : ℤ) * (83 * n ^ 2 - 313 * n + 232) * a (n - 1)
        + 6 * (-9 * (n : ℤ) ^ 3 - 377 * n + 384) * a (n - 2)
        + 9 * (3 * (n : ℤ) - 5) * (83 * n - 64) * (3 * n - 7) * a (n - 3) = 0) := by
  sorry

end OMA.S_oeis_a081204
