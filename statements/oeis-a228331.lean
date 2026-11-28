import Mathlib

/-!
# A228331: `Sum_{k=0..n} (k+1)^5 * T(n,k)^2`, `T` the Catalan triangle A039598

Source: https://oeis.org/A228331 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Let `h(m)` denote the sequence whose `n`-th term is `Sum_{k=0..n} (k+1)^m * T(n,k)^2`, where
`T(n,k)` is the Catalan triangle A039598. A228331 is `h(5)`.
Offset `0`, data `1, 36, 780, 16240, 321300, 6131664, ...`.
We use the formula listed in A039598, `T(n,k) = C(2n+1, n-k) * 2*(k+1)/(n+k+2)` for
`0 ≤ k ≤ n` (rows `1; 2, 1; 5, 4, 1; 14, 14, 6, 1; ...`), computed in `ℚ`.

Conjecture (R. J. Mathar, Sep 08 2013):
`n^2*a(n) + 4*(2*n^2-22*n+11)*a(n-1) + 16*(-7*n^2-54*n+166)*a(n-2)
 - 1088*(2*n-3)*(2*n-7)*a(n-3) = 0`, for `n ≥ 3` (the indices where `a(n-3)` is defined).
This is a known result: it follows from the closed form
`a(n) = binomial(2n,n)^2 * (2n+1)*(3n^2+n-1)/(2n-1)` (V. Kotesovec, Dec 08 2013).
-/

namespace OMA.S_oeis_a228331

/-- Entry `(n, k)` of the Catalan triangle A039598, `0 ≤ k ≤ n`:
`C(2n+1, n-k) * 2*(k+1)/(n+k+2)`. -/
def T (n k : ℕ) : ℚ :=
  ((2 * n + 1).choose (n - k) : ℚ) * (2 * ((k : ℚ) + 1)) / ((n : ℚ) + k + 2)

/-- `h(m)(n) = ∑_{k=0..n} (k+1)^m * T(n,k)^2`. -/
def h (m n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), ((k : ℚ) + 1) ^ m * T n k ^ 2

/-- A228331 is `h(5)`. -/
def a (n : ℕ) : ℚ := h 5 n

/-- Conjecture (R. J. Mathar): the order-3 P-recurrence of A228331, for `n ≥ 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      (n : ℚ) ^ 2 * a n + 4 * (2 * (n : ℚ) ^ 2 - 22 * n + 11) * a (n - 1)
        + 16 * (-7 * (n : ℚ) ^ 2 - 54 * n + 166) * a (n - 2)
        - 1088 * (2 * (n : ℚ) - 3) * (2 * (n : ℚ) - 7) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a228331
