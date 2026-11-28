import Mathlib

/-!
# A116363: dot product of row n of the Catalan triangle A033184 with row n of Pascal's triangle

Source: https://oeis.org/A116363 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Offset `0`, data `1, 2, 7, 30, 141, 698, 3571, ...`. We use the formula listed in the entry,
`a(n) = Sum_{k=0..n} C(n,k)*C(2*n-k+1,n-k)*(k+1)/(2*n-k+1)`, where
`C(2n-k+1, n-k)*(k+1)/(2n-k+1)` is entry `(n, k)` of the Catalan triangle A033184 (rows
`1; 1, 1; 2, 2, 1; 5, 5, 3, 1; ...`), computed in `ℚ`.

Conjecture (R. J. Mathar, Jun 22 2016):
`+(2*n+5)*(n+1)*a(n) +4*(-3*n^2-9*n+5)*a(n-1) +(2*n+7)*(n-1)*a(n-2)=0`, for `n ≥ 2`
(the indices where `a(n-2)` is defined).
-/

namespace OMA.S_oeis_a116363

/-- Entry `(n, k)` of the Catalan triangle A033184, `0 ≤ k ≤ n`: `C(2n-k+1, n-k)*(k+1)/(2n-k+1)`. -/
def catTri (n k : ℕ) : ℚ :=
  ((2 * n - k + 1).choose (n - k) : ℚ) * ((k : ℚ) + 1) / ((2 * n - k + 1 : ℕ) : ℚ)

/-- A116363: `a(n) = ∑_{k=0..n} C(n,k) * A033184(n,k)`. -/
def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * catTri n k

/-- Conjecture (R. J. Mathar): the order-2 P-recurrence of A116363, for `n ≥ 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (2 * (n : ℚ) + 5) * ((n : ℚ) + 1) * a n
      + 4 * (-3 * (n : ℚ) ^ 2 - 9 * (n : ℚ) + 5) * a (n - 1)
      + (2 * (n : ℚ) + 7) * ((n : ℚ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a116363
