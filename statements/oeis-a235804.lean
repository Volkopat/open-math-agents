import Mathlib

/-!
# A235804: the generating functions of the rows and columns of the array n - 2 + k*2^(n-3)

Source: https://oeis.org/A235804
Credit: @ivillar

A235804 is the rectangular array A(n,k) = n - 2 + k*2^(n-3), with row index n ≥ 3 and column
index k ≥ 0, read by upward antidiagonals; data 1, 2, 2, 3, 4, 3, 4, 7, 6, 4, ...

Conjectures (in the comments of A235804):
* the g.f. for row n is F_n(x) = ((n-2) + (2^(n-3) - (n-2))*x)/(1-x)^2, n ≥ 3;
* the g.f. for column k is G_k(x) = (k+1 - 2*(k+1)*x + k*x^2)/((1-2*x)*(1-x)^2), k ≥ 0.

Formalization: generating functions are formal power series over ℤ, and each identity is stated
with the denominator cleared. Row n is the series Sum_{k ≥ 0} A(n,k) x^k. Column k starts at
row 3, so its series is Sum_{m ≥ 0} A(m+3,k) x^m (first terms k+1, 2k+2, 4k+3, as in G_k).
-/

namespace OMA.S_oeis_a235804

open PowerSeries

/-- A(n,k) = n - 2 + k * 2^(n-3), for n ≥ 3 and k ≥ 0. -/
def A (n k : ℕ) : ℤ := (n : ℤ) - 2 + (k : ℤ) * 2 ^ (n - 3)

/-- The conjectured row and column generating functions. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n →
      PowerSeries.mk (fun k => A n k) * (1 - X) ^ 2 =
        C ((n : ℤ) - 2) + C (2 ^ (n - 3) - ((n : ℤ) - 2)) * X) ∧
    (∀ k : ℕ,
      PowerSeries.mk (fun m => A (m + 3) k) * ((1 - 2 * X) * (1 - X) ^ 2) =
        C ((k : ℤ) + 1) - C (2 * ((k : ℤ) + 1)) * X + C (k : ℤ) * X ^ 2) := by
  sorry

end OMA.S_oeis_a235804
