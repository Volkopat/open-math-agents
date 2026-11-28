import Mathlib

/-!
# A187035: Diagonal sums of number triangle A187034.

Source: https://oeis.org/A187035
Credit: @ShoQo

Conjecture (R. J. Mathar, Jun 30 2011): g.f. 1/( (1-x)*(1-x+x^2)*(1+x)^2 ) with
a(n) = +a(n-2) -a(n-3) +a(n-5). (Charles R Greathouse IV, Dec 28 2011: "The above conjecture
is correct.")

Formalization notes:
* A187034 is the triangle T(n,k) = (-1)^(n-k) if binomial(k, n-k) > 0, 0 otherwise, with
  0 <= k <= n; `T m k` is 0 outside the triangle (k > m).
* Diagonal sums (offset 0): a(n) = Sum_k T(n-k, k); terms with k > n - k vanish.
  Data: 1, 0, 1, -1, 1, -1, 2, -1, 2, -2, ...
* The g.f. claim is stated as an identity of formal power series over `ℤ`:
  (Sum a(n) x^n) * ((1-x)(1-x+x^2)(1+x)^2) = 1. The recurrence is stated for n >= 5.
-/

namespace OMA.S_oeis_a187035

open PowerSeries

/-- The triangle A187034: T(m,k) = (-1)^(m-k) if 0 <= k <= m and binomial(k, m-k) > 0. -/
def T (m k : ℕ) : ℤ := if k ≤ m ∧ 0 < Nat.choose k (m - k) then (-1) ^ (m - k) else 0

/-- a(n): the n-th diagonal sum of A187034. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T (n - k) k

theorem main :
    (∀ n : ℕ, 5 ≤ n → a n = a (n - 2) - a (n - 3) + a (n - 5)) ∧
    PowerSeries.mk a * ((1 - X) * (1 - X + X ^ 2) * (1 + X) ^ 2) = 1 := by
  sorry

end OMA.S_oeis_a187035
