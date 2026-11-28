import Mathlib

/-!
# A103995: First column of triangle A103910.

Source: https://oeis.org/A103995
Credit: @agchua

Ralf Stephan, in the formula section of A103995:
  Recurrence: a(n) = -Sum[i=1..n-1, a(i)*A010048(n-1, i-1) ] (conjectured).

A010048 (offset 0) is the triangle of Fibonomial coefficients
((n, k)) = (F(n)*F(n-1)*...*F(n-k+1))/(F(k)*F(k-1)*...*F(1)) for 0 <= k <= n, F = A000045;
equivalently P(n)/(P(k)*P(n-k)) with P(n) = F(1)*F(2)*...*F(n) (P. Bala's form in A010048).
Below this is `fibonomial n k`, and it is 0 for k > n (the triangle is lower triangular).

A103910 is the triangle inverse to A010048, read with row and column indices from 0. Since A010048
is lower triangular with ones on its diagonal, its inverse is the unique lower triangular array
`T : ℕ → ℕ → ℚ` with F*T = I and T*F = I; the theorem is stated for every such `T` (the products
are finite sums because both arrays are lower triangular). A103995 (offset 1) is its first
column, a(n) = T(n-1, 0), with data 1, -1, 0, 1, -1, -6, 35, 181, -6056, ...

At n = 1 the sum is empty while a(1) = 1, so the recurrence is stated for n >= 2, with a(1) = 1
as its initial value.
-/

namespace OMA.S_oeis_a103995

/-- P(n) = F(1)*F(2)*...*F(n), the product of the first n Fibonacci numbers. -/
def fibFact (n : ℕ) : ℚ := ∏ j ∈ Finset.Icc 1 n, (Nat.fib j : ℚ)

/-- A010048(n,k), the Fibonomial coefficient P(n)/(P(k)*P(n-k)) for k ≤ n, and 0 for k > n. -/
def fibonomial (n k : ℕ) : ℚ := if k ≤ n then fibFact n / (fibFact k * fibFact (n - k)) else 0

/-- A103995(n) = T(n-1, 0) for the inverse triangle `T` (offset 1). -/
def a (T : ℕ → ℕ → ℚ) (n : ℕ) : ℚ := T (n - 1) 0

/-- Stephan's conjectured recurrence, for every inverse `T` of the Fibonomial triangle. -/
theorem main : ∀ T : ℕ → ℕ → ℚ,
    (∀ n m : ℕ, n < m → T n m = 0) →
    (∀ n m : ℕ, ∑ k ∈ Finset.range (n + 1), fibonomial n k * T k m = if n = m then 1 else 0) →
    (∀ n m : ℕ, ∑ k ∈ Finset.range (n + 1), T n k * fibonomial k m = if n = m then 1 else 0) →
    ∀ n : ℕ, 2 ≤ n →
      a T n = -∑ i ∈ Finset.Icc 1 (n - 1), a T i * fibonomial (n - 1) (i - 1) := by
  sorry

end OMA.S_oeis_a103995
