import Mathlib

/-!
# A159864: Difference array of Fibonacci numbers A000045 read by antidiagonals.

Source: https://oeis.org/A159864

Conventions: `D j i` is the `j`-th forward difference of the Fibonacci numbers at `i`
(`D 0 i = F(i)`, `D (j+1) i = D j (i+1) - D j i`), computed in ℤ. Row `n` of the triangle
(the `n`-th antidiagonal) is `T(n,k) = D k (n-k)` for `k = 0..n`; this reproduces the data
0; 1, 1; 1, 0, -1; 2, 1, 1, 2; 3, 1, 0, -1, -3; ...
A025169(n) = 2 * Fibonacci(2n+2).

Formalizes the conjecture of R. J. Mathar (May 29 2009, upper limits corrected Nov 24 2026):
Sum_{k=0..2n} T(2n,k) = 0 and Sum_{k=0..2n+1} T(2n+1,k) = A025169(n).
-/

namespace OMA.S_oeis_a159864

/-- `D j i`: the `j`-th forward difference of the Fibonacci sequence, evaluated at `i`. -/
def D : ℕ → ℕ → ℤ
  | 0, i => (Nat.fib i : ℤ)
  | j + 1, i => D j (i + 1) - D j i

/-- The triangle A159864: `T n k = D k (n - k)` (row `n`, `0 ≤ k ≤ n`). -/
def T (n k : ℕ) : ℤ := D k (n - k)

/-- Mathar's conjecture on the row sums of A159864. -/
theorem main : ∀ n : ℕ,
    (∑ k ∈ Finset.range (2 * n + 1), T (2 * n) k = 0) ∧
    (∑ k ∈ Finset.range (2 * n + 2), T (2 * n + 1) k = 2 * (Nat.fib (2 * n + 2) : ℤ)) := by
  sorry

end OMA.S_oeis_a159864
