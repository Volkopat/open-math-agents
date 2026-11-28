import Mathlib

/-!
# A110034: Row sums of a characteristic triangle for the Fibonacci numbers.

Source: https://oeis.org/A110034 (the triangle: https://oeis.org/A110033,
A061646: https://oeis.org/A061646)
Credit: @agchua

J. M. Bergot (Jun 10 2013), comment line of A110034, quoted verbatim:
  Conjecture: |a(n)| = Sum_{k=1..n-1} A061646(k).

Definitions.
* A110033 (offset 0), from its formula line: form the n X n Hankel matrices F(i+j-1),
  1 <= i, j <= n, for the Fibonacci numbers and take their characteristic polynomials; row n of
  the triangle gives the coefficients. Below `H n` is that matrix with 0-based indices
  (entry (i, j) is F(i + j + 1), F = Nat.fib = A000045), and T(n, k) is the coefficient of x^k in
  its characteristic polynomial det(x*I - H(n)) (Mathlib's Matrix.charpoly), k = 0..n. This
  matches the listed rows: 1; -1, 1; 1, -3, 1; 0, 3, -8, 1; 0, 0, 9, -21, 1; ...
* A110034 (offset 0): a(n) = Sum_{k=0..n} T(n, k), the row sums of A110033.
* A061646 (offset -1), from its name line: a(n) = 2*a(n-1) + 2*a(n-2) - a(n-3) with
  a(-1) = 1, a(0) = 1, a(1) = 1. Below B(k) = A061646(k - 1), so A061646(k) = B(k + 1).
Range: the conjecture is stated for n >= 1. For n = 0 the sum Sum_{k=1..-1} is empty, so the
printed formula would give 0, while |a(0)| = 1 (the characteristic polynomial of the empty matrix
is 1); this is a boundary case of the empty sum, not a counterexample.
-/

namespace OMA.S_oeis_a110034

/-- The n X n Hankel matrix of the Fibonacci numbers: entry (i, j) is F(i + j + 1) (0-based). -/
def H (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (Nat.fib ((i : ℕ) + (j : ℕ) + 1) : ℤ)

/-- A110033: T(n, k) is the coefficient of x^k in the characteristic polynomial of H(n). -/
noncomputable def T (n k : ℕ) : ℤ := (H n).charpoly.coeff k

/-- A110034: the row sums of A110033. -/
noncomputable def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

/-- A061646 with the index shifted by one: B(k) = A061646(k - 1). -/
def B : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | k + 3 => 2 * B (k + 2) + 2 * B (k + 1) - B k

/-- Bergot's conjecture: |a(n)| = Sum_{k=1..n-1} A061646(k) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → |a n| = ∑ k ∈ Finset.Icc 1 (n - 1), B (k + 1) := by
  sorry

end OMA.S_oeis_a110034
