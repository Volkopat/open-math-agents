import Mathlib

/-!
# A350050: traces of the exterior powers of the matrices A349107 and A349108

Source: https://oeis.org/A350050 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A350050, offset 0: a(n) = (2*n^4 - 6*(-1)^n*n^2 - 2*n^2 + 3*(-1)^n - 3)/96. Data
0, 0, 0, 2, 4, 14, 24, 52, 80, 140, 200, 310, 420, 602, 784, 1064, 1344, 1752, 2160, ...

Comments, Conjectures:
For n > 1, a(n) is the absolute value of the trace of the 2nd exterior power of an n X n
square matrix A(n) defined as A[i,j,n] = n - abs((n + 1)/2 - j) - abs((n + 1)/2 - i) (see
A349107). Equivalently, a(n) is the absolute value of the coefficient of the term [x^(n-2)] in
the characteristic polynomial of the matrix A(n), or the absolute value of the sum of all
principal minors of A(n) of size 2.
For k > 2, the trace of the k-th exterior power of the matrix A(n) is equal to zero.
The same conjectures hold for an n X n square matrix A(n) defined as
A[i,j,n] = (n mod 2) + abs((n + 1)/2 - j) + abs((n + 1)/2 - i) (see A349108).

Formalization notes.
* The matrices have rational entries (for even n the two absolute values are half-integers).
  The indices i, j of the entry run from 1 to n; `Fin n` has the values 0..n-1, so the entry
  uses `(i : ℕ) + 1` and `(j : ℕ) + 1`.
* The trace of the k-th exterior power of an n X n matrix is the sum of its principal minors of
  size k, and the characteristic polynomial det(x I - A) has the coefficient
  (-1)^k tr(Λ^k A) at x^(n-k). The entry itself gives this form for k = 2. `main` uses the
  coefficients of `Matrix.charpoly`: the absolute value of the coefficient of x^(n-2) is a(n),
  and the coefficient of x^(n-k) is 0 for 2 < k <= n.
* `main` states both conjectures for both matrices, for all n > 1.
-/

namespace OMA.S_oeis_a350050

/-- A350050(n) = (2n^4 - 6(-1)^n n^2 - 2n^2 + 3(-1)^n - 3)/96 (an integer for each n). -/
def a (n : ℕ) : ℚ := (2 * (n : ℚ) ^ 4 - 6 * (-1) ^ n * (n : ℚ) ^ 2 - 2 * (n : ℚ) ^ 2 + 3 * (-1) ^ n - 3) / 96

/-- The n X n matrix A[i,j,n] = n - |(n+1)/2 - j| - |(n+1)/2 - i|, 1 ≤ i, j ≤ n (A349107). -/
def A (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (n : ℚ) - |((n : ℚ) + 1) / 2 - ((j : ℕ) + 1)| - |((n : ℚ) + 1) / 2 - ((i : ℕ) + 1)|

/-- The n X n matrix A[i,j,n] = (n mod 2) + |(n+1)/2 - j| + |(n+1)/2 - i| (A349108). -/
def B (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => ((n % 2 : ℕ) : ℚ) + |((n : ℚ) + 1) / 2 - ((j : ℕ) + 1)| + |((n : ℚ) + 1) / 2 - ((i : ℕ) + 1)|

/-- For n > 1 and for both matrices: the absolute value of the coefficient of x^(n-2) of the
characteristic polynomial is a(n), and the coefficients of x^(n-k) are zero for k > 2. -/
theorem main : ∀ n : ℕ, 1 < n →
    (|(A n).charpoly.coeff (n - 2)| = a n ∧ ∀ k : ℕ, 2 < k → k ≤ n → (A n).charpoly.coeff (n - k) = 0) ∧
    (|(B n).charpoly.coeff (n - 2)| = a n ∧ ∀ k : ℕ, 2 < k → k ≤ n → (B n).charpoly.coeff (n - k) = 0) := by
  sorry

end OMA.S_oeis_a350050
