import Mathlib

/-!
# A350689: a(n) = n*(1 - (-1)^n - 2*(3 + (-1)^n)*n^2 + 2*n^4)/384.

Source: https://oeis.org/A350689
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 0, 1, 4, 15, 36, 84, 160, ...

Conjectures (Stefano Spezia): For n > 1, a(n) is the absolute value of the trace of the 3rd
exterior power of an n X n square matrix M(n) defined as M[i,j] = floor((j - i + 1)/2).
Equivalently, a(n) is the absolute value of the coefficient of the term [x^(n-3)] in the
characteristic polynomial of the matrix M(n), or the absolute value of the sum of all principal
minors of M(n) of size 3. For k > 3, the trace of the k-th exterior power of the matrix M(n) is
equal to zero.

Formalization. The trace of the k-th exterior power of an n X n matrix is expressed through its
characteristic polynomial det(x*I - M), using the equivalence stated in the entry itself: it is
(-1)^k times the coefficient of x^(n-k) for k <= n, and 0 for k > n (the k-th exterior power of an
n-dimensional space is then zero). In particular, for n = 2 the statement says a(2) = 0.
The matrix has rational entries, rows and columns are numbered from 1, and a(n) is defined by the
formula of the name as a rational number.
-/

namespace OMA.S_oeis_a350689

/-- A350689: a(n) = n*(1 - (-1)^n - 2*(3 + (-1)^n)*n^2 + 2*n^4)/384. -/
def a (n : ℕ) : ℚ :=
  (n : ℚ) * (1 - (-1) ^ n - 2 * (3 + (-1) ^ n) * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 4) / 384

/-- The n X n matrix M(n) with M[i,j] = floor((j - i + 1)/2), 1 <= i, j <= n
(`i.val + 1` and `j.val + 1` are the 1-based row and column numbers). -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  ((⌊(((j.val : ℚ) + 1) - ((i.val : ℚ) + 1) + 1) / 2⌋ : ℤ) : ℚ)

/-- The trace of the k-th exterior power of an n X n matrix, read off from its characteristic
polynomial: (-1)^k times the coefficient of x^(n-k) if k <= n, and 0 if k > n. -/
noncomputable def extTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) : ℚ :=
  if k ≤ n then (-1) ^ k * A.charpoly.coeff (n - k) else 0

/-- Spezia's conjectures on the exterior powers of M(n). -/
theorem main : ∀ n : ℕ, 1 < n →
    |extTrace (M n) 3| = a n ∧ ∀ k : ℕ, 3 < k → extTrace (M n) k = 0 := by
  sorry

end OMA.S_oeis_a350689
