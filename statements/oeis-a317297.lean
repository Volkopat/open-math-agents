import Mathlib

/-!
# A317297: a(n) = (n - 1)*(4*n^2 - 8*n + 5).

Source: https://oeis.org/A317297
Credit: @vivanpoddar

The sequence (offset 1) begins 0, 5, 34, 111, 260, 505, 870, 1379, ...

Conjecture (Stefano Spezia, Dec 27 2018): For n > 1, a(n) is the maximum eigenvalue of a
2*(n-1) X 2*(n-1) square matrix M defined as M[i,j,n] = j + n*(i-1) if i is odd and
M[i,j,n] = n*i - j + 1 if i is even (see A317614).

Formalization. As in A317614, M[i,j,m] denotes the entry (i,j), 1 <= i,j <= m, of the m X m matrix
M(m) obtained by writing 1, ..., m^2 forward and backward along the rows in a zig-zag pattern; the
conjecture concerns the member M(2*(n-1)) of this family, i.e. the third index of M[i,j,.] is the
size of the matrix. (This is the reading that agrees with the data: M(4) has eigenvalues
34, -2, 0, 0 and a(3) = 34.) "Maximum eigenvalue" is stated over the complex numbers: a(n) is an
eigenvalue, and every eigenvalue is real and at most a(n).
-/

namespace OMA.S_oeis_a317297

/-- A317297: a(n) = (n - 1)*(4*n^2 - 8*n + 5). -/
def a (n : ℕ) : ℤ := ((n : ℤ) - 1) * (4 * (n : ℤ) ^ 2 - 8 * (n : ℤ) + 5)

/-- The m X m zig-zag matrix M(m) of A317614: with rows and columns numbered from 1,
M[i,j,m] = j + m*(i-1) if i is odd and M[i,j,m] = m*i - j + 1 if i is even.
(`i.val + 1` and `j.val + 1` are the 1-based row and column numbers.) -/
def M (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := fun i j =>
  if (i.val + 1) % 2 = 1 then ((j.val : ℂ) + 1) + (m : ℂ) * (((i.val : ℂ) + 1) - 1)
  else (m : ℂ) * ((i.val : ℂ) + 1) - ((j.val : ℂ) + 1) + 1

/-- For n > 1, a(n) is the maximum eigenvalue of the zig-zag matrix M(2*(n-1)). -/
theorem main : ∀ n : ℕ, 1 < n →
    ((a n : ℤ) : ℂ) ∈ spectrum ℂ (M (2 * (n - 1))) ∧
    ∀ μ ∈ spectrum ℂ (M (2 * (n - 1))), μ.im = 0 ∧ μ.re ≤ ((a n : ℤ) : ℝ) := by
  sorry

end OMA.S_oeis_a317297
