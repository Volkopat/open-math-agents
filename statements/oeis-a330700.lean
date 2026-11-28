import Mathlib

/-!
# A330700: a(n) = (n - 1)*n*(2*n^2 + 4*n - 1)/6

Source: https://oeis.org/A330700
Credit: @jagong-cmu

THE CONJECTURE AS PRINTED IS FALSE. It fails at n = 2 (and at every n >= 2): M(2) is the
matrix [[1, 2], [2, 4]], whose only principal minor of size 2 is det M(2) = 0, but a(2) = 5.

The entry (offset 0, data 0, 0, 5, 29, 94, 230, ...) has the comment (Stefano Spezia, 2019):
For n > 1, a(n) is the absolute value of the trace of the 2nd exterior power of an n X n
square matrix M(n) defined as M[i,j,n] = i*j if i < 3 or j < 3 and M[i,j,n] = 2*(i + j) - 4
otherwise (see A330287). Equivalently, a(n) is the absolute value of the coefficient of the
term [x^(n-2)] in the characteristic polynomial of M(n), or the absolute value of the sum of
all principal minors of M(n) of size 2.

This file states that conjecture exactly as written, so that it can be refuted.
A Python check gives |e2(M(n))| = 0, 5, 29, 94, 230, 475, ... for n = 2, 3, 4, ..., that is,
|e2(M(n))| = a(n-1): the printed text has an index shift. The shifted form is not stated here.
The second conjecture of the entry (the trace of the k-th exterior power is zero for k > 2)
is a separate claim and is not part of this file.

Conventions:
* Matrix indices are `1..n` as in OEIS: the entry at `(i, j) : Fin n × Fin n` uses
  `i.val + 1` and `j.val + 1`. Entries are in `ℤ`.
* The trace of the 2nd exterior power is written as the sum of all principal minors of size 2,
  `∑_{i < j} (M i i * M j j - M i j * M j i)` (the third equivalent form in the comment).
* `a n` is computed in `ℤ`; the division by 6 is exact.
-/

namespace OMA.S_oeis_a330700

/-- `a(n) = (n - 1)*n*(2*n^2 + 4*n - 1)/6`. -/
def a (n : ℕ) : ℤ := ((n : ℤ) - 1) * n * (2 * (n : ℤ) ^ 2 + 4 * n - 1) / 6

/-- The `n × n` matrix `M(n)` with `M[i,j] = i*j` if `i < 3` or `j < 3`, and
`M[i,j] = 2*(i + j) - 4` otherwise (indices `1..n`). -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i.val + 1 < 3 ∨ j.val + 1 < 3 then ((i.val : ℤ) + 1) * ((j.val : ℤ) + 1)
    else 2 * (((i.val : ℤ) + 1) + ((j.val : ℤ) + 1)) - 4

/-- The trace of the 2nd exterior power of `A`: the sum of all principal minors of size 2. -/
def e2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then A i i * A j j - A i j * A j i else 0

/-- The conjecture as printed: for `n > 1`, `a(n) = |e2(M(n))|`. It is false (`n = 2`). -/
theorem main : ∀ n : ℕ, 1 < n → a n = |e2 (M n)| := by
  sorry

end OMA.S_oeis_a330700
