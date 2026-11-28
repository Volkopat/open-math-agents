import Mathlib

/-!
# A292689: Decimal values of the antidiagonals of the Sierpinski carpet as binary numbers

Source: https://oeis.org/A292689 (conjecture by R. J. Cano, Oct 25 2017)

Conjecture: a(k+1) = 2*a(k)+1 for all k in A003462 = (1, 4, 13, 40, 121, 364, ...).

Conventions:
* The Sierpinski carpet matrix (A153490) is indexed from 0 here: `black i j` says whether
  the cell in row i and column j is 1. It is the fractal obtained by repeatedly subdividing
  each square into 3 X 3 smaller squares and removing the middle one: the cell (i, j) is
  removed (0) exactly when at some level both base-3 digits of i and j are 1. Recursively:
  (0, 0) is 1, and otherwise (i, j) is 1 iff not (i mod 3 = 1 and j mod 3 = 1) and the cell
  (i/3, j/3) of the coarser level is 1 (this is how the PARI program of the entry builds
  the matrix).
* a(n) (offset 1) is the n-th antidiagonal (cells with row + column = n - 1, 0-indexed) read
  as a binary number, the cell in row k (k = 0..n-1) giving the bit of weight 2^k, as in the
  PARI program (the carpet is symmetric, so the antidiagonals are palindromes and the reading
  direction does not matter).
* A003462(m) = (3^m - 1)/2; the statement is for every m >= 1.
-/

namespace OMA.S_oeis_a292689

/-- The Sierpinski carpet A153490, 0-indexed. -/
def black (i j : ℕ) : Bool :=
  if h : i = 0 ∧ j = 0 then true
  else (!(i % 3 = 1 && j % 3 = 1)) && black (i / 3) (j / 3)
termination_by i + j
decreasing_by omega

/-- A292689(n): the n-th antidiagonal of the carpet read as a binary number. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, if black k (n - 1 - k) then 2 ^ k else 0

theorem main : ∀ m : ℕ, 1 ≤ m → a ((3 ^ m - 1) / 2 + 1) = 2 * a ((3 ^ m - 1) / 2) + 1 := by
  sorry

end OMA.S_oeis_a292689
