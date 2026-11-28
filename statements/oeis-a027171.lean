import Mathlib

/-!
# A027171: a(n) = A027170(2n, n).

Source: https://oeis.org/A027171
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 10, 42, 156, 570, 2096, 7784, 29168, 110106, 418128, ...
A027170 is the triangular array T (4-diamondization of Pascal's triangle) defined in two steps:
  Step 1: t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k).
  Step 2: T(n,k) = t(n,k) - t(0,0) + 1.
These definitions are used here verbatim; a(n) = T(2n, n) reproduces the data of the entry.

The conjecture (R. J. Mathar, May 06 2026) reads
  Conjecture: D-finite with recurrence 2*(n+1)*a(n) +(-7*n-5)*a(n-1) +2*(-2*n+3)*a(n-2) +12*(-3*n+1)=0.
(an inhomogeneous recurrence). It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a027171

/-- Step 1 of A027170: t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k). -/
def t (n k : ℕ) : ℤ :=
  ((n + 2).choose (k + 1) : ℤ) + ((n + 1).choose k : ℤ) + ((n + 1).choose (k + 1) : ℤ) + (n.choose k : ℤ)

/-- Step 2 of A027170: T(n,k) = t(n,k) - t(0,0) + 1. -/
def T (n k : ℕ) : ℤ := t n k - t 0 0 + 1

/-- A027171: a(n) = T(2n, n). -/
def a (n : ℕ) : ℤ := T (2 * n) n

/-- Mathar's conjectured (inhomogeneous) recurrence for A027171. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    2 * ((n : ℤ) + 1) * a n + (-7 * (n : ℤ) - 5) * a (n - 1) + 2 * (-2 * (n : ℤ) + 3) * a (n - 2)
      + 12 * (-3 * (n : ℤ) + 1) = 0 := by
  sorry

end OMA.S_oeis_a027171
