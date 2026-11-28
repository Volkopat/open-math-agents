import Mathlib

/-!
# A221130: a(n) = 2^(2*n - 1) + n.

Source: https://oeis.org/A221130
Credit: @bnb9001

Offset 1: 3, 10, 35, 132, 517, ...

Conjecture: a(n) = the smallest number w such that the numbers w, w+1, ..., w+n-1 are all of the
form h*2^m + m, where 1 <= h < 2^m and m is a natural number (the numbers of A221129, which
requires m > 0). For example a(5) = 517 because 517, 518, 519, 520, 521 are of that form.
-/

namespace OMA.S_oeis_a221130

/-- Membership in A221129: `N = h * 2^m + m` with `1 ≤ h < 2^m` and `m > 0`. -/
def IsForm (N : ℕ) : Prop := ∃ m h : ℕ, 0 < m ∧ 1 ≤ h ∧ h < 2 ^ m ∧ N = h * 2 ^ m + m

/-- A221130: `a(n) = 2^(2n-1) + n`. -/
def a (n : ℕ) : ℕ := 2 ^ (2 * n - 1) + n

/-- The conjecture: `a(n)` is the least start of a run of `n` consecutive members of A221129. -/
theorem main : ∀ n : ℕ, 1 ≤ n → IsLeast {w : ℕ | ∀ i < n, IsForm (w + i)} (a n) := by
  sorry

end OMA.S_oeis_a221130
