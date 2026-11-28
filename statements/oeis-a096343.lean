import Mathlib

/-!
# A096343: Number of 1's in binary expansion(product of nonzero digits(n^n)).

Source: https://oeis.org/A096343
Credit: @gblacher2

`a(n)` is the number of 1's in the binary expansion of the product of the nonzero decimal digits
of `n^n`. The listed data `1, 1, 3, 4, 4, ...` are the values for `n = 1, 2, 3, 4, 5, ...`, and
the entry's example `n1b(pnd(1091^1091)) = n1b(pnd(1092^1092)) = 1892` uses `a(n)` for `n^n`,
so `a` is defined directly by the formula. The conjecture in the entry:
`a(n) = a(n+1)` for infinitely many positive integers `n`.
-/

namespace OMA.S_oeis_a096343

/-- The number of 1's in the binary expansion of the product of the nonzero decimal digits
of `n ^ n`. -/
def a (n : ℕ) : ℕ :=
  (Nat.digits 2 ((Nat.digits 10 (n ^ n)).filter (· ≠ 0)).prod).count 1

/-- `a(n) = a(n + 1)` for infinitely many positive integers `n`. -/
theorem main : {n : ℕ | 0 < n ∧ a n = a (n + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a096343
