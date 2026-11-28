import Mathlib

/-!
# A297555: a(n) = a(n-1) + 16*a(n-3) - 16*a(n-4), where a(0) = 1, a(1) = 4, a(2) = 8, a(3) = 12,
a(4) = 76.

Source: https://oeis.org/A297555
Credit: @bnb9001

For a number with base-4 digits d(m), d(m-1), ..., d(0) (most significant first), the base-4
down-variation is the sum of d(i) - d(i-1) over the i with d(i) > d(i-1) (see A297552). Below,
`Nat.digits` lists d(0), d(1), ... (least significant first), so each adjacent pair contributes
the truncated difference (more significant - less significant).

Conjecture (Clark Kimberling): a(n) = least positive integer whose base-4 down-variation is n;
see column 1 of A297552.
-/

namespace OMA.S_oeis_a297555

/-- Down-variation of a digit list given least significant digit first: the sum of the drops
`d(i) - d(i-1) > 0` from each digit to the next less significant one. -/
def dvList : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: t => (y - x) + dvList (y :: t)

/-- The base-4 down-variation of `x`. -/
def dv (x : ℕ) : ℕ := dvList (Nat.digits 4 x)

/-- A297555: a(n) = a(n-1) + 16*a(n-3) - 16*a(n-4) with a(0..4) = 1, 4, 8, 12, 76. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 8
  | 3 => 12
  | 4 => 76
  | (n + 5) => a (n + 4) + 16 * a (n + 2) - 16 * a (n + 1)

/-- Kimberling's conjecture: `a(n)` is the least positive integer with base-4 down-variation `n`. -/
theorem main : ∀ n : ℕ, IsLeast {x : ℕ | 0 < x ∧ dv x = n} (a n).toNat := by
  sorry

end OMA.S_oeis_a297555
