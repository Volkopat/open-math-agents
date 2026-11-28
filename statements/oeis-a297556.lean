import Mathlib

/-!
# A297556: a(n) = a(n-1) + 16*a(n-3) - 16*a(n-4), where a(0) = 1, a(1) = 4, a(2) = 7, a(3) = 19.

Source: https://oeis.org/A297556
Credit: @bnb9001

Data (offset 0): 1, 6, 7, 19, 99, 115, 307, 1587, ... The listed data has a(1) = 6, which is also
what the recurrence needs to give a(4) = 99 (with a(1) = 4 it would give 67), so the title's
a(1) = 4 is a typo; `a` below uses the initial terms 1, 6, 7, 19 of the data.

For a number with base-4 digits d(m), ..., d(0) (most significant first), the base-4 up-variation
is the sum of d(k-1) - d(k) over the k with d(k) < d(k-1) (see A297553). Below, `Nat.digits` lists
d(0), d(1), ... (least significant first), so each adjacent pair contributes the truncated
difference (less significant - more significant).

Conjecture (Clark Kimberling): a(n) = least positive integer whose base-4 up-variation is n; see
column 1 of A297553.
-/

namespace OMA.S_oeis_a297556

/-- Up-variation of a digit list given least significant digit first: the sum of the rises
`d(k-1) - d(k) > 0` from each digit to the next less significant one. -/
def uvList : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: t => (x - y) + uvList (y :: t)

/-- The base-4 up-variation of `x`. -/
def uv (x : ℕ) : ℕ := uvList (Nat.digits 4 x)

/-- A297556 (data-faithful form with a(1) = 6, see the module docstring). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 6
  | 2 => 7
  | 3 => 19
  | (n + 4) => a (n + 3) + 16 * a (n + 1) - 16 * a n

/-- Kimberling's conjecture: `a(n)` is the least positive integer with base-4 up-variation `n`. -/
theorem main : ∀ n : ℕ, IsLeast {x : ℕ | 0 < x ∧ uv x = n} (a n).toNat := by
  sorry

end OMA.S_oeis_a297556
