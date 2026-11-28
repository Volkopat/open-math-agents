import Mathlib

/-!
# A297554: a(n) = a(n-2) + 4*a(n-3) - 4*a(n-5), where a(0) = 1, a(1) = 4, a(2) = 7, a(3) = 12,
a(4) = 19, a(5) = 28.

Source: https://oeis.org/A297554
Credit: @bnb9001

The base-4 total variation of a positive integer is the sum of |d(i) - d(i-1)| over adjacent base-4
digits (the down-variation plus the up-variation, see A297551). `Nat.digits` lists the digits
least significant first, which does not change the sum of adjacent absolute differences.

Conjecture (Clark Kimberling): a(n) = least positive integer whose base-4 total variation is n;
see A297551.
-/

namespace OMA.S_oeis_a297554

/-- Total variation of a digit list: the sum of `|d_{i+1} - d_i|` over adjacent digits. -/
def tvList : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: t => ((x - y) + (y - x)) + tvList (y :: t)

/-- The base-4 total variation of `x`. -/
def tv (x : ℕ) : ℕ := tvList (Nat.digits 4 x)

/-- A297554: a(n) = a(n-2) + 4*a(n-3) - 4*a(n-5) with a(0..5) = 1, 4, 7, 12, 19, 28. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 19
  | 5 => 28
  | (n + 6) => a (n + 4) + 4 * a (n + 3) - 4 * a (n + 1)

/-- Kimberling's conjecture: `a(n)` is the least positive integer with base-4 total variation `n`. -/
theorem main : ∀ n : ℕ, IsLeast {x : ℕ | 0 < x ∧ tv x = n} (a n).toNat := by
  sorry

end OMA.S_oeis_a297554
