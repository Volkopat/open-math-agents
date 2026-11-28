import Mathlib

/-!
# A002716: An infinite coprime sequence defined by recursion.

Source: https://oeis.org/A002716
Credit: @marcelopierry

Conjecture (R. J. Mathar, May 15 2007, in the formulas of A002716): a(2n+1) = A001146(n+1) + 1.

Conventions:
* The sequence has offset 0 and follows the recursion recorded in A002716 (Michael Somos,
  Feb 01 2004): a(0) = 3, a(1) = 5, a(2n) = a(2n-1)^2 - 3*a(2n-1) + 3 and
  a(2n+1) = a(2n) + a(2n-1) - 1. It reproduces the data 3, 5, 13, 17, 241, 257, 65281, 65537, ...
  Values are computed in the integers.
* In the definition below the index is m = k + 2: for even m the first rule applies (with
  2n - 1 = k + 1), for odd m the second (with 2n = k + 1 and 2n - 1 = k).
* A001146(m) = 2^(2^m) (offset 0), so A001146(n+1) + 1 = 2^(2^(n+1)) + 1, for every n >= 0.
-/

namespace OMA.S_oeis_a002716

/-- A002716, by its recursion (offset 0). -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 5
  | n + 2 => if n % 2 = 0 then a (n + 1) ^ 2 - 3 * a (n + 1) + 3 else a (n + 1) + a n - 1

/-- Mathar's conjecture: the odd-indexed terms are the Fermat numbers 2^(2^(n+1)) + 1. -/
theorem main : ∀ n : ℕ, a (2 * n + 1) = 2 ^ (2 ^ (n + 1)) + 1 := by
  sorry

end OMA.S_oeis_a002716
