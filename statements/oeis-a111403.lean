import Mathlib

/-!
# A111403: a(n) = f(f(n+1)) - f(f(n)), where f(m) = 2^m.

Source: https://oeis.org/A111403
Credit: @marcelopierry

Conjecture (R. J. Mathar, May 15 2007, in the formulas of A111403): a(n) = A002716(2*n) - 1.

Conventions:
* The sequence has offset 0; f(m) = 2^m on the natural numbers and a(n) is computed in the
  integers, giving the data 2, 12, 240, 65280, 4294901760, ...
* A002716 (offset 0) is defined by the recursion recorded in that entry (Michael Somos,
  Feb 01 2004): a(0) = 3, a(1) = 5, a(2n) = a(2n-1)^2 - 3*a(2n-1) + 3 and
  a(2n+1) = a(2n) + a(2n-1) - 1 (data 3, 5, 13, 17, 241, 257, 65281, ...). In the definition the
  index is m = k + 2: for even m the first rule applies, for odd m the second.
-/

namespace OMA.S_oeis_a111403

/-- A002716, by its recursion (offset 0). -/
def A002716 : ℕ → ℤ
  | 0 => 3
  | 1 => 5
  | n + 2 => if n % 2 = 0 then A002716 (n + 1) ^ 2 - 3 * A002716 (n + 1) + 3
      else A002716 (n + 1) + A002716 n - 1

/-- f(m) = 2^m. -/
def f (m : ℕ) : ℕ := 2 ^ m

/-- A111403(n) = f(f(n+1)) - f(f(n)). -/
def a (n : ℕ) : ℤ := (f (f (n + 1)) : ℤ) - f (f n)

/-- Mathar's conjecture: a(n) = A002716(2n) - 1. -/
theorem main : ∀ n : ℕ, a n = A002716 (2 * n) - 1 := by
  sorry

end OMA.S_oeis_a111403
