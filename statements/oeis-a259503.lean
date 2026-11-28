import Mathlib

/-!
# A259503: Numbers k such that k^2+1 is the product of a Fibonacci number and a Lucas number.

Source: https://oeis.org/A259503
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. Its known terms are 0, 1, 2, 3, 5, 12,
133 (no more below 10^7), e.g. 12^2 + 1 = 145 = 5 * 29 = F(5) * L(7) and
133^2 + 1 = 17690 = 610 * 29 = F(15) * L(7).

Reading of the source:
* `F(i)` is the Fibonacci number `Nat.fib i` and `L(j)` the Lucas number (A000032):
  `L(0) = 2`, `L(1) = 1`, `L(j + 2) = L(j + 1) + L(j)`; the indices `i, j ≥ 0` (the examples use
  `L(0) = 2` and `L(1) = 1`).
* `k` ranges over the natural numbers. With this reading the terms below `10^5` are exactly the
  listed ones.
-/

namespace OMA.S_oeis_a259503

/-- The Lucas numbers: `2, 1, 3, 4, 7, 11, ...`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

theorem main : {k : ℕ | ∃ i j : ℕ, k ^ 2 + 1 = Nat.fib i * lucas j}.Finite := by
  sorry

end OMA.S_oeis_a259503
