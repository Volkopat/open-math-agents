import Mathlib

/-!
# OEIS A295687: Bala's bisection recurrences

Source: https://oeis.org/A295687
Credit: @ceejcake

The sequence has offset 0 and is defined by a(n) = a(n-1) + a(n-3) + a(n-4) with
a(0) = 1, a(1) = 2, a(2) = 2, a(3) = 1; its data begin 1, 2, 2, 1, 4, 8, 11, 16.

The entry records several formulas from Peter Bala, Nov 27 2021. This file formalizes
only the first two of them, the recurrences for the even and odd bisections, stated
together for n >= 2:
a(2n) = 3 a(2n-2) - a(2n-4) - (-1)^n and a(2n+1) = 3 a(2n-1) - a(2n-3) + 7 (-1)^n.
It does not formalize Bala's later Lucas and Fibonacci identities, nor his series conjecture.
The sequence is valued in the integers so that the signed terms are exact. For n >= 2 no
natural-number subtraction in an index below truncates at zero.
-/

namespace OMA.S_oeis_a295687

/-- A295687: a(n) = a(n-1) + a(n-3) + a(n-4) with a(0), a(1), a(2), a(3) = 1, 2, 2, 1. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | (n + 4) => a (n + 3) + a (n + 1) + a n

/-- Bala's two bisection recurrences, for n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a (2 * n) = 3 * a (2 * n - 2) - a (2 * n - 4) - (-1) ^ n ∧
    a (2 * n + 1) = 3 * a (2 * n - 1) - a (2 * n - 3) + 7 * (-1) ^ n := by
  sorry

end OMA.S_oeis_a295687
