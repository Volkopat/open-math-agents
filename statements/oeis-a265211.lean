import Mathlib

/-!
# OEIS A265211: Squares that become prime when their rightmost digit is removed.

Source: https://oeis.org/A265211
Credit: @unserus

OEIS (R. Israel): "All terms except a(1) are of the form 10*p+6 where p is a prime of the form
10*x^2 + 8*x + 1 or 10*x^2 + 12*x + 3. The Bunyakovsky conjecture implies that there are
infinitely many of both of these types."
The open statement is that both types occur infinitely often. Removing the rightmost decimal
digit of `m` gives `m / 10`. Since `(10x + 4)^2 = 10 (10x^2 + 8x + 1) + 6` and
`(10x + 6)^2 = 10 (10x^2 + 12x + 3) + 6`, the two types are the terms whose square root ends in
`4` and those whose square root ends in `6` (`x ≥ 0`).
-/

namespace OMA.S_oeis_a265211

/-- The terms of A265211: squares `m` such that `m / 10` (drop the last digit) is prime. -/
def a265211Set : Set ℕ := {m : ℕ | IsSquare m ∧ (m / 10).Prime}

/-- Infinitely many terms are `(10x + 4)^2` (type `10x^2 + 8x + 1`) and infinitely many are
`(10x + 6)^2` (type `10x^2 + 12x + 3`). -/
theorem main :
    {m : ℕ | m ∈ a265211Set ∧ ∃ x : ℕ, m = (10 * x + 4) ^ 2}.Infinite ∧
      {m : ℕ | m ∈ a265211Set ∧ ∃ x : ℕ, m = (10 * x + 6) ^ 2}.Infinite := by
  sorry

end OMA.S_oeis_a265211
