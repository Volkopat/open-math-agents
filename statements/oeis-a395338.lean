import Mathlib

/-!
# A395338: Primes whose squares are decimal concatenations of two distinct nonzero squares

Source: https://oeis.org/A395338
Credit: @gblacher2
-/

namespace OMA.S_oeis_a395338

/-- The conjecture that there are infinitely many such primes. Since `y` is positive,
`(Nat.digits 10 y).length` counts its decimal digits without leading zeros. -/
theorem main :
    {p : ℕ | p.Prime ∧ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ IsSquare x ∧ IsSquare y ∧
      p ^ 2 = x * 10 ^ (Nat.digits 10 y).length + y}.Infinite := by
  sorry

end OMA.S_oeis_a395338
