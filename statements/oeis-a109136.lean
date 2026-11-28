import Mathlib

/-!
# OEIS A109136: even numbers as a prime plus the square of a prime

Source: https://oeis.org/A109136
The entry lists the even numbers that are not `≡ 1 (mod 3)`, not squares, and not of the form
`p + q²` with `p, q` prime, and conjectures that every sufficiently large even number is
`≡ 1 (mod 3)`, or a square, or a sum of a prime and the square of a prime (so the listed
numbers are the only exceptions).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a109136

theorem main :
    ∀ᶠ n : ℕ in Filter.atTop, Even n →
      n % 3 = 1 ∨ IsSquare n ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q ^ 2 := by
  sorry

end OMA.S_oeis_a109136
