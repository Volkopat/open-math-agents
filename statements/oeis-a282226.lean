import Mathlib

/-!
# A282226: Least nonnegative integer m which can be written in exactly n ways as x^2 + y^2 + z^2 + w^2 with both x and x + 24*y squares, where x,y,z,w are nonnegative integers with z <= w.

Source: https://oeis.org/A282226
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282226 (Zhi-Wei Sun, Feb 09 2017): a(n) exists for any
n > 0.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 10, 18, 34, 41, 52, 66, 100, 90, 130, ...).
* `r m` is the number of quadruples (x, y, z, w) of natural numbers with m = x^2 + y^2 + z^2 +
  w^2, z <= w and both x and x + 24*y squares (`IsSquare`, 0 included); the set of such quadruples
  is finite, so `Set.ncard` is its number of elements.
* `a(n) exists` means that some natural number m can be written in exactly n such ways (then the
  least such m exists); it is stated as the existence of m with r(m) = n.
-/

namespace OMA.S_oeis_a282226

/-- The number of ways to write m as x^2 + y^2 + z^2 + w^2 with z <= w and both x and x + 24*y
squares. -/
noncomputable def r (m : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = m ∧
    t.2.2.1 ≤ t.2.2.2 ∧ IsSquare t.1 ∧ IsSquare (t.1 + 24 * t.2.1)}

/-- The conjecture recorded in A282226. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, r m = n := by
  sorry

end OMA.S_oeis_a282226
