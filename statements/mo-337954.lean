import Mathlib

/-!
# Solutions of `x³ + y³ = z³ + 3` in positive integers

Source: https://mathoverflow.net/questions/337954
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The only known solution of `x³ + y³ = z³ + 3` in positive integers is `4³ + 4³ = 5³ + 3`; the
asker reports that there is reason to think other solutions exist. `main` states that a solution
in positive integers other than `(4, 4, 5)` exists.

Conventions:
* `(x, y, z)` and `(y, x, z)` are the same solution; 'other than `4³ + 4³ = 5³ + 3`' means
  `(x, y, z) ≠ (4, 4, 5)` (which is symmetric in `x, y`).
-/

namespace OMA.S_mo_337954

/-- There is a positive solution of `x³ + y³ = z³ + 3` other than `(4, 4, 5)`. -/
theorem main : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 3 + y ^ 3 = z ^ 3 + 3 ∧
    (x, y, z) ≠ (4, 4, 5) := by
  sorry

end OMA.S_mo_337954
