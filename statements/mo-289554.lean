import Mathlib

/-!
# If `a³ + b³ + c³ = N`, then `x³ + y³ + z³ + t³ = N` in infinitely many ways?

Source: https://mathoverflow.net/questions/289554
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asker): if `N` is a sum of three integer cubes, then `N` is a sum of four integer
cubes in infinitely many ways.

Conventions:
* Cubes of arbitrary integers; 'ways' are ordered quadruples `(x, y, z, t) ∈ ℤ⁴`.
-/

namespace OMA.S_mo_289554

/-- A sum of three cubes has infinitely many representations as a sum of four cubes. -/
theorem main : ∀ N : ℤ, (∃ a b c : ℤ, a ^ 3 + b ^ 3 + c ^ 3 = N) →
    {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = N}.Infinite := by
  sorry

end OMA.S_mo_289554
