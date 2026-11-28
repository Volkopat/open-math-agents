import Mathlib

/-!
# Can `9k ± 4` be written as a sum of four cubes?

Source: https://math.stackexchange.com/questions/2751881
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

All integers except possibly those of the form `9k ± 4` are known to be sums of four integer
cubes. The conjecture behind the question is that every integer is a sum of four integer cubes;
`main` states it for the remaining case `n ≡ ±4 (mod 9)` (equivalently, for all integers).

Conventions:
* Cubes of arbitrary (possibly negative) integers.
-/

namespace OMA.S_mse_2751881

/-- Every integer `n ≡ ±4 (mod 9)` is a sum of four integer cubes. -/
theorem main : ∀ n : ℤ, (n % 9 = 4 ∨ n % 9 = 5) →
    ∃ a b c d : ℤ, n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 := by
  sorry

end OMA.S_mse_2751881
