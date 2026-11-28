import Mathlib

/-!
# A022566: numbers that are not the sum of 4 nonnegative cubes

Source: https://oeis.org/A022566
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A022566, after Deshouillers–Hennecart–Landreau 2000, Conj. 1 and 2): the
sequence is finite, with `113936676` terms, the largest being `7373170279850`.
-/

namespace OMA.S_oeis_a022566

/-- `n` is a sum of 4 nonnegative cubes. -/
def IsSum4Cubes (n : ℕ) : Prop := ∃ a b c d : ℕ, a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = n

theorem main :
    {n : ℕ | ¬ IsSum4Cubes n}.Finite ∧ {n : ℕ | ¬ IsSum4Cubes n}.ncard = 113936676 ∧
      ¬ IsSum4Cubes 7373170279850 ∧ ∀ n > 7373170279850, IsSum4Cubes n := by
  sorry

end OMA.S_oeis_a022566
