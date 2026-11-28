import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card

/-!
# Least coefficients for prescribed integral point counts

Source: https://oeis.org/A393931
Credit: @luciusacarr

The statement quantifies over least coefficients directly. It makes no
existence claim for a point count that might never occur.
-/

namespace OMA.S_oeis_a393931

def integralPoints (k : ℕ) : Set (ℤ × ℤ) :=
  {P | 0 ≤ P.2 ∧ P.2 ^ 2 = P.1 ^ 3 - (k : ℤ) * P.1 + 1}

theorem main : ∀ n : ℕ, 3 < n → ∀ k : ℕ,
    IsLeast {j : ℕ | 0 < j ∧ (integralPoints j).ncard = n} k → ¬ k.Prime := by
  sorry

end OMA.S_oeis_a393931
