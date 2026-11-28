import Mathlib

/-!
# A338309 and its conjectured coverage of the semiprimes

Source: https://oeis.org/A338309
Credit: @yuka30240

-/

namespace OMA.S_oeis_a338309

/-- Start at 4. At each step choose the least unused semiprime whose sum with
the current term is also semiprime. The first term has index 1. -/
def IsA338309 (a : ℕ+ → ℕ) : Prop :=
  a 1 = 4 ∧ ∀ n : ℕ+,
    IsLeast {m : ℕ | m.IsSemiprime ∧ (a n + m).IsSemiprime ∧ ∀ i ≤ n, a i ≠ m}
      (a (n + 1))

/-- Every semiprime occurs in the greedy sequence. -/
theorem main : ∃ a : ℕ+ → ℕ, IsA338309 a ∧
    ∀ m : ℕ, m.IsSemiprime → ∃ n : ℕ+, a n = m := by
  sorry

end OMA.S_oeis_a338309

