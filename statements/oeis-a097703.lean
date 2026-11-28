import Mathlib

/-!
# When the divisor sum differs from twice the unitary divisor sum

Source: https://oeis.org/A097703
Credit: @anmolspace (Lean formalization).

Ralf Stephan's 2004 OEIS entry asks whether every index `j = 3k + 1` occurs.
Amiram Eldar proved the inclusion and characterized all the indices in 2024.
-/

namespace OMA.S_oeis_a097703

/-- Sum of divisors coprime to their complementary divisors. -/
def unitarySum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with d.Coprime (n / d), d

/-- Whether the nonnegative integer `j` is a term of OEIS A097703. -/
def occurs (j : ℕ) : Prop :=
  ArithmeticFunction.sigma 1 (216 * j + 108) ≠ 2 * unitarySum (216 * j + 108)

/-- The original progression and the full characterization in the OEIS entry. -/
theorem main : (∀ k : ℕ, occurs (3 * k + 1)) ∧
    ∀ j : ℕ, occurs j ↔ 3 ∣ 2 * j + 1 ∨ ¬ Squarefree (2 * j + 1) := by
  sorry

end OMA.S_oeis_a097703
