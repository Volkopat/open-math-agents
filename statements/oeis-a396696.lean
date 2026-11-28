import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# A prime-producing factorial constant in OEIS A396696

Eric Campos Bastos Guedes and Anderson Torres ask whether one real constant
makes the floor of its product with every positive factorial squared a prime.
The floor convention is explicit in the intervals in the OEIS entry.
Source: https://oeis.org/A396696 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.
-/

namespace OMA.S_oeis_a396696

theorem main : ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    ∃ p : ℕ, p.Prime ∧ ⌊C * (n.factorial : ℝ) ^ 2⌋ = (p : ℤ) := by
  sorry

end OMA.S_oeis_a396696
