import Mathlib

/-!
# Infinitely many integral points on a quartic surface

MathOverflow question 289840, asked by joro: https://mathoverflow.net/q/289840
Lean statement by @AlfredMelson.
-/

namespace OMA.S_mo_289840

def solutions (N : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {t | let (a, b, c) := t
       a ^ 4 + b ^ 4 - c ^ 4 = N ∧ a ≠ c ∧ a ≠ -c ∧ b ≠ c ∧ b ≠ -c}

theorem main : ∃ N : ℤ, N ≠ 0 ∧ (solutions N).Infinite := by
  sorry

end OMA.S_mo_289840
