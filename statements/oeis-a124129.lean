import Mathlib

/-!
# OEIS A124129

Rémi Eismann conjectured that the listed six primes exhaust A124129.
Source: https://oeis.org/A124129 (OEIS Foundation, CC BY-SA 4.0).
Lean formalization: @xlh1551.
-/

namespace OMA.S_oeis_a124129

theorem main : ∀ p : ℕ,
    (p.Prime ∧ ¬ ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) < (p : ℝ) + Real.sqrt (p : ℝ)) ↔
    p ∈ ([3, 7, 13, 23, 31, 113] : List ℕ) := by
  sorry

end OMA.S_oeis_a124129
