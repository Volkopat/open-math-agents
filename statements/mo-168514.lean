import Mathlib

/-!
# MathOverflow 168514

Source: https://mathoverflow.net/questions/168514
-/

namespace OMA.S_mo_168514

open Polynomial

theorem main : ∀ p q : ℤ[X], Squarefree p → Squarefree q →
    IsRelPrime p q →
    ∃ B : ℕ, ∀ n : ℤ, Int.gcd (p.eval n) (q.eval n) ≤ B := by
  sorry

end OMA.S_mo_168514
