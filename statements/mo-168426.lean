import Mathlib

open scoped BigOperators

namespace OMA.S_mo_168426

/-- The translation and cube permutations on prime fields of order congruent
to two modulo three have a uniform spectral gap after symmetrization. -/
theorem main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ) [Fact p.Prime], p % 3 = 2 →
        ∀ f : ZMod p → ℝ, (∑ x, f x) = 0 →
          (∑ x, (f x) ^ 2) ≤
            C * ∑ x, ((f (x + 1) - f x) ^ 2 + (f (x ^ 3) - f x) ^ 2) := by
  sorry

end OMA.S_mo_168426
