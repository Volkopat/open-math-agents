import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Field.Rat

namespace OMA.S_mo_498167

/-- An integer quadratic evaluated at a natural index. -/
def denominator (a b c : ℤ) (n : ℕ) : ℤ :=
  a * (n : ℤ) ^ 2 + b * (n : ℤ) + c

/-- The reciprocal series has a rational sum exactly when the discriminant is the
square of the leading coefficient times the square of a positive integer. -/
theorem main :
    ∀ (a b c : ℤ), a ≠ 0 →
      (∀ n : ℕ, 0 < n → denominator a b c n ≠ 0) →
        ((∃ q : ℚ, HasSum (fun n : ℕ => ((denominator a b c (n + 1) : ℝ)⁻¹)) (q : ℝ)) ↔
          ∃ k : ℕ, 0 < k ∧ b ^ 2 - 4 * a * c = (k : ℤ) ^ 2 * a ^ 2) := by
  sorry

end OMA.S_mo_498167
