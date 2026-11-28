import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Source: https://mathoverflow.net/questions/491563 -/

open scoped BigOperators

namespace OMA.S_mo_491563

/-- The coefficient of X ^ n in (X ^ 2 + X + 1) ^ n. -/
def centralTrinomial (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * (2 * k).choose k

/-- The polynomial with the source's weighted central trinomial coefficients. -/
noncomputable def weightedTrinomial (e n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k
    ((n.choose k ^ e * centralTrinomial k * centralTrinomial (n - k)) : ℤ)

/-- Coefficientwise log-convexity of the tail whose first term is P 4. -/
def qLogConvexTail (P : ℕ → Polynomial ℤ) : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ k : ℕ, 0 ≤ (P n * P (n + 2) - P (n + 1) ^ 2).coeff k

theorem main :
    (∀ n b e : ℕ, 1 < n → 1 < e → centralTrinomial n ≠ b ^ e) ∧
      qLogConvexTail (weightedTrinomial 2) ∧ qLogConvexTail (weightedTrinomial 1) := by
  sorry

end OMA.S_mo_491563
