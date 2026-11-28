import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace OMA.S_oeis_a268553

/-- Coefficient of `(u v w)^(2n)` in `1 / (1 - u v - u w - v w) = ∑_{a,b,c} (a+b+c)!/(a!b!c!) u^{a+b} v^{a+c} w^{b+c}`. -/
def diagFactor (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (2 * n + 1),
    ∑ b ∈ Finset.range (2 * n + 1),
      ∑ c ∈ Finset.range (2 * n + 1),
        if a + b = 2 * n ∧ a + c = 2 * n ∧ b + c = 2 * n then
          (a + b + c).factorial / (a.factorial * b.factorial * c.factorial)
        else 0

/-- OEIS A268553: diagonal of `1 / ((1 - u v - u w - v w) * (1 - x y - x z - y z))`
at index `2n` (where odd-index diagonal terms vanish). -/
def a268553 (n : ℕ) : ℕ :=
  diagFactor n * diagFactor n

/-- OEIS A268553 (R. J. Mathar conjecture): for all `n ≥ 1`,
`n^4 * a(n) = 9 * (3n - 1)^2 * (3n - 2)^2 * a(n - 1)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → n ^ 4 * a268553 n = 9 * (3 * n - 1) ^ 2 * (3 * n - 2) ^ 2 * a268553 (n - 1) := by
  sorry

end OMA.S_oeis_a268553
