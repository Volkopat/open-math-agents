import Mathlib

/-!
# A078535: Coefficients of power series that satisfies A(x)^6 - 36x*A(x)^7 = 1, A(0)=1.

Source: https://oeis.org/A078535
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

If A(x) = Sum_{k>=0} a(k)*x^k with A(0) = 1 satisfies A(x)^n - (n^2)*x*A(x)^(n+1) = 1,
then a(n-1) = n^(2n-3) and a(2n-1) = n^(4n-2) (conjecture).
-/

namespace OMA.S_oeis_a078535

/-- Cauchy product of two formal power series over `ℤ`. -/
def mulPS (f g : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), f i * g (k - i)

/-- The `m`-th power of a formal power series over `ℤ`. -/
def powPS (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, k => mulPS (powPS f m) f k

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∀ a : ℕ → ℤ,
      a 0 = 1 →
      (∀ k : ℕ, 1 ≤ k → powPS a n k - (n : ℤ) ^ 2 * powPS a (n + 1) (k - 1) = 0) →
      a (n - 1) = (n : ℤ) ^ (2 * n - 3) ∧ a (2 * n - 1) = (n : ℤ) ^ (4 * n - 2) := by sorry

end OMA.S_oeis_a078535
