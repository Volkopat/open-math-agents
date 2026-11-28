import Mathlib

/-!
# A076905: a(1)=1, a(n)=n-a(n-1)+a(a(n-1))-a(a(a(n-1))).

Source: https://oeis.org/A076905
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: let c be the real root of 1-2*x+x^2-x^3, c=0.5698402909980532659113..., then a(n)=floor(cn) +0 /+ 1
-/

namespace OMA.S_oeis_a076905

/-- Defining recurrence of A076905. -/
def IsA076905 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → a n = n - a (n - 1) + a (a (n - 1)) - a (a (a (n - 1)))

/-- Conjecture: if `c` is the real root of `1 - 2x + x^2 - x^3 = 0`, then for all `n ≥ 1`,
`a(n)` is either `⌊c * n⌋` or `⌊c * n⌋ + 1`. -/
theorem main :
    ∀ a : ℕ → ℕ, IsA076905 a →
      ∀ c : ℝ, 1 - 2 * c + c ^ 2 - c ^ 3 = 0 →
        ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = ⌊c * (n : ℝ)⌋ ∨ (a n : ℤ) = ⌊c * (n : ℝ)⌋ + 1 := by sorry

end OMA.S_oeis_a076905
