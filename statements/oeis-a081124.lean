import Mathlib

/-!
# A081124: Binomial transform of floor(n/2)!

Source: https://oeis.org/A081124
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Binomial transform of floor(n/2)!.
Conjecture: 2*a(n) - 4*a(n-1) + (-n+2)*a(n-2) + (n-1)*a(n-3) = 0.
-/

namespace OMA.S_oeis_a081124

def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * (Nat.factorial (k / 2) : ℤ)

theorem main :
    ∀ n : ℕ, 3 ≤ n →
      2 * a n - 4 * a (n - 1) + (-(n : ℤ) + 2) * a (n - 2) + ((n : ℤ) - 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081124
