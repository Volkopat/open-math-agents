import Mathlib

/-!
# A071823: Lower bound n/2 + sqrt(n) for numbers <= n with largest prime factor == 3 (mod 4)

Source: https://oeis.org/A071823
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A071823: Number of numbers x <= n with largest prime factor of the form 4k+3.

Statement:
Conjecture: for n > 1000, a(n) - n/2 > sqrt(n).
-/

namespace OMA.S_oeis_a071823

/-- Largest prime factor of `x` (0 if `x <= 1`). -/
noncomputable def largestPrimeFactor (x : ℕ) : ℕ :=
  sSup {p : ℕ | Nat.Prime p ∧ p ∣ x}

/-- `A071823(n)`: number of `1 <= x <= n` whose largest prime factor is `3 (mod 4)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun x => largestPrimeFactor x % 4 = 3)).card

theorem main :
    ∀ n : ℕ, 1000 < n → (a n : ℝ) - (n : ℝ) / 2 > Real.sqrt (n : ℝ) := by
  sorry

end OMA.S_oeis_a071823
