import Mathlib

/-!
# A074399: Erdos's conjecture on the largest prime divisor of n(n+1)

Source: https://oeis.org/A074399
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A074399: a(n) is the largest prime divisor of n(n+1).

Statement:
Erdos conjectures that for every e > 0, a(n) < (log n)^(2+e) infinitely often,
while a(n) < (log n)^(2-e) only finitely often.
-/

namespace OMA.S_oeis_a074399

/-- Largest prime factor of `m`. -/
noncomputable def largestPrimeFactor (m : ℕ) : ℕ :=
  sSup {p : ℕ | Nat.Prime p ∧ p ∣ m}

theorem main :
    ∀ ε : ℝ, 0 < ε →
      Set.Infinite {n : ℕ | 2 ≤ n ∧ (largestPrimeFactor (n * (n + 1)) : ℝ) < (Real.log (n : ℝ)) ^ (2 + ε)} ∧
      Set.Finite {n : ℕ | 2 ≤ n ∧ (largestPrimeFactor (n * (n + 1)) : ℝ) < (Real.log (n : ℝ)) ^ (2 - ε)} := by
  sorry

end OMA.S_oeis_a074399
