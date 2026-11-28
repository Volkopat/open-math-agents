import Mathlib

/-!
# A002587: Quadratic lower bound infinitely often for the largest prime factor of 2^n + 1

Source: https://oeis.org/A002587
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A002587: Largest prime factor of 2^n + 1.

Statement:
Charles proves that a(n) >> n^(4/3) infinitely often under the abc conjecture, and reports
that Granville has improved this to a(n) >> n^2 (also under abc). `main` states the n^2 bound
unconditionally.

Conventions:
- We formalize the conjectured lower bound `a(n) >> n^2` infinitely often: there exists a
  positive constant `c > 0` such that for infinitely many `n`, the largest prime factor of
  `2^n + 1` is at least `c * n^2`.
-/

namespace OMA.S_oeis_a002587

/-- The largest prime factor of `m`. -/
noncomputable def largestPrimeFactor (m : ℕ) : ℕ :=
  sSup {p : ℕ | Nat.Prime p ∧ p ∣ m}

theorem main :
    ∃ c : ℝ, 0 < c ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c * (n : ℝ) ^ 2 ≤ (largestPrimeFactor (2 ^ n + 1) : ℝ) := by
  sorry

end OMA.S_oeis_a002587
