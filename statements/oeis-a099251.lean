import Mathlib

/-!
# A099251: Integral representation for the bisection of Riordan numbers (Motzkin sums)

Source: https://oeis.org/A099251
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A099251: Bisection of Motzkin sums (A005043).

Statement:
Conjecture: a(n) = (2/Pi)*Integral_{t=0..1} sqrt((1 - t)/t)*(1 - 8*t + 16*t^2)^n dt.

Conventions:
- The Riordan numbers (Motzkin sums `A005043`) satisfy `R(0) = 1`, `R(1) = 0`, and
  `(m + 3) * R(m + 2) = (m + 1) * (2 * R(m + 1) + 3 * R(m))` for `m >= 0`.
- `A099251(n) = R(2 * n)`.
-/

namespace OMA.S_oeis_a099251

/-- The Riordan numbers (Motzkin sums `A005043`). -/
def riordan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | m + 2 => (m + 1) * (2 * riordan (m + 1) + 3 * riordan m) / (m + 3)

theorem main :
    ∀ n : ℕ,
      (riordan (2 * n) : ℝ) =
        (2 / Real.pi) *
          ∫ t in (0 : ℝ)..1, Real.sqrt ((1 - t) / t) * (1 - 8 * t + 16 * t ^ 2) ^ n := by
  sorry

end OMA.S_oeis_a099251
