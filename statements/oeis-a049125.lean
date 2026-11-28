import Mathlib

/-!
# A049125: Inversion sequences avoiding e(i) >= e(k) for i < j < k

Source: https://oeis.org/A049125
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A049125: Revert transform of (1 + x - x^2) / (1 + x)^2.

Statement:
Conjecturally, the number of sequences (e(1), ..., e(n-1)), 0 <= e(i) < i, such that there is
no triple i < j < k with e(i) >= e(k). [Martinez and Savage, 2.10]

Conventions:
- The revert transform `A(x) = Sum_{n >= 1} a(n) * x^n` of `x * (1 + x - x^2) / (1 + x)^2`
  is characterized in `PowerSeries ℚ` by `(1 + A)^2 * X = A * (1 + A - A^2)`.
-/

namespace OMA.S_oeis_a049125

/-- Number of inversion sequences of length `m` avoiding `e(i) >= e(k)` for `i < j < k`. -/
noncomputable def invSeqCount (m : ℕ) : ℕ :=
  {e : Fin m → ℕ | (∀ i : Fin m, e i ≤ i.val) ∧
    ∀ i j k : Fin m, i < j → j < k → e i < e k}.ncard

/-- Ordinary generating function `Sum_{n >= 1} invSeqCount (n - 1) * X^n`. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (invSeqCount (n - 1) : ℚ))

theorem main :
    (1 + A) ^ 2 * PowerSeries.X = A * (1 + A - A ^ 2) := by
  sorry

end OMA.S_oeis_a049125
