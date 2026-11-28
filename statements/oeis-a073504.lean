import Mathlib

/-!
# OEIS A073504

Source: https://oeis.org/A073504 (OEIS Foundation, CC BY-SA 4.0).
This is the formula conjectured by Alan Michael Gómez Calderón and proved by Sela Fried
in Corollary 15 of https://arxiv.org/abs/2607.24832. The recurrence is indexed from zero.
The asserted limit is given as an eventual constant, and the denominator is cleared.
-/

namespace OMA.S_oeis_a073504

/-- The rounded recurrence defining A073504. -/
def term (n : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => n
  | k + 2 => term n k / 2 + term n (k + 1) / 2

/-- A decreasing measure for stripping base `-2` digits. -/
private def measure (d : ℤ) : ℕ :=
  (if d < 0 then 1 - 2 * d else 2 * d).toNat

/-- The sum of the base `-2` digits, extended to signed integers. -/
def digitSum (d : ℤ) : ℤ :=
  if d = 0 then 0 else d % 2 + digitSum (d / (-2))
termination_by measure d
decreasing_by
  unfold measure
  by_cases h : d < 0 <;> by_cases h' : d / (-2) < 0 <;>
    simp [h, h'] <;> omega

/-- The recurrence stabilizes at `2 * (n - A027615(n)) / 3`. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ v : ℤ, 3 * v = 2 * ((n : ℤ) - digitSum n) ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → term n k = v := by
  sorry

end OMA.S_oeis_a073504
