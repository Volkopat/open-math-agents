import Mathlib

/-!
# OEIS A045650: numbers not of the form k + ⌊log k⌋

Source: https://oeis.org/A045650
`a n` lists the numbers that cannot be expressed as `k + ⌊log k⌋` with `k` a (positive)
integer (3, 9, 23, 58, …). Conjecture: `lim a(n) = e^n`, read as `a(n) ~ e^n`.

Conventions. `k ≥ 1` and `log` is the natural logarithm; offset `1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a045650

open Filter Asymptotics Real

/-- `m` is not of the form `k + ⌊log k⌋`. -/
def P (m : ℕ) : Prop := ¬ ∃ k : ℕ, 1 ≤ k ∧ (m : ℤ) = k + ⌊log k⌋

/-- A045650, indexed from `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

theorem main : (fun n : ℕ => (a n : ℝ)) ~[atTop] fun n => exp n := by
  sorry

end OMA.S_oeis_a045650
