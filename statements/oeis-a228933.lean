import Mathlib

/-!
# Signed optimal ascending continued fraction of φ − 1

The expansion uses Artico's nearest-integer algorithm from A228929. Start at
the fractional part `φ − 1`, and, with residual `z`, round `1/|z|` to get
the magnitude of the next digit. The digit has the sign of `z`.
The first residual supplies digit one, as in the published expansion.

Sources: https://oeis.org/A228933 and https://oeis.org/A228929
(OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a228933

noncomputable def magnitude (z : ℝ) : ℤ := round (1 / |z|)

noncomputable def step (z : ℝ) : ℝ := |z| * magnitude z - 1

noncomputable def residual : ℕ → ℝ
  | 0 => Real.goldenRatio - 1
  | n+1 => step (residual n)

noncomputable def digit (z : ℝ) : ℤ :=
  if z < 0 then -magnitude z else magnitude z

noncomputable def a (n : ℕ) : ℤ := digit (residual (n-1))

theorem main : a 1 = 2 ∧ a 2 = 4 ∧ a 3 = -18 ∧
    (∀ n : ℕ, 4 ≤ n → 0 < a n) ∧
    (∀ n : ℕ, 3 ≤ n → a (n+1) = (a n)^2 - 2) := by
  sorry

end OMA.S_oeis_a228933
