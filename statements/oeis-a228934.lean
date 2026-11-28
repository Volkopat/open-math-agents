import Mathlib

/-!
# Signed optimal ascending continued fraction of √44 − 6

The expansion uses Artico's nearest-integer algorithm from A228929. Start at
the fractional part `√44 − 6`, and, with residual `z`, round `1/|z|` to get
the magnitude of the next digit. The digit has the sign of `z`.
The first residual supplies digit one, as in the published expansion.

Sources: https://oeis.org/A228934 and https://oeis.org/A228929
(OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a228934

noncomputable def magnitude (z : ℝ) : ℤ := round (1 / |z|)

noncomputable def step (z : ℝ) : ℝ := |z| * magnitude z - 1

noncomputable def residual : ℕ → ℝ
  | 0 => Real.sqrt 44 - 6
  | n+1 => step (residual n)

noncomputable def digit (z : ℝ) : ℤ :=
  if z < 0 then -magnitude z else magnitude z

noncomputable def a (n : ℕ) : ℤ := digit (residual (n-1))

theorem main : (∀ n : ℕ, 4 ≤ n → a n < 0) ∧
    ∀ n : ℕ, 3 ≤ n →
      a (2*n) = 4*a (2*n-1)-4 ∧ a (2*n+1) = -2*(a (2*n-1))^2+1 := by
  sorry

end OMA.S_oeis_a228934
