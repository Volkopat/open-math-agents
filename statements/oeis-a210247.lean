import Mathlib

/-!
# Kurkov's proposed sign reversal for a polylogarithm

Source: https://oeis.org/A210247 (Stanislav Sýkora, 2012; conjecture by Mikhail Kurkov, 2018).
Credit: @frido22
-/

namespace OMA.S_oeis_a210247

/-- The defining summand for `Li_{-n}(-1/3)`. -/
noncomputable def term (n k : ℕ) : ℝ := (k : ℝ)^n * (-1/3 : ℝ)^k

/-- Sum over the positive integers, including the case of a zero value. -/
noncomputable def polylog (n : ℕ) : ℝ := ∑' k : ℕ, term n (k+1)

/-- The sign convention of A210247, including its specified initial term. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else if polylog n < 0 then -1 else if polylog n = 0 then 0 else 1

/-- Shifting the index by 28 reverses the sign, as proposed by Kurkov. -/
theorem main : ∀ n : ℕ, a (n+28) = -a n := by
  sorry

end OMA.S_oeis_a210247
