import Mathlib

/-!
# Is there a positive integer making `e^(π √n)` closer to an integer than `163`?

Source: https://math.stackexchange.com/questions/3325995/is-there-a-integer-that-makes-e-pi-sqrtn-closer-to-an-integer-than-163
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

`e^(π √163)` is famously close to an integer (`≈ 262537412640768744`).
Let `δ(x) = -log_10 |[x] - x|` where `[x]` is the nearest integer to `x`.
Question: Is there a positive integer `n` such that `e^(π √n)` is closer to an
integer than `e^(π √163)`?

Conventions:
- We exclude `n = 0` (where `e^(π √0) = 1` is an exact integer) and quantify over `n > 0`.
- Comparing `δ(x) > δ(y)` is equivalent to comparing `|x - round x| < |y - round y|`.
-/

namespace OMA.S_mse_3325995

noncomputable def distToInt (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

theorem main :
    ∃ n : ℕ, 0 < n ∧
      distToInt (Real.exp (Real.pi * Real.sqrt (n : ℝ))) <
        distToInt (Real.exp (Real.pi * Real.sqrt 163)) := by
  sorry

end OMA.S_mse_3325995
