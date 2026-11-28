import OMAReductions.R_Kaplansky_idempotent_conjecture_R1

-- Step Kaplansky.idempotent_conjecture.R1.H1: hypothesis H1 of reduction
-- Kaplansky.idempotent_conjecture.R1.
-- Written with Claude Code (AI-assisted).
-- For a unique-product group, K[G] has no zero divisors (Mathlib), so an idempotent `a`,
-- with `a * (a - 1) = 0`, is `0` or `1`.

theorem OMA.solution : OMA.R_Kaplansky_idempotent_conjecture_R1.H1 := by
  intro K _ G _ _ a ha
  exact IsIdempotentElem.iff_eq_zero_or_one.mp ha
