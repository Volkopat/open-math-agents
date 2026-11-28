import OMAReductions.R_HardyLittlewood_first_hardy_littlewood_conjecture_R1

-- Step HardyLittlewood.first_hardy_littlewood_conjecture.R1.H1: hypothesis H1 of reduction HardyLittlewood.first_hardy_littlewood_conjecture.R1
-- Credit: @hoodbroskillson

/-! The reduction file (merged from pull request 12886, same author) proves this hypothesis in full as
`euler_product`: every local factor is within `O(k^2 / q^2)` of one, so the logarithms are summable and the
Euler product over the odd primes converges to a positive real. This file files that proof as the step. -/

theorem OMA.solution : OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R1.H1 :=
  OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R1.euler_product
