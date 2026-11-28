import Mathlib

/-!
# A prime in (n², n² + ⌊(n+1)/2⌋] for every n ≠ 5?

Source: https://math.stackexchange.com/questions/5154430

For `n ≥ 1` let `I_n = (n², n² + ⌊(n+1)/2⌋]`. The interval `I_5 = (25, 28]` contains no prime,
and `n = 5` appears to be the only exception up to `n = 10^6` (OEIS A402211 counts the primes
in `I_n`). The question asks whether `n = 5` is the only exception.

Formalization notes:
* `main` states that `n = 5` is the only exception: every `n ≥ 1` with `n ≠ 5` has a prime
  `p` with `n² < p ≤ n² + ⌊(n+1)/2⌋`, where `(n + 1) / 2` is floor division in `ℕ`.
-/

namespace OMA.S_mse_5154430

/-- For every `n ≥ 1` other than `5` there is a prime in `(n², n² + ⌊(n+1)/2⌋]`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ≠ 5 →
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p ≤ n ^ 2 + (n + 1) / 2 := by
  sorry

end OMA.S_mse_5154430
