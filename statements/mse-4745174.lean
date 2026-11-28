import Mathlib

/-!
# Primes as a primorial minus a prime

Source: https://math.stackexchange.com/questions/4745174
Conjecture (asker): every prime `p ≥ 7` can be written as `p = p_k# - q` with `p_k#` a
primorial and `q` a prime.

Conventions. Primorials are Mathlib's `primorial m` (the product of the primes `≤ m`); every
`p_k#` is of this form and every `primorial m` equals some `p_k#` (or `1`, which is too small
to matter here).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_4745174

theorem main :
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∃ m q : ℕ, q.Prime ∧ primorial m = p + q := by
  sorry

end OMA.S_mse_4745174
