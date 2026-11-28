import Mathlib

/-!
# Generalised harmonic numbers whose numerator plus denominator is prime

Source: https://math.stackexchange.com/questions/2931716
Conjecture (asker's friend): for every `i ≥ 1` there is a natural number `r` such that, writing
`∑_{n=1}^{i} 1/n^r = p/q` in lowest terms, `p + q` is prime.

Conventions. `r ≥ 1`; `p/q` is the reduced form given by `Rat.num` and `Rat.den`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_2931716

theorem main :
    ∀ i : ℕ, 1 ≤ i → ∃ r : ℕ, 1 ≤ r ∧
      let s : ℚ := ∑ n ∈ Finset.Icc 1 i, 1 / (n : ℚ) ^ r
      (s.num.natAbs + s.den).Prime := by
  sorry

end OMA.S_mse_2931716
