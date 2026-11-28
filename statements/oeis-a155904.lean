import Mathlib

/-!
# OEIS A155904: odd numbers as `p + 2^x + 5·2^y`

Source: https://oeis.org/A155904
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ways to write `2n - 1` as `p + 2^x + 5·2^y` with `p` an odd prime and
`x, y` positive integers. Conjecture (Sun, 2009): `a(n) > 0` for `n ≥ 8`, i.e. every odd integer
`m ≥ 15` is the sum of an odd prime, a positive power of `2` and five times a positive power of
`2`.
-/

namespace OMA.S_oeis_a155904

/-- Every odd `m ≥ 15` is `p + 2^x + 5·2^y` with `p` an odd prime and `x, y ≥ 1`. -/
theorem main : ∀ m : ℕ, 15 ≤ m → Odd m →
    ∃ p x y : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ x ∧ 1 ≤ y ∧ m = p + 2 ^ x + 5 * 2 ^ y := by
  sorry

end OMA.S_oeis_a155904
