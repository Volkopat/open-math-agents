import Mathlib

/-!
# OEIS A009190: missing '2p-twin peaks'

Source: https://oeis.org/A009190
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For `p = prime(n)`, a `2p`-twin peak is an `x` with `lpf(x) = lpf(x + 2p) = p` and `lpf(y) < p`
for all `x < y < x + 2p` (`lpf` = least prime factor); `a(n)` is the least such `x`, or `-1` if
none exists. Conjecture (weak, OEIS entry): `a(n) = -1` for `14 ≤ n ≤ 19`, i.e. there is no
`2p`-twin peak for `p = prime(n)`, `14 ≤ n ≤ 19` (`p = 43, 47, 53, 59, 61, 67`).

Conventions:
* `prime(n)` is the `n`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`; `lpf` is
  `Nat.minFac`, and `x ≥ 2`.
-/

namespace OMA.S_oeis_a009190

/-- `x` is a `2p`-twin peak. -/
def IsTwinPeak (p x : ℕ) : Prop :=
  2 ≤ x ∧ Nat.minFac x = p ∧ Nat.minFac (x + 2 * p) = p ∧
    ∀ y, x < y → y < x + 2 * p → Nat.minFac y < p

/-- No `2p`-twin peaks for `p = prime(n)`, `14 ≤ n ≤ 19`. -/
theorem main : ∀ n : ℕ, 14 ≤ n → n ≤ 19 → ∀ x : ℕ, ¬ IsTwinPeak (Nat.nth Nat.Prime (n - 1)) x := by
  sorry

end OMA.S_oeis_a009190
