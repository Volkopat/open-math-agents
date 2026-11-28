import Mathlib

/-!
# A217157: least k such that the decimal expansion of n^k contains two consecutive identical digits

Source: https://oeis.org/A217157
Credit: @warshanks

For `n ≥ 2` (offset 2), `a(n)` is the least `k` such that the decimal expansion of `n^k` contains
two consecutive identical digits. The entry records one conjecture (Chai Wah Wu, 2019):

  `1 ≤ a(n) ≤ 16` for `n > 1`, and `a(n) < 16` for `n > 2`.

(The entry links a proof by Robert Israel that `a(n)` exists and is bounded, by a bound that the
proof does not make explicit; the bound `16` is the conjecture.)

Since `n^0 = 1` has a single digit, the least such `k` is at least `1` whenever it exists, so
`1 ≤ a(n) ≤ 16` says exactly that some `k` with `1 ≤ k ≤ 16` works, and `a(n) < 16` that some `k`
with `1 ≤ k ≤ 15` works. `main` states the two parts in this form.

Two digits are consecutive when they are adjacent in the decimal expansion; Mathlib's
`Nat.digits 10 m` lists the digits of `m` from the least significant one, which does not change
which digits are adjacent.
-/

namespace OMA.S_oeis_a217157

/-- The decimal expansion of `m` contains two consecutive identical digits. -/
def HasRepeatedDigit (m : ℕ) : Prop :=
  ∃ i : ℕ, ∃ h : i + 1 < (Nat.digits 10 m).length,
    (Nat.digits 10 m)[i] = (Nat.digits 10 m)[i + 1]

/-- The conjecture of OEIS A217157: `1 ≤ a(n) ≤ 16` for `n > 1` and `a(n) < 16` for `n > 2`, where
`a(n)` is the least `k` such that `n^k` has two consecutive identical decimal digits. -/
theorem main : (∀ n : ℕ, 1 < n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 16 ∧ HasRepeatedDigit (n ^ k)) ∧
    (∀ n : ℕ, 2 < n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 15 ∧ HasRepeatedDigit (n ^ k)) := by
  sorry

end OMA.S_oeis_a217157
