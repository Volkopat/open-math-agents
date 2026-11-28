import Mathlib

/-!
# A130694: exponents of powers of 2 that contain all ten digits

Source: https://oeis.org/A130694
Credit: @sntntHb

A130694 (offset 1) lists, in increasing order, the exponents `k` such that the decimal expansion of `2^k` contains each of the ten digits `0, ..., 9`:
`68, 70, 79, 82, 84, 87, 88, 89, 94, 95, ...`. The entry records the conjecture
  `a(n) = n + 91 for n >= 78`.
Proposed by Chai Wah Wu; equivalently, every power `2^k` with `k ≥ 169` contains all ten digits.
The decimal digits of a number are Mathlib's `Nat.digits 10` (least significant digit first), and
`a(n)` is `Nat.nth` of the defining predicate at `n - 1`. If only finitely many exponents had
the property, `Nat.nth` would return `0` beyond them and the statement would fail, as it should.
-/

namespace OMA.S_oeis_a130694

/-- The defining property of A130694. -/
def P (k : ℕ) : Prop := ∀ d : ℕ, d < 10 → d ∈ Nat.digits 10 (2 ^ k)

/-- `a n`: the `n`-th exponent with property `P` (offset 1; OEIS A130694). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- The conjecture in OEIS A130694. -/
theorem main : ∀ n : ℕ, 78 ≤ n → a n = n + 91 := by
  sorry

end OMA.S_oeis_a130694
