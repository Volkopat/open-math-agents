import Mathlib

/-!
# A098608: a(n) = 100^n.

Source: https://oeis.org/A098608
Credit: @divmxnd0x

Conjecture (Manfred Boergens, Feb 10 2025): the terms `100^n` (`n ≥ 0`) are the only positive
squares whose decimal digits all lie in `{0, 1}`.

Formalization notes:
* "Positive square" is `m ^ 2` with `m ≥ 1`; "digits in `{0, 1}`" says that every decimal digit of
  `m ^ 2` (as listed by `Nat.digits 10`, which has no leading zeros) is at most `1`.
* The positive squares below `200000 ^ 2` with all digits in `{0, 1}` are 1, 100, 10000, 1000000,
  100000000, 10000000000, all of the form `100 ^ n`.
-/

namespace OMA.S_oeis_a098608

/-- Boergens' conjecture: a positive square whose decimal digits are all `0` or `1` is a power
of `100`. -/
theorem main : ∀ m : ℕ, 0 < m → (∀ d ∈ Nat.digits 10 (m ^ 2), d ≤ 1) → ∃ n : ℕ, m ^ 2 = 100 ^ n := by
  sorry

end OMA.S_oeis_a098608
