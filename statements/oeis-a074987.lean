import Mathlib

/-!
# A074987: a(n) is the least m not equal to n such that phi(m) = phi(n)

Source: https://oeis.org/A074987
Credit: @FFD-007

Conjecture (T. D. Noe): `a(n) <= 2 * n`, where `a(n)` is the least `m` different from
`n` such that `phi(m) = phi(n)`. Equivalently, every positive integer `n` has a distinct
totient twin `m <= 2 * n`: some `m ≠ n` with `m ≤ 2 * n` and `Nat.totient m = Nat.totient n`.

The formulation below is exactly `a(n) ≤ 2 * n` for `n ≥ 1` (the range of the sequence,
which begins `a(1) = 2`, and where `a(11) = 2 * 11` shows the constant 2 cannot be lowered):
by well-ordering, the least such `m` exists exactly when some such `m` exists, and then
`a(n) ≤ 2 * n` holds exactly when some such `m` with `m ≤ 2 * n` exists. So the statement
also covers the implicit existence of `a(n)`, which for even `n` is part of the conjecture.
-/

namespace OMA.S_oeis_a074987

/-- **A074987 conjecture (T. D. Noe)**: every positive integer `n` has a distinct
totient twin `m ≤ 2 * n`, i.e. some `m ≠ n` with `m ≤ 2 * n` and
`Nat.totient m = Nat.totient n`. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m, m ≠ n ∧ m ≤ 2 * n ∧ Nat.totient m = Nat.totient n := by
  sorry

end OMA.S_oeis_a074987
