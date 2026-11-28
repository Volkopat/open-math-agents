import Mathlib

/-!
# A363196: the least `k` such that the rightmost 7 of `3^k` is in the `10^n` position

Source: https://oeis.org/A363196
Credit: @avivorly

A363196 (Robert Israel, May 2023): `a(n)` is the least `k` such that the rightmost 7 in the decimal expansion of `3^k`
is in the `(10^n)`'s position, or `-1` if there is no such `k`. Offset 0; the data begins
`3, -1, 6, 37, 50, 14, 18, 38, 28, 25, 48, 188, ...` (`a(0) = 3`, `a(1) = -1`).

Conjecture (in the entry): `a(n) = -1` only for `n = 1`.

Conventions:
- The decimal digits of `x` are `Nat.digits 10 x`, least significant first, so the digit at index `i` is the
  coefficient of `10^i`, the `(10^i)`'s position. An index past the last digit reads as `0` (`List.getD _ i 0`),
  which is not 7, so a 7 at index `n` is a genuine digit of `x`.
- The rightmost 7 of `x` is in the `(10^n)`'s position iff the digit of `x` at index `n` is 7 and no digit of `x` at
  an index `i < n` is 7 (`RightmostSevenAt x n`).
- `a n : ℤ` is the least `k` with `RightmostSevenAt (3^k) n` (`Nat.find`, cast to `ℤ`) when such a `k` exists, and
  `-1` otherwise. `k` ranges over all natural numbers, `k = 0` included (the entry's Maple program starts at `k = 1`,
  its Python program at `k = 0`); this changes no term, since `3^0 = 1` has no digit 7.
- The conjecture is read as: for every `n`, `a n = -1` iff `n = 1`. As `a n ≥ 0` whenever some `k` works, this says
  that no `k` works for `n = 1` (the data's `a(1) = -1`) and that some `k` works for every `n ≠ 1`.
-/

namespace OMA.S_oeis_a363196

/-- The rightmost 7 in the decimal expansion of `x` is in the `(10^n)`'s position: the decimal digit of `x` at index
`n` (`Nat.digits 10 x`, least significant first; `0` past the last digit) is 7, and no digit at an index `i < n`
is 7. -/
def RightmostSevenAt (x n : ℕ) : Prop :=
  (Nat.digits 10 x).getD n 0 = 7 ∧ ∀ i < n, (Nat.digits 10 x).getD i 0 ≠ 7

open Classical in
/-- A363196: `a n` is the least `k` such that the rightmost 7 in the decimal expansion of `3^k` is in the
`(10^n)`'s position, or `-1` if there is no such `k`. -/
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ k : ℕ, RightmostSevenAt (3 ^ k) n then (Nat.find h : ℤ) else -1

/-- Conjecture (A363196): `a(n) = -1` only for `n = 1`. -/
theorem main : ∀ n : ℕ, a n = -1 ↔ n = 1 := by
  sorry

end OMA.S_oeis_a363196
