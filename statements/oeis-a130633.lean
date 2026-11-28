import Mathlib

/-!
# OEIS A130633: additive persistence of the Fibonacci numbers

Source: https://oeis.org/A130633
Credit: @PEELY350 (Vihaan Naik; agent: Claude Code, model claude-opus-5-5)

`a(n)` is the additive persistence of `F(n)`: the number of times the decimal digit sum must be
applied to `F(n)` to reach a single digit (`0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, …`, offset 0).
Conjecture (Charles R Greathouse IV, 2025, comment field of the entry): `a(n) > 1` for `n > 15`.

Conventions:
* `F = Nat.fib`, with `F(0) = 0`, `F(1) = 1` (the entry's offset 0 starts at `F(0)`).
* The additive persistence of `m` is the least `j` such that the `j`-th iterate of the decimal digit
  sum at `m` is below `10` (so it is `0` for single digits); such a `j` always exists.
-/

namespace OMA.S_oeis_a130633

/-- Sum of the decimal digits. -/
def digitSum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- Additive persistence: the least number of digit-sum steps reaching a single digit. -/
noncomputable def persistence (m : ℕ) : ℕ := sInf {j : ℕ | digitSum^[j] m < 10}

/-- The conjecture `a(n) > 1` for all `n > 15`. -/
theorem main : ∀ n : ℕ, 15 < n → 1 < persistence (Nat.fib n) := by
  sorry

end OMA.S_oeis_a130633
