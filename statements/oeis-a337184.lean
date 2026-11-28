import Mathlib

/-!
# A337184: Numbers divisible by their first digit and their last digit.

Source: https://oeis.org/A337184
Credit: @EmircanEsen

Conjecture (Charles R Greathouse IV, Dec 02 2024): 3n < a(n) < 7n for n > 75.

Formalization notes:
* Digits are decimal. A number ending in `0` is not a term: it would have to be divisible by `0`.
  (The OEIS data skips `10, 20, …` accordingly.)
* The first digit of `m > 0` is the last entry of `Nat.digits 10 m` (least significant digit
  first); the last digit is `m % 10`.
* `a n = Nat.nth IsTerm (n - 1)` restores the offset 1: `a 1 = 1`, …, `a 10 = 11`, `a 24 = 101`.
  The set of terms is infinite (every repdigit is a term), so `Nat.nth` never takes its junk value.
* Checked numerically for `75 < n ≤ 2·10⁶` (the ratio `a(n)/n` stays in `[3.05, 6.19]`); the
  inequality fails at `n = 75`.
-/

namespace OMA.S_oeis_a337184

/-- `m` is a term: positive, its last digit is nonzero and divides `m`, and its first digit
divides `m`. -/
def IsTerm (m : ℕ) : Prop :=
  0 < m ∧ m % 10 ≠ 0 ∧ m % 10 ∣ m ∧ (Nat.digits 10 m).getLastD 0 ∣ m

/-- A337184 with offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- For `n > 75`, `3n < a(n) < 7n`. -/
theorem main : ∀ n : ℕ, 75 < n → 3 * n < a n ∧ a n < 7 * n := by
  sorry

end OMA.S_oeis_a337184
