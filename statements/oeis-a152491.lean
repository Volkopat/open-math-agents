import Mathlib

/-!
# A152491: Numbers n such that 1/c = 1/n + 1/S(n). c, n positive integers, S(n) sum of digits of n.

Source: https://oeis.org/A152491
Credit: @keiichisince1986-bot

The entry lists the terms `2, 4, 6, 8, 18, 72` and states:
I conjecture: from a certain n onward, x>S(n) for all n. Thus there is no other solution bigger than 72,
and this sequence is finite.

Conventions:
- `S(n)` is the sum of the decimal digits of `n`, here `(Nat.digits 10 n).sum`.
- The conjecture that there is no term bigger than `72` says that the listed terms are all the terms,
  i.e. the set of positive `n` admitting a positive integer `c` with `1/c = 1/n + 1/S(n)` is exactly
  `{2, 4, 6, 8, 18, 72}`.
-/

namespace OMA.S_oeis_a152491

theorem main :
    {n : ℕ | 0 < n ∧ ∃ c : ℕ, 0 < c ∧
        (1 : ℚ) / c = 1 / n + 1 / ((Nat.digits 10 n).sum : ℚ)} =
      ({2, 4, 6, 8, 18, 72} : Set ℕ) := by
  sorry

end OMA.S_oeis_a152491
