import Mathlib

/-!
# A389000: Smallest k such that the sums of digits of k and k^2 in base 10 are both divisible by n
or a(n) = -1 if no such k exists.

Source: https://oeis.org/A389000
Credit: @Squee451

Data (offset 1): 1, 2, 3, 13, 19, 24, 149, 583, 9, 19, 74, 264, 2236, 1999, 1374, 19499, 299833, 99, ...

The entry's comment: Conjecture: a(9*m+5) = 2*10^(2*m+1)-1 for m >= 0.
(For m = 0, 1: a(5) = 19 and a(14) = 1999, as in the data.)

Conventions.
* k ranges over the positive integers: a(1) = 1 in the data, whereas k = 0 has digit sum 0, which
  every n divides.
* The conjecture is stated with `IsLeast`: the number `2*10^(2*m+1) - 1` has the property and no
  smaller positive integer has it. In particular such a k exists, so the "-1" case of the definition
  does not occur at these indices.
* `2 * 10 ^ (2 * m + 1) - 1` is a natural-number subtraction that does not truncate.
-/

namespace OMA.S_oeis_a389000

/-- Sum of the decimal digits of `k`. -/
def digitSum (k : ℕ) : ℕ := (Nat.digits 10 k).sum

/-- `k` is a positive integer such that the digit sums of `k` and of `k^2` are both divisible by `n`. -/
def Good (n k : ℕ) : Prop := 0 < k ∧ n ∣ digitSum k ∧ n ∣ digitSum (k ^ 2)

/-- For every `m ≥ 0`, the smallest good `k` for `n = 9*m + 5` is `2*10^(2*m+1) - 1`. -/
theorem main : ∀ m : ℕ, IsLeast {k : ℕ | Good (9 * m + 5) k} (2 * 10 ^ (2 * m + 1) - 1) := by
  sorry

end OMA.S_oeis_a389000
