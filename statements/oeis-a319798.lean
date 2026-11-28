import Mathlib

/-!
# A319798: Smallest fixed points (>0) of the base-n Kaprekar map.

Source: https://oeis.org/A319798. Related: https://oeis.org/A000567 (octagonal numbers n*(3*n-2))
Credit: @Squee451

Data (offset 2): 9, 184, 30, 8, 105, 1922263344, 21, 41520, 495, 40, 858, 3488424, 65, 30996, 2040, ...

The entry's comment: Conjecture: If n = 3*k - 1 (>2), a(n) = A000567(k). For example,
a(29) = 10 * (3*10 - 2) = 280.
(In the data: a(5) = 8 = A000567(2), a(8) = 21 = A000567(3), a(11) = 40 = A000567(4).)

Conventions.
* The Kaprekar map in base `b` sends `m` to (the number whose base-`b` digits are those of `m`
  in descending order) minus (the number whose digits are those of `m` in ascending order), using
  the digits of `m` without leading zeros. `Nat.digits b m` lists the digits least significant
  first, so `Nat.ofDigits b` of the ascending list is the larger number and `Nat.ofDigits b` of the
  descending list is the smaller one; the subtraction never truncates.
* "Smallest fixed point (> 0)" is stated with `IsLeast` over positive `m`, so the statement also says
  that a positive fixed point exists.
* `n = 3*k - 1 > 2` means `k ≥ 2`.
-/

namespace OMA.S_oeis_a319798

/-- The base-`b` Kaprekar map: digits in descending order minus digits in ascending order. -/
def kaprekar (b m : ℕ) : ℕ :=
  let asc := (Nat.digits b m).insertionSort (· ≤ ·)
  Nat.ofDigits b asc - Nat.ofDigits b asc.reverse

/-- For `k ≥ 2`, the smallest positive fixed point of the Kaprekar map in base `3*k - 1` is the
octagonal number `k * (3*k - 2)`. -/
theorem main : ∀ k : ℕ, 2 ≤ k →
    IsLeast {m : ℕ | 0 < m ∧ kaprekar (3 * k - 1) m = m} (k * (3 * k - 2)) := by
  sorry

end OMA.S_oeis_a319798
