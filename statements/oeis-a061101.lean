import Mathlib

/-!
# A061101: Squares with digital root 7.

Source: https://oeis.org/A061101
Credit: @bnb9001

The sequence lists, in increasing order, the perfect squares whose digital root is 7:
16, 25, 169, 196, 484, ... (offset 1, so `a 1 = 16`).

Conjecture (Colin Barker, 2012): a(n) = (9 n - 8)^2/4 for n even, and a(n) = (9 n - 1)^2/4
for n odd. Robert Israel notes that the conjecture is true. The same entry also gives a
generating function, which is equivalent to these two closed forms; we state the closed forms,
multiplied by 4 and read in the integers to avoid truncating division and natural-number
subtraction.

The digital root of `n` is the repeated digit sum in base 10; for `n > 0` it equals
`1 + (n - 1) % 9`, and it is `0` for `n = 0` (OEIS A010888).
-/

namespace OMA.S_oeis_a061101

/-- The base-10 digital root: `0` for `0`, otherwise `1 + (n - 1) % 9` (OEIS A010888). -/
def digitalRoot (n : ℕ) : ℕ := if n = 0 then 0 else 1 + (n - 1) % 9

/-- `a n` is the `n`-th (1-indexed) perfect square whose digital root is 7. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => IsSquare m ∧ digitalRoot m = 7) (n - 1)

/-- For every `n ≥ 1`: `4 a(n) = (9 n - 8)^2` if `n` is even, and `4 a(n) = (9 n - 1)^2` if `n`
is odd. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (Even n → 4 * (a n : ℤ) = (9 * n - 8) ^ 2) ∧
    (Odd n → 4 * (a n : ℤ) = (9 * n - 1) ^ 2) := by
  sorry

end OMA.S_oeis_a061101
