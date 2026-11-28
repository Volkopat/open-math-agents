import Mathlib

/-!
# A380876: a(1) = 1; a(2) = 4; for n > 2, a(n) = least unused positive y such that gcd(y,n-1) > 1 and
|y-n| > 1.

Source: https://oeis.org/A380876
Credit: @Squee451

Data (offset 1): 1, 4, 6, 9, 2, 10, 3, 14, 12, 15, 5, 22, 8, 26, 7, 18, 20, 34, 16, 38, 24, 27, 11, 46, 21, 30, ...

The entry's formula line: For prime numbers p, a(2p+1) = p, and for p > 3, a(p+1) = 2p. (Conjectured.)

Conventions.
* `IsSeq a` says that `a : ℕ → ℕ` (indices from 1; the value at 0 is irrelevant) satisfies the
  definition: `a 1 = 1`, `a 2 = 4`, and for `n > 2`, `a n` is the least positive `y` that is unused
  (different from `a m` for all `1 ≤ m < n`) with `gcd(y, n-1) > 1` and `|y - n| > 1`. The absolute
  value is taken in the integers.
* The statement asserts that such a sequence exists (the greedy choice is always possible) and that
  the conjectured identities hold for every such sequence (it is unique on positive indices).
-/

namespace OMA.S_oeis_a380876

/-- `y` may be chosen as the `n`-th term: positive, unused so far, `gcd(y, n-1) > 1`, `|y - n| > 1`. -/
def Eligible (a : ℕ → ℕ) (n y : ℕ) : Prop :=
  0 < y ∧ (∀ m, 1 ≤ m → m < n → a m ≠ y) ∧ 1 < Nat.gcd y (n - 1) ∧ 1 < |(y : ℤ) - (n : ℤ)|

/-- `a` is the sequence A380876 on positive indices. -/
def IsSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 4 ∧ ∀ n, 2 < n → IsLeast {y : ℕ | Eligible a n y} (a n)

theorem main :
    (∃ a : ℕ → ℕ, IsSeq a) ∧
    ∀ a : ℕ → ℕ, IsSeq a → ∀ p : ℕ, p.Prime → a (2 * p + 1) = p ∧ (3 < p → a (p + 1) = 2 * p) := by
  sorry

end OMA.S_oeis_a380876
