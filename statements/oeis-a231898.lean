import Mathlib

/-!
# A231898: squares with exactly n binary 1's and every large number of binary 0's

Source: https://oeis.org/A231898
Credit: @avivorly

Definition (A231898, N. J. A. Sloane, Nov 2013): a(n) = smallest k with property that for all m >= k, there is a
square N^2 whose binary expansion contains exactly n 1's and m 0's; or -1 if no such k exists.

The entry comments: a(n) = -1 for n = 1, 2 and 4, because all squares with exactly 1, 2 or 4 1's in their binary
expansion must contain an even number of 0's.

Conjecture (in the entry): Apart from n=1, 2 and 4, no other a(n) is -1.

Conventions:
- The binary expansion of `x` is `Nat.digits 2 x` (least significant digit first, no leading zeros). `ones x` and
  `zeros x` count its digits equal to `1` and to `0`; for `x ≥ 1` these are the counts in the entry. The square `0`
  never has `n ≥ 1` ones (under any convention for the expansion of `0`), so it plays no role.
- `N` ranges over the natural numbers (as in the table of the entry, which starts at `N = 0`); the offset is `n ≥ 1`.
- `HasK n` says that some `k` has the property in the definition, so `a(n)` is not `-1` exactly when `HasK n`
  holds (and then `a(n)` is the least such `k`).
- Only the conjecture is stated. The values a(1) = a(2) = a(4) = -1 are the entry's own comment, not part of the
  conjecture, and are not stated here.
-/

namespace OMA.S_oeis_a231898

/-- The number of 1's in the binary expansion of `x`. -/
def ones (x : ℕ) : ℕ := (Nat.digits 2 x).count 1

/-- The number of 0's in the binary expansion of `x` (no leading zeros). -/
def zeros (x : ℕ) : ℕ := (Nat.digits 2 x).count 0

/-- Some `k` is such that for every `m ≥ k` there is a square `N^2` whose binary expansion contains exactly `n` 1's
and `m` 0's; that is, `a(n)` is not `-1` in A231898. -/
def HasK (n : ℕ) : Prop :=
  ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∃ N : ℕ, ones (N ^ 2) = n ∧ zeros (N ^ 2) = m

theorem main : ∀ n : ℕ, 1 ≤ n → n ≠ 1 → n ≠ 2 → n ≠ 4 → HasK n := by
  sorry

end OMA.S_oeis_a231898
