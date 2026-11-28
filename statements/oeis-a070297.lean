import Mathlib

/-!
# A070297: the smallest number with `n` unrelated numbers

Source: https://oeis.org/A070297
Credit: @avivorly

A070297: Smallest number with n unrelated numbers (numbers which are neither coprime nor a divisor), or 0 if no such
number exists.

Claim (in the entry): The 0's are only conjectures (search extended to 2000).

The data (offset 0) has its zeros at `a(2) = 0` and `a(13) = 0`.

Conventions:
- The unrelated numbers of `m` are the `k` with `1 ≤ k < m` that are neither coprime to `m` (`Nat.gcd k m ≠ 1`) nor
  a divisor of `m`; `unrelated m` counts them, as in A045763 (the number of `k < m` that are neither a divisor of `m`
  nor relatively prime to `m`). Only positive `k` count; `k = m` divides `m`, so counting the `k ≤ m` instead of the
  `k < m` gives the same number.
- `a(n) = 0` exactly when no number `m` has `unrelated m = n`. So the conjectured zeros `a(2) = 0` and `a(13) = 0`
  say that no number has exactly 2, or exactly 13, unrelated numbers. These are the only zeros in the data
  (`n = 0..61`).
- `m` ranges over all of `ℕ`; `unrelated 0 = unrelated 1 = 0`, so including `0` changes nothing.
-/

namespace OMA.S_oeis_a070297

/-- The number of unrelated numbers of `m` (A045763): the `k` with `1 ≤ k < m`, `Nat.gcd k m ≠ 1` and `¬ k ∣ m`. -/
def unrelated (m : ℕ) : ℕ :=
  ((Finset.Ico 1 m).filter (fun k => Nat.gcd k m ≠ 1 ∧ ¬ k ∣ m)).card

theorem main : (∀ m : ℕ, unrelated m ≠ 2) ∧ (∀ m : ℕ, unrelated m ≠ 13) := by
  sorry

end OMA.S_oeis_a070297
