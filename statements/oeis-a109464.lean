import Mathlib

/-!
# A109464: Numbers n such that A112131(n) and A112131(n + 1) are both Harshad numbers

Source: https://oeis.org/A109464
Author: Jason Earls (2005)

Conjecture (OEIS A109464):
Let `H(n)` be the `n`-th base-10 Harshad (Niven) number (OEIS A005349: positive
integers divisible by the sum of their base-10 digits), and let `A112131(n)` be the
base-10 concatenation of all consecutive integers from `H(n)` to `H(n + 1)` inclusive.
Then there are infinitely many `n ≥ 1` such that both `A112131(n)` and `A112131(n + 1)`
are Harshad numbers.

Conventions:
- First Harshad numbers: `H(1) = 1, ..., H(9) = 9, H(10) = 10, H(11) = 12, H(12) = 18, ...`.
- First terms of A112131 (`n ≥ 1`): `12, 23, 34, 45, 56, 67, 78, 89, 910, 101112, 12131415161718, ...`.
- `n = 9` gives `A112131(9) = 910` (digit sum `10 ∣ 910`) and `A112131(10) = 101112`
  (digit sum `6 ∣ 101112`), so `9` is a member of A109464.
-/

namespace OMA.S_oeis_a109464

/-- Predicate stating that `m` is a base-10 Harshad (Niven) number (OEIS A005349). -/
def IsHarshad (m : ℕ) : Prop :=
  1 ≤ m ∧ (Nat.digits 10 m).sum ∣ m

/-- Base-10 concatenation `u || v` for `v ≥ 1`. -/
def concat10 (u v : ℕ) : ℕ :=
  u * 10 ^ (Nat.digits 10 v).length + v

/-- Base-10 concatenation of consecutive integers `a, a + 1, ..., b` (for `1 ≤ a ≤ b`). -/
def concatRange (a b : ℕ) : ℕ :=
  (List.range' a (b + 1 - a)).foldl concat10 0

/-- The `n`-th base-10 Harshad number (`1`-indexed: `nthHarshad 1 = 1`). -/
noncomputable def nthHarshad (n : ℕ) : ℕ :=
  Nat.nth IsHarshad (n - 1)

/-- `A112131(n)`: concatenation of consecutive integers from `H(n)` to `H(n + 1)`. -/
noncomputable def a112131 (n : ℕ) : ℕ :=
  concatRange (nthHarshad n) (nthHarshad (n + 1))

/-- Conjecture: infinitely many `n ≥ 1` have both `A112131(n)` and `A112131(n + 1)`
Harshad numbers. -/
theorem main :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ IsHarshad (a112131 n) ∧ IsHarshad (a112131 (n + 1))} := by
  sorry

end OMA.S_oeis_a109464
