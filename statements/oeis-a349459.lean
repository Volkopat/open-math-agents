import Mathlib

/-!
# A349459: least m making k^2*(k^2-1), k = 1..n, pairwise distinct modulo m

Source: https://oeis.org/A349459

A349459 (offset 1): `a(n)` is the least positive integer `m` such that the `n` numbers
`k^2*(k^2-1)` (`k = 1..n`) are pairwise distinct modulo `m`:
1, 5, 7, 11, 13, 23, 23, 23, 23, 41, …  For example `a(2) = 5` since `0` and `12` are distinct
modulo 5, but congruent modulo each of 1, 2, 3, 4.

Conjecture (Zhi-Wei Sun, Nov 18 2021): for any integer `n > 1`, the term `a(n)` is the least
prime `p > 2*n` with `p` dividing `a^2 + b^2 - 1` for no `1 ≤ a < b ≤ n`. The entry notes that
this has been verified for all `n = 2..15000`.

Conventions:
- `IsAdmissible n m` says that `m` is positive and the numbers `k^2*(k^2-1)` for `1 ≤ k ≤ n` are
  pairwise incongruent modulo `m`; `a(n)` is the least admissible `m`.
- `IsGoodPrime n p` says that `p` is a prime with `p > 2*n` that divides `a^2 + b^2 - 1` for no
  `1 ≤ a < b ≤ n`.
- The statement is: for every `n > 1`, any `m` that is the least admissible modulus (`IsLeast`)
  is also the least good prime.
- Everything is in `ℕ`; `k^2 - 1` and `a^2 + b^2 - 1` are exact subtractions for `k, a ≥ 1`.
-/

namespace OMA.S_oeis_a349459

/-- The numbers `k^2*(k^2-1)`, `1 ≤ k ≤ n`, are pairwise distinct modulo the positive
integer `m`. -/
def IsAdmissible (n m : ℕ) : Prop :=
  0 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n →
    ¬ (i ^ 2 * (i ^ 2 - 1) ≡ j ^ 2 * (j ^ 2 - 1) [MOD m])

/-- `p` is a prime greater than `2n` dividing `a^2 + b^2 - 1` for no `1 ≤ a < b ≤ n`. -/
def IsGoodPrime (n p : ℕ) : Prop :=
  Nat.Prime p ∧ 2 * n < p ∧ ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ n → ¬ p ∣ a ^ 2 + b ^ 2 - 1

theorem main :
    ∀ n m : ℕ, 1 < n → IsLeast {m : ℕ | IsAdmissible n m} m →
      IsLeast {p : ℕ | IsGoodPrime n p} m := by
  sorry

end OMA.S_oeis_a349459
