import Mathlib

/-!
# A229140: Smallest k such that k^2 + l^2 = n-th number expressible as sum of two squares (A001481).

Source: https://oeis.org/A229140
Credit: @luciusacarr

Data: 0, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 3, 2, 0, 1, 2, 4, 3, 0, 1, 2, 4, 3, 0, ... (offset 1).
Example: A001481(6) = 8 = 2^2 + 2^2, so a(6) = 2.

The entry's comment: Conjecture: the values between two zeros are always distinct from each
other. `main` states that conjecture.

Reading of the source:
* A001481 (offset 1) lists the nonnegative integers that are a sum of two squares of nonnegative
  integers, in increasing order: 0, 1, 2, 4, 5, 8, 9, 10, ... So `A001481 n = Nat.nth IsSumTwoSq (n - 1)`
  for `n ≥ 1` (`Nat.nth` is 0-indexed).
* `a n` is the least `k ≥ 0` such that `k^2 + l^2 = A001481 n` for some `l ≥ 0`.
* "The values between two zeros" are the values `a i` for indices `i` strictly between two
  consecutive zeros `z1 < z2` of the sequence (`a z1 = a z2 = 0` and `a t ≠ 0` for
  `z1 < t < z2`); the conjecture says that any two such values at different indices `i < j`
  differ. (Between non-consecutive zeros the claim would fail trivially: `a = 1` occurs right
  after every zero except the first, since `j^2 + 1 = 1^2 + j^2`.)
-/

namespace OMA.S_oeis_a229140

/-- `m` is a sum of two squares of nonnegative integers. -/
def IsSumTwoSq (m : ℕ) : Prop := ∃ k l : ℕ, k ^ 2 + l ^ 2 = m

/-- A001481 with offset 1: the `n`-th number expressible as a sum of two squares. -/
noncomputable def A001481 (n : ℕ) : ℕ := Nat.nth IsSumTwoSq (n - 1)

/-- A229140: the smallest `k` with `k^2 + l^2 = A001481 n` for some `l`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | ∃ l : ℕ, k ^ 2 + l ^ 2 = A001481 n}

theorem main :
    ∀ z1 z2 : ℕ, 1 ≤ z1 → z1 < z2 → a z1 = 0 → a z2 = 0 →
      (∀ t, z1 < t → t < z2 → a t ≠ 0) →
      ∀ i j : ℕ, z1 < i → i < j → j < z2 → a i ≠ a j := by
  sorry

end OMA.S_oeis_a229140
