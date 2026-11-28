import Mathlib

/-!
# A082613: Smallest palindrome divisible by an n-th power.

Source: https://oeis.org/A082613
Credit: @gblacher2

Conjecture (comment section of A082613, Amarnath Murthy and Meenakshi Srikanth, Apr 29 2003):
"the n-th power that divides a(n) is 2^n."

The sequence has offset 0: 1, 2, 4, 8, 272, 2112, 2112, 4224, 8448, 44544, ...

Modelling choices:
* "Palindrome" means a positive integer whose base-10 digit list reads the same backwards
  (`Nat.digits 10` lists the digits from least to most significant, without leading zeros).
* "Divisible by an n-th power" means divisible by `m ^ n` for some integer `m ≥ 2`; with
  `m = 1` allowed every number would qualify and a(1) would be 1, while the data has a(1) = 2.
  For `n = 0` every positive integer qualifies, so a(0) = 1, which matches the data.
* "The n-th power that divides a(n) is 2^n" is read in the standard way: `2 ^ n` divides a(n)
  (equivalently, a(n) is the smallest palindrome divisible by `2 ^ n`).
* To avoid a vacuous statement, the theorem also asserts that a(n) exists, i.e. that the set of
  such palindromes has a least element, as the definition of the sequence presupposes.
-/

namespace OMA.S_oeis_a082613

/-- `P` is a decimal palindrome: its base-10 digits read the same in both directions. -/
def IsDecimalPalindrome (P : ℕ) : Prop := (Nat.digits 10 P).reverse = Nat.digits 10 P

/-- `P` is a candidate for A082613(n): a positive decimal palindrome divisible by `m ^ n`
for some `m ≥ 2`. -/
def IsCandidate (n P : ℕ) : Prop :=
  0 < P ∧ IsDecimalPalindrome P ∧ ∃ m : ℕ, 2 ≤ m ∧ m ^ n ∣ P

/-- The conjecture: for every `n`, the smallest candidate a(n) exists and `2 ^ n` divides it. -/
theorem main : ∀ n : ℕ, ∃ P : ℕ, IsLeast {P : ℕ | IsCandidate n P} P ∧ 2 ^ n ∣ P := by
  sorry

end OMA.S_oeis_a082613
