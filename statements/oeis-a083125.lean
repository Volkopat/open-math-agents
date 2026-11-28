import Mathlib

/-!
# A083125: a(1) = 1, then the smallest number not occurring earlier such that the product of a pair of successive terms is a palindrome.

Source: https://oeis.org/A083125
Credit: @gblacher2

Conjecture (Reinhard Zumkeller, May 02 2003, comment in A083125): "except for multiples of 10,
all natural numbers belong to this sequence."

Conventions:
* the offset of A083125 is 1; the sequence is encoded as `a : ℕ → ℕ` with `a n = a(n+1)`, so
  `a 0 = 1`;
* "number" means a positive integer: the terms are positive (`0` is excluded, otherwise the
  product `a(n) * 0 = 0` would make `0` the second term), and "all natural numbers" means all
  positive integers;
* palindromes are taken in base 10: a natural number whose list of decimal digits equals its
  reverse;
* "smallest number not occurring earlier" means the least positive `k` different from
  `a 0, ..., a n`; the greedy recursion is encoded by the predicate `IsA083125`, which pins down
  the sequence uniquely when it exists; the conjecture is stated for every sequence satisfying it;
* "except for multiples of 10, all natural numbers belong to this sequence" is read as: the set
  of terms is exactly the set of positive integers not divisible by 10. (A multiple of 10 can
  never occur, since a positive palindrome does not end in the digit 0.)
-/

namespace OMA.S_oeis_a083125

/-- `n` is a base-10 palindrome. -/
def IsPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- `a` is the sequence A083125, shifted to offset 0: `a 0 = 1` and, for `n ≥ 0`, `a (n + 1)`
is the least positive `k` not among `a 0, ..., a n` such that `a n * k` is a palindrome. -/
def IsA083125 (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ,
    IsLeast {k : ℕ | 0 < k ∧ (∀ i ≤ n, a i ≠ k) ∧ IsPalindrome (a n * k)} (a (n + 1))

/-- The conjecture: the terms of A083125 are exactly the positive integers that are not
multiples of 10. -/
theorem main : ∀ a : ℕ → ℕ, IsA083125 a →
    Set.range a = {k : ℕ | 0 < k ∧ ¬ 10 ∣ k} := by
  sorry

end OMA.S_oeis_a083125
