import Mathlib

/-!
# A295319: a(n) is the sum of all n-digit palindromes.

Source: https://oeis.org/A295319
Credit: @Harsha0912

Conjecture (Harvey P. Dale, Mar 05 2023, in the comments of A295319): all terms after a(1) are
of the form 495*10^x where x is any nonnegative integer k such that k != 1 (mod 3).

Conventions:
* The sequence has offset 1. The n-digit numbers are those m with 10^(n-1) <= m < 10^n.
* m is a palindrome when its list of decimal digits equals its reverse.
* The conjecture is read as: the set of terms a(n) with n >= 2 is exactly the set of numbers
  495*10^k with k a natural number, k mod 3 different from 1.
-/

namespace OMA.S_oeis_a295319

/-- `m` is a decimal palindrome. -/
def IsPal (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

instance : DecidablePred IsPal := fun _ => inferInstanceAs (Decidable (_ = _))

/-- A295319: the sum of all `n`-digit palindromes. -/
def a (n : ℕ) : ℕ := ∑ m ∈ (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter IsPal, m

/-- The terms after `a(1)` are exactly the numbers `495 * 10^k` with `k % 3 ≠ 1`. -/
theorem main : {x : ℕ | ∃ n, 2 ≤ n ∧ a n = x} = {x : ℕ | ∃ k, k % 3 ≠ 1 ∧ x = 495 * 10 ^ k} := by
  sorry

end OMA.S_oeis_a295319
