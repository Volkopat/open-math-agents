import Mathlib

/-!
# A210650: Least number k>0 such that at least one of (2^k-1)*2^n-1, (2^k-1)*2^n+1, (2^k+1)*2^n-1, or (2^k+1)*2^n+1 is a prime number.

Source: https://oeis.org/A210650
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A210650 (Pierre CAMI, Mar 27 2012): for n>1 a(n) is
always < n.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, ...).
* a(n) is the least k > 0 such that at least one of (2^k-1)*2^n-1, (2^k-1)*2^n+1, (2^k+1)*2^n-1,
  (2^k+1)*2^n+1 is prime. The claim a(n) < n (which includes that a(n) exists) is stated as: there
  is such a k with 0 < k < n; this is the same as a(n) < n for the least such k.
* The subtractions are exact natural-number subtractions (2^k >= 2 and the products are at least 2
  for k, n >= 1).
-/

namespace OMA.S_oeis_a210650

/-- The conjecture recorded in A210650. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧
    (((2 ^ k - 1) * 2 ^ n - 1).Prime ∨ ((2 ^ k - 1) * 2 ^ n + 1).Prime ∨
      ((2 ^ k + 1) * 2 ^ n - 1).Prime ∨ ((2 ^ k + 1) * 2 ^ n + 1).Prime) := by
  sorry

end OMA.S_oeis_a210650
