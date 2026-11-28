import Mathlib

/-!
# A352148: Integers m such that nonzero digits of A000217(m) are all the same.

Source: https://oeis.org/A352148
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A352148 (Steven Lu, Mar 06 2022): a(n) = 10^(n-13) for
n >= 17.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 3, 4, 10, 11, 24, 36, 44, 77, 100, ...).
* A000217(m) = m*(m+1)/2 is the m-th triangular number (exact division). `P m` says that all
  nonzero decimal digits of m*(m+1)/2 are the same digit d (for m = 0 there are no digits and the
  condition holds, in agreement with a(1) = 0).
* a(n) is the n-th natural number with this property in increasing order, i.e. `Nat.nth P (n - 1)`
  (`Nat.nth` is 0-indexed).
-/

namespace OMA.S_oeis_a352148

/-- All nonzero decimal digits of the triangular number m*(m+1)/2 are the same. -/
def P (m : ℕ) : Prop := ∃ d : ℕ, ∀ x ∈ Nat.digits 10 (m * (m + 1) / 2), x = 0 ∨ x = d

/-- The conjecture recorded in A352148. -/
theorem main : ∀ n : ℕ, 17 ≤ n → Nat.nth P (n - 1) = 10 ^ (n - 13) := by
  sorry

end OMA.S_oeis_a352148
