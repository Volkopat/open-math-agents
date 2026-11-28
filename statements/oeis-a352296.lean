import Mathlib

/-!
# A352296: Smallest number that can be expressed as the sum of two primes in exactly n ways or -1 if no such number exists.

Source: https://oeis.org/A352296
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A352296 (Chai Wah Wu, Mar 11 2022): a(n) != -1 for all
n.

Conventions:
* The sequence has offset 0 (data 1, 4, 10, 22, 34, 48, 60, 78, 84, 90, 114, 144, ...).
* A way to express m as the sum of two primes is an unordered pair, i.e. a pair (p, q) of primes
  with p <= q and p + q = m; the number of ways is `Set.ncard` of this (finite) set. This
  reproduces the data (a(0) = 1, a(1) = 4, a(2) = 10 = 3 + 7 = 5 + 5).
* `a(n) != -1` means that some number can be expressed as the sum of two primes in exactly n ways;
  it is stated for all n >= 0 (the offset of the sequence).
-/

namespace OMA.S_oeis_a352296

/-- The conjecture recorded in A352296. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ,
    Set.ncard {t : ℕ × ℕ | t.1.Prime ∧ t.2.Prime ∧ t.1 ≤ t.2 ∧ t.1 + t.2 = m} = n := by
  sorry

end OMA.S_oeis_a352296
