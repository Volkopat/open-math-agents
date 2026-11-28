import Mathlib

/-!
# A229927: Smallest k >= n such that (4^n-1)*2^k - 1 is prime.

Source: https://oeis.org/A229927
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A229927 (Pierre CAMI, Oct 03 2013): there is no Riesel
number of the form 4^n-1; that is, a(n) exists for all n.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 8, 6, 7, 13, 11, 16, 103, 12, ...).
* `a(n) exists` is the statement that for every n >= 1 (the offset) there is k >= n such that
  (4^n-1)*2^k - 1 is prime; a(n) is then the smallest such k. This is the `that is` form given in
  the entry itself.
* The subtractions are exact natural-number subtractions for n >= 1.
-/

namespace OMA.S_oeis_a229927

/-- The conjecture recorded in A229927. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, n ≤ k ∧ ((4 ^ n - 1) * 2 ^ k - 1).Prime := by
  sorry

end OMA.S_oeis_a229927
