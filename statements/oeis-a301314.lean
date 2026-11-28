import Mathlib

/-!
# A301314: Number of ways to write n as x^2 + y^2 + z^2 + w^2, where w is a positive integer and x,y,z are nonnegative integers such that x + 3*y + 9*z = 2^k*m^3 for some k,m = 0,1,2,....

Source: https://oeis.org/A301314
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry; the first verified for n = 1..10^7):
1. a(n) > 0 for all n > 0.
2. Any positive integer can be written as x^2 + y^2 + z^2 + w^2, where x is a positive integer and
   y, z, w are nonnegative integers such that 2*x + 7*y = 2^k*m^3 for some k = 0, 1, 2 and
   m = 1, 2, 3, ....

Formalization notes:
* In conjecture 1, k, m ≥ 0 (so the value 0 = 2^0 * 0^3 is allowed); in conjecture 2, k ≤ 2 and m ≥ 1.
* Controls (computed): both conjectures hold for 1 ≤ n < 2500.
-/

namespace OMA.S_oeis_a301314

/-- Both conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        ∃ k m : ℕ, x + 3 * y + 9 * z = 2 ^ k * m ^ 3) ∧
      ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < x ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        ∃ k m : ℕ, k ≤ 2 ∧ 0 < m ∧ 2 * x + 7 * y = 2 ^ k * m ^ 3 := by
  sorry

end OMA.S_oeis_a301314
