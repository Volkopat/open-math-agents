import Mathlib

/-!
# A230494: Number of ways to write n = x^2 + y (x, y >= 0) with 2*y^2 - 1 prime.

Source: https://oeis.org/A230494
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 1. Moreover, if n > 1 is not among 2, 69, 76, then there are positive
integers x and y such that x^2 + y is equal to n and 2*y^2 - 1 is prime.
(ii) Any integer n > 1 can be written as x*(x+1)/2 + y with 2*y^2 - 1 prime, where x and y are
nonnegative integers. Moreover, if n is not equal to 2 or 15, then we may require additionally
that x and y are both positive.

Formalization notes:
* 2y^2 - 1 is in ℕ; for y = 0 it is 0, not prime, as -1 is not prime.
* Controls (computed): for n < 1500 all claims hold; the exceptions to the "positive" versions are
  exactly 2, 69, 76 in (i) and 2, 15 in (ii).
-/

namespace OMA.S_oeis_a230494

/-- A230494(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun x => x ^ 2 ≤ n ∧ (2 * (n - x ^ 2) ^ 2 - 1).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 < n → n ≠ 2 → n ≠ 69 → n ≠ 76 →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y = n ∧ (2 * y ^ 2 - 1).Prime) ∧
      (∀ n : ℕ, 1 < n → ∃ x y : ℕ, x * (x + 1) / 2 + y = n ∧ (2 * y ^ 2 - 1).Prime) ∧
      ∀ n : ℕ, 1 < n → n ≠ 2 → n ≠ 15 →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x * (x + 1) / 2 + y = n ∧ (2 * y ^ 2 - 1).Prime := by
  sorry

end OMA.S_oeis_a230494
