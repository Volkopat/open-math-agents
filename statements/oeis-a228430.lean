import Mathlib

/-!
# A228430: Number of ways to write n = x + y (x, y > 0) with x^4 + y*(y+1)/2 prime.

Source: https://oeis.org/A228430
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 except for n = 1, 6.
(ii) For any positive integer n not among 1, 3, 14, 25, there are positive integers x and y with
x + y = n such that x^3 + y*(y+1)/2 is prime.

Formalization notes:
* (i) is stated for n ≥ 1 as: a representation exists iff n ∉ {1, 6}.
* Controls (computed): for 1 ≤ n < 1500 the exceptions are exactly 1, 6 in (i) and 1, 3, 14, 25 in
  (ii).
-/

namespace OMA.S_oeis_a228430



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ((∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 4 + y * (y + 1) / 2).Prime) ↔
        n ≠ 1 ∧ n ≠ 6)) ∧
      ∀ n : ℕ, 1 ≤ n → n ∉ ({1, 3, 14, 25} : Finset ℕ) →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 3 + y * (y + 1) / 2).Prime := by
  sorry

end OMA.S_oeis_a228430
