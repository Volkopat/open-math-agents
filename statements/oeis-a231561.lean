import Mathlib

/-!
# A231561: Number of ways to write n = x + y with 0 < x <= y such that 2^x * y + 1 is prime.

Source: https://oeis.org/A231561
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 1. Also, any integer n > 1 can be written as x + y (x, y > 0) with
2^x * y^2 + 1 prime.
(ii) Each integer n > 2 can be written as x + y (x, y > 0) with 2^x * y - 1 prime. Also, every
n = 3, 4, ... can be expressed as x + y (x, y > 0) with 2^x * y^2 - 1 prime.

Formalization notes:
* y = n - x; "0 < x <= y" is 0 < x and 2x ≤ n. In (ii) the subtractions are exact since
  2^x * y ≥ 2.
* Controls (computed): all four claims hold for n < 250.
-/

namespace OMA.S_oeis_a231561

/-- A231561(n). -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 (n / 2)).filter fun x => (2 ^ x * (n - x) + 1).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 < n → ∃ x, 0 < x ∧ x < n ∧ (2 ^ x * (n - x) ^ 2 + 1).Prime) ∧
      (∀ n : ℕ, 2 < n → ∃ x, 0 < x ∧ x < n ∧ (2 ^ x * (n - x) - 1).Prime) ∧
      ∀ n : ℕ, 3 ≤ n → ∃ x, 0 < x ∧ x < n ∧ (2 ^ x * (n - x) ^ 2 - 1).Prime := by
  sorry

end OMA.S_oeis_a231561
