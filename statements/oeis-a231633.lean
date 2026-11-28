import Mathlib

/-!
# A231633: Number of ways to write n = x + y (x, y > 0) with x^2 * y - 1 prime.

Source: https://oeis.org/A231633
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 2. Also, any integer n > 4 can be written as x + y (x, y > 0) with
x^2 * y + 1 prime.
(ii) Each n = 2, 3, ... can be expressed as x + y (x, y > 0) with (x*y)^2 + x*y + 1 prime.

Formalization notes:
* y = n - x with 0 < x < n; x^2 * y - 1 is in ℕ (where x^2 y = 0 it would be 0, not prime).
* Controls (computed): all claims hold for n < 800.
-/

namespace OMA.S_oeis_a231633

/-- A231633(n). -/
def a (n : ℕ) : ℕ := ((Finset.Ioo 0 n).filter fun x => (x ^ 2 * (n - x) - 1).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 2 < n → 0 < a n) ∧
      (∀ n : ℕ, 4 < n → ∃ x, 0 < x ∧ x < n ∧ (x ^ 2 * (n - x) + 1).Prime) ∧
      ∀ n : ℕ, 2 ≤ n → ∃ x, 0 < x ∧ x < n ∧ ((x * (n - x)) ^ 2 + x * (n - x) + 1).Prime := by
  sorry

end OMA.S_oeis_a231633
