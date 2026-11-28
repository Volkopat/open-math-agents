import Mathlib

/-!
# A230037: Number of ways to write n = x + y + z (0 < x <= y <= z) such that the four pairs {6*x-1, 6*x+1}, {6*y-1, 6*y+1}, {6*z-1, 6*z+1} and {6*x*y-1, 6*x*y+1} are twin prime pairs.

Source: https://oeis.org/A230037
Credit: @keiichisince1986-bot

A230037 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 2. [The entry adds a stronger form with x = 1 or 5; it is not
formalized here.]

Conventions:
- A twin prime pair `{6v - 1, 6v + 1}` means that both numbers are prime.
- All natural-number subtractions `6v - 1` and `6v - 5` with `v ≥ 1` are exact.
-/

namespace OMA.S_oeis_a230037

theorem main :
    ∀ n : ℕ, 2 < n → ∃ x y z : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z + 1).Prime ∧ (6 * x * y - 1).Prime ∧ (6 * x * y + 1).Prime := by
  sorry

end OMA.S_oeis_a230037
