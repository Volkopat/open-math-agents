import Mathlib

/-!
# Pillai's conjecture

Source: https://lefttosolve.com/p/wp-pillai-s-conjecture
Pillai's conjecture: for any integers `A`, `B`, `C` the equation `A * x ^ m - B * y ^ n = C` has
only finitely many solutions in positive integers `x`, `y` whenever the exponents `m`, `n` are
at least two and are not both equal to two.
-/

namespace OMA.S_wp_pillai_s_conjecture

/-- Pillai's conjecture, stated over the integers: for `m, n ≥ 2` and `(m, n) ≠ (2, 2)` the
solutions in positive integers of `A * x ^ m - B * y ^ n = C` are finite. -/
theorem main : ∀ (A B C : ℤ) (m n : ℕ), 2 ≤ m → 2 ≤ n → ¬ (m = 2 ∧ n = 2) →
    Set.Finite {p : ℤ × ℤ | 0 < p.1 ∧ 0 < p.2 ∧ A * p.1 ^ m - B * p.2 ^ n = C} := by
  sorry

end OMA.S_wp_pillai_s_conjecture
