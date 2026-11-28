import Mathlib

/-!
# OEIS A077038

Franklin T. Adams-Watters conjectures that every even integer greater than 2
occurs infinitely often as the least gap between two primes that strictly
bracket a cube. The sequence starts at cube index 2.

Source: https://oeis.org/A077038
Formalization: @a5teri5k
-/

namespace OMA.S_oeis_a077038

/-- Differences of prime pairs that strictly bracket `n ^ 3`. -/
def gapsAtCube (n : ℕ) : Set ℕ :=
  {d | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < n ^ 3 ∧ n ^ 3 < q ∧ d = q - p}

theorem main : ∀ d : ℕ, Even d → 2 < d →
    {n : ℕ | 2 ≤ n ∧ IsLeast (gapsAtCube n) d}.Infinite := by
  sorry

end OMA.S_oeis_a077038
