import Mathlib

/-!
# OEIS A386843

Seiichi Manyama's binomial sum and both conjectured recurrences listed
by Left to Solve. Source: https://oeis.org/A386843 (offset zero).
The shifts start each recurrence at its first defined index.
-/

namespace OMA.S_oeis_a386843

def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    ((2 * n + 2).choose k : ℤ) * ((2 * n - k).choose (n - k) : ℤ)

theorem main :
    (∀ k : ℕ, let n : ℤ := k + 3
      5 * n * a (k + 3) + 3 * (-13 * n + 11) * a (k + 2) +
        12 * (-n - 8) * a (k + 1) + 16 * (2 * n - 3) * a k = 0) ∧
    (∀ k : ℕ, let n : ℤ := k + 2
      n * (n - 1) * a (k + 2) - (7 * n - 5) * (n - 1) * a (k + 1) -
        4 * n * (2 * n - 1) * a k = 0) := by
  sorry

end OMA.S_oeis_a386843
