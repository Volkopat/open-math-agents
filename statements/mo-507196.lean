import Mathlib

/-!
# Monotonicity of a product of a set and its iterated sumset

Source: https://mathoverflow.net/questions/507196
Credit: @Mapika

Marcel K. Goh's Statement 1 asks whether the cardinality of (hA)·A is
nondecreasing in the positive integer h for every finite real set A.
In the Pointwise scope, h • A is the h-fold sumset. It satisfies
1 • A = A and (h + 1) • A = h • A + A.
-/

namespace OMA.S_mo_507196

open scoped Pointwise

theorem main : ∀ (A : Finset ℝ) (h : ℕ), 0 < h →
    ((h • A) * A).card ≤ (((h + 1) • A) * A).card := by
  sorry

end OMA.S_mo_507196
