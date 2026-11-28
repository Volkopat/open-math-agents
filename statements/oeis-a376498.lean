import Mathlib

/-!
# Integrality of the cosine-power array A376498

Source: https://oeis.org/A376498
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a376498

/-- Zero-based j runs over the same odd numerators 1,3,...,2n−1. -/
noncomputable def theta (n j : ℕ) : ℝ := (2*(j:ℝ)+1)*Real.pi/(2*n+1)

noncomputable def entry (n k : ℕ) : ℝ :=
  2^k * ∑ j ∈ Finset.range n, Real.cos (theta n j)^k

theorem main : ∀ n k : ℕ, ∃ z : ℤ, entry n k = z := by
  sorry

end OMA.S_oeis_a376498
