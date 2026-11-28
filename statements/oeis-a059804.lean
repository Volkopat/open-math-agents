import Mathlib

/-!
# OEIS A059804: lattice points near the segment to the prime point

Source: https://oeis.org/A059804
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

In `ℝⁿ` take the segment from the origin to `v = (2, 3, 5, 7, 11, …)` (first `n` primes); let `d`
be the squared distance to it from the closest point of `ℤⁿ`, excluding the endpoints; `a(n) = d · (v·v)`.
The entry states (as a conjecture: "officially these are just conjectures"): for `n ≥ 19`,
`a(n) = A024450(n-1)`, the sum of the squares of the first `n - 1` primes.

Reading: distance from a lattice point to the closed segment `[0, v]` (Euclidean), minimized over
lattice points other than `0` and `v`.
-/

namespace OMA.S_oeis_a059804

/-- The point `v = (p₁, …, pₙ)`. -/
noncomputable def v (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (Nat.nth Nat.Prime i : ℝ)

/-- The integer point `x` as a point of `ℝⁿ`. -/
noncomputable def pt {n : ℕ} (x : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (x i : ℝ)

/-- `d`: least squared distance from a non-endpoint lattice point to the segment `[0, v]`. -/
noncomputable def d (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ x : Fin n → ℤ, pt x ≠ 0 ∧ pt x ≠ v n ∧
    r = Metric.infDist (pt x) (segment ℝ 0 (v n)) ^ 2}

/-- For `n ≥ 19`, `d · (v·v)` is the sum of the squares of the first `n - 1` primes. -/
theorem main : ∀ n : ℕ, 19 ≤ n →
    d n * ‖v n‖ ^ 2 = ∑ i ∈ Finset.range (n - 1), ((Nat.nth Nat.Prime i : ℝ)) ^ 2 := by
  sorry

end OMA.S_oeis_a059804
