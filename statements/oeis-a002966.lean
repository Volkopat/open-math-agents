import Mathlib

/-!
# OEIS A002966: Egyptian fractions, second row

Source: https://oeis.org/A002966
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The OEIS entry (R. J. Mathar) considers the array `T(n, m)`, the number of ways to write `1/n`
as a sum of `m` (not necessarily distinct) unit fractions; A002966 is its first row.
Conjecture (D. S. McNeil): the second row `T(2, m)` is A003167, the number of `m`-dimensional
cuboids with integral edge lengths whose volume equals their surface area.

Conventions:
* A way to write `1/n` as a sum of `m` unit fractions is a nondecreasing tuple
  `0 < x₁ ≤ ⋯ ≤ x_m` of integers with `∑ 1/xᵢ = 1/n` (as in A002966).
* An `m`-dimensional cuboid with integral edges is a nondecreasing tuple of positive integer edge
  lengths `x₁ ≤ ⋯ ≤ x_m`; its volume is `∏ xᵢ` and its surface area is `2 ∑ᵢ ∏_{j ≠ i} xⱼ`.
* A003167 has offset `2`, so `main` is for `m ≥ 2`.
-/

namespace OMA.S_oeis_a002966

/-- `T(n, m)`: nondecreasing `m`-tuples of positive integers whose reciprocals sum to `1/n`. -/
noncomputable def T (n m : ℕ) : ℕ :=
  {x : Fin m → ℕ | Monotone x ∧ (∀ i, 0 < x i) ∧
    ∑ i, (1 : ℚ) / (x i : ℚ) = 1 / (n : ℚ)}.ncard

/-- A003167: `m`-dimensional integral cuboids with volume equal to surface area. -/
noncomputable def A003167 (m : ℕ) : ℕ :=
  {x : Fin m → ℕ | Monotone x ∧ (∀ i, 0 < x i) ∧
    ∏ i, x i = 2 * ∑ i, ∏ j ∈ Finset.univ.erase i, x j}.ncard

/-- McNeil's conjecture: `T(2, m) = A003167(m)` for all `m ≥ 2`. -/
theorem main : ∀ m : ℕ, 2 ≤ m → T 2 m = A003167 m := by
  sorry

end OMA.S_oeis_a002966
