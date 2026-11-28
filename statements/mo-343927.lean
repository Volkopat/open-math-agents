import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Sparse perturbation

Source: https://mathoverflow.net/questions/343927/sparse-perturbation
Question by Yiming Xu, 16 October 2019. Formalization for @etaubman.

The source asks for one constant, independent of the dimension and support size,
bounding the l1/l2 ratio of a perturbation when the original l1/l2 ratio does
not increase. The EuclideanSpace norm is the usual l2 norm; oneNorm is l1.
The support size s is written explicitly as the cardinality of nonzero coordinates.
Nonzero assumptions record the three denominators implicit in the source.
The proof also gives the division-free bound when the perturbation is zero.
-/

open scoped BigOperators

namespace OMA.S_mo_343927

noncomputable def oneNorm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, |x i|

noncomputable def support {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

theorem main : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (x x₀ : EuclideanSpace ℝ (Fin n)),
      x ≠ 0 → x₀ ≠ 0 → x ≠ x₀ →
      oneNorm x / ‖x‖ ≤ oneNorm x₀ / ‖x₀‖ →
      oneNorm (x - x₀) / ‖x - x₀‖ ≤
        c * Real.sqrt ((support x₀).card : ℝ) := by
  sorry

end OMA.S_mo_343927
