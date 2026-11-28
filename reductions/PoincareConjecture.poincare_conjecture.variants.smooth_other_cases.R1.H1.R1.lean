import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1

-- Reduction PoincareConjecture.poincare_conjecture.variants.smooth_other_cases.R1.H1.R1 of step PoincareConjecture.poincare_conjecture.variants.smooth_other_cases.R1.H1
-- Credit: @hiattco

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1_H1_R1

open PoincareConjecture
open scoped Manifold ContDiff EuclideanGeometry ContinuousMap

private theorem exotic_sphere_refutes (n : ℕ)
    (hexotic : ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (_ : IsManifold (𝓡 n) ∞ M) (_ : M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      IsEmpty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ¬ SmoothConjectureFor.{0} n := by
  obtain ⟨M, t, c, s, e, hempty⟩ := hexotic
  letI : TopologicalSpace M := t
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := c
  letI : IsManifold (𝓡 n) ∞ M := s
  letI : T2Space M := e.symm.t2Space
  intro hall
  obtain ⟨d⟩ := hall M e.toHomotopyEquiv
  exact hempty.false d

-- For n = 4k − 1 with k ≥ 2, the Kervaire–Milnor order formula gives a
-- nontrivial subgroup of homotopy spheres bounding parallelizable manifolds.
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n % 4 = 3 →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (_ : IsManifold (𝓡 n) ∞ M) (_ : M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      IsEmpty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

-- For n = 4k + 1, vanishing of the Kervaire invariant in dimension n+1
-- gives a subgroup of order two. The exceptional stems above 4 are omitted.
def H2 : Prop :=
  ∀ n : ℕ, 4 < n → n % 4 = 1 →
    n + 1 ≠ 6 → n + 1 ≠ 14 → n + 1 ≠ 30 → n + 1 ≠ 62 → n + 1 ≠ 126 →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (_ : IsManifold (𝓡 n) ∞ M) (_ : M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      IsEmpty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

-- Of the exceptional stems, 5 and 61 are outside the target. In dimensions
-- 13 and 29 use May's 3-primary classes, and in 125 use Wang–Xu Prop. 1.12.
def H3 : Prop :=
  ∀ n : ℕ, n = 13 ∨ n = 29 ∨ n = 125 →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (_ : IsManifold (𝓡 n) ∞ M) (_ : M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      IsEmpty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

theorem main : H1 → H2 → H3 → OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1.H1 := by
  intro horder hkervaire hcoker n hn hexcluded hodd
  apply exotic_sphere_refutes n
  by_cases h3 : n % 4 = 3
  · exact horder n hn h3
  by_cases hsporadic : n = 13 ∨ n = 29 ∨ n = 125
  · exact hcoker n hsporadic
  have h5 : n ≠ 5 := by
    rintro rfl
    exact hexcluded (by simp [SmoothTrueValues])
  have h61 : n ≠ 61 := by
    rintro rfl
    exact hexcluded (by simp [SmoothTrueValues])
  apply hkervaire n hn <;> omega

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1_H1_R1
