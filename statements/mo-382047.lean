import Mathlib

namespace OMA.S_mo_382047

open Manifold
open scoped Manifold ContDiff

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

abbrev Sphere (n : ℕ) := Metric.sphere (0 : Ambient n) 1

/-- An orthonormal frame of the normal bundle in the target sphere. -/
def HasNormalFrame {k n : ℕ} (f : Sphere k → Sphere n) : Prop :=
  ∃ frame : Fin (n - k) → Sphere k → Ambient n,
    (∀ i, Continuous (frame i)) ∧
      ∀ x, Orthonormal ℝ (fun i => frame i x) ∧
        ∀ i, inner ℝ (f x : Ambient n) (frame i x) = 0 ∧
          ∀ w, inner ℝ (E := Ambient n)
            (mfderiv (𝓡 k) 𝓘(ℝ, Ambient n) (fun y => (f y : Ambient n)) x w)
            (frame i x) = 0

/-- Some smooth embedding of standard spheres has a nontrivial normal bundle. -/
theorem main :
    ∃ (k n : ℕ) (f : Sphere k → Sphere n),
      k < n ∧ IsSmoothEmbedding (𝓡 k) (𝓡 n) ∞ f ∧ ¬ HasNormalFrame f := by
  sorry

end OMA.S_mo_382047
