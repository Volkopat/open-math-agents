import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Non-negative matrices with prescribed Perron-Frobenius eigenvectors

Source: https://mathoverflow.net/questions/16670
Credit: @etaubman

The question explicitly permits zero coordinates, as its author confirms in
comment 31210. Pavel Etingof's comment 31100 already points out a related
counterexample by adjoining zero coordinates. The present fixed-size family
has entries [[1,m],[0,0]], so it also disproves finiteness with dimension fixed.
This is a formalization of the general question, not the irreducible variant.

A Perron eigenvalue is required to dominate the modulus of every complex
characteristic root. This includes the usual spectral-radius condition in
addition to the eigenvector and probability conditions stated in the question.
-/

namespace OMA.S_mo_16670

abbrev NatMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℕ

def generatedGroup {n : ℕ} (x : Fin n → ℝ) : AddSubgroup ℝ :=
  AddSubgroup.closure (Set.range x)

def probabilityPerron {n : ℕ} (A : NatMatrix n) (r : ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧
  (∑ i, x i) = 1 ∧
  (A.map (fun a => (a : ℝ))).mulVec x = r • x ∧
  (∀ z : ℂ,
    Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ) -
      A.map (fun a => (a : ℂ))) = 0 → ‖z‖ ≤ r)

def compatibleMatrices {n : ℕ} (r : ℝ) (x : Fin n → ℝ) :
    Set (Σ k : ℕ, NatMatrix k) :=
  {B | ∃ y : Fin B.1 → ℝ,
    probabilityPerron B.2 r y ∧ generatedGroup y = generatedGroup x}

def finitenessClaim : Prop :=
  ∀ (n : ℕ) (A : NatMatrix n) (r : ℝ) (x : Fin n → ℝ),
    probabilityPerron A r x → (compatibleMatrices r x).Finite

/-- The general finiteness question, with dimensions allowed to vary as in the source. -/
theorem main : ∀ (n : ℕ) (A : NatMatrix n) (r : ℝ) (x : Fin n → ℝ),
    probabilityPerron A r x → (compatibleMatrices r x).Finite := by
  sorry

end OMA.S_mo_16670
