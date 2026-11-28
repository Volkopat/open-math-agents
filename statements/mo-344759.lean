import Mathlib

/-!
# When do compatible affine maps have a global affine extension?

Source: https://mathoverflow.net/questions/344759 (Johannes Treutlein, CC BY-SA 4.0).
Credit: @connoranderson

Use a separate copy of homogeneous coordinate space for each member of the
family. The condition below depends only on the sets: every relation among
their labeled points that vanishes after adding the coordinates must be a
linear combination of differences of copies of points in pairwise overlaps.
Finite linear combinations suffice even for an uncountable family.
For related finite hypergraph criteria, see Gortler, Gotsman, Liu and Thurston,
"On affine rigidity", https://arxiv.org/abs/1011.5553.
-/

namespace OMA.S_mo_344759
noncomputable section

abbrev Point (n : ℕ) := Fin n → ℝ
abbrev Homogeneous (n : ℕ) := ℝ × Point n
abbrev Copies (ι : Type*) (n : ℕ) := ι →₀ Homogeneous n

def marked {ι : Type*} {n : ℕ} (i : ι) (x : Point n) : Copies ι n :=
  Finsupp.single i (1, x)

def coordinateSum (ι : Type*) (n : ℕ) : Copies ι n →ₗ[ℝ] Homogeneous n :=
  Finsupp.lsum ℝ (fun _ => LinearMap.id)

def pointSpan {ι : Type*} {n : ℕ} (A : ι → Set (Point n)) : Submodule ℝ (Copies ι n) :=
  Submodule.span ℝ {w | ∃ i x, x ∈ A i ∧ w = marked i x}

def overlapSpan {ι : Type*} {n : ℕ} (A : ι → Set (Point n)) : Submodule ℝ (Copies ι n) :=
  Submodule.span ℝ {w | ∃ i j x, x ∈ A i ∧ x ∈ A j ∧ w = marked i x - marked j x}

universe u

theorem main : ∀ {ι : Type u} {n : ℕ} (A : ι → Set (Point n)) (_ : ∀ i, Convex ℝ (A i)),
    (∀ f : ι → Point n →ᵃ[ℝ] ℝ,
      (∀ i j x, x ∈ A i → x ∈ A j → f i x = f j x) →
      ∃ g : Point n →ᵃ[ℝ] ℝ, ∀ i x, x ∈ A i → g x = f i x) ↔
    pointSpan A ⊓ LinearMap.ker (coordinateSum ι n) ≤ overlapSpan A := by
  sorry

end
end OMA.S_mo_344759
