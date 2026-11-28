import Mathlib

/-!
# Fujita conjecture

Source: https://en.wikipedia.org/wiki/Fujita_conjecture
Credit: @Bondyboy2001

For a positive holomorphic line bundle `L` on a compact complex manifold `M` of
dimension `n`, the adjoint bundle `K_M ⊗ L^⊗m` is spanned by global holomorphic
sections for `m ≥ n + 1` and is very ample for `m ≥ n + 2`.
-/

namespace OMA.S_wp_fujita_conjecture

open scoped Manifold ContDiff

noncomputable section

abbrev Coordinates (n : ℕ) := Fin n → ℂ

/-- A holomorphic line bundle presented by local frames on a coordinate cover.
`transition i j x` takes the scalar in frame `i` to the scalar in frame `j`.
Each chart is indexed by a point it contains, so these charts cover `M`. -/
structure HolomorphicLineBundle (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] where
  chart : M → OpenPartialHomeomorph M (Coordinates n)
  mem_source : ∀ x, x ∈ (chart x).source
  compatible : ∀ i, chart i ∈ IsManifold.maximalAtlas (𝓘(ℂ, Coordinates n)) ω M
  transition : M → M → M → ℂ
  transition_ne : ∀ i j x, x ∈ (chart i).source → x ∈ (chart j).source →
    transition i j x ≠ 0
  transition_holomorphic : ∀ i j, AnalyticOnNhd ℂ (transition i j ∘ (chart i).symm)
    ((chart i).target ∩ (chart i).symm ⁻¹' (chart j).source)
  transition_comp : ∀ i j k x, x ∈ (chart i).source → x ∈ (chart j).source →
    x ∈ (chart k).source → transition j k x * transition i j x = transition i k x

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]

/-- The Levi form of `-log h` on `v`, up to a positive constant, computed by
taking the real Laplacian along the complex line with direction `v`. -/
def curvature (h : Coordinates n → ℝ) (z v : Coordinates n) : ℝ :=
  -iteratedDeriv 2 (fun t : ℝ => Real.log (h (z + t • v))) 0 -
    iteratedDeriv 2 (fun t : ℝ => Real.log (h (z + t • (Complex.I • v)))) 0

/-- A smooth Hermitian metric with strictly positive curvature. In each frame,
`h i` is the squared length of the frame vector in chart coordinates. -/
def IsPositive (L : HolomorphicLineBundle n M) : Prop :=
  ∃ h : M → Coordinates n → ℝ,
    (∀ i, ContDiffOn ℝ ∞ (h i) (L.chart i).target) ∧
    (∀ i z, z ∈ (L.chart i).target → 0 < h i z) ∧
    (∀ i j x, x ∈ (L.chart i).source → x ∈ (L.chart j).source →
      h i (L.chart i x) = ‖L.transition i j x‖ ^ 2 * h j (L.chart j x)) ∧
    (∀ i z, z ∈ (L.chart i).target → ∀ v ≠ 0, 0 < curvature (h i) z v)

/-- Global holomorphic sections in local coordinates for a specified transition
function on the cover. Only values on chart targets enter the conditions. -/
def GlobalSection (L : HolomorphicLineBundle n M) (g : M → M → M → ℂ) :=
  {s : M → Coordinates n → ℂ //
    (∀ i, AnalyticOnNhd ℂ (s i) (L.chart i).target) ∧
    (∀ i j x, x ∈ (L.chart i).source → x ∈ (L.chart j).source →
      s j (L.chart j x) = g i j x * s i (L.chart i x))}

def SpannedBySections (L : HolomorphicLineBundle n M) (g : M → M → M → ℂ) : Prop :=
  ∀ x, ∃ s : GlobalSection L g, s.val x (L.chart x x) ≠ 0

/-- On a compact complex manifold, the global sections give a projective
embedding exactly when they generate the fibres and separate points and
tangent directions. At a zero of a section, its differential in a local frame
tests tangent separation independently of the frame. -/
def VeryAmple (L : HolomorphicLineBundle n M) (g : M → M → M → ℂ) : Prop :=
  SpannedBySections L g ∧
    (∀ x y, x ≠ y → ∃ s : GlobalSection L g,
      s.val x (L.chart x x) = 0 ∧ s.val y (L.chart y y) ≠ 0) ∧
    (∀ x (v : Coordinates n), v ≠ 0 → ∃ s : GlobalSection L g,
      s.val x (L.chart x x) = 0 ∧ fderiv ℂ (s.val x) (L.chart x x) v ≠ 0)

/-- To express a top form in chart `j` instead of chart `i`, multiply its
coefficient by the Jacobian determinant of the change from `j` to `i`. -/
def adjointTransition (L : HolomorphicLineBundle n M) (m : ℕ) (i j x : M) : ℂ :=
  LinearMap.det ((fderiv ℂ (L.chart i ∘ (L.chart j).symm) (L.chart j x)).toLinearMap) *
    L.transition i j x ^ m

theorem main :
    ∀ (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (Coordinates n) M] [IsManifold (𝓘(ℂ, Coordinates n)) ω M]
      (L : HolomorphicLineBundle n M), IsPositive L → ∀ m : ℕ,
      (n + 1 ≤ m → SpannedBySections L (adjointTransition L m)) ∧
      (n + 2 ≤ m → VeryAmple L (adjointTransition L m)) := by
  sorry

end

end OMA.S_wp_fujita_conjecture
