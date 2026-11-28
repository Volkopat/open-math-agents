import Mathlib

/-!
# Angular aperture and sampling density in a sine-phase Vandermonde matrix

Source: jqka, https://mathoverflow.net/questions/123377 (CC BY-SA 3.0).
Credit: @connoranderson.

The grid has m intervals and m+1 points, including both endpoints. After
normalization by the number of columns, its Gram matrix converges to an
explicit integral matrix at every fixed aperture. At fixed sampling density,
a triangular binomial change of basis resolves the vanishing orders at zero
aperture. The resulting Vandermonde limit gives a positive leading determinant
constant, and singular value i (numbered from zero) has exact order K^i.
-/
namespace OMA.S_mo_123377
open Matrix Filter MeasureTheory
open scoped Topology
noncomputable def node (K t : ℝ) : ℂ :=
  Complex.exp ((Real.pi * Real.sin (K*t) : ℝ) * Complex.I)
noncomputable def grid (m : ℕ) (j : Fin (m+1)) : ℝ := 2*(j.val:ℝ)/m-1
noncomputable def samples (n m : ℕ) (K : ℝ) : Matrix (Fin n) (Fin (m+1)) ℂ :=
  .of fun i j => node K (grid m j)^i.val
noncomputable def empirical (n m : ℕ) (K : ℝ) :=
  ((m+1:ℂ)⁻¹) • (samples n m K*(samples n m K)ᴴ)
noncomputable def continuum (n : ℕ) (K : ℝ) : Matrix (Fin n) (Fin n) ℂ := .of fun i j =>
  ∫ u in (0:ℝ)..1, node K (2*u-1)^i.val * star (node K (2*u-1)^j.val)
noncomputable def tangent (n m : ℕ) : Matrix (Fin n) (Fin (m+1)) ℂ :=
  .of fun i j => ((Real.pi*grid m j:ℝ)*Complex.I)^i.val

theorem main :
    (∀ (n : ℕ) (K : ℝ), Tendsto (fun m : ℕ => empirical n m K) atTop (𝓝 (continuum n K))) ∧
    (∀ n m : ℕ, 0 < m → n ≤ m+1 →
      0 < ((tangent n m*(tangent n m)ᴴ).det).re ∧
      Tendsto (fun K : ℝ => (samples n m K*(samples n m K)ᴴ).det / (K:ℂ)^(n*(n-1)))
        (𝓝[≠] 0) (𝓝 ((tangent n m*(tangent n m)ᴴ).det))) ∧
    (∀ n m : ℕ, 0 < m → n ≤ m+1 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ K : ℝ in 𝓝[>] 0, ∀ i : Fin n, c*K^i.val ≤ (samples n m K).toEuclideanLin.singularValues i.val ∧
        (samples n m K).toEuclideanLin.singularValues i.val ≤ C*K^i.val) := by
  sorry
end OMA.S_mo_123377
