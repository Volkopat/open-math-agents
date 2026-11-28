import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# A finite-product formula for the generalized derivative equation

Source: https://math.stackexchange.com/questions/4439933
Question by Galen, licensed CC BY-SA 4.0.
Formalization and proof prepared for @etaubman.

For n given functions, write A for their product, B for the product of their
first derivatives, and A' for the product-rule sum. The equation for one
additional factor g is exactly (B - A) g' = A' g, including singular points.

On an arbitrary open interval where B - A never vanishes, assume the given
functions are continuously differentiable. Then every differentiable solution
is g(x) = g(x₀) exp (integral from x₀ to x of A' / (B - A)). These are the
regularity and domain restrictions required by the indefinite-integral formula
in the source. No claim of a global nonsingular formula is made at B = A.
-/

open scoped BigOperators
open Set MeasureTheory

namespace OMA.S_mse_4439933

noncomputable def productValue {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∏ i, f i x

noncomputable def productDerivative {n : ℕ} (f df : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i, f j x) * df i x

noncomputable def coefficient {n : ℕ} (f df : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  productDerivative f df x / (productValue df x - productValue f x)

noncomputable def primitive {n : ℕ} (f df : Fin n → ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  ∫ t in x₀..x, coefficient f df t

noncomputable def solution {n : ℕ} (f df : Fin n → ℝ → ℝ) (x₀ C x : ℝ) : ℝ :=
  C * Real.exp (primitive f df x₀ x)

theorem main :
    (∀ (n : ℕ) (f df : Fin n → ℝ → ℝ) (g : ℝ → ℝ) (dg x : ℝ),
      (∀ i, HasDerivAt (f i) (df i x) x) → HasDerivAt g dg x →
      ((deriv (fun t => productValue f t * g t) x = productValue df x * dg) ↔
        (productValue df x - productValue f x) * dg =
          productDerivative f df x * g x)) ∧
    (∀ (n : ℕ) (f df : Fin n → ℝ → ℝ) (s : Set ℝ),
      IsOpen s → OrdConnected s →
      (∀ i x, x ∈ s → HasDerivAt (f i) (df i x) x) →
      (∀ i, ContinuousOn (df i) s) →
      (∀ x ∈ s, productValue df x ≠ productValue f x) →
      ∀ x₀ ∈ s,
      (∀ C : ℝ, solution f df x₀ C x₀ = C ∧
        ∀ x ∈ s, DifferentiableAt ℝ (solution f df x₀ C) x ∧
          deriv (fun t => productValue f t * solution f df x₀ C t) x =
            productValue df x * deriv (solution f df x₀ C) x) ∧
      (∀ (g : ℝ → ℝ), (∀ x ∈ s, DifferentiableAt ℝ g x) →
        (∀ x ∈ s, deriv (fun t => productValue f t * g t) x =
            productValue df x * deriv g x) →
        ∀ x ∈ s, g x = solution f df x₀ (g x₀) x)) := by
  sorry

end OMA.S_mse_4439933
