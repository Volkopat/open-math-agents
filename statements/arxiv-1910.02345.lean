import Mathlib

/-!
# Convolving an MTP₂ density with a standard Gaussian keeps it MTP₂

Source: https://arxiv.org/abs/1910.02345
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

A. Zartash and E. Robeva, "Convolutions of Totally Positive Distributions with applications to
Kernel Density Estimation" (arXiv:1910.02345, Alg. Stat. 2022). A density `f` on `ℝ^d` is
multivariate totally positive of order 2 (MTP₂) if `f(x) f(y) ≤ f(x ∧ y) f(x ∨ y)` for all `x, y`,
with `∧, ∨` the coordinatewise minimum and maximum. The abstract states: "We further conjecture that
convolving any totally positive density with a standard Gaussian remains totally positive." (The
paper proves it for densities satisfying an extra "Constraint A", e.g. uniform laws on min-max
closed sets, and shows that a non-standard MTP₂ Gaussian kernel can destroy the property.) This file
states the conjecture in every dimension `d`.

Modelling choices:
* `ℝ^d` is `Fin d → ℝ`, whose `⊓, ⊔` are the coordinatewise minimum and maximum.
* A density is a nonnegative integrable function with total integral `1` (Lebesgue measure).
* The standard Gaussian density is `φ(z) = (2π)^{-d/2} exp(-∑ zᵢ² / 2)` (written with the sum of
  squares, since the default norm on `Fin d → ℝ` is the sup norm), and the convolution is
  `(f ∗ φ)(x) = ∫ f(y) φ(x - y) dy`.
-/

namespace OMA.S_arxiv_1910_02345

open MeasureTheory

/-- `f` is MTP₂: `f x * f y ≤ f (x ⊓ y) * f (x ⊔ y)`. -/
def MTP2 {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ x y, f x * f y ≤ f (x ⊓ y) * f (x ⊔ y)

/-- The standard Gaussian density on `ℝ^d`. -/
noncomputable def φ (d : ℕ) (z : Fin d → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ i, z i ^ 2) / 2)

/-- The convolution `f ∗ φ`. -/
noncomputable def convGauss {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ y, f y * φ d (x - y)

/-- **Zartash–Robeva conjecture.** -/
theorem main :
    ∀ (d : ℕ) (f : (Fin d → ℝ) → ℝ), (∀ x, 0 ≤ f x) → Integrable f → ∫ x, f x = 1 →
      MTP2 f → MTP2 (convGauss f) := by
  sorry

end OMA.S_arxiv_1910_02345
