import Mathlib

/-!
# Two integral inequalities with oscillatory integrands

Source: Marija Stanić, Lviv Scottish Book, https://mathoverflow.net/questions/313560
(CC BY-SA 4.0). See also G. Milovanović, A. Cvetković, and M. Stanić,
"Two conjectures for integrals with oscillatory integrands" (2007).
Credit: @connoranderson.
-/

namespace OMA.S_mo_313560

open Real

noncomputable def sineIntegral (ξ : ℝ) (N n : ℕ) : ℝ :=
  ∫ t in (-1:ℝ)..1, t*(∏ j ∈ Finset.range n,
    (t^2-(((N:ℝ)-j)*π/ξ)^2))*sin (ξ*t)

noncomputable def cosineIntegral (ξ : ℝ) (N n : ℕ) : ℝ :=
  ∫ t in (-1:ℝ)..1, (∏ j ∈ Finset.range n,
    (t^2-(((N:ℝ)-j-1/2)*π/ξ)^2))*cos (ξ*t)

theorem main : ∀ ξ : ℝ, 0 < ξ → ∀ n : ℕ, 0 < n → n ≤ ⌊ξ/π⌋₊ →
    (sin (2*ξ) < 0 → 0 < Real.sign (sin ξ)*sineIntegral ξ ⌊ξ/π⌋₊ n) ∧
    (0 < sin (2*ξ) → 0 < Real.sign (sin ξ)*cosineIntegral ξ ⌊ξ/π⌋₊ n) := by
  sorry

end OMA.S_mo_313560
