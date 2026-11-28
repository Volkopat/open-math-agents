import Mathlib

/-!
# Discrete Fresnel operator

Source: https://mathoverflow.net/questions/479056/discrete-fresnel-operator
Question by MathOverflow user Not a good mathematician (CC BY-SA 4.0).
Credit: @city-ships

Write `s = λ d > 0`. The Boolean selects the Fresnel kernel (`false`) or the
Fraunhofer kernel as given in the question (`true`). In both cases the phase
includes the principal-square-root prefactor's angle of −π/4.

The question leaves the output sampling grid and the mode of convergence open.
We use reciprocal pitches: Δy = L/N at the aperture and Δx = s/L at the
detector. The aperture origin a and detector origin b are arbitrary.
Matrices act on field samples weighted by the square root of their pixel width,
so ordinary matrix unitarity expresses conservation of discrete optical power.
Convergence means pointwise convergence of the complex field at every fixed
detector row, for every continuous field on the illuminated aperture.
-/

namespace OMA.S_mo_479056

open Filter
open scoped Topology

noncomputable def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

noncomputable def angle (far : Bool) (s x y : ℝ) : ℝ :=
  (if far then 0 else Real.pi * x ^ 2 / s) + Real.pi * (y ^ 2 - 2 * x * y) / s - Real.pi / 4

noncomputable def kernel (far : Bool) (s x y : ℝ) : ℂ :=
  (Real.sqrt s : ℂ)⁻¹ * phase (angle far s x y)

noncomputable def inputPoint (a L : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  a + (j.val : ℝ) * (L / (n + 1 : ℕ))

noncomputable def outputPoint (b s L : ℝ) (k : ℕ) : ℝ :=
  b + (k : ℝ) * s / L

/-- Convert raw input samples to power-normalized coordinates and convert the
output back to field amplitude. The factor is √(Δy/Δx) = L/(√N √s). -/
noncomputable def outputField (a L s : ℝ) (n : ℕ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f : ℝ → ℂ) (i : Fin (n + 1)) : ℂ :=
  ((L / Real.sqrt (n + 1 : ℕ) / Real.sqrt s : ℝ) : ℂ) *
    U.mulVec (fun j => f (inputPoint a L n j)) i

/-- Indexing by n+1 covers every positive matrix size. For a fixed row k the
limit uses sizes n+k+1, so that the row always exists. -/
theorem main :
    ∀ (far : Bool) (s L a b : ℝ), 0 < s → 0 < L →
      ∃ U : (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        (∀ n, (U n).conjTranspose * U n = 1) ∧
        ∀ (f : ℝ → ℂ), ContinuousOn f (Set.Icc a (a + L)) → ∀ k : ℕ,
          Tendsto (fun n : ℕ => outputField a L s (n + k) (U (n + k)) f ⟨k, by omega⟩)
            atTop (𝓝 (∫ y in a..a + L, kernel far s (outputPoint b s L k) y * f y)) := by
  sorry

end OMA.S_mo_479056
