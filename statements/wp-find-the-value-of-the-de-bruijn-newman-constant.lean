import Mathlib

/-!
# Value of the de Bruijn–Newman constant

Source: https://en.wikipedia.org/wiki/De_Bruijn–Newman_constant
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem: find the value of the de Bruijn–Newman constant `Λ`. Newman conjectured `Λ ≥ 0`
(proved by Rodgers–Tao), and the Riemann hypothesis is equivalent to `Λ ≤ 0`; the open
question recorded on the source page is whether `Λ = 0`, which is the statement below.

Definitions (as on the source page).
* `Φ(u) = ∑_{n ≥ 1} (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u})`.
* `H_t(z) = ∫₀^∞ e^{tu²} Φ(u) cos(zu) du` for real `t` and complex `z`.
* `Λ` is the infimum of the real `t` such that `H_t` has only real zeros (de Bruijn: this set
  is an up-closed half-line, and Newman: it is bounded below).
-/

namespace OMA.S_wp_find_the_value_of_the_de_bruijn_newman_constant

open Complex MeasureTheory

/-- The super-exponentially decaying function `Φ`. -/
noncomputable def Φ (u : ℝ) : ℝ :=
  ∑' n : ℕ, ((2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) -
      3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)))

/-- `H_t(z)`. -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), (Real.exp (t * u ^ 2) * Φ u : ℂ) * Complex.cos (z * u)

/-- The de Bruijn–Newman constant. -/
noncomputable def Λ : ℝ :=
  sInf {t : ℝ | ∀ z : ℂ, H t z = 0 → z.im = 0}

/-- Conjecture: `Λ = 0`. -/
theorem main : Λ = 0 := by
  sorry

end OMA.S_wp_find_the_value_of_the_de_bruijn_newman_constant
