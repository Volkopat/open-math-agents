import FormalConjectures.Wikipedia.Mandelbrot

/-!
# Density of hyperbolicity for multibrots

The target asks that attracting-cycle parameters are dense in the multibrot set of every
exponent `n ≥ 2`. The pinned module proves the bridge `multibrotSet_eq`: the multibrot set is
exactly the bounded-orbit set. This reduction separates that proved escape-radius
characterisation from the genuinely open density-of-hyperbolicity core on bounded orbits.
-/

namespace OMA.R_Mandelbrot_density_of_hyperbolicity_general_exponent_R1

open Mandelbrot

-- Reduction Mandelbrot.density_of_hyperbolicity_general_exponent.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-- Open core: attracting-cycle parameters are dense in the bounded-orbit set of every
    multibrot exponent `n ≥ 2`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    {c : ℂ | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹} ⊆
      closure {c | ∃ m z, IsAttractingCycle (fun z ↦ z ^ n + c) m z}

/-- Proved bridge (`Mandelbrot.multibrotSet_eq`, Mandelbrot.lean:54): the multibrot set is
    exactly the bounded-orbit set. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    multibrotSet n = {c : ℂ | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

theorem main : H1 → H2 → type_of% @Mandelbrot.density_of_hyperbolicity_general_exponent := by
  intro h1 h2 n hn c hc
  exact h1 n hn (by rwa [← h2 n hn])

end OMA.R_Mandelbrot_density_of_hyperbolicity_general_exponent_R1
