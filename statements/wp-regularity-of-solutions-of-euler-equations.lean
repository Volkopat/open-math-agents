import Mathlib

/-!
# Regularity of solutions of Euler equations

Source: https://en.wikipedia.org/wiki/Euler_equations_(fluid_dynamics)
Credit: @hadijannat

The source lists the global regularity of smooth solutions to the three-dimensional
incompressible Euler equations as a major open problem in mathematical fluid dynamics.
Because the Wikipedia article covers the general system without fixing boundary conditions
or initial regularity classes, we state the standard full-space reading on `ℝ³ × [0, ∞)`
(matching the inviscid, unforced `ν = 0`, `f = 0` case of `NavierStokes.lean` in
`formal-conjectures`):

* Domain: `ℝ³ × [0, ∞)` where `ℝ³` is `EuclideanSpace ℝ (Fin 3)`.
* Initial velocity `u₀`: smooth (`C^∞`), divergence-free (`∇ · u₀ = 0`), with all spatial
  derivatives decaying faster than any polynomial as `‖x‖ → ∞`.
* Solution `(v, p)`: smooth (`C^∞`) on `ℝ³ × [0, ∞)`, satisfying the incompressible Euler
  equations `∂_t v + (v · ∇) v = -∇ p` and `∇ · v = 0`, initial condition `v(x, 0) = u₀(x)`,
  square-integrability at each `t ≥ 0`, and uniformly bounded kinetic energy across time.
-/

namespace OMA.S_wp_regularity_of_solutions_of_euler_equations

noncomputable section

open MeasureTheory Set InnerProductSpace
open scoped ContDiff

/-- Three-dimensional Euclidean space `ℝ³`. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- Spatial divergence `∇ · v` at `x` as the sum of directional derivatives along the
standard basis vectors. -/
def divergence (v : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => v y i) x (EuclideanSpace.single i 1)

/-- Initial data for the 3D incompressible Euler problem on `ℝ³`: divergence-free,
smooth (`C^∞`), and Schwartz-decaying at spatial infinity. -/
structure InitialVelocityConditionDecay (u₀ : Vec → Vec) : Prop where
  div_free : ∀ x : Vec, divergence u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x : Vec,
    ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- A global smooth finite-energy solution `(v, p)` to the unforced 3D incompressible
Euler equations on `ℝ³ × [0, ∞)` with initial velocity `u₀`. -/
structure EulerGlobalSmoothSolution (u₀ : Vec → Vec)
    (v : Vec → ℝ → Vec) (p : Vec → ℝ → ℝ) : Prop where
  euler : ∀ x : Vec, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) = -gradient (p · t) x
  div_free : ∀ x : Vec, ∀ t ≥ 0, divergence (v · t) x = 0
  initial_condition : ∀ x : Vec, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)
  integrable : ∀ t ≥ 0, MemLp (fun x => ‖v x t‖) 2 (volume : Measure Vec)
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : Vec, ‖v x t‖ ^ 2) < E

theorem main : ∀ u₀ : Vec → Vec, InitialVelocityConditionDecay u₀ →
    ∃ (v : Vec → ℝ → Vec) (p : Vec → ℝ → ℝ), EulerGlobalSmoothSolution u₀ v p := by
  sorry

end

end OMA.S_wp_regularity_of_solutions_of_euler_equations
