import Mathlib

/-!
# Smale's 6th problem: finiteness of central configurations

Source: https://en.wikipedia.org/wiki/Smale%27s_problems
Credit: @pyaf (agent: Claude Code, model claude-opus-5-5)

Source statement (Smale's 6th problem): "Is the number of relative equilibria (central
configurations) finite in the `n`-body problem of celestial mechanics, for any choice of positive
real numbers `m₁, ..., mₙ` as the masses?"

Conventions:
* relative equilibria are the planar central configurations; the plane is `ℂ`, so a
  configuration is `q : Fin n → ℂ`, with no collisions (`q` injective);
* `q` is a central configuration for the masses `m` if, for some `l : ℝ` and every body `i`,
  `∑_{j ≠ i} m_j (q_j - q_i) / |q_j - q_i|³ = l (q_i - c)`, where `c = (∑ m_k q_k) / (∑ m_k)` is
  the centre of mass (Newton's equations with the acceleration proportional to the position
  relative to `c`; for `n ≥ 2` such an `l` is automatically negative);
* configurations are counted up to rotation, scaling and translation, i.e. up to
  `q ↦ a q + b` with `a ∈ ℂ` nonzero and `b ∈ ℂ`; whether reflections are also identified does
  not affect finiteness;
* "finite" means: finitely many configurations `T` represent every central configuration;
* the yes/no question is stated in its expected (affirmative) direction, for every `n`.
-/

namespace OMA.S_wpc_smale_6_central_configurations

open Finset

/-- The centre of mass of the configuration `q` with masses `m`. -/
noncomputable def centreOfMass {n : ℕ} (m : Fin n → ℝ) (q : Fin n → ℂ) : ℂ :=
  (∑ k, m k)⁻¹ • ∑ k, m k • q k

/-- `q` is a (planar, collision-free) central configuration for the masses `m`. -/
def IsCentralConfiguration {n : ℕ} (m : Fin n → ℝ) (q : Fin n → ℂ) : Prop :=
  Function.Injective q ∧ ∃ l : ℝ, ∀ i,
    ∑ j ∈ univ.erase i, (m j / ‖q j - q i‖ ^ 3) • (q j - q i) = l • (q i - centreOfMass m q)

/-- **Smale's 6th problem.** For every `n` and all positive masses, there are only finitely many
central configurations up to rotation, scaling and translation. -/
theorem main : ∀ (n : ℕ) (m : Fin n → ℝ), (∀ i, 0 < m i) →
    ∃ T : Finset (Fin n → ℂ), ∀ q, IsCentralConfiguration m q →
      ∃ p ∈ T, ∃ a b : ℂ, a ≠ 0 ∧ ∀ i, q i = a * p i + b := by
  sorry

end OMA.S_wpc_smale_6_central_configurations
