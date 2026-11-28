import OMAStatements.S_wp_atiyah_conjecture_on_configurations

-- Reduction wp-atiyah-conjecture-on-configurations.R1 of Atiyah's conjecture on configurations.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 is the collinear case, proved by Atiyah himself (2001): if the n points lie on a line with
-- direction u, every direction from a point is u or -u, so column i is a nonzero multiple of the
-- coefficients of F^(a i) G^(n-1-a i), with F, G the factors of u and -u and a i the number of
-- points beyond point i. The ranks a i are distinct and F, G have distinct roots on the Riemann
-- sphere, so these polynomials are linearly independent. H2 is the open rest: configurations
-- that do not lie on one line.

namespace OMA.R_wp_atiyah_conjecture_on_configurations_R1

open OMA.S_wp_atiyah_conjecture_on_configurations

/-- Atiyah's collinear case: distinct points on a line give a nonsingular matrix. -/
def H1 : Prop :=
  ∀ (n : ℕ) (p : Fin n → Fin 3 → ℝ), Function.Injective p →
    (∃ (c u : Fin 3 → ℝ) (t : Fin n → ℝ), u ≠ 0 ∧ ∀ j, p j = c + t j • u) →
      (configurationMatrix p).det ≠ 0

/-- The open core: configurations of distinct points not all on one line. -/
def H2 : Prop :=
  ∀ (n : ℕ) (p : Fin n → Fin 3 → ℝ), Function.Injective p →
    ¬ (∃ (c u : Fin 3 → ℝ) (t : Fin n → ℝ), u ≠ 0 ∧ ∀ j, p j = c + t j • u) →
      (configurationMatrix p).det ≠ 0

theorem main : H1 → H2 → type_of% @OMA.S_wp_atiyah_conjecture_on_configurations.main := by
  intro h1 h2 n p hp
  by_cases hc : ∃ (c u : Fin 3 → ℝ) (t : Fin n → ℝ), u ≠ 0 ∧ ∀ j, p j = c + t j • u
  · exact h1 n p hp hc
  · exact h2 n p hp hc

end OMA.R_wp_atiyah_conjecture_on_configurations_R1
