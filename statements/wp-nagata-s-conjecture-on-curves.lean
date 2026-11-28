import Mathlib

/-!
# Nagata's conjecture on curves
Source: https://en.wikipedia.org/wiki/Nagata's_conjecture_on_curves
Credit: @my-other-github-account (catalog statement only).
Prior formalization and proof: openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6,
OAI.Nagata.nagata_conjecture_coordinates. This independent affine-chart statement does not import that proof.
Use the dense chart Z ≠ 0 for all marked points. Discarding the line at infinity as a component
can only decrease degree and does not change multiplicities there. Conversely affine equations
homogenize to their total degree. A countable union of proper hypersurfaces expresses very general:
every proper closed subset of affine space is contained in such a hypersurface.
-/
namespace OMA.S_wp_nagata_s_conjecture_on_curves

abbrev PlanePoly := MvPolynomial (Fin 2) ℂ

noncomputable def pointIdeal (p : Fin 2 → ℂ) : Ideal PlanePoly :=
  Ideal.span (Set.range (fun j : Fin 2 => (MvPolynomial.X j : PlanePoly) - MvPolynomial.C (p j)))

def outside {r : ℕ} (E : ℕ → MvPolynomial (Fin r × Fin 2) ℂ)
    (p : Fin r → Fin 2 → ℂ) : Prop :=
  Function.Injective p ∧ ∀ n, MvPolynomial.eval (fun ij => p ij.1 ij.2) (E n) ≠ 0

theorem main : ∀ r : ℕ, 10 ≤ r →
    ∃ E : ℕ → MvPolynomial (Fin r × Fin 2) ℂ,
      (∀ n, E n ≠ 0) ∧ (∃ p, outside E p) ∧
      ∀ p, outside E p → ∀ F : PlanePoly, F ≠ 0 → 0 < F.totalDegree →
        ∀ m : Fin r → ℕ, (∀ i, F ∈ pointIdeal (p i) ^ m i) →
          (∑ i, (m i : ℝ)) < (F.totalDegree : ℝ) * Real.sqrt (r : ℝ) := by
  sorry

end OMA.S_wp_nagata_s_conjecture_on_curves
