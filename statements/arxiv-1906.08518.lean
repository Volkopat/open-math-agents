import Mathlib

/-!
# The uniform plane Nagata conjecture in Nivoche's introduction

Source: https://arxiv.org/abs/1906.08518v1, §1.1, p. 2.
Credit: @my-other-github-account (statement only).

For each fixed positive multiplicity, “general” means on a nonempty Zariski open
set of ordered configurations, not merely outside a countable union. Work on the
dense chart Z ≠ 0 and shrink the open to a principal open in the distinct locus.
Every affine equation homogenizes to its total degree; removing line-at-infinity
components in the converse direction only lowers degree and preserves the local
multiplicities. Membership in the l-th power of the point ideal expresses order
at least l. Bounding every such curve is equivalent to bounding the least degree.
This is not a statement about the paper's pluripotential-theoretic conjectures.
Affine point-ideal encoding as in the companion Nagata catalog formalization;
related very-general theorem: openai/math@3344da59991ed94f9ba711217b29c1d760badfa6,
OAI.Nagata.nagata_conjecture. No proof is imported here.
-/
namespace OMA.S_arxiv_1906_08518

abbrev PlanePoly := MvPolynomial (Fin 2) ℂ

noncomputable def pointIdeal (p : Fin 2 → ℂ) : Ideal PlanePoly :=
  Ideal.span (Set.range (fun j : Fin 2 => (MvPolynomial.X j : PlanePoly) - MvPolynomial.C (p j)))

def inOpen {r : ℕ} (G : MvPolynomial (Fin r × Fin 2) ℂ)
    (p : Fin r → Fin 2 → ℂ) : Prop :=
  Function.Injective p ∧ MvPolynomial.eval (fun ij => p ij.1 ij.2) G ≠ 0

theorem main : ∀ r : ℕ, 10 ≤ r → ∀ l : ℕ, 0 < l →
    ∃ G : MvPolynomial (Fin r × Fin 2) ℂ, (∃ p, inOpen G p) ∧
      ∀ p, inOpen G p → ∀ F : PlanePoly, F ≠ 0 → 0 < F.totalDegree →
        (∀ i, F ∈ pointIdeal (p i) ^ l) →
          Real.sqrt (r : ℝ) * (l : ℝ) < (F.totalDegree : ℝ) := by
  sorry

end OMA.S_arxiv_1906_08518
