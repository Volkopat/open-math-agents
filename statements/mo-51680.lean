import Mathlib

/-!
# Amenability of groups in terms of a perturbation condition

Source: https://mathoverflow.net/questions/51680/amenability-of-groups-in-terms-of-a-perturbation-condition
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `G` be a countable group with left-regular representation `λ` on `ℓ²G`. Suppose there is
`C > 0` with `inf {‖T - S‖ : S ∈ λ(G)'} ≤ C · sup_g ‖λ(g) T - T λ(g)‖` for all `T ∈ B(ℓ²G)`.
Question: is `G` amenable? (The converse is easy.) `main` states the affirmative answer.

Encoding: `ℓ²G` is any complex Hilbert space `H` with a Hilbert basis `b` indexed by `G`, and
`λ(g)` is the bounded operator with `λ(g) (b x) = b (g x)` (unitarily equivalent to the
left-regular representation; the condition and the conclusion are invariant). Amenable: there is
a left-invariant finitely additive probability mean on all subsets of `G`.
-/

namespace OMA.S_mo_51680

/-- `G` is amenable: a left-invariant finitely additive mean on all subsets. -/
def Amenable (G : Type*) [Group G] : Prop :=
  ∃ μ : Set G → ℝ, (∀ A, 0 ≤ μ A) ∧ μ Set.univ = 1 ∧
    (∀ A B, Disjoint A B → μ (A ∪ B) = μ A + μ B) ∧
    ∀ (g : G) (A : Set G), μ ((fun x => g * x) '' A) = μ A

/-- The perturbation condition implies amenability. -/
theorem main : ∀ (G : Type) [Group G] [Countable G]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis G ℂ H) (lam : G → H →L[ℂ] H), (∀ g x, lam g (b x) = b (g * x)) →
    (∃ C : ℝ, 0 < C ∧ ∀ T : H →L[ℂ] H,
      Metric.infDist T {S : H →L[ℂ] H | ∀ g, S * lam g = lam g * S} ≤
        C * ⨆ g, ‖lam g * T - T * lam g‖) →
    Amenable G := by
  sorry

end OMA.S_mo_51680
