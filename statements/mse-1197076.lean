import Mathlib

/-!
# Quotients of weakly contractible spaces by free group actions

Source: https://math.stackexchange.com/questions/1197076/are-all-quotients-of-a-weakly-contractible-space-via-a-free-group-action-classif
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Question: Given a topological group `G` acting continuously and freely on a
weakly contractible topological space `E` (with no further topological
restrictions on `G` or `E`), is the quotient map `E → E / G` always a locally
trivial principal `G`-bundle? The expected answer is no (e.g. `ℚ` acting on `ℝ` by
translation: `ℝ / ℚ` is indiscrete, and connected `ℝ` is not homeomorphic to `ℝ / ℚ × ℚ`), so
`main` states the negation of the universal claim.

Conventions:
- Weak contractibility of `E` is formalized as `Nonempty E` together with every
  continuous map from the `n`-sphere `S^n` into `E` being nullhomotopic (`n ≥ 0`).
- Local triviality as a principal `G`-bundle requires that every orbit `b ∈ E / G`
  has an open neighborhood `U` and a `G`-equivariant homeomorphism
  `q⁻¹(U) ≃ₜ U × G` commuting with projection to `U`.
-/

namespace OMA.S_mse_1197076

def IsWeaklyContractible (E : Type*) [TopologicalSpace E] : Prop :=
  Nonempty E ∧
  ∀ (n : ℕ) (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, E)),
    ∃ c : E, ContinuousMap.Homotopic f (ContinuousMap.const _ c)

def IsLocallyTrivialPrincipalBundle (G E : Type*) [Group G] [TopologicalSpace G]
    [TopologicalSpace E] [MulAction G E] : Prop :=
  ∀ b : Quotient (MulAction.orbitRel G E),
    ∃ (U : Set (Quotient (MulAction.orbitRel G E))),
      IsOpen U ∧ b ∈ U ∧
      ∃ φ : (Quotient.mk (MulAction.orbitRel G E) ⁻¹' U) ≃ₜ U × G,
        (∀ x, (φ x).1.1 = Quotient.mk (MulAction.orbitRel G E) x.1) ∧
        (∀ (g : G) (x : Quotient.mk (MulAction.orbitRel G E) ⁻¹' U)
          (hx : g • x.1 ∈ Quotient.mk (MulAction.orbitRel G E) ⁻¹' U),
          φ ⟨g • x.1, hx⟩ = ((φ x).1, g * (φ x).2))

theorem main :
    ¬ ∀ (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [TopologicalSpace E] [MulAction G E] [ContinuousSMul G E],
      IsWeaklyContractible E →
      (∀ (g : G) (x : E), g • x = x → g = 1) →
      IsLocallyTrivialPrincipalBundle G E := by
  sorry

end OMA.S_mse_1197076
