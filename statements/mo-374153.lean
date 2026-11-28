import Mathlib

/-!
# Embedding contractible spaces as convex subsets of topological vector spaces

Source: https://mathoverflow.net/questions/374153
Asked by MathOverflow user Qfwfq.

Given a contractible topological space `X`, is there a continuous embedding
`ι : X ↪ V` into some topological vector space `V` such that `ι(X)` is a convex subset?

Translation choices.
* Topological vector spaces are real: `V` is a real module with a topology making addition
  and scalar multiplication continuous (`IsTopologicalAddGroup V`, `ContinuousSMul ℝ V`).
* An embedding is a `Topology.IsEmbedding` (a homeomorphism onto its image).
* Spaces are taken in `Type`. `main` is the affirmative answer to the first question, for
  every contractible space. The follow-up questions (conditions for existence, the
  metrizable case) are not formalized.
-/

namespace OMA.S_mo_374153

theorem main :
    ∀ (X : Type) [TopologicalSpace X], ContractibleSpace X →
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : TopologicalSpace V)
        (_ : IsTopologicalAddGroup V) (_ : ContinuousSMul ℝ V) (ι : X → V),
        Topology.IsEmbedding ι ∧ Convex ℝ (Set.range ι) := by
  sorry

end OMA.S_mo_374153
