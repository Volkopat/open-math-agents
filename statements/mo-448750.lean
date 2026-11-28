import Mathlib

/-!
# Orthogonal complement of an arbitrary intersection of closed subspaces

Source: https://mathoverflow.net/questions/448750
Asked by MathOverflow user Nathaël.

Let `H` be a Hilbert space and `𝒞` an arbitrary set of closed subspaces of `H`. The question
asks whether
`(⋂_{Z ∈ 𝒞} Z)^⊥ = closure (∑_{Z ∈ 𝒞} Z^⊥)`,
where the sum consists of the finite sums of elements of the spaces `Z^⊥`, for arbitrary
(countable or uncountable) families `𝒞`.

Translation choices.
* The Hilbert space is a complete inner product space `H` over `𝕜 = ℝ` or `ℂ` (any `RCLike`
  field), and subspaces are `Submodule 𝕜 H`; closedness is closedness of the carrier set.
* The intersection of the family is `sInf 𝒞`, and the space of finite sums of elements of
  the `Z^⊥` is the supremum `⨆ Z ∈ 𝒞, Zᗮ` of submodules; its closure is its
  `topologicalClosure`.
* `main` is the affirmative answer.
-/

namespace OMA.S_mo_448750

theorem main :
    ∀ (𝕜 : Type) [RCLike 𝕜] (H : Type) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [CompleteSpace H] (C : Set (Submodule 𝕜 H)), (∀ Z ∈ C, IsClosed (Z : Set H)) →
      (sInf C)ᗮ = (⨆ Z ∈ C, Zᗮ).topologicalClosure := by
  sorry

end OMA.S_mo_448750
