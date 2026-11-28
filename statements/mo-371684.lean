import Mathlib

/-!
# A congruence relation on the projection lattice

Source: https://mathoverflow.net/questions/371684
Asked by MathOverflow user passerby51.

Let `A` be a von Neumann algebra and `P` its lattice of projections. Fix `a ∈ A` and
consider the equivalence relation `p ∼ q` iff `p a = q a`. The question asks whether this
is a lattice congruence on `P`, i.e. whether `p₁ ∼ p₂` and `q₁ ∼ q₂` imply
`p₁ ∨ q₁ ∼ p₂ ∨ q₂` and `p₁ ∧ q₁ ∼ p₂ ∧ q₂`.

Translation choices.
* We formalize the question for the von Neumann algebras `B(H)` with `H` a
  finite-dimensional complex Hilbert space (the matrix algebras). A negative answer for
  these algebras answers the general question negatively.
* The projection lattice of `B(H)` is identified, as usual, with the lattice of (closed)
  subspaces of `H`: the subspace `K` corresponds to the orthogonal projection
  `K.starProjection`, and join and meet of projections correspond to `⊔` and `⊓` of
  subspaces.
* `Rel a K L` is `p a = q a` for the projections `p`, `q` onto `K`, `L`, i.e.
  `K.starProjection (a x) = L.starProjection (a x)` for all `x`.
* `main` is the affirmative answer.
-/

namespace OMA.S_mo_371684

/-- `p ∼ q` iff `p a = q a`, for the orthogonal projections `p`, `q` onto `K`, `L`. -/
def Rel {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (a : H →L[ℂ] H) (K L : Submodule ℂ H) : Prop :=
  ∀ x, K.starProjection (a x) = L.starProjection (a x)

theorem main :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
      (a : H →L[ℂ] H) (K₁ K₂ L₁ L₂ : Submodule ℂ H),
      Rel a K₁ K₂ → Rel a L₁ L₂ → Rel a (K₁ ⊔ L₁) (K₂ ⊔ L₂) ∧ Rel a (K₁ ⊓ L₁) (K₂ ⊓ L₂) := by
  sorry

end OMA.S_mo_371684
