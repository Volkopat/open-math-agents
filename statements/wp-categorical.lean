import Mathlib

/-!
# Categorical: categoricity of the class of atomic models in every `ℵ_n`

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics
(linked from https://en.wikipedia.org/wiki/Categorical_(model_theory)), citing J. T. Baldwin,
*Categoricity* (AMS, 2009) and S. Shelah, *Introduction to classification theory for abstract
elementary classes* (arXiv:0903.3428).
Credit: @prasledi

The question: if the class of atomic models of a complete first order theory is categorical in
`ℵ_n` (for every `n < ω`), is it categorical in every cardinal? It is stated in its expected
positive form; a disproof answers it negatively.

## Formalization notes

* As in the cited sources (Baldwin, Ch. on atomic classes; Shelah), the language is countable:
  `L.card ≤ ℵ₀`. The theory `T` is complete in Mathlib's sense (`Theory.IsComplete`).
* A model `M` of `T` is *atomic* if every finite tuple `a` of `M` realizes a principal
  (isolated) type: some formula `φ(x̄)` holds of `a` and implies in `M` every formula `ψ(x̄)` that
  holds of `a`. Since `T` is complete and `M ⊨ T`, "`M ⊨ ∀ x̄, φ → ψ`" is equivalent to
  "`T ⊢ ∀ x̄, φ → ψ`", so this is the usual definition of isolation over `T`.
* As in the sources (and in `OMA.S_wp_aec`), a class is *categorical in `κ`* if it has, up to
  isomorphism, exactly one model of cardinality `κ` (in particular at least one).
* "Categorical in the `ℵ_n`" is read, as in the sources, as categorical in `ℵ_n` for every
  natural number `n`. "Every cardinal" means every infinite cardinal: an atomic model of a theory
  with infinite models is infinite, and the question is about infinite models only.
* The language, the structures and the cardinals live in a fixed universe `w`.
-/

namespace OMA.S_wp_categorical

universe w

open FirstOrder Language Cardinal

/-- `M` is an atomic structure: every finite tuple of `M` realizes an isolated type, i.e. some
formula `φ` true of the tuple implies (in `M`) every formula true of the tuple. -/
def IsAtomicModel (L : FirstOrder.Language.{w, w}) (M : Type w) [L.Structure M] : Prop :=
  ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n), φ.Realize a ∧
    ∀ ψ : L.Formula (Fin n), ψ.Realize a → ∀ b : Fin n → M, φ.Realize b → ψ.Realize b

/-- The class of atomic models of `T` is categorical in `κ`: it has a model of cardinality `κ`,
and any two of its models of cardinality `κ` are isomorphic. -/
def AtomicCategorical {L : FirstOrder.Language.{w, w}} (T : L.Theory) (κ : Cardinal.{w}) :
    Prop :=
  (∃ (M : Type w) (_ : L.Structure M), M ⊨ T ∧ IsAtomicModel L M ∧ #M = κ) ∧
  ∀ (M N : Type w) [L.Structure M] [L.Structure N], M ⊨ T → N ⊨ T →
    IsAtomicModel L M → IsAtomicModel L N → #M = κ → #N = κ → Nonempty (M ≃[L] N)

/-- If the class of atomic models of a complete theory in a countable language is categorical
in `ℵ_n` for every `n`, then it is categorical in every infinite cardinal. -/
theorem main :
    ∀ (L : FirstOrder.Language.{w, w}) (T : L.Theory), L.card ≤ ℵ₀ → T.IsComplete →
      (∀ n : ℕ, AtomicCategorical T (ℵ_ n)) →
      ∀ κ : Cardinal.{w}, ℵ₀ ≤ κ → AtomicCategorical T κ := by
  sorry

end OMA.S_wp_categorical
