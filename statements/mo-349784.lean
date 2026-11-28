import Mathlib

/-!
# Positive definiteness of intersection matrices of weighted counting measures

Source: https://mathoverflow.net/questions/349784
Asked by MathOverflow user user6671 (Is the matrix mu_f(X_i ∩ X_j) positive definite?).

Let `X_1, ..., X_n` be subsets of a finite set `Z`, let `f : Z → ℝ_{>0}` and let
`μ_f(X) = ∑_{x ∈ X} f x`. The question asks whether the matrix `(μ_f(X_i ∩ X_j))_{i,j}` is
positive definite.

Translation choices.
* `Z` is a finite type, the sets are `X : Fin n → Finset Z`, and `gram f X` is the matrix
  with entries `∑_{x ∈ X i ∩ X j} f x`. Positive definiteness is Mathlib `Matrix.PosDef`.
* To exclude degenerate cases (an empty set gives a zero row, a repeated set gives two equal
  rows), `main` additionally assumes that the sets are nonempty and pairwise distinct.
  These extra hypotheses only make `main` weaker.
-/

namespace OMA.S_mo_349784

/-- The matrix `(μ_f(X_i ∩ X_j))_{i,j}`. -/
def gram {Z : Type} [DecidableEq Z] {n : ℕ} (f : Z → ℝ) (X : Fin n → Finset Z) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ x ∈ X i ∩ X j, f x

theorem main :
    ∀ (Z : Type) [Fintype Z] [DecidableEq Z] (n : ℕ) (f : Z → ℝ), (∀ z, 0 < f z) →
      ∀ X : Fin n → Finset Z, Function.Injective X → (∀ i, (X i).Nonempty) →
        (gram f X).PosDef := by
  sorry

end OMA.S_mo_349784
