import Mathlib

/-!
# Bass–Quillen conjecture

Source: https://en.wikipedia.org/wiki/Bass–Quillen_conjecture
Credit: @iancbaer

A vector bundle of rank `r` over a commutative ring `R` is a finitely generated projective
`R`-module of constant rank `r`; `Vect_r R` is the set of isomorphism classes of such modules.

Conjecture (Bass–Quillen). Let `A` be a regular Noetherian ring. Then for all `n` and `r` the
assignment `M ↦ M ⊗_A A[t_1, …, t_n]` yields a bijection `Vect_r A → Vect_r A[t_1, …, t_n]`.

Formalization notes.
* `IsRegularRing A` is Mathlib's notion: `A` is Noetherian and its localization at every prime
  ideal is a regular local ring. No finiteness of the Krull dimension is assumed, as in the source.
* Constant rank `r` is `Module.rankAtStalk M p = r` at every prime `p`.
* `A[t_1, …, t_n]` is `MvPolynomial (Fin n) A`.
* The bijection is stated as its two halves. Surjectivity: every rank `r` bundle over the
  polynomial ring is isomorphic to the base change of a rank `r` bundle over `A`. Injectivity:
  two rank `r` bundles over `A` with isomorphic base changes are isomorphic. That the base change
  of a rank `r` bundle is again one is standard and is not part of the statement.
* `A` and the modules live in `Type`; every isomorphism class of finitely generated modules over a
  ring in `Type` has a representative in `Type`.
-/

namespace OMA.S_wp_bass_quillen_conjecture

open TensorProduct

/-- `M` is a vector bundle of rank `r` over `R`: finitely generated, projective, of constant
rank `r`. -/
def IsVectorBundle (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) :
    Prop :=
  Module.Finite R M ∧ Module.Projective R M ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r

theorem main :
    ∀ (A : Type) [CommRing A] [IsRegularRing A] (n r : ℕ),
      (∀ (P : Type) [AddCommGroup P] [Module (MvPolynomial (Fin n) A) P],
        IsVectorBundle (MvPolynomial (Fin n) A) P r →
          ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M), IsVectorBundle A M r ∧
            Nonempty (P ≃ₗ[MvPolynomial (Fin n) A] (MvPolynomial (Fin n) A ⊗[A] M))) ∧
      (∀ (M N : Type) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N],
        IsVectorBundle A M r → IsVectorBundle A N r →
          Nonempty ((MvPolynomial (Fin n) A ⊗[A] M) ≃ₗ[MvPolynomial (Fin n) A]
            (MvPolynomial (Fin n) A ⊗[A] N)) →
          Nonempty (M ≃ₗ[A] N)) := by
  sorry

end OMA.S_wp_bass_quillen_conjecture
