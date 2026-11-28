import Mathlib

/-!
# Multivariate polynomials over an infinite domain versus polynomial functions

Source: https://mathoverflow.net/questions/381980
Asked by MathOverflow user Michael Orlitzky (Ring isomorphism of multivariate polynomials/functions).

Over an infinite integral domain `R`, the ring `R[X_1]` is isomorphic to the ring of
one-variable polynomial functions `R → R`. The question asks whether, more generally,
`R[X_1, ..., X_n]` is isomorphic to the corresponding ring of polynomial functions
`R^n → R`.

Translation choices.
* `evalHom R n : MvPolynomial (Fin n) R →+* ((Fin n → R) → R)` sends a polynomial `p` to the
  function `x ↦ eval x p`. The ring of polynomial functions `R^n → R` is its range, a subring
  of the ring of all functions.
* `main` asserts that the natural map is an isomorphism onto the ring of polynomial
  functions: there is a ring isomorphism `e` from `MvPolynomial (Fin n) R` onto this subring
  with `e p` equal to the function of `p`, for every infinite integral domain `R` (in `Type`)
  and every `n`.
-/

namespace OMA.S_mo_381980

/-- The ring homomorphism sending a polynomial to its polynomial function. -/
noncomputable def evalHom (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R →+* ((Fin n → R) → R) :=
  RingHom.pi fun x => MvPolynomial.eval x

theorem main :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Infinite R] (n : ℕ),
      ∃ e : MvPolynomial (Fin n) R ≃+* (evalHom R n).range,
        ∀ p, ((e p : (evalHom R n).range) : (Fin n → R) → R) = fun x => MvPolynomial.eval x p := by
  sorry

end OMA.S_mo_381980
