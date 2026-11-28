import Mathlib

/-!
# Irreducibility of the generic Sylvester resultant

Source: Mariano Suárez-Álvarez, https://mathoverflow.net/questions/295178
(CC BY-SA 3.0). François Brunault pointed out the obstruction from a
product of rings in the source comments.
Credit: @connoranderson

The two independent coefficient lists are indexed by a disjoint union.
The specified degree parameters are retained in the Sylvester determinant.
The proposed classification uses connectedness of the prime spectrum,
which includes nonemptiness and hence excludes the zero ring.
-/

namespace OMA.S_mo_295178

noncomputable def withCoefficients {A : Type*} [CommRing A] {d : ℕ}
    (v : Fin (d+1) → A) : Polynomial A :=
  ∑ i, Polynomial.C (v i) * Polynomial.X^i.val

noncomputable def genericResultant (R : Type*) [CommRing R] (r s : ℕ) :
    MvPolynomial (Fin (r+1) ⊕ Fin (s+1)) R :=
  (withCoefficients (fun i : Fin (r+1) => MvPolynomial.X (Sum.inl i))).resultant
    (withCoefficients (fun j : Fin (s+1) => MvPolynomial.X (Sum.inr j))) r s

theorem main : ∀ (R : Type*) [CommRing R] (r s : ℕ), 0 < r → 0 < s →
    (Irreducible (genericResultant R r s) ↔ ConnectedSpace (PrimeSpectrum R)) := by
  sorry

end OMA.S_mo_295178
