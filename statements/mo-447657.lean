import Mathlib

/-!
# Does going down property imply a corresponding map is open without "finiteness"?

Source: https://mathoverflow.net/questions/447657
Credit: @ivillar

Does the following proposition hold?

Proposition. Let $f : A \to B$ be a ring homomorphism. If $f$ has the going down property then
the corresponding map $f^* : \operatorname{Spec} B \to \operatorname{Spec} A$ is an open map.

(This is known when $A$ is noetherian and $B$ is finitely generated over $A$.)

Formalization notes:
* Rings are commutative with unit, and the ring homomorphism `f` is given as an algebra
  structure `Algebra A B` (so `f = algebraMap A B`).
* The going down property is Mathlib's `Algebra.HasGoingDown A B`.
* `f^*` is `PrimeSpectrum.comap (algebraMap A B)`, with the Zariski topology on both spectra.
* `main` is the proposition asked about, without any finiteness hypothesis.
-/

namespace OMA.S_mo_447657

theorem main : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
    Algebra.HasGoingDown A B → IsOpenMap (PrimeSpectrum.comap (algebraMap A B)) := by
  sorry

end OMA.S_mo_447657
