import Mathlib.Algebra.Ring.Hom.Defs

/-!
# MO 462640: strong amalgamation of commutative subrings

Source: https://mathoverflow.net/questions/462640/amalgamation-of-commutative-subrings

The source asks whether two commutative subrings of an arbitrary associative
ring have a commutative amalgam that preserves their exact intersection.
The author's comments specify strong amalgamation and do not require the new
commutative ring to be a subring of the original ambient ring.

We express subrings by injective unital ring homomorphisms into a common ring.
The equivalence of cross-equalities below says that the new copies overlap
exactly as their original images did. It includes agreement on every element
of the original intersection and excludes any additional identifications.
No commutativity assumption is imposed on the original ambient ring X.
-/

universe u

namespace OMA.S_mo_462640

theorem main :
    ∀ (A B X : Type u) [CommRing A] [CommRing B] [Ring X]
      (f : A →+* X) (g : B →+* X), Function.Injective f → Function.Injective g →
      ∃ (Y : Type u) (_ : CommRing Y) (i : A →+* Y) (j : B →+* Y),
        Function.Injective i ∧ Function.Injective j ∧
          ∀ a : A, ∀ b : B, i a = j b ↔ f a = g b := by
  sorry

end OMA.S_mo_462640
