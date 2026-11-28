import Mathlib

/-!
# Collisions of nonhomogeneous cubics on the integer lattice

The question asks for equal values at distinct integer pairs for a cubic
polynomial that takes integer values on the lattice, in the nonhomogeneous case.

[MathOverflow question](https://mathoverflow.net/questions/392283/cubic-function-mathbbz2-to-mathbbz-cannot-be-injective)
-/

namespace OMA.S_mo_392283

noncomputable def latticeValue (p : MvPolynomial (Fin 2) ℚ) (x : Fin 2 → ℤ) : ℚ :=
  MvPolynomial.eval (fun i => (x i : ℚ)) p

theorem main :
    ∀ p : MvPolynomial (Fin 2) ℚ,
      p.totalDegree = 3 → ¬ p.IsHomogeneous 3 →
      (∀ x : Fin 2 → ℤ, ∃ z : ℤ, latticeValue p x = (z : ℚ)) →
      ∃ x y : Fin 2 → ℤ, x ≠ y ∧ latticeValue p x = latticeValue p y := by
  sorry

end OMA.S_mo_392283
