import Mathlib

/-!
# A matrix for a product of cross differences

For disjoint nonempty index sets `A` and `B`, user173856 asks for a specific
matrix whose determinant is the product of all `x j - x i` with `i ∈ A` and
`j ∈ B`. Darij Grinberg suggests the Sylvester matrix of the two monic node
polynomials. The first polynomial uses `B`, fixing the sign in the requested
orientation. Repeated values within either individual set are allowed.

Source: https://mathoverflow.net/questions/211338
-/

namespace OMA.S_mo_211338
open Polynomial
open scoped Polynomial

/-- The monic polynomial with the selected nodes as roots, counted with multiplicities. -/
noncomputable def node {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R) (S : Finset (Fin n)) : R[X] :=
  ∏ i ∈ S, (X-C (x i))

/-- The square Sylvester matrix has one block of coefficient shifts for each node polynomial. -/
noncomputable def crossMatrix {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (A B : Finset (Fin n)) : Matrix (Fin (B.card+A.card)) (Fin (B.card+A.card)) R :=
  sylvester (node x B) (node x A) B.card A.card

/-- The determinant is the full cross product. It is nonzero precisely when values from
opposite sets do not coincide. -/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (x : Fin n → R)
    (A B : Finset (Fin n)), A.Nonempty → B.Nonempty → Disjoint A B →
    (crossMatrix x A B).det = ∏ i ∈ A, ∏ j ∈ B, (x j - x i) ∧
      ((crossMatrix x A B).det ≠ 0 ↔ ∀ i ∈ A, ∀ j ∈ B, x i ≠ x j) := by
  sorry

end OMA.S_mo_211338
