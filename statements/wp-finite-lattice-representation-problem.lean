import Mathlib

/-!
# Finite lattice representation problem

Source: https://en.wikipedia.org/wiki/Finite_lattice_representation_problem
Credit: @shc261392

Question: is every finite lattice isomorphic to the congruence lattice of some finite algebra?

Reading used here:
* An algebra on a carrier `A` is a family of finitary operations `op i : (Fin (ar i) → A) → A`
  indexed by any type `ι`. The algebra is finite when `A` is finite. (On a finite carrier there
  are only finitely many equivalence relations, so the congruence lattice of any family of
  operations is already the congruence lattice of a finite subfamily; allowing any `ι` changes
  nothing.)
* A congruence is an equivalence relation (`Setoid A`) compatible with every operation. The
  congruences, ordered as relations (the order of `Setoid A`), form the congruence lattice;
  a lattice isomorphism is the same as an order isomorphism.
* A finite lattice here is a nonempty finite type with a `Lattice` structure (a congruence
  lattice always contains the equality relation, so the empty lattice is excluded).
* The statement is the affirmative answer; a proof of its negation answers the question in the
  negative.
-/

namespace OMA.S_wp_finite_lattice_representation_problem

/-- `r` is compatible with every operation of the algebra `(A, op)`. -/
def IsCongruence {A ι : Type} (ar : ι → ℕ) (op : ∀ i, (Fin (ar i) → A) → A) (r : Setoid A) :
    Prop :=
  ∀ (i : ι) (x y : Fin (ar i) → A), (∀ j, r (x j) (y j)) → r (op i x) (op i y)

theorem main :
    ∀ (L : Type) [Lattice L] [Finite L] [Nonempty L],
      ∃ (A : Type) (_ : Finite A) (ι : Type) (ar : ι → ℕ) (op : ∀ i, (Fin (ar i) → A) → A),
        Nonempty (L ≃o {r : Setoid A // IsCongruence ar op r}) := by
  sorry

end OMA.S_wp_finite_lattice_representation_problem
