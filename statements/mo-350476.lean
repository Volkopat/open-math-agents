import Mathlib

/-!
# Upper bound for an expression for distributive lattices

Source: https://mathoverflow.net/questions/350476
Credit: @connoranderson (agent: Codex)

Mare's Question 1 asks whether every finite distributive lattice satisfies
`X_L > 0`. Equivalently, the absolute difference between the two sums of
interval sizes is strictly smaller than the number of join-irreducibles.
The source's Questions 2 and 3 ask separate classification and enumeration
questions. The decidability instances below exist classically for every finite lattice.
-/

namespace OMA.S_mo_350476

variable (L : Type*) [Fintype L] [DistribLattice L] [DecidableEq L] [DecidableLE L]

/-- The join-irreducible elements of the lattice, excluding its bottom element. -/
def joinIrreducibles : Finset L := by
  letI : DecidablePred (SupIrred (α := L)) := fun x => by
    unfold SupIrred IsMin
    infer_instance
  exact Finset.univ.filter SupIrred

/-- The meet-irreducible elements of the lattice, excluding its top element. -/
def meetIrreducibles : Finset L := by
  letI : DecidablePred (InfIrred (α := L)) := fun x => by
    unfold InfIrred IsMax
    infer_instance
  exact Finset.univ.filter InfIrred

/-- Sum of the sizes of the upper intervals of the join-irreducibles. -/
def upperSum : ℕ :=
  ∑ x ∈ joinIrreducibles L, (Finset.univ.filter fun y : L => x ≤ y).card

/-- Sum of the sizes of the lower intervals of the meet-irreducibles. -/
def lowerSum : ℕ :=
  ∑ x ∈ meetIrreducibles L, (Finset.univ.filter fun y : L => y ≤ x).card

/-- Mare's proposed strict bound for every finite bounded distributive lattice. -/
theorem main : ∀ (L : Type) [Fintype L] [DistribLattice L] [BoundedOrder L]
    [DecidableEq L] [DecidableLE L],
    Nat.dist (upperSum L) (lowerSum L) < (joinIrreducibles L).card := by
  sorry

end OMA.S_mo_350476
