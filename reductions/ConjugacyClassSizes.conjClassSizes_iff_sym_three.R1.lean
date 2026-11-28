import FormalConjectures.Paper.ConjugacyClassSizes
import Mathlib

-- Reduction ConjugacyClassSizes.conjClassSizes_iff_sym_three.R1 of Markel's S_3-conjecture: a finite
-- nontrivial group whose conjugacy classes have pairwise distinct sizes (an anti-homogeneous group)
-- is isomorphic to S_3.
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This is a classical slice, not progress on the conjecture itself. H1 collects the elementary
-- structure every anti-homogeneous group has:
--   * every element x is conjugate to x ^ n for each n coprime to the group order (the classes of
--     x and x ^ n are in bijection, so they have the same size and coincide); in particular every
--     element is conjugate to its inverse;
--   * the center is trivial (a central element is a class of size 1, like the identity);
--   * the order is even: by Burnside's argument, in a group of odd order only the identity is
--     conjugate to its inverse (if c g c⁻¹ = g⁻¹ then c ^ 2 centralises g, and c is a power of c ^ 2
--     when c has odd order, so g = g⁻¹ and g = 1).
-- H2 is the conjecture for groups that have all three properties, which is where every open case
-- lies (Gow's theorem on rational solvable groups and the Zhou-Gorshkov classification apply to it).

namespace OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_R1

open ConjugacyClassSizes

/-- Elementary structure of anti-homogeneous groups: rational, centerless, of even order. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G], HasDistinctConjClassSizes G →
    (∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n)) ∧
    Subgroup.center G = ⊥ ∧ Even (Nat.card G)

/-- The conjecture for rational, centerless anti-homogeneous groups of even order. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G], HasDistinctConjClassSizes G →
    (∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n)) →
    Subgroup.center G = ⊥ → Even (Nat.card G) →
    Nonempty (G ≃* Equiv.Perm (Fin 3))

theorem main : H1 → H2 → type_of% @ConjugacyClassSizes.conjClassSizes_iff_sym_three := by
  intro h1 h2 G _ _ _ h
  obtain ⟨hr, hz, he⟩ := h1 G h
  exact h2 G h hr hz he

end OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_R1
