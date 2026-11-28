import Mathlib

/-!
# Existence of perfect cuboids and associated cuboid conjectures

Source: https://en.wikipedia.org/wiki/perfect_cuboid (Euler brick article, section Perfect cuboid)
Credit: @sntntHb

The source: an Euler brick is a rectangular cuboid whose edges and face diagonals all have
integer lengths, and a perfect cuboid (also called a perfect Euler brick or perfect box) is an
Euler brick whose space diagonal also has integer length. The article states that no example of a
perfect cuboid has been found and no one has proven that none exist (unsolved problem box:
Does a perfect cuboid exist?). The associated cuboid conjectures of Sharipov are irreducibility
statements for certain integer polynomials; the article notes they are not equivalent to the
perfect cuboid problem (if all three hold, no perfect cuboid exists). This file formalizes the
central question, the existence of a perfect cuboid.

So the proposition formalized below is: there exist positive integers a, b, c (the edges) such
that a^2 + b^2, a^2 + c^2, b^2 + c^2 (the squared face diagonals) and a^2 + b^2 + c^2 (the
squared space diagonal) are all perfect squares. The statement is posed in its existential form;
a proof of the negation would settle the problem the other way.
-/

namespace OMA.S_wp_existence_of_perfect_cuboids_and_associated_cuboid_conjectures

/-- A perfect cuboid: positive integer edges with integer face diagonals and space diagonal. -/
def IsPerfectCuboid (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
    IsSquare (a ^ 2 + b ^ 2) ∧ IsSquare (a ^ 2 + c ^ 2) ∧ IsSquare (b ^ 2 + c ^ 2) ∧
    IsSquare (a ^ 2 + b ^ 2 + c ^ 2)

/-- Does a perfect cuboid exist? -/
theorem main : ∃ a b c : ℕ, IsPerfectCuboid a b c := by
  sorry

end OMA.S_wp_existence_of_perfect_cuboids_and_associated_cuboid_conjectures
