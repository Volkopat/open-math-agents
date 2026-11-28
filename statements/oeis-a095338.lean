import Mathlib

/-!
# Jovovic's leaf-count formula for OEIS A095338

Source: https://oeis.org/A095338
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A095/A095338.seq
Credit: @sntntHb

OEIS A095338 (offset 1) is the total number of leaves in the labeled graphs of order n,
where a leaf is a vertex of degree 1. The first terms are 0, 2, 12, 96, 1280, 30720.

Conjecture (Vladeta Jovovic, Jan 26 2006, quoted from the entry):
a(n) = n*(n-1)*2^binomial(n-1,2).
Status: the entry reports this as correct (Bertran Steinsky): counting the leaves of all
labeled graphs is the same as counting labeled rooted graphs whose root is a leaf. This file
formalizes the statement and does not supply a Lean proof.

Labeled graphs of order n are the simple graphs on the vertex set Fin n.
-/

namespace OMA.S_oeis_a095338

open Classical

/-- The number of leaves (vertices of degree 1) of a simple graph on Fin n. -/
noncomputable def leaves {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = 1).card

/-- OEIS A095338: the total number of leaves in the labeled graphs of order n. -/
noncomputable def a (n : ℕ) : ℕ := ∑ G : SimpleGraph (Fin n), leaves G

/-- Jovovic's formula, for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = n * (n - 1) * 2 ^ Nat.choose (n - 1) 2 := by
  sorry

end OMA.S_oeis_a095338
