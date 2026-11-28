import Mathlib

/-!
# CRIM: every losing partition has even rank

Ina Bašić, Eric Gottlieb and Matjaž Krnc, CRIM: A Natural Game on Integer Partitions,
https://arxiv.org/abs/2606.16828, Conjecture 1 (Section 5), with the definitions of
Sections 2.1, 2.3 and 3.
Credit: @pyaf

A partition is the multiset of its positive parts. A row move deletes one part; a column
move deletes the j-th column of the Young diagram, so every part at least j drops by one.
The game is played under normal play, and each move lowers the number of cells plus the
number of parts, so the set of P-positions is the unique set `P` satisfying `IsPSet`.
Dyson's rank |r - λ₁| is even exactly when the number of parts plus the largest part is.
-/

namespace OMA.S_arxiv_2606_16828

def Move (l m : Multiset ℕ) : Prop :=
  (∃ p ∈ l, m = l.erase p) ∨
    ∃ j, 1 ≤ j ∧ j ≤ l.sup ∧ m = (l.map fun p => if j ≤ p then p - 1 else p).filter (0 < ·)

def IsPSet (P : Set (Multiset ℕ)) : Prop :=
  ∀ l, l ∈ P ↔ ∀ m, Move l m → m ∉ P

theorem main :
    ∀ P : Set (Multiset ℕ), IsPSet P →
      ∀ l : Multiset ℕ, (∀ p ∈ l, 0 < p) → l ∈ P → Even (Multiset.card l + l.sup) := by
  sorry

end OMA.S_arxiv_2606_16828
