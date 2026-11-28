import Mathlib

/-!
# A colored-partition model for the k-central binomial coefficients

Tewodros Amdeberhan asks for a combinatorial interpretation, for any
positive k. This statement supplies a particular family of objects.
The alphabet consists of ordered pairs of k colors. A word is primitive
when every nonidentity rotation changes at least one letter.

Source: https://mathoverflow.net/questions/257555
-/

namespace OMA.S_mo_257555

open Finset

/-- Number of primitive indexed words of length j+1 on an alphabet of k² letters. -/
def primitiveWords (k j : ℕ) : ℕ :=
  (univ.filter fun w : Fin (j+1) → Fin k × Fin k =>
    ∀ s : Fin (j+1), s ≠ 0 → ∃ i : Fin (j+1), w (i+s) ≠ w i).card

/-- Number of available colors for a part of size j+1. Rotation accounts
for the factor j+1, and translation of the alphabet accounts for k. -/
def colors (k j : ℕ) : ℕ := primitiveWords k j / ((j+1)*k)

/-- An unordered multiset of positive parts totaling n. Each multiplicity
is indexed by the part size and its color. The upper bound n on a
multiplicity follows automatically from total weight n. -/
def ColoredPartition (k n : ℕ) :=
  { a : (j : Fin n) → Fin (colors k j.val) → Fin (n+1) //
    ∑ j : Fin n, (j.val+1) * ∑ c : Fin (colors k j.val), (a j c).val = n }

theorem main : ∀ k n : ℕ, 0 < k →
    n.factorial * Nat.card (ColoredPartition k n) =
      k^n * ∏ m ∈ range n, (1+k*m) := by
  sorry

end OMA.S_mo_257555
