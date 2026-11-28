import Mathlib

/-!
# OEIS A006012 and permutations avoiding four generalized patterns

David Callan proposed this enumeration in the OEIS entry https://oeis.org/A006012.
Yonah Biers-Ariel proved it in the Journal of Integer Sequences 20 (2017), Article 17.8.3,
https://cs.uwaterloo.ca/journals/JIS/VOL20/Biers/biers3.html.

Credit: @connoranderson
-/

namespace OMA.S_oeis_a006012

/-- The sequence with its original OEIS indexing, starting at index zero. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 4 * a (n + 1) - 2 * a n

/-- The four entries occur in order, with the middle two in consecutive positions. -/
def containsPattern {m : ℕ} (σ : Equiv.Perm (Fin m)) : Prop :=
  ∃ i j k l : Fin m, i < j ∧ (k : ℕ) = (j : ℕ) + 1 ∧ k < l ∧
    max (σ i) (σ k) < min (σ j) (σ l)

/-- With the offset shifted to one, the sequence counts the pattern-avoiding permutations. -/
theorem main : ∀ n : ℕ,
    (Nat.card {σ : Equiv.Perm (Fin (n + 1)) // ¬ containsPattern σ} : ℤ) = a n := by
  sorry

end OMA.S_oeis_a006012
