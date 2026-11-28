import Mathlib

/-!
# Practical complements in the upper half of an interval

Source: Frank M. Jackson, OEIS A321152 (2018), OEIS Foundation, CC BY-SA 4.0.
Practicality means that every positive integer up to the number is a sum of
distinct positive divisors. Zero is represented by the empty sum.
-/

namespace OMA.S_oeis_a321152

def practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m, m ≤ n → ∃ s : Finset ℕ, s ⊆ n.divisors ∧ m = ∑ i ∈ s, i

def upperPractical (n s : ℕ) : Prop := n ≤ 2*s ∧ s < n ∧ practical s

def isTerm (n : ℕ) : Prop :=
  (∃ s, upperPractical n s) ∧ ∀ s, upperPractical n s → practical (n-s)

theorem main : ∀ n : ℕ, isTerm n ↔
    n ∈ ([2,3,4,5,6,8,10,12,14,16,18,20,24,36,48,60,72,84,96,120] : List ℕ) := by
  sorry

end OMA.S_oeis_a321152
