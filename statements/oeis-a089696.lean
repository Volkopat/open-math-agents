import Mathlib

/-!
# Finiteness of the integers in OEIS A089696

Partition the ordinary decimal digits into consecutive nonempty blocks.
For every partition, multiply the block values and add one. The question
asks whether only finitely many positive integers always give a prime.
Source: https://oeis.org/A089696
-/

namespace OMA.S_oeis_a089696

/-- Interpret a decimal block written with its most significant digit first. -/
def blockValue (w : List ℕ) : ℕ := Nat.ofDigits 10 w.reverse

/-- Include the unsplit numeral and every possible placement of multiplication signs. -/
def allProductsPrime (n : ℕ) : Prop :=
  0 < n ∧ ∀ blocks : List (List ℕ), blocks.flatten = (Nat.digits 10 n).reverse →
    (∀ c ∈ blocks, c ≠ []) → (((blocks.map blockValue).prod) + 1).Prime

theorem main : {n : ℕ | allProductsPrime n}.Finite := by
  sorry

end OMA.S_oeis_a089696
