import Mathlib

/-!
# Finiteness of the integers in OEIS A089695

A member is a positive integer such that every way of partitioning its
decimal digits into consecutive nonempty blocks gives a prime sum. A single
block retains the integer, and a partition into single digits gives its
digit sum. Source: https://oeis.org/A089695
-/

namespace OMA.S_oeis_a089695

/-- The value of a decimal block listed from its most significant digit. -/
def blockValue (w : List ℕ) : ℕ := Nat.ofDigits 10 w.reverse

/-- Allow every choice of cuts in the canonical decimal digit string. -/
def allSumsPrime (n : ℕ) : Prop :=
  0 < n ∧ ∀ blocks : List (List ℕ), blocks.flatten = (Nat.digits 10 n).reverse →
    (∀ c ∈ blocks, c ≠ []) → ((blocks.map blockValue).sum).Prime

theorem main : {n : ℕ | allSumsPrime n}.Finite := by
  sorry

end OMA.S_oeis_a089695
