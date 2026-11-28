import Mathlib

/-!
# Bouton's three-heap Nim numbers and A063915

A363166 counts unordered losing positions with three positive heaps of
size at most n. By Bouton's criterion their nim-sum is zero. Such heaps
are distinct: two equal heaps would force the third to be zero. With
largest heap z and middle heap y < z, the remaining heap is y XOR z.
It is counted exactly when it is positive and strictly smaller than y.

A063915 has generating function
(1 + Σ_{i≥0} 2^i x^(2^(i+1)-1))/(1-x)^2, starting at index zero.
One division by 1-x gives the numerator's cumulative coefficients:
at degree j-1 this is 1 plus the sum of 2^i for 2^(i+1) ≤ j. Summing
once more gives the coefficient of degree m in the original series.
A000217(n) is the sum of the first n positive integers.

The identity was conjectured by Alan Michael Gómez Calderón in 2025.
Sources: https://oeis.org/A363166 and https://oeis.org/A063915
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a363166
open Finset

def largestHeapCount (z : ℕ) : ℕ :=
  ((range z).filter fun y => 0 < y ^^^ z ∧ y ^^^ z < y).card

def bouton (n : ℕ) : ℕ := ∑ i ∈ range n, largestHeapCount (i+1)

def firstCumulative (j : ℕ) : ℕ :=
  1 + ∑ i ∈ (range j).filter (fun i => 2^(i+1) ≤ j), 2^i

def a063915 (m : ℕ) : ℕ := ∑ i ∈ range (m+1), firstCumulative (i+1)

theorem main : ∀ n : ℕ, 0 < n →
    bouton n = (∑ i ∈ range n, (i+1)) - a063915 (n-1) := by
  sorry

end OMA.S_oeis_a363166
