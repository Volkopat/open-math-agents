import Mathlib

/-!
# Partitions with a consecutive pair and the multiplicities in A116931

Write a partition with distinct part sizes in increasing order. Store,
for each size, its positive difference from the preceding size (from
zero for the first size) and its positive multiplicity. This is a unique
description: the part sizes are the successive partial sums of the
differences. For a partition of n, there are at most n distinct sizes,
and every stored number is between 1 and n. The finite indices below
store each positive number minus one.

The sum of the parts is the sum of each difference times every
multiplicity at or after its index. Consecutive distinct sizes occur
exactly when a difference after the first one is 1. A116931 instead
requires each multiplicity other than that of the largest size to be
at least 2. A000041 counts all partitions of the same weight.

Václav Kotěšovec conjectured the identity in January 2022.
Sources: https://oeis.org/A237666, https://oeis.org/A116931,
https://oeis.org/A000041
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a237666
open Finset

abbrev Code (n : ℕ) := (k : Fin (n+1)) × (Fin k.val → Fin n × Fin n)

def weight {n : ℕ} (p : Code n) : ℕ :=
  ∑ i : Fin p.1.val, ∑ j : Fin p.1.val,
    if i ≤ j then ((p.2 i).1.val + 1) * ((p.2 j).2.val + 1) else 0

def hasConsecutive {n : ℕ} (p : Code n) : Prop :=
  ∃ i : Fin p.1.val, 0 < i.val ∧ (p.2 i).1.val = 0

def repeats {n : ℕ} (p : Code n) : Prop :=
  ∀ i : Fin p.1.val, i.val+1 < p.1.val → 0 < (p.2 i).2.val

noncomputable def partitions (n : ℕ) : Finset (Code n) := by
  classical exact univ.filter fun p => weight p = n

noncomputable def countWith (n : ℕ) (q : Code n → Prop) : ℕ := by
  classical exact ((partitions n).filter q).card

theorem main : ∀ n : ℕ, 0 < n →
    countWith n hasConsecutive = (partitions n).card - countWith n repeats := by
  sorry

end OMA.S_oeis_a237666
