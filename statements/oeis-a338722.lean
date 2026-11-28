import Mathlib

/-!
# Row sums of A338721 and partial sums of A335616

The first nonzero entry of column k is in the triangular row 1+...+k.
The column then repeats each odd number k times. Independently, A335616
weights each partition into consecutive parts twice, subtracting one
for a partition containing 1. A partition of length k begins at t+1;
it contains 1 exactly when t=0. At a positive total n one has k≤n and t<n.
Omar E. Pol described the double-staircase interpretations of the two
sequences, and Alois P. Heinz recorded the column formula used here.

https://oeis.org/A338722 · https://oeis.org/A338721 · https://oeis.org/A335616
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a338722

def firstRow (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (i+1)

def column (n k : ℕ) : ℕ :=
  if firstRow k ≤ n then 2*((n-firstRow k)/k)+1 else 0

def partTotal (t k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (t+(i+1))

def weight (n k : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, if partTotal t k = n then (if t = 0 then 1 else 2) else 0

def level (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, weight n (j+1)

def row (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, column n (j+1)

theorem main : ∀ n : ℕ, 0 < n → row n = ∑ j ∈ Finset.range n, level (j+1) := by
  sorry

end OMA.S_oeis_a338722
