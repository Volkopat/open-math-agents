import Mathlib

/-!
# Largest parts of consecutive partitions

Every partition into positive consecutive parts has a unique length k
and smallest part t+1. Its sum is the sum of t+1 through t+k, and its
largest part is t+k. For total n>0 both t and k-1 lie in 0,...,n-1.

The other side uses the column definition of A286013. Column k begins
in the triangular row 1+...+k, where it has value k; successive values
k+1,k+2,... occur k rows apart, with zeros in the intervening rows.
Peter Munn described the associated trapezoids in the A286013 entry in 2017.

https://oeis.org/A286015 · https://oeis.org/A286013
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a286015

def partTotal (t k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (t + (i+1))

def firstRow (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (i+1)

def entry (n k : ℕ) : ℕ :=
  if firstRow k ≤ n ∧ k ∣ n - firstRow k then k + (n-firstRow k)/k else 0

theorem main : ∀ n : ℕ, 0 < n →
    (∑ j ∈ Finset.range n, ∑ t ∈ Finset.range n,
      if partTotal t (j+1) = n then t+(j+1) else 0) =
    ∑ j ∈ Finset.range n, entry n (j+1) := by
  sorry

end OMA.S_oeis_a286015
