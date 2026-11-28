import Mathlib

/-!
# Shallow diagonals of the generalized Pascal triangle

A114213 is the parity of a binomial sum restricted to even indices.
A114214 sums the entries in row n-k, column k, for 0 ≤ 2k ≤ n.
The right side is the denominator in the Farey tree on [0,1].
Its root interval has endpoint denominators (1,1). Inserting a mediant
adds the endpoint denominators; the left and right child intervals each
retain their adjacent endpoint. The parameter m numbers the intervals in
heap order from 1. A007306(1) is the initial endpoint denominator 1;
for m ≥ 1, A007306(m+1) is the mediant denominator of interval m.

Conjecture by Georg Fischer. Jeffrey Shallit corrected the diagonal
binomial formula in 2016.
Sources: https://oeis.org/A114214, https://oeis.org/A114213 and https://oeis.org/A007306
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a114214

def parityEntry (a b : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (b+1), if j%2 = 0 then a.choose j * b.choose j else 0) % 2

def diagonal (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n/2+1), parityEntry k (n-2*k)

def edge : (m : ℕ) → ℕ × ℕ
  | 0 => (0,1)
  | n+1 =>
    let p := edge ((n+1)/2)
    if (n+1)%2 = 0 then (p.1,p.1+p.2) else (p.1+p.2,p.2)
termination_by m => m

def fareyDenominator (m : ℕ) : ℕ := (edge m).1 + (edge m).2

theorem main : ∀ n : ℕ, diagonal n = fareyDenominator (n/2) := by
  sorry

end OMA.S_oeis_a114214
