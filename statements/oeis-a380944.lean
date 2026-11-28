import Mathlib

/-!
# A380944: a binary recurrence and cumulative Stirling numbers

Source: https://oeis.org/A380944 (Mikhail Kurkov, February 9, 2025).
Credit: @VestigeClub.

A000120 is the number of ones in the binary expansion. The entry defines
b(2r+1,k)=b(r,k)+b(r,k-1), and for positive r and k,
b(2r,k)=(A000120(r)-k+1)*b(2r+1,k), with b(r,0)=1 and b(0,k)=0 for k>0.
The labels T in the two boundary conditions of the comment refer to b, as
confirmed by the entry's PARI program. We substitute the odd equation into
the even equation, so the recursive argument always decreases.

The conjecture includes m=0 and n=0. In c(m,k), the sum is empty when m<k;
`range (m+1-k)` implements this convention, including c(0,0)=1.
The factor A000120(r)-k+1 is computed in the integers.
-/

namespace OMA.S_oeis_a380944

def binaryWeight (n : ℕ) : ℕ := (Nat.digits 2 n).count 1

def b (n k : ℕ) : ℤ :=
  if hk : k=0 then 1
  else if hn : n=0 then 0
  else
    let s := b (n/2) k + b (n/2) (k-1)
    if n%2=1 then s else ((binaryWeight (n/2) : ℤ)-(k : ℤ)+1)*s
termination_by n
decreasing_by all_goals exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

def a (n : ℕ) : ℤ := b n (binaryWeight n)

def c (m k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (m+1-k), Nat.stirlingSecond (k+i) k

theorem main : ∀ m n : ℕ,
    a (2^m*(2^n-1)) = ((n : ℤ)+1)^m - (n : ℤ)*(n.factorial : ℤ)*(c m (n+1) : ℤ) := by
  sorry

end OMA.S_oeis_a380944
