import Mathlib

/-!
# Absolute row sums of Mathar's signed Stirling-type triangle

The triangle A159881 has T(n,0)=n+1 and satisfies
T(n,k)=k T(n−1,k)−T(n−1,k−1) for k>0, with zero outside the row.
R. J. Mathar conjectured that its absolute row sums give A029761.

A029761 gives the convolution of the positive integers, starting with
1 at index zero, and the Bell numbers. A Bell number is the sum over
the possible numbers of blocks of the corresponding Stirling numbers.
This also gives the two successive partial sums in the definition via A005001.

Sources: https://oeis.org/A159881, https://oeis.org/A029761, https://oeis.org/A005001
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a159881
open Finset

def triangle : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _+1 => 0
  | n+1, 0 => n+2
  | n+1, k+1 => (k+1:ℤ)*triangle n (k+1)-triangle n k

def bellCount (m : ℕ) : ℕ := ∑ k ∈ range (m+1), Nat.stirlingSecond m k

theorem main : ∀ n : ℕ, ∑ k ∈ range (n+1), (triangle n k).natAbs =
    ∑ m ∈ range (n+1), (n+1-m)*bellCount m := by
  sorry

end OMA.S_oeis_a159881
