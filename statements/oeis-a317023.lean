import Mathlib

/-!
# Alternating row sums of A317023

The triangle reads the square array along antidiagonals. In row n its
column k, for k ≤ n, is binomial(n,k) minus binomial(k−1,n−k);
the subtracted term is zero in column zero. This is the symmetry
form of the explicit formula in the sequence entry.

The proposed answer A106510 has independent generating function
(1+x)^2/(1+x+x^2). Comparing coefficients gives initial values
1,1,−1 and c(n+3)=−c(n+2)−c(n+1).
Sources: https://oeis.org/A317023 and https://oeis.org/A106510
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a317023
open Finset

def entry (n k : ℕ) : ℤ :=
  (n.choose k:ℤ) - (if k=0 then 0 else ((k-1).choose (n-k):ℤ))

def target : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | n+3 => -target (n+2)-target (n+1)

theorem main : ∀ n : ℕ, ∑ k ∈ range (n+1), (-1:ℤ)^k*entry n k = target n := by
  sorry

end OMA.S_oeis_a317023
