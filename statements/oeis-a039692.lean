import Mathlib

/-!
# Row sums in the Jabotinsky triangle A039692

Vladimir Kruchinin's 2013 formula gives the entries as a finite sum of
binomial coefficients and unsigned Stirling numbers of the first kind.
The latter absorb the two sign factors in the published signed formula.
Terms with k<m vanish. At positive n the extension to column m=0 is zero.

Mathar conjectured that the row sums are A005442(n), independently
defined as n! times Fibonacci(n+1), for rows n starting at one.
Sources: https://oeis.org/A039692 and https://oeis.org/A005442
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a039692
open Finset

def entry (n m : ℕ) : ℚ := (n.factorial:ℚ) *
  ∑ k ∈ range (n+1), (Nat.stirlingFirst k m:ℚ)*(k.choose (n-k):ℚ)/k.factorial

theorem main : ∀ n : ℕ, 0<n → ∑ m ∈ range (n+1), entry n m =
    (n.factorial:ℚ)*(Nat.fib (n+1):ℚ) := by
  sorry

end OMA.S_oeis_a039692
