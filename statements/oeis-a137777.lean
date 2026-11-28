import Mathlib

/-!
# The Bernoulli derivative row sums of A137777

In the indexing of Mathar's sum from k=0 through n+1, derivative row n
has degree n+1. It is the row of coefficients of 2(n+2)! B_(n+1)(X),
as in the description of Luschny and Pein. Row zero in this convention
is [-2,4]. The optional constant row [2] of the undifferentiated
polynomial family precedes these rows in the flattened OEIS data.

The proposed value is twice A129825(n+2). Its special term A129825(2)
is 1, and its terms m>2 are m! times the ordinary Bernoulli number B_(m−1).
Sources: https://oeis.org/A137777 and https://oeis.org/A129825
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a137777
open Finset

noncomputable def derivativeEntry (n k : ℕ) : ℚ :=
  2 * ((n+2).factorial:ℚ) * (Polynomial.bernoulli (n+1)).coeff k

def targetSequence (m : ℕ) : ℚ :=
  if m=0 then 0 else if m≤2 then 1 else (m.factorial:ℚ)*bernoulli (m-1)

theorem main : ∀ n : ℕ, ∑ k ∈ range (n+2), derivativeEntry n k = 2*targetSequence (n+2) := by
  sorry

end OMA.S_oeis_a137777
