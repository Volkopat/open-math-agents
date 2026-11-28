import Mathlib

/-!
# A121285: a(0) = 1; for n>0, a(n) = (n+3)*2^(n-2)-n*binomial(n-1, floor( (n-1)/2 ))-(n-1)*binomial(n-2,floor((n-2)/2)).

Source: https://oeis.org/A121285
Credit: @agchua

R. J. Mathar (Jan 04 2017), in the formula section of A121285:
  Conjecture: -(n-1)*(3*n^2-27*n+56)*a(n) +2*(n-5)*(3*n^2-12*n+5)*a(n-1)
  +4*(3*n^3-33*n^2+110*n-118)*a(n-2) -8*(n-3)*(3*n^2-21*n+32)*a(n-3)=0.
The sequence has offset 0. The definition is computed in ℚ, where (n+3)*2^(n-2) is written as
(n+3)*2^n/4 (at n = 1 it is 2, as in the data). For n ≥ 2 the subtractions n-1 and n-2 are exact
and n / 2 is floor division; at n = 1 the last term has the factor n-1 = 0. The recurrence uses
a(n-3), so the conjecture is stated for n ≥ 3.
-/

namespace OMA.S_oeis_a121285

/-- A121285: a(0) = 1 and, for n > 0,
a(n) = (n+3) 2^(n-2) - n C(n-1, floor((n-1)/2)) - (n-1) C(n-2, floor((n-2)/2)). -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else ((n : ℚ) + 3) * 2 ^ n / 4 - (n : ℚ) * ((n - 1).choose ((n - 1) / 2) : ℚ)
    - ((n : ℚ) - 1) * ((n - 2).choose ((n - 2) / 2) : ℚ)

/-- Mathar's conjecture: the order-3 recurrence holds for all n ≥ 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    -((n : ℚ) - 1) * (3 * (n : ℚ) ^ 2 - 27 * (n : ℚ) + 56) * a n
      + 2 * ((n : ℚ) - 5) * (3 * (n : ℚ) ^ 2 - 12 * (n : ℚ) + 5) * a (n - 1)
      + 4 * (3 * (n : ℚ) ^ 3 - 33 * (n : ℚ) ^ 2 + 110 * (n : ℚ) - 118) * a (n - 2)
      - 8 * ((n : ℚ) - 3) * (3 * (n : ℚ) ^ 2 - 21 * (n : ℚ) + 32) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a121285
