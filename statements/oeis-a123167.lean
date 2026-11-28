import Mathlib

/-!
# A123167: Continued fraction for c=sqrt(2)*(exp(sqrt(2))+1)/(exp(sqrt(2))-1). a(2*n-1) = 8*n-6, a(2*n) = 4*n-1.

Source: https://oeis.org/A123167
Credit: @xor2k

Formalizes the OEIS A123167 conjecture (Wesley Ivan Hurt, Jul 11 2016):
Conjecture: Numerator of 4/n - 2/n^2.

Conventions:
* Offset 1. The sequence is taken from the explicit formula in the entry's name,
  `a(2*n-1) = 8*n-6` and `a(2*n) = 4*n-1` for `n ≥ 1`, which matches the OEIS data
  2, 3, 10, 7, 18, 11, ... (also the PARI program `(2*n-1) * 2^(n%2)`). The continued-fraction
  description of the constant `c` is not used; the conjecture is the identity between this formula
  and the numerator below.
* For odd `n` the code computes `8 * ((n+1)/2) - 6` and for even `n` it computes `4 * (n/2) - 1`;
  for `n ≥ 1` no truncation occurs.
* Numerator means the numerator `Rat.num` of the reduced rational number `4/n - 2/n^2` in `ℚ`.
-/

namespace OMA.S_oeis_a123167

/-- A123167 via the formula in its name: `a(2n-1) = 8n-6`, `a(2n) = 4n-1` (offset 1). -/
def a (n : ℕ) : ℕ :=
  if n % 2 = 1 then 8 * ((n + 1) / 2) - 6 else 4 * (n / 2) - 1

/-- For every `n ≥ 1`, `a(n)` is the numerator of the reduced fraction `4/n - 2/n^2`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ((4 / n - 2 / n ^ 2 : ℚ).num = a n) := by
  sorry

end OMA.S_oeis_a123167
