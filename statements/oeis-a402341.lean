import Mathlib

/-!
# A402341: Central (largest) coefficient of (1 + x + x^2 + ... + x^15)^n.

Source: https://oeis.org/A402341
Credit: @ShadowAlzazel

The OEIS name (and the definition of a(n)) is the central, equivalently largest,
coefficient of (1 + x + ⋯ + x^15)^n, with offset 0.

The valuation conjecture is recorded in the Comments section of the same entry
(not in the name, and not in the Formula section):
  Conjecture: for even n, the 2-adic valuation of a(n) equals A000120(15*n/2).
  Verified for n <= 1500.

Formalization.
* `geom16` is the polynomial 1 + X + ⋯ + X^15 over ℕ.
* `a n` is the coefficient of X^{⌊15n/2⌋} in `geom16 ^ n`. For even n the degree 15n
  is even, so this is the unique central coefficient, which is also the largest
  (as in the OEIS name, the example n = 2, and the PARI program on the entry,
  which reads the coefficient of X^{15n/2}). The statement only uses even n.
* `A000120 n` is the 1's-counting sequence (binary weight) of OEIS A000120, encoded
  as the sum of the binary digits of n.
* `main` is the Comments-section conjecture: for every even n (including n = 0),
  ν₂(a(n)) = A000120(15n/2). It does not claim a law at odd n, and it does not
  include the numerical bound n ≤ 1500 as part of the statement.
-/

namespace OMA.S_oeis_a402341

/-- The polynomial `1 + X + ⋯ + X^15`. -/
noncomputable def geom16 : Polynomial ℕ :=
  (Finset.range 16).sum fun k => (Polynomial.X : Polynomial ℕ) ^ k

/-- A402341: the coefficient of `X^{⌊15n/2⌋}` in `(1 + X + ⋯ + X^15)^n`.
For even `n` this is the unique central coefficient. -/
noncomputable def a (n : ℕ) : ℕ :=
  Polynomial.coeff (geom16 ^ n) (15 * n / 2)

/-- A000120, the 1's-counting sequence: the sum of the binary digits of `n`. -/
def A000120 (n : ℕ) : ℕ :=
  (Nat.digits 2 n).sum

/-- Comments-section conjecture on OEIS A402341: for even `n`,
`ν₂(a(n)) = A000120(15n/2)`. -/
theorem main : ∀ n : ℕ, Even n →
    padicValNat 2 (a n) = A000120 (15 * n / 2) := by
  sorry

end OMA.S_oeis_a402341
