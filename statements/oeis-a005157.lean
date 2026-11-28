import Mathlib

/-!
# A005157: Number of totally symmetric plane partitions that fit in an n X n X n box.

Source: https://oeis.org/A005157
Credit: @MartinFoxy

The entry carries the comment: Conjectures: if `p == 1 (mod 6)` is prime then
`a(p) == 2^((p+5)/6) (mod p^2)`; if `p == 5 (mod 6)` is prime then
`a(p) == 2^((p+1)/6) (mod p^2)` (checked up to p = 1009).

Formalization notes:
* The sequence has offset 0 and is given by the product formula recorded in its OEIS entry
  (Paul Barry, May 13 2008), which is Stembridge's theorem on totally symmetric plane
  partitions: `a(n) = Product_{i=1..n} Product_{j=i..n} Product_{k=j..n} (i+j+k-1)/(i+j+k-2)`
  (data from n = 0: 1, 2, 5, 16, 66, 352, 2431, 21760, ...).
* The product is computed in `ℚ`; its values are integers. A congruence `x == y (mod p^2)` is
  therefore stated as: `x - y` equals `p^2` times an integer.
* The exponents `(p+5)/6` and `(p+1)/6` are exact integer quotients in the respective residue
  classes, so natural-number division is that quotient.
-/

namespace OMA.S_oeis_a005157

/-- A005157 by the product formula
`a(n) = Product_{1 <= i <= j <= k <= n} (i+j+k-1)/(i+j+k-2)`. -/
def a (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc i n, ∏ k ∈ Finset.Icc j n,
    ((i + j + k : ℚ) - 1) / ((i + j + k : ℚ) - 2)

/-- The two conjectured congruences modulo `p^2`. -/
theorem main :
    (∀ p : ℕ, p.Prime → p % 6 = 1 →
      ∃ m : ℤ, a p - (2 : ℚ) ^ ((p + 5) / 6) = (p : ℚ) ^ 2 * m) ∧
    (∀ p : ℕ, p.Prime → p % 6 = 5 →
      ∃ m : ℤ, a p - (2 : ℚ) ^ ((p + 1) / 6) = (p : ℚ) ^ 2 * m) := by
  sorry

end OMA.S_oeis_a005157
