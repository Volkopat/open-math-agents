import Mathlib

/-!
# A recurrence for OEIS A099038

Source: https://oeis.org/A099038
Credit: @hermitokatt

The sequence (offset 0): diagonal sums of a Krawtchouk triangle, given in the entry by
`a(n) = Sum_{k=0..floor(n/2)} C(n-k, k) * Sum_{i=0..n} (-1)^i C(k, i) C(n-2k, k-i)`,
used as the definition (`C(m, j) = 0` for `j < 0`). Data: 1, 1, 0, 1, 5, 6, 3, 13, 42, ….

The conjecture (R. J. Mathar, Dec 21 2014):
`n a(n) - n a(n-1) + n a(n-2) + 3(-n+1) a(n-3) + (-5n+13) a(n-4) + (n-3) a(n-5) = 0`.

Reading.
* The recurrence is stated for every `n` for which all six terms are defined, i.e. `n ≥ 5`
  (checked numerically for `5 ≤ n ≤ 39`).
* In the inner sum, `C(k, i) = 0` for `i > k`, so the natural-number subtraction `k - i` is only
  evaluated where it is exact.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a099038

/-- A099038. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((n - k).choose k : ℤ) *
    ∑ i ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ i * (k.choose i : ℤ) * (if i ≤ k then ((n - 2 * k).choose (k - i) : ℤ) else 0)

/-- Mathar's conjectured recurrence, for all `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℤ) * a n - (n : ℤ) * a (n - 1) + (n : ℤ) * a (n - 2) + 3 * (-(n : ℤ) + 1) * a (n - 3) +
      (-5 * (n : ℤ) + 13) * a (n - 4) + ((n : ℤ) - 3) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a099038
